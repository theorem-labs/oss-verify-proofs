(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA
     W_item_d2i_stmtA W_item_d2i_imgA W_frkitA W_freeStmtB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.




Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.




Definition EMBED_FREE_A : Z := 0x243c58.
Definition PRIM_FREE_A : Z := 0x24446c.

(* [comment removed for export] *)
Lemma embed_free_nullA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo PVAL IT w PB PBn : Z) (POST : machine_state -> Prop),
  stk ctasegs m lo (bv_unsigned sp) -> SHHI <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp + 16 <= USTACK_TOP -> mem_inv ctasegs m ->
  shb_cells ctasegs A_GOT_SHB A_SHB_CELL m ->
  acc ctasegs m PB PBn -> PB <= PVAL -> PVAL + 8 <= PB + PBn -> 0 < PB -> PB + PBn <= lo -> (PB + PBn <= SHLO \/ SHHI <= PB) -> PVAL mod 8 = 0 ->
  rw_cells ctasegs m PVAL [C8 (Z_to_bv 64 0)] ->
  item_cellsA m IT w -> 0 < IT -> IT + 56 <= SHLO -> IT mod 8 = 0 -> bv_unsigned (sx32 (Z_to_bv 64 w)) <> 1 ->
  a0 = wz PVAL -> a1 = wz IT -> a2 = wz 0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
     munch [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' -> stk ctasegs m' lo (bv_unsigned sp) ->
     evt ctasegs POST
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom ctasegs))) ->
  evt ctasegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz EMBED_FREE_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until POST. intros ST SHL LO TOP MI SHB0 ACCP P1 P2 P3 P4 P5 P8 HPV (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT) ITP ITH IT8A W1 -> -> -> KONT.
  unfold EMBED_FREE_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
  unfold SHLO, SHHI, USTACK_TOP in *.
  assert (EPV : bv_unsigned (Z_to_bv 64 PVAL) = PVAL) by (apply unsigned_lit; clear - P1 P2 P3 P4 LO SPR; lia).
  assert (EIT : bv_unsigned (Z_to_bv 64 IT) = IT) by (apply unsigned_lit; clear - ITP ITH; lia).
  assert (OFFW : offshW [(bv_unsigned sp - 160, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - SHL LO; lia).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  hide P5.
  (* [comment removed for export] *)
  carve_frame 128%nat ST. do 15 step. step.
  match goal with MUx : munch _ m ?mc |- _ => destruct (shb_cells_munch _ _ _ _ _ SHB0 MUx ltac:(intros x Hx; unfold A_GOT_SHB, A_SHB_CELL in Hx; cbn [outside]; clear - Hx SHL LO; lia)) as [SB1 SB2] end.
  unfold A_GOT_SHB, A_SHB_CELL in SB1, SB2.
  (* [comment removed for export] *)
  step. step.
  step. if_cases KP; zc KP; [exfalso; rewrite ?EPV in KP; clear - KP P1 P3; lia|]. clear KP.
  (* [comment removed for export] *)
  step. step. rewrite ?EIT. ab_shload 1. step. step. rewrite ?zxb_z8, ?sxb_z8. if_false.
  step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true. step. try if_true.
  (* [comment removed for export] *)
  step. step. step. try if_false. step. step. step. zstep.
  match goal with H : mem_inv ctasegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_embed_freeA mx H) as JT end.
  step. clear JT. rewrite (sx32_small 1904572) by (clear; lia). step. setreg 10 (Z_to_bv 64 0x243dd4) ltac:(reflexivity). step.
  (* [comment removed for export] *)
  step. step. try if_true.
  step. step. step. do 13 step. step. release_frame FR ST (bv_unsigned sp). step.
  (* [comment removed for export] *)
  unfold PRIM_FREE_A. carve_frame 32%nat ST. do 6 step.
  clear SB1 SB2.
  match goal with MUx : munch _ m ?mc |- _ => destruct (shb_cells_munch _ _ _ _ _ SHB0 MUx ltac:(intros x Hx; unfold A_GOT_SHB, A_SHB_CELL in Hx; cbn [outside]; clear - Hx SHL LO; lia)) as [SB1 SB2] end.
  unfold A_GOT_SHB, A_SHB_CELL in SB1, SB2.
  step. step. if_cases KI; zc KI; [exfalso; rewrite ?EIT in KI; clear - KI ITP; lia|]. clear KI.
  step. step. try if_true. step. try if_true.
  (* [comment removed for export] *)
  step. step.
  step. try if_true.
  step. step. step. if_cases KB; zc KB; [exfalso; exact (W1 KB)|]. clear KB.
  step. step. try if_true.
  do 4 step. step. release_frame FR ST (bv_unsigned sp). step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    match goal with MUx : munch _ m mx, WMx : wmono ctasegs m mx, MIx : mem_inv ctasegs mx, STx : stk ctasegs mx lo _ |- _ =>
      eapply KONT; [exact MUx| exact WMx| exact MIx| exact STx] end end.
Qed.

Theorem item_ex_free_null_walkA : item_ex_free_null_specA.
Proof.
  unfold item_ex_free_null_specA. intros until POST. intros ST SHL LO TOP MI SHB0 ACCP P1 P2 P3 P4 P5 P8 HPV ITC ITP ITH IT8A W1 -> -> KONT.
  unfold ITEM_EX_FREE_STACK_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 176, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - SHL LO; lia).
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  name_mem mt.
  match goal with H : munch _ m mt |- _ => rename H into MUt end. match goal with H : wmono ctasegs m mt |- _ => rename H into WMt end.
  match goal with H : mem_inv ctasegs mt |- _ => rename H into MIt end. match goal with H : stk ctasegs mt lo _ |- _ => rename H into STt end.
  pose proof (agree_on_of_munch_nw _ _ _ MUt) as AGt.
  assert (ITO : forall a, IT <= a < IT + 56 -> outside [(bv_unsigned sp - 176, bv_unsigned sp)]%Z a) by (intros a Ha; cbn [outside fst snd]; unfold SHLO, SHHI in *; clear - Ha ITH SHL LO; lia).
  destruct ITC as (I0 & I8 & I8L & I16 & I32 & IA).
  apply (ro_cells_agree _ _ _ _ _ AGt) in I0; [| intros a Ha; cbn in Ha; apply ITO; clear - Ha; lia].
  apply (ro_cells_agree _ _ _ _ _ AGt) in I8; [| intros a Ha; cbn in Ha; apply ITO; clear - Ha; lia].
  apply (ro_cells_agree _ _ _ _ _ AGt) in I8L; [| intros a Ha; cbn in Ha; apply ITO; clear - Ha; lia].
  apply (ro_cells_agree _ _ _ _ _ AGt) in I16; [| intros a Ha; cbn in Ha; apply ITO; clear - Ha; lia].
  apply (ro_cells_agree _ _ _ _ _ AGt) in I32; [| intros a Ha; cbn in Ha; apply ITO; clear - Ha; lia].
  pose proof (acc_munch ctasegs _ m mt IT 56 IA MUt OFFW ltac:(clear - ITP; lia) ltac:(unfold SHLO in *; clear - ITH; lia)) as IA'.
  pose proof (acc_munch ctasegs _ m mt PB PBn ACCP MUt OFFW ltac:(clear - P3; lia) ltac:(unfold SHLO, SHHI, USTACK_TOP in *; clear - P4 LO SPR TOP; lia)) as ACCP'.
  pose proof (shb_cells_munch _ _ _ _ _ SHB0 MUt ltac:(intros x Hx; unfold A_GOT_SHB, A_SHB_CELL in Hx; cbn [outside]; unfold SHLO, SHHI in *; clear - Hx SHL LO; lia)) as SHBt.
  eapply (embed_free_nullA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mt lo PVAL IT w PB PBn POST);
    [exact STt| exact SHL| clear - LO; lia| exact TOP| exact MIt| exact SHBt| exact ACCP'
    | exact P1| exact P2| exact P3| exact P4| exact P5| exact P8| exact HPV
    | split; [exact I0| split; [exact I8| split; [exact I8L| split; [exact I16| split; [exact I32| exact IA']]]]]
    | exact ITP| exact ITH| exact IT8A| exact W1| reflexivity| reflexivity| reflexivity|].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU' WM' MI' ST'.
  eapply KONT; [eapply munch_trans; [exact MUt| eapply munch_weaken; [| exact MU']; intros iv; cbn; clear; lia]| exact (wmono_trans _ _ _ _ WMt WM')| exact MI'| exact ST'].
Qed.
