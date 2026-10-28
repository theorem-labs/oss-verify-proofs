(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AC6_acc ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_AC7_rd ECH_AC7_read ECH_AC7_rd2.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma le8_wz_split : forall z, 0 <= z < 2^64 -> le8 (wz z) = le4 (wz z) ++ le4 (wz (Z.shiftr z 32)).
Proof.
  intros z Hz. unfold le8, le4, word_to_le_bytes, wz.
  assert (S32 : 0 <= Z.shiftr z 32 < 2^32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^32) with (2^64). lia. }
  rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. reflexivity.
Qed.
Lemma rw_cells_C8_C4C4 : forall segs m A pre z post, 0 <= z < 2^64 ->
  rw_cells segs m A (pre ++ C8 (wz z) :: post) -> rw_cells segs m A (pre ++ C4 (wz z) :: C4 (wz (Z.shiftr z 32)) :: post).
Proof.
  intros segs m A pre z post Hz [[Hwf Hb] Hw].
  split; [split|].
  - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_wz_split in Hb by exact Hz. rewrite <- app_assoc in Hb. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.

(* [comment removed for export] *)
Section X.
  Context {HCEIL : HeapCeil}.
  Definition winX (A n : Z) (iv : Z * Z) : Prop :=
    snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv \/ sh A + nsh n <= fst iv \/ snd iv <= sh A.
  Lemma disjoint_of_winX : forall W A n, 0 <= A -> 0 <= n -> A + n <= AAPP_HI -> Forall (winX A n) W -> disjoint_from W (sh A) (nsh n).
  Proof.
    intros W A n HA Hn Htop FW.
    assert (S0 : ASHADOW_BASE <= sh A) by (unfold sh; Z.div_mod_to_equations; lia).
    pose proof (sh_nsh_high A n HA Hn Htop) as S1.
    induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. unfold winX in K. cbn in K.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.
  Lemma addressable_acrossX : forall W m m' A n, addressable m A n -> munch W m m' -> wmono asegs m m' ->
    0 <= A -> A + n <= AAPP_HI -> Forall (winX A n) W -> addressable m' A n.
  Proof.
    intros W m m' A n AD MU WM HA Htop FW. eapply addressable_transport; [exact AD| exact MU| exact WM|].
    apply disjoint_of_winX; [exact HA| destruct AD; lia| exact Htop| exact FW].
  Qed.
  (* [comment removed for export] *)
  Definition winH (lo hi : Z) (iv : Z * Z) : Prop :=
    snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv \/ sh (hull_hi hi) <= fst iv \/ snd iv <= sh (hull_lo lo).
  Lemma accessible_acrossX : forall W m m' A n, accessible m A n -> munch W m m' ->
    0 <= n -> Forall (winH A (A + n)) W -> accessible m' A n.
  Proof.
    intros W m m' A n ACC MU Hn FW. pose proof ACC as (Q0 & Q1 & _). eapply accessible_transport; [exact ACC| exact MU|].
    intros x Hx.
    pose proof (hull_lo_le A Q0) as (A1 & A2 & A3). pose proof (hull_hi_ge (A + n) ltac:(lia)) as (B1 & B2 & B3).
    assert (SX : sh (hull_lo A) <= sh x < sh (hull_hi (A + n))) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (S0 : ASHADOW_BASE <= sh (hull_lo A)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi (A + n) <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi (A + n)) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    clear - FW SX S0 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. unfold winH in K. cbn in K.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.
  Lemma shvis_acrossX : forall W m m' lo hi, shvis m lo hi -> munch W m m' -> wmono asegs m m' -> 0 <= lo -> lo <= hi <= AAPP_HI ->
    Forall (winH lo hi) W -> shvis m' lo hi.
  Proof.
    intros W m m' lo hi SV MU WM L0 LH FW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
    pose proof (hull_lo_le lo L0) as (A1 & A2 & A3). pose proof (hull_hi_ge hi ltac:(lia)) as (B1 & B2 & B3).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo lo)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi hi <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi hi) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    clear - FW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K1. unfold winH in K1. cbn in K1.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.
End X.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let HSM0 : stack_malloc_0_stmt H := proj1 (proj2 (proj2 HX)).
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition ABR_SM : Z := 0x237620.    (* [comment removed for export] *)
  Definition ABR_RI : Z := 0x2376c4.    (* [comment removed for export] *)
  Definition ABR_T  : Z := 0x237704.    (* [comment removed for export] *)

  Lemma abioread_mem_spec : bioread_mem_stmt H.
  Proof.
    unfold bioread_mem_stmt. intros until junk; intros A0 A1 A2 OUTL MB BL SEP NM BS LEN OUTC MO SH PAY OSH AC RFS LFN TP THR AWO OIMG FP SPA RL ST CEIL LO MI RAE.
    subst a0 a1 a2.
    unfold P_BIO_read, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_read, FR_bio_read_intern,
      FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, AFS_STACK, AINTRIN_STACK in *. acb.
    pose proof BL as BL0. pose proof SH as SH0. pose proof MO as MO0. pose proof PAY as PAY0. pose proof OSH as OSH0.
    membio_open m a R MB BL SH AC.
    pose proof RB1 as (_ & _ & _ & _ & _ & AFSa & _). pose proof RB2 as (_ & _ & _ & _ & _ & AFSbb & _).
    pose proof RB3 as (_ & _ & _ & _ & _ & AFSbm & _). pose proof RB4 as (_ & _ & _ & _ & _ & AFSrp & _).
    hide AFSa; hide AFSbb; hide AFSbm; hide AFSrp.
    pose proof SEP as SEP0. destruct SEP0 as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6, PS1, PS2, PS3, PS4.
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4.
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    destruct PAY as (PACC & PVIS & PAPP). destruct OSH as (OACC & OVIS & OAPP & OAOK).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    (* [comment removed for export] *)
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
    assert (FO : fsobj H LF out outl) by (destruct AWO as [[W1 _]|(f & IN & W1 & W2)]; [left; cbn [fst snd] in W1; exact W1| right; exists f; cbn [fst snd] in W1, W2; auto]).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    pose proof (munch_refl [(lo, bv_unsigned sp); (out, out + outl); (a, a + 128); (mb_bm R, mb_bm R + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
                          [(lo, bv_unsigned sp); (out, out + outl); (a, a + 128); (mb_bm R, mb_bm R + 32)]) by nsw_tac.
    (* [comment removed for export] *)
    pose proof (ACONST_uar _ AC) as [GUA UAR]. unfold AGOT_UAR, AUAR_CELL, wz in GUA, UAR.
    assert (GFD : rw_cells asegs m 0x5e8630 [C8 (wz P_BIO_read)]).
    { apply relro_cell7; [exact RL| lia| cbn; lia| cbn; repeat split; try exact I; try lia| vm_compute; reflexivity]. }
    unfold P_BIO_read, wz in GFD.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    unfold A_mem_buf_method in BC.
    clear ACCa ACCbb ACCbm ACCrp.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. carve_frame 16%nat ST.
    unhide OUTR. step. st1. do 10 step. step.
    (* [comment removed for export] *)
    zstep.
    rewrite land_m32 by lia.
    remember (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) as sp2 eqn:Hsp2.
    assert (SP2 : bv_unsigned sp - 112 <= sp2 <= bv_unsigned sp - 96 /\ sp2 mod 16 = 0).
    { subst sp2. unhide OUTR. split; [Z.div_mod_to_equations; lia|]. rewrite <- Zminus_mod_idemp_r. Z.div_mod_to_equations. lia. }
    clear Hsp2. destruct SP2 as [SP2 SP2A].
    (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -80).
    destruct (stk_split asegs _ lo sp2 _ ST ltac:(lia)) as [STc STm]. clear ST.
    destruct (stk_split asegs _ sp2 (sp2 + 16) _ STm ltac:(lia)) as [ST2 ST3]. clear STm.
    carve_frame 16%nat ST2. clear ST2. rename STc into ST. rewrite ?Z.add_0_r in FR0.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. st1. rewrite sx32_lit by lia. step. step. step. if_false.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    assert (FWS : Forall (afs_write_ok H LF) [(lo, bv_unsigned sp)]).
    { constructor; [| constructor]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. split; lia. }
    assert (RFS1 : as_RFS H LF m0) by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU0| exact WM| exact FWS]).
    assert (AC1 : ACONST m0) by (eapply ACONST_stack_frame7; [exact AC| exact MU0| exact WM| exact CEIL]).
    assert (THR1 : athr_cells m0) by (eapply athr_cells_frame; [exact THR| exact MU0| exact WM| constructor; [cbn [fst]; lia| constructor]]).
    pose proof HSM0 as SM. unfold stack_malloc_0_stmt, stack_malloc_stmt, AFS_MALLOC_0, AFS_STACK in SM.
    eapply evt_cut.
    { eapply SM with (lo := lo) (LF := LF); clear SM; rewrite ?unsigned_lit by lia;
        [exact RFS1| exact LFN| exact ST| exact CEIL| lia| assumption| exact TP| exact AC1| exact THR1]. }
    clear SM. unfold stack_malloc_post.
    intros ms' PO. change (fsz 0) with 64 in PO. change (fshn 0) with 8 in PO. unfold AFS_STACK, AFS_FLAGS in PO.
    change (Z.to_nat (64 - 40)) with 24%nat in PO. change (Z.to_nat 8) with 8%nat in PO.
    rewrite ?unsigned_lit in PO by lia. revert ms' PO.
    aland_open MU.
    match goal with X : as_RFS H ((0, ?f, ?p) :: LF) ?mx |- _ => rename X into RFS2; rename f into ff; rename p into fp end.
    match goal with X : rw_cells asegs _ ff _ |- _ => rename X into FFR end.
    match goal with X : SHAD _ ff _ |- _ => rename X into SHD end.
    match goal with X : rw_cells asegs _ fp _ |- _ => rename X into FPC end.
    match goal with X : ACONST ?mx, Y : as_RFS H _ ?mx |- _ => rename X into AC2 end.
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS2) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 0) with 64 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    unfold ALOWSH_LO, AHI_LO in NSa, NSbb, NSbm, NSrp. hide NSa; hide NSbb; hide NSbm; hide NSrp. clear SP2A.
    (* [comment removed for export] *)
    pose proof (SHAD_rw_cells _ _ _ SHD) as SHC. change (poison_bytes 8 0) with [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] in SHC. cbn [length] in SHC.
    assert (APff : aapp ff 64) by (clear - FB3 FF5 FF6; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (SHF : ASHADOW_BASE <= sh ff /\ sh ff + 8 < AHI_LO).
    { clear - APff FF1. pose proof (sh_aapp_range ff 64 APff ltac:(lia)) as (Q1 & Q2 & Q3).
      change (nsh 64) with 8 in Q2. split; [unfold sh; Z.div_mod_to_equations; lia| lia]. }
    unfold AHI_LO in SHF.
    rewrite <- (sh_shiftr ff) in SHC, SHF, MUc by lia. rewrite ASHADOW_BASE_val in SHC, SHF, MUc.
    pose proof (aapp_not_shadowland _ _ APff) as NSff. unfold ALOWSH_LO, AHI_LO in NSff.
    (* [comment removed for export] *)
    pose proof OACC as (_ & OHI & _). unfold AAPP_HI in OHI.
    pose proof (fsobj_windows H HH LF out outl 0 ff fp m0 RFS1 FO FRESH ltac:(clear - OUTP; lia) ltac:(clear - OUTL; lia) ltac:(clear - OHI; unfold AAPP_HI; lia)) as (OW1 & OW2 & OW3 & OW4).
    pose proof (fsobj_windows H HH LF (mb_buf R) (mb_len R) 0 ff fp m0 RFS1 FP FRESH ltac:(clear - BUFP; lia) ltac:(clear - LENR; lia) ltac:(clear - BUFH HCEIL; acb; unfold AAPP_HI; lia)) as (PW1 & PW2 & PW3 & PW4).
    assert (FSa : fsobj H LF a 128) by (clear - AFSa; unhide AFSa; apply fsobj_outside; unfold AFS_SIZE in *; lia).
    assert (FSbb : fsobj H LF (mb_bb R) 16) by (clear - AFSbb; unhide AFSbb; apply fsobj_outside; unfold AFS_SIZE in *; lia).
    assert (FSbm : fsobj H LF (mb_bm R) 32) by (clear - AFSbm; unhide AFSbm; apply fsobj_outside; unfold AFS_SIZE in *; lia).
    assert (FSrp : fsobj H LF (mb_rp R) 32) by (clear - AFSrp; unhide AFSrp; apply fsobj_outside; unfold AFS_SIZE in *; lia).
    pose proof (fsobj_windows H HH LF a 128 0 ff fp m0 RFS1 FSa FRESH ltac:(clear - AP; lia) ltac:(clear; lia) ltac:(clear - AHIa; unfold AAPP_HI; lia)) as (AW1 & AW2 & AW3 & AW4).
    pose proof (fsobj_windows H HH LF (mb_bb R) 16 0 ff fp m0 RFS1 FSbb FRESH ltac:(clear - BBP; lia) ltac:(clear; lia) ltac:(clear - AHIbb; unfold AAPP_HI; lia)) as (BBW1 & BBW2 & BBW3 & BBW4).
    pose proof (fsobj_windows H HH LF (mb_bm R) 32 0 ff fp m0 RFS1 FSbm FRESH ltac:(clear - BMP; lia) ltac:(clear; lia) ltac:(clear - AHIbm; unfold AAPP_HI; lia)) as (BMW1 & BMW2 & BMW3 & BMW4).
    pose proof (fsobj_windows H HH LF (mb_rp R) 32 0 ff fp m0 RFS1 FSrp FRESH ltac:(clear - RPP; lia) ltac:(clear; lia) ltac:(clear - AHIrp; unfold AAPP_HI; lia)) as (RPW1 & RPW2 & RPW3 & RPW4).
    change (fsz 0) with 64 in OW1, PW1, AW1, BBW1, BMW1, RPW1. change (fshn 0) with 8 in OW2, PW2, AW2, BBW2, BMW2, RPW2.
    unfold AFS_FLAGS in OW4, PW4, AW4, BBW4, BMW4, RPW4.
    rewrite <- (sh_shiftr ff) in OW2, PW2, AW2, BBW2, BMW2, RPW2 by lia. rewrite ASHADOW_BASE_val in OW2, PW2, AW2, BBW2, BMW2, RPW2.
    hide OW1; hide OW2; hide OW3; hide OW4; hide PW1; hide PW2; hide PW3; hide PW4.
    hide AW1; hide AW2; hide AW3; hide AW4; hide BBW1; hide BBW2; hide BBW3; hide BBW4; hide BMW1; hide BMW2; hide BMW3; hide BMW4; hide RPW1; hide RPW2; hide RPW3; hide RPW4.
    (* [comment removed for export] *)
    unfold in_app_mem, AHI_LO, AAPP_HI in OAPP, PAPP. rewrite ASHADOW_BASE_val in OAPP, PAPP.
    carry1k MUc WMc FR by (clear - FR MUc WMc SP2 LO CEIL ACEILB FB2 FP4 FF6 SHF SPR).
    carry1k MUc WMc FR0 by (clear - FR0 MUc WMc SP2 LO CEIL ACEILB FB2 FP4 FF6 SHF SPR).
    carry1k MUc WMc ST3 by (clear - ST3 MUc WMc SP2 LO CEIL ACEILB FB2 FP4 FF6 SHF SPR).
    carry1k MUc WMc BC by (clear - BC MUc WMc SP2 LO BL1 AW1 AW3 AW4 NSa SHF; unhide AW1; unhide AW3; unhide AW4; unhide NSa).
    carry1k MUc WMc BBC by (clear - BBC MUc WMc SP2 LO BL2 BBW1 BBW3 BBW4 NSbb SHF; unhide BBW1; unhide BBW3; unhide BBW4; unhide NSbb).
    carry1k MUc WMc BMC by (clear - BMC MUc WMc SP2 LO BL3 BMW1 BMW3 BMW4 NSbm SHF; unhide BMW1; unhide BMW3; unhide BMW4; unhide NSbm).
    carry1k MUc WMc RPC by (clear - RPC MUc WMc SP2 LO BL4 RPW1 RPW3 RPW4 NSrp SHF; unhide RPW1; unhide RPW3; unhide RPW4; unhide NSrp).
    carry1k MUc WMc OUTC by (clear - OUTC MUc WMc SP2 LO OUTR OW1 OW3 OW4 OAPP SHF OUTL; unhide OUTR; unhide OW1; unhide OW3; unhide OW4).
    carry1k MUc WMc BS by (clear - BS MUc WMc SP2 LO CEIL BUFH LEN LENR PW1 PW3 PW4 PAPP SHF; unhide PW1; unhide PW3; unhide PW4).
    carry1k MUc WMc MT by (clear - MT MUc WMc SP2 LO CEIL ACEILB FB1 FP1 FF1 SHF).
    carry1k MUc WMc GFD by (clear - GFD MUc WMc SP2 LO CEIL ACEILB FB1 FP1 FF1 SHF).
    hide OAPP; hide PAPP; hide NSff.
    (* [comment removed for export] *)
    lazymatch type of MUc with munch [_; ?w1; ?w2; ?w3; ?w4] _ _ =>
      let T := fresh "MUw" in
      assert (T : munch ((lo, bv_unsigned sp) :: [w1; w2; w3; w4] ++ [(out, out + outl); (a, a + 128); (mb_bm R, mb_bm R + 32)]) m m0)
        by (eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside app] in Hx |- *; tauto);
      clear MU; rename T into MU; cbn [app] in MU
    end.
    aland_close MU WM MUc WMc. unfold ABR_SM || idtac.
    rename ST into ST3. match goal with X : stk _ _ lo sp2 |- _ => rename X into ST end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(lo, bv_unsigned sp); (out, out + outl); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8);
                              (fp, fp + 1); (a, a + 128); (mb_bm R, mb_bm R + 32)] mx) as MU2;
      pose proof (wmono_refl asegs mx) as WM2 end.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    (* [comment removed for export] *)
    unhide OUTR. st1. hide OUTR.
    (* [comment removed for export] *)
    step. step. zstep. zstep. step. zstep. st1. step.
    (* [comment removed for export] *)
    assert (DJf1 : chunk_disj a 128 ff 64) by (clear - AW1; unhide AW1; unfold chunk_disj; lia).
    assert (DJf2 : chunk_disj (mb_bb R) 16 ff 64) by (clear - BBW1; unhide BBW1; unfold chunk_disj; lia).
    assert (DJf3 : chunk_disj (mb_bm R) 32 ff 64) by (clear - BMW1; unhide BMW1; unfold chunk_disj; lia).
    assert (DJf4 : chunk_disj (mb_rp R) 32 ff 64) by (clear - RPW1; unhide RPW1; unfold chunk_disj; lia).
    assert (DJf5 : chunk_disj out (Z.of_nat (cells_size [CB (Z.to_nat outl) junk])) ff 64) by (clear - OW1 OUTL; unhide OW1; unfold chunk_disj; cbn [cells_size csize]; lia).
    assert (DJf6 : chunk_disj (mb_buf R) (Z.of_nat (length ds)) ff 64) by (clear - PW1 LEN; unhide PW1; unfold chunk_disj; lia).
    assert (DJf7 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 ff 64) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJs1 : chunk_disj a 128 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSa SHF; unhide NSa; unfold chunk_disj; lia).
    assert (DJs2 : chunk_disj (mb_bb R) 16 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSbb SHF; unhide NSbb; unfold chunk_disj; lia).
    assert (DJs3 : chunk_disj (mb_bm R) 32 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSbm SHF; unhide NSbm; unfold chunk_disj; lia).
    assert (DJs4 : chunk_disj (mb_rp R) 32 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSrp SHF; unhide NSrp; unfold chunk_disj; lia).
    assert (DJs5 : chunk_disj out (Z.of_nat (cells_size [CB (Z.to_nat outl) junk])) (Z.shiftr ff 3 + 2147450880) 8) by (clear - OAPP SHF OUTL; unhide OAPP; unfold chunk_disj; cbn [cells_size csize]; lia).
    assert (DJs6 : chunk_disj (mb_buf R) (Z.of_nat (length ds)) (Z.shiftr ff 3 + 2147450880) 8) by (clear - PAPP SHF LEN LENR; unhide PAPP; unfold chunk_disj; lia).
    assert (DJs7 : chunk_disj ff 64 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (APfp : aapp fp 1) by (clear - FB3 FP3 FP4; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (DJs8 : chunk_disj fp 1 (Z.shiftr ff 3 + 2147450880) 8) by (clear - APfp SHF; pose proof (aapp_not_shadowland _ _ APfp) as X; unfold ALOWSH_LO, AHI_LO in X; unfold chunk_disj; lia).
    (* [comment removed for export] *)
    st1. st1. st1.
    (* [comment removed for export] *)
    apply (arw_cells_recut _ _ _ [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)]) in SHC; [| cbn; repeat split; exact I| reflexivity].
    step. st1. st1. st1. st1. step. st1. st1. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    zstep. step. step. step. step. unfold P_bio_read_intern. step.
    (* [comment removed for export] *)
    lazymatch type of FFR with rw_cells _ _ ff (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: nil) with ([c0; c1; c2; c3] ++ ([c4] ++ [c5])) in FFR end.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFR. destruct FFR as [FFA FFB]. cbn [cells_size csize Nat.add] in FFB.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFB. destruct FFB as [FFB FFC]. cbn [cells_size csize Nat.add] in FFC.
    pose proof (rw_cells_CB_split _ _ _ _ 8 _ FFB ltac:(lia)) as [RBC FFB']. clear FFB. cbn [Nat.sub] in FFB'.
    apply (rw_cells_CB8_C8 asegs _ _ [] _ []) in RBC. cbn [app] in RBC. unfold wz in RBC.
    replace (ff + Z.of_nat 32 + Z.of_nat 8) with (ff + 40) in FFB' by lia. replace (ff + Z.of_nat 32 + Z.of_nat 24) with (ff + 56) in FFC by lia.
    replace (ff + Z.of_nat 32) with (ff + 32) in RBC by lia.
    lazymatch type of SHC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in SHC end.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in SHC. destruct SHC as [SHA SHB4]. cbn [cells_size csize Nat.add] in SHB4.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in SHB4. destruct SHB4 as [SHB4 SHCr]. cbn [cells_size csize Nat.add] in SHCr.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RACC : accessible mx (ff + 32) 8)
        by (apply acc8_of_C1_7; [unfold sh; rewrite ASHADOW_BASE_val; replace (2147450880 + (ff + 32) / 8) with (Z.shiftr ff 3 + 2147450880 + 4)
                                    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia); exact SHB4
                               | lia| Z.div_mod_to_equations; lia| unfold AAPP_HI; lia]) end.
    (* [comment removed for export] *)
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (fs_scratch_of_fresh H _ _ _ _ FRESH))))) as SC4.
    change (fshn 0) with 8 in SC4.
    pose proof (fsobj_scratch_hull H HH _ _ _ _ _ RFS1 FO ltac:(clear - OUTP; lia) ltac:(clear - OUTL; lia) ltac:(clear - OHI; unfold AAPP_HI; lia) SC4) as OWH.
    pose proof (fsobj_scratch_hull H HH _ _ _ _ _ RFS1 FP ltac:(clear - BUFP; lia) ltac:(clear - LENR; lia) ltac:(clear - BUFH ACEILB; unfold AAPP_HI; lia) SC4) as PWH.
    cbn [fst snd] in OWH, PWH. rewrite <- (sh_shiftr ff) in OWH, PWH by lia. rewrite ASHADOW_BASE_val in OWH, PWH. hide OWH; hide PWH. clear SC4.
    pose proof (aapp_not_shadowland _ _ FB3) as NSfs. unfold ALOWSH_LO, AHI_LO, AFS_SIZE in NSfs. hide NSfs.
    (* [comment removed for export] *)
    Local Ltac win8 NSfs NSff OAPP t5 t7 t8 :=
      repeat apply Forall_cons; try apply Forall_nil; unfold winX, winH; cbn [fst snd]; unfold AHI_LO; rewrite ?ASHADOW_BASE_val;
      [> lia | unhide NSfs; lia | unhide NSfs; lia | unhide NSff; lia | t5 | unhide OAPP; lia | t7 | t8 ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (SHX : MEMBIO_shad mx a R) end.
    { clear - SHa SHbb SHbm SHrp MU WM AP BBP BMP RPP AHIa AHIbb AHIbm AHIrp ACEILB CEIL LO NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF AW2 BBW2 BMW2 RPW2 OAPP NSa NSbb NSbm NSrp.
      unfold MEMBIO_shad, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. split; [| split; [| split]].
      - eapply addressable_acrossX; [exact SHa| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win8 NSfs NSff OAPP ltac:(unhide AW2; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia).
      - eapply addressable_acrossX; [exact SHbb| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win8 NSfs NSff OAPP ltac:(unhide BBW2; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia).
      - eapply addressable_acrossX; [exact SHbm| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win8 NSfs NSff OAPP ltac:(unhide BMW2; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia).
      - eapply addressable_acrossX; [exact SHrp| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win8 NSfs NSff OAPP ltac:(unhide RPW2; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (PAYX : PAYLOAD_shad mx R) end.
    { clear - PACC PVIS PAPP MU WM BUFP BUFH LENR ACEILB CEIL LO NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF PWH OAPP NSa NSbm.
      split; [| split; [| unhide PAPP; exact PAPP]].
      - eapply accessible_acrossX; [exact PACC| exact MU| lia|]. win8 NSfs NSff OAPP ltac:(unhide PWH; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia).
      - eapply shvis_acrossX; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win8 NSfs NSff OAPP ltac:(unhide PWH; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (OUTX : OUT_shad mx out outl) end.
    { clear - OACC OVIS OAPP OAOK OHI MU WM OUTP OUTL ACEILB CEIL LO NSfs NSff FB1 FB2 FP3 FP4 FF5 FF6 SHF OWH NSa NSbm.
      split; [| split; [| split; [unhide OAPP; exact OAPP| exact OAOK]]].
      - eapply accessible_acrossX; [exact OACC| exact MU| lia|]. win8 NSfs NSff OAPP ltac:(unhide OWH; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia).
      - eapply shvis_acrossX; [exact OVIS| exact MU| exact WM| lia| unfold AAPP_HI; lia|]. win8 NSfs NSff OAPP ltac:(unhide OWH; lia) ltac:(unhide NSa; lia) ltac:(unhide NSbm; lia). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RSHX : RB_shad mx (ff + 32)) end.
    { split; [exact RACC| split]; [eapply aapp_in_app_mem; [exact APff| lia| lia]| eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia]]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (ACX : ACONST mx) end.
    { clear - AC2 MU2 WM2 OAOK APff APfp AAP BMAP ACEILB CEIL LO FF1 FF5 FB1 SHF HCEIL.
      eapply ACONST_frame; [exact AC2| exact MU2| exact WM2|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - exact OAOK.
      - eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; change (12599296 / 8) with 1574912;
          rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
      - eapply aconst_ok_aapp; [exact APfp| cbn; lia| cbn; lia].
      - eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia].
      - eapply aconst_ok_aapp; [exact BMAP| cbn; lia| cbn; lia]. }
    (* [comment removed for export] *)
    pose proof (areadintern_mem_spec H HH) as RIS. unfold readintern_mem_stmt, readintern_mem_stmt_at, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK,
      FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_BIO_eof, AINTRIN_STACK, P_bio_read_intern in RIS.
    eapply evt_cut.
    { eapply RIS with (lo := lo) (R := R) (LB := LB) (junk := junk); clear RIS;
        [reflexivity| reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL0| exact SEP| unfold METH_mem, O_METH_BREAD, A_mem_buf_method; exact MT
        | exact BS| exact LEN| exact OUTC| | first [clear - FF64; lia | clear - FF8; lia]| exact RBC| | unhide OW1; clear - OW1; lia
        | exact SHX| exact PAYX| exact OUTX| exact RSHX| exact ACX
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      - unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTR; unhide OUTB; unhide OF1; unhide OF2; unhide OF3; unhide OF4; unhide OUTM.
        clear - OUTR OUTB OF1 OF2 OF3 OF4 OUTM OUTP OUTH SP2.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| split; [lia| unfold A_mem_buf_method, O_METH_BREAD; lia]].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil.
      - unfold memrd_out. rewrite unsigned_lit by lia. unhide AW1; unhide BBW1; unhide BMW1; unhide RPW1; unhide PW1.
        clear - AW1 BBW1 BMW1 RPW1 PW1 FF1 FF5 FB1 FF6 FB2 CEIL ACEILB.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| split; [lia| unfold A_mem_buf_method, O_METH_BREAD; lia]].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil. }
    clear RIS. intros ms' PO. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in PO. revert ms' PO.
    aland_open MU.
    pose proof MUc as MUc2. pose proof WMc as WMc2. extm MU2 WM2 MUc2 WMc2.
    carry1k MUc WMc FR by (clear - FR MUc WMc SP2 LO OUTR BL1 BL3 FF6 FB2 CEIL SPR; unhide OUTR).
    carry1k MUc WMc FR0 by (clear - FR0 MUc WMc SP2 LO OUTR BL1 BL3 FF6 FB2 CEIL SPR; unhide OUTR).
    carry1k MUc WMc ST3 by (clear - ST3 MUc WMc SP2 LO OUTR BL1 BL3 FF6 FB2 CEIL SPR; unhide OUTR).
    carry1k MUc WMc FFA by (clear - FFA MUc WMc OW1 AW1 BMW1 FF6 FB2 CEIL LO SP2; unhide OW1; unhide AW1; unhide BMW1).
    carry1k MUc WMc FFB' by (clear - FFB' MUc WMc OW1 AW1 BMW1 FF6 FB2 CEIL LO SP2; unhide OW1; unhide AW1; unhide BMW1).
    carry1k MUc WMc FFC by (clear - FFC MUc WMc OW1 AW1 BMW1 FF6 FB2 CEIL LO SP2; unhide OW1; unhide AW1; unhide BMW1).
    carry1k MUc WMc SHA by (clear - SHA MUc WMc SHF ACEILB CEIL LO SP2 OAPP NSff NSa NSbm; unhide OAPP; unhide NSff; unhide NSa; unhide NSbm).
    carry1k MUc WMc SHB4 by (clear - SHB4 MUc WMc SHF ACEILB CEIL LO SP2 OAPP NSff NSa NSbm; unhide OAPP; unhide NSff; unhide NSa; unhide NSbm).
    carry1k MUc WMc SHCr by (clear - SHCr MUc WMc SHF ACEILB CEIL LO SP2 OAPP NSff NSa NSbm; unhide OAPP; unhide NSff; unhide NSa; unhide NSbm).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FP4 FB2 CEIL LO SP2 OW3 AW3 BMW3; unhide OW3; unhide AW3; unhide BMW3).
    aland_close MU WM MUc WMc. unfold ABR_RI || idtac.
    try rename ST into STx. match goal with X : stk _ _ lo sp2 |- _ => rename X into ST end. try rename STx into ST3.
    match goal with X : MEMBIO H LB _ a _ |- _ => destruct X as (BC3 & BBC3 & BMC3 & RPC3 & _) end.
    unfold bio_cells, membio_bio, buf_cells, mb_after_read, mb_advance, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC3, BBC3, BMC3, RPC3.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC3, BBC3, BMC3, RPC3.
    match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTCf end.
    match goal with X : rw_cells asegs _ (ff + 32) _ |- _ => rename X into RBCf end.
    match goal with X : bytes_at asegs _ (mb_buf _) ds |- _ => cbn [mb_buf mb_after_read mb_advance] in X; rename X into BSf end.
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (clear - OUTL POSR LENR; unfold mb_rdn, mb_avail in *; lia).
    (* [comment removed for export] *)
    evar (TGT : machine_state).
    eapply evt_cut with (P := fun msx => msx = TGT).
    { unfold rd_ok. destruct (Z.eq_dec (mb_rdn R outl) 0) as [KN|KN].
      2: { replace (0 <? mb_rdn R outl) with true by (symmetry; apply Z.ltb_lt; lia). step. if_false.
           apply (rw_cells_C8_C4C4 asegs _ _ [] (mb_rdn R outl) [] ltac:(lia)) in RBCf. cbn [app] in RBCf.
           st1. rewrite sx32_lit by lia. step. apply evt_done. subst TGT. reflexivity. }
      replace (0 <? mb_rdn R outl) with false by (symmetry; apply Z.ltb_ge; lia). step. if_true. apply evt_done.
      rewrite <- KN. reflexivity. }
    subst TGT. cbv beta. intros ms' ->.
    (* [comment removed for export] *)
    lazymatch type of SHA with rw_cells _ ?mx ?A ?csA =>
    lazymatch type of SHB4 with rw_cells _ _ _ ?csB =>
    lazymatch type of SHCr with rw_cells _ _ _ ?csC =>
      assert (SHC : rw_cells asegs mx A (csA ++ csB ++ csC))
        by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact SHA|]; apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact SHB4| exact SHCr]);
      clear SHA SHB4 SHCr; cbn [app] in SHC
    end end end.
    (* [comment removed for export] *)
    assert (DJt1 : chunk_disj ff 32 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt2 : chunk_disj (ff + 40) 16 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt3 : chunk_disj (ff + 56) 8 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJt4 : chunk_disj (ff + 32) 8 (Z.shiftr ff 3 + 2147450880) 8) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJu1 : chunk_disj a 128 ff 32) by (clear - AW1; unhide AW1; unfold chunk_disj; lia).
    assert (DJu2 : chunk_disj (mb_bb R) 16 ff 32) by (clear - BBW1; unhide BBW1; unfold chunk_disj; lia).
    assert (DJu3 : chunk_disj (mb_bm R) 32 ff 32) by (clear - BMW1; unhide BMW1; unfold chunk_disj; lia).
    assert (DJu4 : chunk_disj (mb_rp R) 32 ff 32) by (clear - RPW1; unhide RPW1; unfold chunk_disj; lia).
    assert (DJu5 : chunk_disj (mb_buf R) (Z.of_nat (length ds)) ff 32) by (clear - PW1 LEN; unhide PW1; unfold chunk_disj; lia).
    assert (DJu6 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 ff 32) by (clear - NSff SHF; unhide NSff; unfold chunk_disj; lia).
    assert (DJv1 : chunk_disj a 128 fp 1) by (clear - AW3; unhide AW3; unfold chunk_disj; lia).
    assert (DJv2 : chunk_disj (mb_bb R) 16 fp 1) by (clear - BBW3; unhide BBW3; unfold chunk_disj; lia).
    assert (DJv3 : chunk_disj (mb_bm R) 32 fp 1) by (clear - BMW3; unhide BMW3; unfold chunk_disj; lia).
    assert (DJv4 : chunk_disj (mb_rp R) 32 fp 1) by (clear - RPW3; unhide RPW3; unfold chunk_disj; lia).
    assert (DJv5 : chunk_disj (mb_buf R) (Z.of_nat (length ds)) fp 1) by (clear - PW3 LEN; unhide PW3; unfold chunk_disj; lia).
    assert (DJv6 : chunk_disj (Z.shiftr ff 3 + 2147450880) 8 fp 1) by (clear - DJs8; unfold chunk_disj in *; lia).
    (* [comment removed for export] *)
    assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
    { clear - NR LEN POSR LENR OUTL. unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
    rewrite SL in OUTCf.
    unhide OAPP; unhide OW1; unhide OW3.
    step. st1. step. zstep. st1. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. step.
    hide OAPP; hide OW1; hide OW3.
    (* [comment removed for export] *)
    zstep. do 10 st1. step. step.
    (* [comment removed for export] *)
    release_frame FR0 ST (sp2 + 16).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (STm : stk asegs mx lo (bv_unsigned sp + -80)) by (eapply stk_merge; [exact ST| exact ST3| lia]) end.
    clear ST ST3. rename STm into ST. release_frame FR ST (bv_unsigned sp).
    apply evt_done.
    exists [(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8)].
    split.
    { pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FS4. change (fsz 0) with 64 in FS4. change (fshn 0) with 8 in FS4. unfold AFS_FLAGS in FS4.
      rewrite <- (sh_shiftr ff) in FS4 by lia. rewrite ASHADOW_BASE_val in FS4. exact FS4. }
    split.
    { unfold memrd_post. do 15 eexists. eexists. split; [reflexivity|].
      split; [cbn [app]; unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split. { clear - AC2 MU2 WM2 OAOK APff APfp AAP BMAP ACEILB CEIL LO FF1 FF5 FB1 SHF HCEIL.
               eapply ACONST_frame; [exact AC2| exact MU2| exact WM2|].
               repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
               - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
               - exact OAOK.
               - eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia].
               - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; change (12599296 / 8) with 1574912;
                   rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
               - eapply aconst_ok_aapp; [exact APfp| cbn; lia| cbn; lia].
               - eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia].
               - eapply aconst_ok_aapp; [exact BMAP| cbn; lia| cbn; lia]. }
      split; [exact ST|].
      split. { pose proof (clr_flags_facts (mb_flags R) FLR RDO AEOF) as (FL1 & FL2 & FL3). membio_tac. }
      split; [exact BSf|].
      split; [rewrite <- ?SL in OUTCf; exact OUTCf| exact I]. }
    split.
    { (* [comment removed for export] *)
      rewrite <- (lf_remove_head 0 ff fp LF).
      eapply (ah_release H HH); [exact RFS2| left; reflexivity| exact MU2| exact WM2| |].
      - unhide AFSa; unhide AFSbm; unhide NSfs. clear - AWO AFSa AFSbm AH BMH NSfs SHF FB1 FB2 FP3 FP4 FF5 FF6 ACEILB CEIL LO.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; cbn [fst snd] in *.
        + left. left. lia.
        + left. destruct AWO as [A|(f & IN & B)]; [left; exact A| right; exists f; split; [right; exact IN| exact B]].
        + left. right. exists (0, ff, fp). split; [left; reflexivity|]. cbn. change (fsz 0) with 64. lia.
        + left. left. lia.
        + right. split; reflexivity.
        + left. left. lia.
        + left. left. lia.
      - destruct FPC as [[_ (B0 & B1 & B2)] _]. specialize (B2 0%nat ltac:(cbn; lia)). cbn in B2. rewrite Z.add_0_r in B2. exact B2. }
    (* [comment removed for export] *)
    eapply arelro_across7; [exact RL| exact MU|].
    clear - OIMG AH BMH FB1 FP3 FF5 SHF ACEILB CEIL. unfold AIMG_TOP in *.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
  Qed.
End S.
