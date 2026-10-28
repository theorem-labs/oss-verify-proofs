(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit ECH_AC7_rd ECH_AC9_ctrl.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition B64HDR0 : list byte := cells_bytes [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0)].
Lemma B64HDR0_len : length B64HDR0 = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma B64HDR0_cont : map bv_unsigned (firstn 4 (skipn 24 B64HDR0)) = map (fun z => z mod 256) [1; 1 / 256; 1 / 65536; 1 / 16777216].
Proof. vm_compute. reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Lemma b64ctx_fresh_used : forall m C enc junk,
    length junk = 2528%nat -> rw_cells asegs m C (b64ctx_fresh_cells enc junk) -> rw_cells asegs m C (b64ctx_used_cells enc B64HDR0 junk 0).
  Proof.
    intros m C enc junk LJ HB. unfold b64ctx_fresh_cells in HB. unfold b64ctx_used_cells.
    change ([C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)])
      with ([C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0)] ++ [C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)]) in HB.
    apply rw_cells_app in HB. destruct HB as [H1 H2].
    change ([CB 32 B64HDR0; C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)]) with ([CB 32 B64HDR0] ++ [C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)]).
    apply rw_cells_app. split; [| exact H2].
    destruct H1 as [[W B] R]. split; [split|]; [| exact B| exact R]. cbn. split; [exact B64HDR0_len| exact I].
  Qed.
  (* [comment removed for export] *)
  Lemma MEMBIO_sep_hdr : forall mb M fl nf nx pv, MEMBIO_sep mb (mb_with_hdr M fl nf nx pv) = MEMBIO_sep mb M.
  Proof. intros. reflexivity. Qed.
  Lemma MEMBIO_below_hdr : forall mb M fl nf nx pv lo, MEMBIO_below mb (mb_with_hdr M fl nf nx pv) lo = MEMBIO_below mb M lo.
  Proof. intros. reflexivity. Qed.
  Lemma MEMBIO_shad_hdr : forall m mb M fl nf nx pv, MEMBIO_shad m mb (mb_with_hdr M fl nf nx pv) = MEMBIO_shad m mb M.
  Proof. intros. reflexivity. Qed.
  Lemma ACONST_stack_obj2 : forall m m' lo hi a n b k, ACONST m -> munch [(lo, hi); (a, a + n); (b, b + k)] m m' -> wmono asegs m m' -> aceil <= lo ->
    aapp a n -> 0 <= n -> aapp b k -> 0 <= k -> ACONST m'.
  Proof.
    intros m m' lo hi a n b k AC MU WM CE AP NN BP KN. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    constructor; [eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia]|].
    constructor; [eapply aconst_ok_aapp; [exact BP| cbn; lia| cbn; lia]| constructor].
  Qed.
  Lemma blocks_MEMBIO_hdr : forall mb M fl nf nx pv, blocks_MEMBIO mb (mb_with_hdr M fl nf nx pv) = blocks_MEMBIO mb M.
  Proof. intros. reflexivity. Qed.
End HCW.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac if_lit :=
    match goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        tryif (match c with context [?x] => is_var x end) then fail 1 "if_lit: open condition" else
        let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
    end.

  (* [comment removed for export] *)
  Definition bioctrl_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb cmd parg lo : Z) (R : b64frep) (M : membio)
           (hdr junk : list byte) (elen cont : Z),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 parg -> 0 <= parg < 2^64 ->
      rw_cells asegs m a (bio_cells (b64f_bio R)) -> bf_next R = mb -> B64F_blocks H LB a R -> B64F_below a R lo ->
      rw_cells asegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) -> length hdr = 32%nat ->
      map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [cont; cont / 256; cont / 65536; cont / 16777216] ->
      ((cmd = BIO_CTRL_PUSH /\ MEMBIO H LB m mb M /\ MEMBIO_below mb M lo /\ MEMBIO_sep mb M /\ METH_mem m /\ MEMBIO_shad m mb M
        /\ Forall (fun b => a + BIO_SIZE <= blk_addr b \/ blk_addr b + blk_size b <= a) (blocks_MEMBIO mb M))
       \/ (cmd = BIO_CTRL_EOF /\ - 2^31 <= cont <= 0)) ->
      B64F_apart a R -> B64F_shad m a R -> ACONST m -> METH_b64 m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOCTRL_B64_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b64ctrl_rv cmd)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
                   /\ rw_cells asegs m' a (bio_cells (b64f_bio R)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_ctrl) fc None m (seg_rom asegs)).

  Lemma abioctrl_b64_spec : bioctrl_b64_stmt.
  Proof.
    unfold bioctrl_b64_stmt. intros until cont. intros A0 A1 A2 A3 PR BC NX BLK BEL CTX LH CONT CASE APT BSH AC MT ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl in LO.
    unfold P_BIO_ctrl in *. acb.
    assert (CMDR : 0 <= cmd < 7) by (destruct CASE as [(-> & _)|(-> & _)]; unfold BIO_CTRL_EOF, BIO_CTRL_PUSH; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & _ & _ & AAP).
    destruct BEL as (BL1 & BL2 & BL3). pose proof BSH as (SHa & SHc & SHe).
    unfold B64F_apart in APT. unfold BIO_SIZE, B64CTX_SIZE, AIMG_TOP in *.
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & _). unfold AAPP_HI in AHIa.
    assert (ACCa : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SHa| lia| lia| unfold AAPP_HI; lia]).
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 128)]) by nsw_tac.
    (* [comment removed for export] *)
    pose proof MT as MT0. unfold METH_b64, O_METH_BREAD, wz in MT. unfold A_b64_method in MT.
    assert (IN : In (A_b64_method, 112, 112) aglobals) by (unfold A_b64_method; in_nth).
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : id (accessible m A_b64_method 112)).
    { unfold id. eapply addressable_accessible; [exact ADmt| lia| lia| unfold A_b64_method, AAPP_HI; lia]. }
    unfold A_b64_method in ACCmt, ADmt. norm_addr MT.
    hide CTX.
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. rewrite NX in BC.
    carve_frame 96%nat ST.
    do 14 st1. ub_dead.                                                (* [comment removed for export] *)
    do 3 st1. ubal_any. if_lit. do 6 st1.                              (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCa1 : accessible mx a 128) by (unfold id in ACCa; eapply accessible_across2; [exact ACCa| exact MU| exact NSW0]);
      lazymatch type of ACCmt with id (accessible _ ?x ?n) => assert (ACCmt1 : accessible mx x n) by (unfold id in ACCmt; eapply accessible_across2; [exact ACCmt| exact MU| exact NSW0]) end end.
    (* [comment removed for export] *)
    ck8_check ACCa1 (a + 8). do 2 st1. if_lit. do 3 st1. if_lit. do 3 st1.
    (* [comment removed for export] *)
    lazymatch type of ACCmt1 with accessible _ ?x _ => ck8_check_lit ACCmt1 (x + 64) end.
    (* [comment removed for export] *)
    do 2 st1. if_lit. do 3 st1.
    (* [comment removed for export] *)
    ck8_check ACCa1 (a + 16).
    (* [comment removed for export] *)
    do 4 st1. if_lit. do 3 st1.
    (* [comment removed for export] *)
    ck8_check ACCa1 (a + 24).
    (* [comment removed for export] *)
    do 2 st1. if_lit.
    (* [comment removed for export] *)
    ck8_check ACCa1 (a + 8). do 2 st1. if_lit. do 2 st1. if_lit. do 3 st1.
    (* [comment removed for export] *)
    lazymatch type of ACCmt1 with accessible _ ?x _ => ck8_check_lit ACCmt1 (x + 64) end.
    (* [comment removed for export] *)
    do 5 st1. unfold P_b64_ctrl. step.
    eapply evt_cut.
    { eapply (ab64ctrl_spec H) with (lo := lo) (LB := LB) (a := a) (mb := mb) (cmd := cmd) (parg := parg) (R := R) (M := M)
        (hdr := hdr) (junk := junk) (elen := elen) (cont := cont); try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, b64f_bio, wz, A_b64_method; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; rewrite NX; exact BC
           | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unhide CTX; eapply rw_cells_transport; [exact CTX| exact MU| exact WM| cbn; destruct APT as (APT1 & _); unfold BIO_SIZE, B64CTX_SIZE in APT1; lia]
           | |- B64F_blocks _ _ _ _ => exact BLK
           | |- B64F_below _ _ _ => split; [| split]; unfold BIO_SIZE, B64CTX_SIZE; assumption
           | |- length _ = _ => exact LH
           | |- map _ _ = _ => exact CONT
           | |- _ \/ _ => destruct CASE as [(-> & MB & MBL & MSEP & METH & MSH & APM)|(-> & CONTR)];
                          [left| right; split; [reflexivity| exact CONTR]];
                          split; [reflexivity|]; split; [| split; [exact MBL| split; [exact MSEP| split; [| split; [| exact APM]]]]];
                          [ (* [comment removed for export] *)
                            pose proof MBL as (MBL1 & MBL2 & MBL3 & MBL4);
                            pose proof (Forall_inv APM) as APM1; pose proof (Forall_inv (Forall_inv_tail APM)) as APM2;
                            pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3; pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM)))) as APM4;
                            cbn [blk_addr blk_size fst snd] in APM1, APM2, APM3, APM4; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in APM1, APM2, APM3, APM4, MBL1, MBL2, MBL3, MBL4;
                            eapply MEMBIO_frame_disj; [exact MB| exact MU| exact WM| cbn; unfold BIO_SIZE; lia| cbn; unfold BIOBUFMEM_SIZE; lia| cbn; unfold BUFMEM_SIZE; lia| cbn; unfold BUFMEM_SIZE; lia]
                          | eapply METH_mem_frame_disj; [exact METH| exact MU| exact WM| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia]
                          | eapply MEMBIO_shad_across2; [exact MB| exact MSH| exact MU| exact WM| exact NSW0] ]
           | |- 0 <= _ < 2 ^ 64 => exact PR
           | |- B64F_apart _ _ => exact APT
           | |- B64F_below _ _ _ => split; [| split]; assumption
           | |- B64F_shad _ _ _ => split; [| split]; (eapply addressable_across2; [eassumption| | exact MU| exact WM| exact NSW0]);
                                   [exact AAP| destruct RB2 as (_ & _ & _ & _ & _ & _ & K); exact K| destruct RB3 as (_ & _ & _ & _ & _ & _ & K); exact K]
           | |- ACONST _ => eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]
           | |- stk _ _ _ _ => try rewrite unsigned_lit by lia; exact ST
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (unfold B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_b64_ctrl, FR_BIO_ctrl, FR_mem_ctrl; rewrite ?unsigned_lit by lia; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CALL-LEFT:" G end. }
    cbv beta. unfold BIO_SIZE. clear BC. aland_open MU.
    carry1 MUc WMc FR. carry1 MUc WMc GSB. carry1 MUc WMc SHB.
    match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC0 end.
    aland_close MU WM MUc WMc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCa2 : accessible mx a 128) by (unfold id in ACCa; eapply accessible_across2; [exact ACCa| exact MU| exact NSW0]) end.
    (* [comment removed for export] *)
    pose proof BC0 as BC. unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    ck8_check ACCa2 (a + 16). do 3 st1. if_lit. do 3 st1.
    (* [comment removed for export] *)
    ck8_check ACCa2 (a + 24). do 2 st1. if_lit.
    (* [comment removed for export] *)
    do 13 st1. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (eapply ACONST_stack_obj6; [eassumption| exact MU| exact WM| exact CEIL| exact AAP| lia]).
    all: match goal with |- ?G => idtac "END-LEFT:" G end.
  Qed.

  Definition ABP_RA : Z := 0x238f40.   (* [comment removed for export] *)

  Lemma abiopush_spec : biopush_stmt H.
  Proof.
    unfold biopush_stmt. intros until M. intros A0 A1 BF BAP NX0 BEL MB MBL MSEP APT METHB METHM BSH MSH AC ST CEIL LO MI RAE. subst a0 a1.
    pose proof BAP as BAP0. unfold B64F_apart in BAP. pose proof BAP as (BA1 & BA2 & BA3).
    unfold BIOPUSH_STACK, BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_push, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl in LO.
    unfold P_BIO_push in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BF as (BC & (junk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & _ & _ & AAP). pose proof RB2 as (CP & _ & _ & CH & _ & _ & CAP). pose proof RB3 as (EP & _ & _ & EH & _ & _ & EAP).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BSH as (SHa & SHc & SHe).
    pose proof MB as MB0.
    destruct MB0 as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & MAL & _ & MH & _ & _ & MAP). pose proof MBL as (ML1 & ML2 & ML3 & ML4). pose proof MSH as (MSHa & MSHbb & MSHbm & MSHrp).
    (* [comment removed for export] *)
    pose proof (Forall_inv APT) as APT1. pose proof (Forall_inv APT1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APT1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APT1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APT1.
    pose proof (Forall_inv (Forall_inv_tail APT)) as APT2. pose proof (Forall_inv APT2) as DJ_c_mb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APT2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bm, DJ_c_rp. clear APT2.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & _).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_CTRL_PUSH, AIMG_TOP in *.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ MAP) as NSm.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & _). pose proof (aapp_bounds _ _ MAP ltac:(lia)) as (_ & _ & AHIm & _). unfold AAPP_HI in AHIa, AHIm.
    assert (ACCa : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SHa| lia| lia| unfold AAPP_HI; lia]).
    assert (ACCm : id (accessible m mb 128)) by (unfold id; eapply addressable_accessible; [exact MSHa| lia| lia| unfold AAPP_HI; lia]).
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 128); (mb, mb + 128)]) by nsw_tac.
    hide BA2; hide BA3. hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp. hide DJ_c_bm; hide DJ_c_rp. hide SP4; hide SP5; hide SP6.
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128); (mb, mb + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. rewrite NX0, RT0, NR0 in BC.
    unfold bio_cells, membio_bio, wz in MC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in MC.
    unfold A_mem_buf_method in MC. rewrite NUMR in MC.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB. norm_addr METHB.
    pose proof METHM as METHM0. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM. norm_addr METHM.
    unfold b64ctx_fresh_cells, wz in BX. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 4 step. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. st1. st1. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCa1 : accessible mx a 128) by (unfold id in ACCa; eapply accessible_across2; [exact ACCa| exact MU| exact NSW0]);
      assert (ACCm1 : accessible mx mb 128) by (unfold id in ACCm; eapply accessible_across2; [exact ACCm| exact MU| exact NSW0]) end.
    (* [comment removed for export] *)
    step. ubal_by AAL. step. if_lit.
    step. zstep. zstep. zstep. ck8_check ACCa1 (a + 72). st1. step. if_false.
    (* [comment removed for export] *)
    ck8_check ACCa1 (a + 72).
    unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp.
    step.
    hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. ubal_by MAL. step. if_lit.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCm2 : accessible mx mb 128) by (unfold id in ACCm; eapply accessible_across2; [exact ACCm| exact MU| exact NSW0]) end.
    zstep. zstep. zstep. ck8_check ACCm2 (mb + 80).
    step.
    (* [comment removed for export] *)
    step. step. step. unfold P_BIO_ctrl. step.
    eapply evt_cut.
    { eapply abioctrl_b64_spec with (lo := lo) (LB := LB) (a := a) (mb := mb) (cmd := 6) (parg := a)
        (R := bf_with_hdr R (bf_flags R) (bf_retry R) (bf_nread R) mb (bf_prev R)) (M := mb_with_hdr M (mb_flags M) (mb_numf M) (mb_next M) a)
        (hdr := B64HDR0) (junk := junk) (elen := 0) (cont := 1);
        cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, b64f_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
                                       bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_with_hdr]; unfold A_b64_method; rewrite RT0, NR0; exact BC
           | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => apply b64ctx_fresh_used; [exact LJ|]; unfold b64ctx_fresh_cells, wz; exact BX
           | |- B64F_blocks _ _ _ _ => unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; unfold BIO_SIZE, B64CTX_SIZE;
                                    repeat (split; [first [assumption| lia]|]); first [assumption| lia]
           | |- B64F_below _ _ _ => unfold B64F_below, BIO_SIZE, B64CTX_SIZE; cbn [bf_ctx bf_enc bf_with_hdr]; lia
           | |- length _ = _ => exact B64HDR0_len
           | |- map _ _ = _ => exact B64HDR0_cont
           | |- _ \/ _ => left; split; [reflexivity|]; split; [| split; [rewrite MEMBIO_below_hdr; exact MBL| split; [rewrite MEMBIO_sep_hdr; exact MSEP| split; [| split; [rewrite MEMBIO_shad_hdr| rewrite blocks_MEMBIO_hdr; exact (Forall_inv APT)]]]]]
           | |- B64F_apart _ _ => exact BAP0
           | |- B64F_shad _ _ _ => split; [| split]; cbn [bf_ctx bf_enc bf_with_hdr]; (eapply addressable_across2; [eassumption| | exact MU| exact WM| exact NSW0]); [exact AAP| exact CAP| exact EAP]
           | |- ACONST _ => eapply ACONST_stack_obj2; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia| exact MAP| lia]
           | |- METH_b64 _ => unfold METH_b64 in METHB0 |- *; eapply rw_cells_transport; [exact METHB0| exact MU| exact WM| unfold A_b64_method, O_METH_BREAD; cbn; lia]
           | |- stk _ _ _ _ => exact ST
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_b64_ctrl, FR_BIO_ctrl, FR_mem_ctrl; lia); try lia
           end.
      - (* [comment removed for export] *)
        unhide SP4; unhide SP5; unhide SP6.
        membio_tac.
        all: try (unfold bio_cells, membio_bio, wz;
                  cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
                       mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
                  unfold A_mem_buf_method; rewrite ?NUMR; assumption).
        all: match goal with |- ?G => idtac "MB-LEFT:" G end.
      - eapply METH_mem_frame_disj; [exact METHM0| exact MU| exact WM| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia].
      - eapply MEMBIO_shad_across2; [exact MB| exact MSH| exact MU| exact WM| exact NSW0].
      all: match goal with |- ?G => idtac "CTRL-LEFT:" G end. }
    cbv beta. unfold BIO_SIZE. clear BC. unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp. aland_open MU.
    carry1 MUc WMc FR. carry1 MUc WMc BX. carry1 MUc WMc MC. carry1 MUc WMc MBB. carry1 MUc WMc MBM. carry1 MUc WMc MRP. carry1 MUc WMc GSB. carry1 MUc WMc SHB.
    match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC0 end.
    aland_close MU WM MUc WMc. unfold ABP_RA || idtac.
    (* [comment removed for export] *)
    step. step. do 3 st1. step. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. unfold biopush_post.
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split. { eapply ACONST_stack_obj2; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia| exact MAP| lia]. }
    split; [exact ST|].
    split.
    - (* [comment removed for export] *)
      unfold B64F_fresh, B64F_blocks. cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr].
      split; [exact BC0|].
      split. { exists junk. split; [exact LJ|]. unfold b64ctx_fresh_cells, wz. assumption. }
      unfold BIO_SIZE, B64CTX_SIZE. split; [| split; [exact NONL| split; [exact RT0| exact NR0]]].
      repeat (split; [first [assumption| lia]|]). first [assumption| lia].
    - (* [comment removed for export] *)
      clear DJ_a_mb DJ_a_bb DJ_a_bm DJ_a_rp DJ_c_mb DJ_c_bm DJ_c_rp SP1 SP2 SP3 SP4 SP5 SP6 BA1 BA2 BA3 NSa NSm NSW0 APT MSEP BAP BAP0 MU WM.
      membio_tac.
      all: try (unfold bio_cells, membio_bio, wz;
                cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
                     mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
                unfold A_mem_buf_method; rewrite ?NUMR; assumption).
      all: match goal with |- ?G => idtac "MB2-LEFT:" G end.
  Qed.
End S.
