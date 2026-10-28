(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit ECH_AC7_rd.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_C9_ctrl.
Local Abbreviation disjoint_from_above := ECH_C9_ctrl.disjoint_from_above.

(* [comment removed for export] *)
Lemma land64_pos_signed_false : forall c, - 2^31 <= c <= 0 ->
  0 < Z.land c 18446744073709551615 -> Z.land c 18446744073709551615 < 9223372036854775808 -> False.
Proof.
  intros c Hc K0 K1. change 18446744073709551615 with (Z.ones 64) in K0, K1. rewrite Z.land_ones in K0, K1 by lia.
  destruct (Z.eq_dec c 0) as [->|NE]; [cbn in K0; lia|].
  replace (c mod 2 ^ 64) with (c + 2^64) in K0, K1; [lia|].
  symmetry. replace c with ((c + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Lemma MEMBIO_frame_above : forall HI LB m m' a R lo W,
    MEMBIO HI LB m a R -> MEMBIO_below a R lo -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => lo <= fst iv) W -> MEMBIO HI LB m' a R.
  Proof.
    intros HI LB m m' a R lo W MB (B1 & B2 & B3 & B4) MU WM FW.
    destruct MB as (C1 & C2 & C3 & C4 & REST).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    split; [| split; [| split; [| split; [| exact REST]]]];
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]; eapply disjoint_from_above; [exact FW| cbn; lia]).
  Qed.
  Lemma METH_mem_frame_above : forall m m' W,
    METH_mem m -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => aceil <= fst iv) W -> METH_mem m'.
  Proof.
    intros m m' W ME MU WM FW. acb. unfold METH_mem in *. eapply rw_cells_transport; [exact ME| exact MU| exact WM|].
    eapply disjoint_from_above; [exact FW|]. unfold A_mem_buf_method, O_METH_BREAD. cbn. unfold AIMG_TOP in *. lia.
  Qed.
  Lemma MEMBIO_shad_frame_above : forall HI LB m0 m m' a R W,
    MEMBIO HI LB m0 a R -> MEMBIO_shad m a R -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => aceil <= fst iv) W -> MEMBIO_shad m' a R.
  Proof.
    intros HI LB m0 m m' a R W MB SH MU WM FW. eapply MEMBIO_shad_across2; [exact MB| exact SH| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [l h] K; cbn in *. right. pose proof aceil_range. unfold AHI_LO. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma MEMBIO_frame_disj : forall HI LB m m' a R W,
    MEMBIO HI LB m a R -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W a BIO_SIZE -> disjoint_from W (mb_bb R) BIOBUFMEM_SIZE -> disjoint_from W (mb_bm R) BUFMEM_SIZE -> disjoint_from W (mb_rp R) BUFMEM_SIZE ->
    MEMBIO HI LB m' a R.
  Proof.
    intros HI LB m m' a R W MB MU WM D1 D2 D3 D4. destruct MB as (C1 & C2 & C3 & C4 & REST).
    split; [| split; [| split; [| split; [| exact REST]]]]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize buf_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]).
  Qed.
  Lemma METH_mem_frame_disj : forall m m' W,
    METH_mem m -> munch W m m' -> wmono asegs m m' -> disjoint_from W (A_mem_buf_method + O_METH_BREAD) 64 -> METH_mem m'.
  Proof.
    intros m m' W ME MU WM D. unfold METH_mem in *. eapply rw_cells_transport; [exact ME| exact MU| exact WM| exact D].
  Qed.
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
  Local Ltac ubal_any :=
    lazymatch goal with
    | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
        lazymatch R with
        | context [Z.land ?x 7] =>
            first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                  | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                  | idtac ]
        | context [Z.land ?x 3] =>
            first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                  | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                  | match goal with H : _ mod 4 = 0 |- _ => ubal_by H end
                  | idtac ]
        | _ => idtac
        end
    | _ => idtac
    end.

  Definition AB64C_RA1 : Z := 0x556f34.   (* [comment removed for export] *)
  Definition AB64C_RA2 : Z := 0x556f44.   (* [comment removed for export] *)

  Lemma ab64ctrl_spec : b64ctrl_stmt H.
  Proof.
    unfold b64ctrl_stmt. intros until cont. intros A0 A1 A2 A3 PR BC NX BLK BEL CTX LH CONT CASE APT BSH AC ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_b64_ctrl, FR_BIO_ctrl, FR_mem_ctrl in LO.
    unfold P_b64_ctrl in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & _ & _ & AAP). pose proof RB2 as (CP & CAL & _ & CH & _ & _ & CAP).
    destruct BEL as (BL1 & BL2 & BL3). destruct BSH as (SHa & SHc & SHe). destruct APT as (APT1 & APT2 & APT3).
    unfold BIO_SIZE, B64CTX_SIZE, BIO_CTRL_EOF, BIO_CTRL_PUSH, b64ctrl_rv, AIMG_TOP in *.
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ CAP) as NSc.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & _). pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _).
    unfold AAPP_HI in AHIa, AHIc.
    assert (ACCc : id (accessible m (bf_ctx R) 2584)) by (unfold id; eapply addressable_accessible; [exact SHc| lia| lia| unfold AAPP_HI; lia]).
    assert (BOK : bio_ok (b64f_bio R)).
    { unfold bio_ok, b64f_bio; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_b64_method. lia. }
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. rewrite NX in BC.
    unfold b64ctx_used_cells, wz in CTX.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 128)]) by nsw_tac.
    (* [comment removed for export] *)
    carve_frame 128%nat ST. do 15 step.
    (* [comment removed for export] *)
    step. step. step. step. st1. st1. step. step. unfold P_BIO_get_data. step.
    eapply evt_cut.
    { eapply (abiogetdata_spec H) with (B := b64f_bio R) (lo := lo) (x := ASHBASE_CELL); [reflexivity| reflexivity| unfold ASHBASE_CELL; lia| | exact BOK| unfold BIO_SIZE; lia
        | eapply addressable_across2; [exact SHa| exact AAP| exact MU| exact WM| exact NSW0]
        | exact RB1
        | eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| unfold BIOACC_STACK, FR_BIO_set_data; rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      unfold bio_cells, b64f_bio, wz, A_b64_method; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      rewrite NX. exact BC. }
    unfold bioacc_post, BIO_SIZE. clear BC. aland_open MU.
    carry1 MUc WMc FR. carry1 MUc WMc CTX. carry1 MUc WMc GSB. carry1 MUc WMc SHB.
    match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC0 end.
    aland_close MU WM MUc WMc. unfold AB64C_RA1 || idtac.
    cbn [bio_ptr b64f_bio].
    (* [comment removed for export] *)
    step. step. step. unfold P_BIO_next. step.
    eapply evt_cut.
    { eapply (abionext_spec H) with (B := b64f_bio R) (lo := lo) (x := 0); [reflexivity| lia| exact BC0 | exact BOK| unfold BIO_SIZE; lia
        | eapply addressable_across2; [exact SHa| exact AAP| exact MU| exact WM| exact NSW0]
        | exact RB1
        | eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]
        | try rewrite unsigned_lit by lia; exact ST| exact CEIL| unfold BIOACC_STACK, FR_BIO_set_data; try rewrite unsigned_lit by lia; lia| assumption| try rewrite unsigned_lit by lia; reflexivity]. }
    unfold bioacc_post, BIO_SIZE. clear BC0. aland_open MU.
    carry1 MUc WMc FR. carry1 MUc WMc CTX. carry1 MUc WMc GSB. carry1 MUc WMc SHB.
    match goal with X : rw_cells asegs _ a (bio_cells _) |- _ => rename X into BC0 end.
    aland_close MU WM MUc WMc. unfold AB64C_RA2 || idtac.
    cbn [bio_next b64f_bio]. rewrite NX.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step.
    destruct CASE as [(-> & MB & MBL & MSEP & METH & MSH & APM)|(-> & CONTR)].
    - (* [comment removed for export] *)
      pose proof MB as MB0. destruct MB0 as (_ & _ & _ & _ & _ & _ & _ & _ & RBm & RBbb & RBbm & RBrp & _).
      pose proof RBm as (MP & _ & _ & MH & _ & _ & MAP).
      pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv (Forall_inv_tail APM)) as APM2.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM)))) as APM4.
      clear APM. cbn [blk_addr blk_size fst snd] in APM1, APM2, APM3, APM4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in APM1, APM2, APM3, APM4.
      destruct MBL as (MBL1 & MBL2 & MBL3 & MBL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in MBL1, MBL2, MBL3, MBL4.
      step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
      (* [comment removed for export] *)
      zstep. step. step. if_lit. zstep. step. zstep. zstep. st1. zstep. step. step.
      (* [comment removed for export] *)
      step. step. step. step. step. do 13 st1. step. release_frame FR ST (bv_unsigned sp). step. step.
      eapply evt_mono.
      { eapply (abioctrl_mem_spec H) with (lo := lo) (LB := LB) (R := M) (cmd := 6) (larg := 0) (parg := parg) (a := mb); try reflexivity.
        all: try first [right; reflexivity| exact MSEP| exact CEIL| exact RAE].
        all: lazymatch goal with
             | |- MEMBIO _ _ _ _ _ => eapply MEMBIO_frame_disj; [exact MB| exact MU| exact WM| cbn; unfold BIO_SIZE; lia| cbn; unfold BIOBUFMEM_SIZE; lia| cbn; unfold BUFMEM_SIZE; lia| cbn; unfold BUFMEM_SIZE; lia]
             | |- MEMBIO_below _ _ _ => split; [| split; [| split]]; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; assumption
             | |- _ -> METH_mem _ => intros _; eapply METH_mem_frame_disj; [exact METH| exact MU| exact WM| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia]
             | |- MEMBIO_shad _ _ _ => eapply MEMBIO_shad_across2; [exact MB| exact MSH| exact MU| exact WM| exact NSW0]
             | |- ACONST _ => eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]
             | |- stk _ _ _ _ => exact ST
             | |- mem_inv _ _ => assumption
             | |- _ => try (unfold BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl; lia); try lia
             end.
        all: match goal with |- ?G => idtac "PUSH-LEFT:" G end. }
      cbv beta. intros ms' PO. unfold memctrl_post in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & AC2 & ST2 & _).
      unfold mem_ctrl_rv, BIO_CTRL_EOF in *. change (6 =? 2) with false. cbv iota.
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2. split; [reflexivity|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xa Hxa; cbn in Hxa |- *; lia. }
      split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
      eapply rw_cells_transport; [exact BC0| exact MU2| exact WM2| cbn; lia].
    - (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zstep. zstep. step. do 13 st1. step. release_frame FR ST (bv_unsigned sp). step.
        finish.
        all: try (eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]).
        all: match goal with |- ?G => idtac "EOF0-LEFT:" G end.
      + zstep. step. step. if_lit. zstep. step. zstep. zstep. st1. zstep. step. step.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACC24 : accessible mx (bf_ctx R) 2584) by (unfold id in ACCc; eapply accessible_across2; [exact ACCc| exact MU| exact NSW0]) end.
        step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_load ACC24 (bf_ctx R + 24). step. if_false_by (ck1_bnez_false 0 eq_refl).
        (* [comment removed for export] *)
        st1. rewrite (ECH_C9_ctrl.le4_bytes_of_cont _ _ CONT). rewrite sext_extract_le4. rewrite ECH_C9_ctrl.sx32_wz_small by lia.
        step. if_cases K3; zify_cond K3; [| exfalso; exact (land64_pos_signed_false cont CONTR K0 K1)].
        step. do 13 st1. step. release_frame FR ST (bv_unsigned sp). step.
        finish.
        all: try (eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| exact AAP| lia]).
        all: match goal with |- ?G => idtac "EOF-LEFT:" G end.
  Qed.
End S.
