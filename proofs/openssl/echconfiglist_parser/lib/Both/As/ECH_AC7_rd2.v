(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AC6_acc ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_AC7_rd ECH_AC7_read.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land_clr7_id : forall x, 0 <= x < 2^31 -> Z.land x 128 = 0 -> Z.land x 18446744073709551487 = x.
Proof.
  intros x Hx H7. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 7) as [->|NE].
  - apply (f_equal (fun z => Z.testbit z 7)) in H7. rewrite Z.land_spec, Z.bits_0 in H7. change (Z.testbit 128 7) with true in H7.
    rewrite Bool.andb_true_r in H7. rewrite H7. reflexivity.
  - destruct (Z.lt_ge_cases n 64) as [L|L].
    + replace (Z.testbit 18446744073709551487 n) with true; [apply Bool.andb_true_r|].
      symmetry. change 18446744073709551487 with (Z.lor (Z.ones 7) (Z.shiftl (Z.ones 56) 8)).
      rewrite Z.lor_spec. destruct (Z.lt_ge_cases n 7) as [L7|L7].
      * rewrite Z.ones_spec_low by lia. reflexivity.
      * rewrite Z.shiftl_spec, (Z.ones_spec_low 56) by lia. apply Bool.orb_true_r.
    + assert (LG : Z.log2 x <= 30) by (change 30 with (Z.log2 2147483647); apply Z.log2_le_mono; lia).
      rewrite (Z.bits_above_log2 x n) by lia. reflexivity.
Qed.


Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac nzal X := rewrite ?v_sltu_b2z, ?v_sltiu_b2z; rewrite ?(unsigned_lit 0) by lia; rewrite ?(unsigned_lit X) by lia; rewrite (proj2 (Z.ltb_lt 0 X)) by lia; if_lit.
  (* [comment removed for export] *)
  Local Ltac aconst_of AC MU WM :=
    eapply ACONST_frame; [exact AC| exact MU| exact WM|];
    repeat (apply Forall_cons;
            [cbn [fst snd]; first [ assumption
                                  | apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia
                                  | match goal with X : aapp ?A ?n |- _ => eapply (aconst_ok_aapp A n _ _ X); cbn; lia end ] |]);
    apply Forall_nil.

  Definition ABR_RA1 : Z := 0x23970c.   (* [comment removed for export] *)
  Definition ABR_RA2 : Z := 0x23977c.   (* [comment removed for export] *)

  Lemma abreadconv_mem_spec : breadconv_mem_stmt H.
  Proof.
    unfold breadconv_mem_stmt. intros until junk; intros A0 A1 A2 A3 OUTL MB BL SEP NM BS LEN OUTC MO RBAL RBC MORB RBO SH PAY OSH RSH AC ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_bread_conv, BREADCONV_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, AINTRIN_STACK in *. acb.
    pose proof BL as BL0. pose proof SH as SH0. pose proof MO as MO0.
    membio_open m a R MB BL SH AC.
    pose proof SEP as SEP0. destruct SEP0 as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6, PS1, PS2, PS3, PS4.
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4.
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    destruct MORB as (RBR & RBP & RBH & RBF & RBB & RBM). unfold A_mem_buf_method, O_METH_BREAD in RBM.
    pose proof (Forall_inv RBF) as RF1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBF)))) as RF4.
    clear RBF. cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in RF1, RF2, RF3, RF4.
    hide RF1; hide RF2; hide RF3; hide RF4; hide RBR; hide RBB; hide RBO; hide RBM.
    destruct PAY as (PACC & PVIS & PAPP). destruct OSH as (OACC & OVIS & OAPP & OAOK). destruct RSH as (RACC & RAPP & RAOK).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
                          [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (mb_bm R, mb_bm R + 32)]) by nsw_tac.
    pose proof ACCa as ACCa0. hide ACCa0. pose proof RACC as RACC0. change (id (accessible m rbp 8)) in RACC0. hide RACC0.
    unfold A_mem_buf_method in BC. unfold wz in RBC.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    assert (IN : In (A_mem_buf_method, 112, 112) aglobals) by (unfold A_mem_buf_method; in_nth).
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt. unfold A_mem_buf_method in ADmt.
    assert (ACCmt : id (accessible m 0x5ae5a0 112)) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    clear ACCbb ACCbm ACCrp. pose proof ACCmt as ACCmt0. hide ACCmt0.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    unhide OUTR; unhide RBR. do 9 step. hide RBR.
    unhide OF1; unhide OF3; unhide RF1; unhide RF3. membio_reacc MU. hide OF1; hide OF3; hide RF1; hide RF3; hide OUTR.
    unfold id in ACCa, ACCmt.
    (* [comment removed for export] *)
    step. step. step. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    (* [comment removed for export] *)
    step. step. zstep.
    evar (TGT : machine_state).
    eapply evt_cut with (P := fun msx => msx = TGT).
    { step. if_cases K1; zify_cond K1.
      - apply evt_done; subst TGT; reflexivity.
      - step. apply evt_done. subst TGT. repeat f_equal. lia. }
    subst TGT. cbv beta. intros ms' ->.
    (* [comment removed for export] *)
    step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check ACCa (a + 8). st1.
    (* [comment removed for export] *)
    step. ub_dead. step. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACCmt (0x5ae5a0 + 40). st1. step. unfold P_mem_read. step.
    (* [comment removed for export] *)
    pose proof (amemread_spec H HH) as MRS. unfold memread_stmt, MEMREAD_STACK, FR_mem_read, AINTRIN_STACK, P_mem_read in MRS.
    eapply evt_cut.
    { eapply MRS with (lo := lo) (R := R) (LB := LB) (junk := junk); clear MRS;
        [reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL0| exact SEP| exact BS| exact LEN| exact OUTC|
        | exact (MEMBIO_shad_across2 H LB _ m m _ a R MB SH0 MU WM NSW0)
        | split; [| split]; [eapply accessible_across2; [exact PACC| exact MU| exact NSW0]| eapply shvis_across2; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| exact PAPP]
        | pose proof OACC as (_ & OHI & _); split; [| split; [| split]]; [eapply accessible_across2; [exact OACC| exact MU| exact NSW0]| eapply shvis_across2; [exact OVIS| exact MU| exact WM| lia| lia| exact NSW0]| exact OAPP| exact OAOK]
        | aconst_of AC MU WM
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTR; unhide OUTB; unhide OF1; unhide OF2; unhide OF3; unhide OF4. unhide OUTM.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [| split; [lia| unfold A_mem_buf_method, O_METH_BREAD; lia]].
      unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil. }
    clear MRS. intros ms' PO. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in PO. revert ms' PO.
    aland_open MU.
    carry1 MUc WMc FR using OUTR. unhide RF1; unhide RF3. carry1 MUc WMc RBC using RBR RBO. hide RF1; hide RF3. carry1 MUc WMc MT using OUTM.
    aland_close MU WM MUc WMc. unfold ABR_RA1 || idtac.
    match goal with X : MEMBIO H LB _ a _ |- _ => destruct X as (BC1 & BBC1 & BMC1 & RPC1 & _) end.
    unfold bio_cells, membio_bio, buf_cells, mb_after_bread, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC1, BBC1, BMC1, RPC1.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC1, BBC1, BMC1, RPC1.
    match goal with X : bytes_at asegs _ (mb_buf _) ds |- _ => cbn [mb_buf mb_after_bread] in X; rename X into BS2 end.
    match goal with X : True |- _ => clear X | _ => idtac end.
    pose proof (clr_flags_facts (mb_flags R) FLR RDO AEOF) as (FL1 & FL2 & FL3).
    assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
    { unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. unfold mb_rdn, mb_avail in *. lia. }
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (unfold mb_rdn, mb_avail in *; lia).
    match goal with X : rw_cells asegs _ out _ |- _ => rewrite SL in X; rename X into OUTC2 end.
    clear ACCa ACCmt. pose proof ACCa0 as ACCa; unhide ACCa. unhide OF1; unhide RF1; unhide OUTR. membio_reacc MU. hide OF1; hide RF1; hide OUTR. unfold id in ACCa.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_load ACCa (a + 48). step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    st1. rewrite zx32_lit by lia. zstep. rewrite N6_tac.land_ones64, (Z.mod_small (Z.land (mb_flags R) (Z.lnot 15))) by lia. rewrite land_clr7_id by lia.
    assert (DJ1 : chunk_disj (mb_bb R) 16 a 128) by (unhide AP1; unfold chunk_disj; lia).
    assert (DJ2 : chunk_disj (mb_bm R) 32 a 128) by (unhide AP2; unfold chunk_disj; lia).
    assert (DJ3 : chunk_disj (mb_rp R) 32 a 128) by (unhide AP3; unfold chunk_disj; lia).
    assert (DJ4 : chunk_disj rbp 8 a 128) by (unhide RF1; unfold chunk_disj; lia).
    unhide OF1; unhide PS1. st1. hide OF1; hide PS1.
    (* [comment removed for export] *)
    step. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      step. step. step. step. unfold P_BIO_ctrl. step.
      pose proof (abioctrl_mem_spec H) as BCS. unfold bioctrl_mem_stmt, memctrl_stmt_at, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl, P_BIO_ctrl in BCS.
      eapply evt_cut.
      { eapply BCS with (lo := lo) (R := mb_after_bread R (mb_rdn R outl)) (LB := LB) (cmd := BIO_CTRL_EOF); clear BCS;
          [reflexivity| reflexivity| reflexivity| reflexivity| left; reflexivity| lia| lia| membio_tac| | exact SEP| intros _; unfold METH_mem, O_METH_BREAD, A_mem_buf_method; exact MT
          | exact (MEMBIO_shad_across2 H LB _ m _ _ a R MB SH0 MU WM NSW0)
          | aconst_of AC MU WM
          | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
        unfold MEMBIO_below; cbn [mb_bb mb_bm mb_rp mb_after_bread]; exact BL0. }
      clear BCS. unfold memctrl_post, BIO_SIZE.
      aland_open MU.
      carry1 MUc WMc FR. carry1 MUc WMc RBC using RBR. carry1 MUc WMc OUTC2 using OUTR. carry1 MUc WMc BS2.
      aland_close MU WM MUc WMc. unfold ABR_RA2 || idtac.
      match goal with X : MEMBIO H LB _ a _ |- _ => destruct X as (BC3 & BBC3 & BMC3 & RPC3 & _) end.
      unfold bio_cells, membio_bio, buf_cells, mb_after_bread, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC3, BBC3, BMC3, RPC3.
      cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
           mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC3, BBC3, BMC3, RPC3.
      replace (mem_ctrl_rv (mb_after_bread R (mb_rdn R outl)) BIO_CTRL_EOF) with 1.
      2:{ unfold mem_ctrl_rv, mb_avail, mb_after_bread; cbn [mb_len mb_pos]. rewrite Z.eqb_refl.
          replace (mb_len R - (mb_pos R + mb_rdn R outl) =? 0) with true; [reflexivity|]. symmetry; apply Z.eqb_eq. unfold mb_rdn, mb_avail in *. lia. }
      (* [comment removed for export] *)
      step. if_lit.
      (* [comment removed for export] *)
      pose proof RACC0 as RACC1; unhide RACC1.
      unhide RF1; unhide RF3; unhide OF1; unhide OF3; unhide OUTR; unhide RBR. membio_reacc MU. hide RF1; hide RF3; hide OF1; hide OF3; hide OUTR; hide RBR.
      unfold id in RACC1. step. ub_dead. step. ubal_by RBAL. step. if_lit. step. zstep. zstep. ck8_check RACC1 rbp.
      assert (DR1 : chunk_disj a 128 rbp 8) by (unhide RF1; unfold chunk_disj; lia).
      assert (DR2 : chunk_disj (mb_bb R) 16 rbp 8) by (unhide RF2; unfold chunk_disj; lia).
      assert (DR3 : chunk_disj (mb_bm R) 32 rbp 8) by (unhide RF3; unfold chunk_disj; lia).
      assert (DR4 : chunk_disj (mb_rp R) 32 rbp 8) by (unhide RF4; unfold chunk_disj; lia).
      assert (DR5 : chunk_disj (bv_unsigned sp + -64) 64 rbp 8) by (unhide RBR; unfold chunk_disj; lia).
      assert (DR6 : chunk_disj 5957056 64 rbp 8) by (unhide RBM; unfold chunk_disj; lia).
      change (Z_to_bv 64 0 : word) with (wz 0) at 2.
      unhide RBO; unhide RBB. st1. hide RBO; hide RBB.
      do 7 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post, rd_ok. rewrite KN in *. cbn [Z.ltb].
      match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTCf end.
      match goal with X : rw_cells asegs _ rbp _ |- _ => rename X into RBCf end.
      do 15 eexists. eexists. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [aconst_of AC MU WM|]. split; [exact ST|].
      split. { membio_tac. }
      split. { exact BS2. }
      split. { first [exact OUTCf| rewrite <- SL in OUTCf; exact OUTCf| rewrite SL in OUTCf; exact OUTCf| rewrite SL; exact OUTCf]. }
      exact RBCf.
    - (* [comment removed for export] *)
      assert (NP : 0 < mb_rdn R outl) by lia.
      do 4 step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. ubal_by RBAL. step. nzal rbp. step. step. step. step.
      pose proof RACC0 as RACC1; unhide RACC1.
      unhide RF1; unhide RF3; unhide OF1; unhide OF3; unhide OUTR; unhide RBR. membio_reacc MU. hide RF1; hide RF3; hide OF1; hide OF3; hide OUTR; hide RBR.
      unfold id in RACC1. zstep. zstep. ck8_check RACC1 rbp.
      assert (DR1 : chunk_disj a 128 rbp 8) by (unhide RF1; unfold chunk_disj; lia).
      assert (DR2 : chunk_disj (mb_bb R) 16 rbp 8) by (unhide RF2; unfold chunk_disj; lia).
      assert (DR3 : chunk_disj (mb_bm R) 32 rbp 8) by (unhide RF3; unfold chunk_disj; lia).
      assert (DR4 : chunk_disj (mb_rp R) 32 rbp 8) by (unhide RF4; unfold chunk_disj; lia).
      assert (DR5 : chunk_disj (bv_unsigned sp + -64) 64 rbp 8) by (unhide RBR; unfold chunk_disj; lia).
      assert (DR6 : chunk_disj 5957056 64 rbp 8) by (unhide RBM; unfold chunk_disj; lia).
      change (Z_to_bv 64 (mb_rdn R outl) : word) with (wz (mb_rdn R outl)) at 1.
      unhide RBO; unhide RBB. st1. hide RBO; hide RBB.
      do 7 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post, rd_ok. replace (0 <? mb_rdn R outl) with true by (symmetry; apply Z.ltb_lt; lia).
      match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTCf end.
      match goal with X : rw_cells asegs _ rbp _ |- _ => rename X into RBCf end.
      do 15 eexists. eexists. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [aconst_of AC MU WM|]. split; [exact ST|].
      split. { membio_tac. }
      split. { exact BS2. }
      split. { first [exact OUTCf| rewrite <- SL in OUTCf; exact OUTCf| rewrite SL in OUTCf; exact OUTCf| rewrite SL; exact OUTCf]. }
      exact RBCf.
  Qed.

  (* [comment removed for export] *)
  Definition ARI_RA1 : Z := 0x237910.   (* [comment removed for export] *)
  Definition ARI_RA2 : Z := 0x2379f0.   (* [comment removed for export] *)

  Lemma areadintern_mem_spec : readintern_mem_stmt H.
  Proof.
    unfold readintern_mem_stmt, readintern_mem_stmt_at. intros until junk; intros A0 A1 A2 A3 OUTL MB BL SEP NM BS LEN OUTC MO RBAL RBC MORB RBO SH PAY OSH RSH AC ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_bio_read_intern, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl,
      FR_mem_ctrl, AINTRIN_STACK in *. acb.
    pose proof BL as BL0. pose proof SH as SH0. pose proof MO as MO0. pose proof MORB as MORB0. pose proof PAY as PAY0. pose proof OSH as OSH0. pose proof RSH as RSH0.
    membio_open m a R MB BL SH AC.
    pose proof SEP as SEP0. destruct SEP0 as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6, PS1, PS2, PS3, PS4.
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4.
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    destruct MORB as (RBR & RBP & RBH & RBF & RBB & RBM). unfold A_mem_buf_method, O_METH_BREAD in RBM.
    pose proof (Forall_inv RBF) as RF1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBF)))) as RF4.
    clear RBF. cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in RF1, RF2, RF3, RF4.
    hide RF1; hide RF2; hide RF3; hide RF4; hide RBR; hide RBB; hide RBO; hide RBM.
    destruct PAY as (PACC & PVIS & PAPP). destruct OSH as (OACC & OVIS & OAPP & OAOK). destruct RSH as (RACC & RAPP & RAOK).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
                          [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (mb_bm R, mb_bm R + 32)]) by nsw_tac.
    pose proof ACCa as ACCa0. hide ACCa0. pose proof RACC as RACC0. change (id (accessible m rbp 8)) in RACC0. hide RACC0.
    unfold A_mem_buf_method in BC. unfold wz in RBC.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    assert (IN : In (A_mem_buf_method, 112, 112) aglobals) by (unfold A_mem_buf_method; in_nth).
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt. unfold A_mem_buf_method in ADmt.
    assert (ACCmt : id (accessible m 0x5ae5a0 112)) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    clear ACCbb ACCbm ACCrp. pose proof ACCmt as ACCmt0. hide ACCmt0.
    (* [comment removed for export] *)
    carve_frame 96%nat ST.
    unhide OUTR; unhide RBR. do 14 step. hide RBR.
    unhide OF1; unhide OF3; unhide RF1; unhide RF3. membio_reacc MU. hide OF1; hide OF3; hide RF1; hide RF3; hide OUTR.
    unfold id in ACCa, ACCmt.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step. ubal_any. step. if_lit. step. step. step.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACCa (a + 8). st1. do 3 step. step. if_false.
    (* [comment removed for export] *)
    step. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACCmt (0x5ae5a0 + 32). st1. step. if_false.
    (* [comment removed for export] *)
    do 2 step. zstep. ck8_check ACCa (a + 16). step. step. do 2 step. if_false.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACCa (a + 24). st1. step. if_true.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACCa (a + 40). st1. rewrite sx32_lit by lia. step. if_false.
    (* [comment removed for export] *)
    ck8_check ACCa (a + 8). st1. step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACCmt (0x5ae5a0 + 32). st1.
    (* [comment removed for export] *)
    step. step. step. step. unfold P_bread_conv. step.
    (* [comment removed for export] *)
    pose proof abreadconv_mem_spec as BRS. unfold breadconv_mem_stmt, BREADCONV_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
      AINTRIN_STACK, P_bread_conv in BRS.
    eapply evt_cut.
    { eapply BRS with (lo := lo) (R := R) (LB := LB) (junk := junk) (rbv := rbv); clear BRS;
        [reflexivity| reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL0| exact SEP| unfold METH_mem, O_METH_BREAD, A_mem_buf_method; exact MT
        | exact BS| exact LEN| exact OUTC| | exact RBAL| exact RBC| | exact RBO
        | exact (MEMBIO_shad_across2 H LB _ m m _ a R MB SH0 MU WM NSW0)
        | split; [| split]; [eapply accessible_across2; [exact PACC| exact MU| exact NSW0]| eapply shvis_across2; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| exact PAPP]
        | pose proof OACC as (_ & OHI & _); split; [| split; [| split]]; [eapply accessible_across2; [exact OACC| exact MU| exact NSW0]| eapply shvis_across2; [exact OVIS| exact MU| exact WM| lia| lia| exact NSW0]| exact OAPP| exact OAOK]
        | split; [| split]; [eapply accessible_across2; [exact RACC| exact MU| exact NSW0]| exact RAPP| exact RAOK]
        | aconst_of AC MU WM
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      - unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTR; unhide OUTB; unhide OF1; unhide OF2; unhide OF3; unhide OF4; unhide OUTM.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold A_mem_buf_method, O_METH_BREAD; lia].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil.
      - unfold memrd_out. rewrite unsigned_lit by lia. unhide RBR; unhide RBB; unhide RF1; unhide RF2; unhide RF3; unhide RF4; unhide RBM.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold A_mem_buf_method, O_METH_BREAD; lia].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil. }
    clear BRS. intros ms' PO. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in PO. revert ms' PO.
    aland_open MU.
    carry1 MUc WMc FR using OUTR RBR. carry1 MUc WMc MT using OUTM RBM.
    aland_close MU WM MUc WMc. unfold ARI_RA1 || idtac.
    match goal with X : MEMBIO H LB _ a _ |- _ => destruct X as (BC1 & BBC1 & BMC1 & RPC1 & _) end.
    unfold bio_cells, membio_bio, buf_cells, mb_after_bread, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC1, BBC1, BMC1, RPC1.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC1, BBC1, BMC1, RPC1.
    match goal with X : bytes_at asegs _ (mb_buf _) ds |- _ => cbn [mb_buf mb_after_bread] in X; rename X into BS2 end.
    pose proof (clr_flags_facts (mb_flags R) FLR RDO AEOF) as (FL1 & FL2 & FL3).
    assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
    { unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. unfold mb_rdn, mb_avail in *. lia. }
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (unfold mb_rdn, mb_avail in *; lia).
    match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTC2 end.
    match goal with X : rw_cells asegs _ rbp _ |- _ => rename X into RBC2 end.
    clear ACCa ACCmt.
    pose proof ACCa0 as ACCa; unhide ACCa. pose proof ACCmt0 as ACCmt; unhide ACCmt. pose proof RACC0 as RACC1; unhide RACC1.
    unhide OF1; unhide OF3; unhide RF1; unhide RF3; unhide OUTR; unhide RBR. membio_reacc MU. hide OF1; hide OF3; hide RF1; hide RF3; hide OUTR; hide RBR.
    unfold id in ACCa, ACCmt, RACC1.
    (* [comment removed for export] *)
    step. step. step.
    destruct (Z.eq_dec (mb_rdn R outl) 0) as [KN|KN].
    - (* [comment removed for export] *)
      unfold rd_ok. rewrite KN in *. cbn [Z.ltb].
      step. if_lit.
      (* [comment removed for export] *)
      step. if_lit. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
      (* [comment removed for export] *)
      step. unfold P_BIO_eof. step.
      pose proof (abioeof_mem_spec H) as BES. unfold bioeof_mem_stmt, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_eof, FR_BIO_ctrl, FR_mem_ctrl, P_BIO_eof in BES.
      eapply evt_cut.
      { eapply BES with (lo := lo) (R := mb_after_bread R 0) (LB := LB); clear BES;
          [reflexivity| membio_tac| | exact SEP| unfold METH_mem, O_METH_BREAD, A_mem_buf_method; exact MT
          | exact (MEMBIO_shad_across2 H LB _ m _ _ a R MB SH0 MU WM NSW0)
          | aconst_of AC MU WM
          | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
        unfold MEMBIO_below; cbn [mb_bb mb_bm mb_rp mb_after_bread]; exact BL0. }
      clear BES. unfold memctrl_post, BIO_SIZE.
      aland_open MU.
      carry1 MUc WMc FR. carry1 MUc WMc RBC2 using RBR. carry1 MUc WMc OUTC2 using OUTR. carry1 MUc WMc BS2.
      aland_close MU WM MUc WMc. unfold ARI_RA2 || idtac.
      match goal with X : MEMBIO H LB _ a _ |- _ => destruct X as (BC3 & BBC3 & BMC3 & RPC3 & _) end.
      unfold bio_cells, membio_bio, buf_cells, mb_after_bread, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC3, BBC3, BMC3, RPC3.
      cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
           mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC3, BBC3, BMC3, RPC3.
      replace (mem_ctrl_rv (mb_after_bread R 0) BIO_CTRL_EOF) with 1.
      2:{ unfold mem_ctrl_rv, mb_avail, mb_after_bread; cbn [mb_len mb_pos]. rewrite Z.eqb_refl.
          replace (mb_len R - (mb_pos R + 0) =? 0) with true; [reflexivity|]. symmetry; apply Z.eqb_eq. unfold mb_rdn, mb_avail in *. lia. }
      (* [comment removed for export] *)
      zstep. step. step.
      change (Z.b2z (0 <? 1) + -1) with 0.
      (* [comment removed for export] *)
      clear ACCa ACCmt RACC1. pose proof ACCa0 as ACCa; unhide ACCa.
      unhide OF1; unhide OF3; unhide RF1; unhide RF3; unhide OUTR; unhide RBR. membio_reacc MU. hide OF1; hide OF3; hide RF1; hide RF3; hide OUTR; hide RBR. unfold id in ACCa.
      ck8_check ACCa (a + 16). do 2 step. if_false. zstep. zstep. zstep. ck8_check ACCa (a + 24). st1. step. if_true.
      (* [comment removed for export] *)
      do 2 step. if_true. step. do 12 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post. rewrite ?SL.
      match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTCf end.
      match goal with X : rw_cells asegs _ rbp _ |- _ => rename X into RBCf end.
      do 15 eexists. eexists. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [aconst_of AC MU WM|]. split; [exact ST|].
      split. { membio_tac. }
      split. { exact BS2. }
      split. { first [exact OUTCf| rewrite <- SL in OUTCf; exact OUTCf| rewrite SL in OUTCf; exact OUTCf| rewrite SL; exact OUTCf]. }
      exact RBCf.
    - (* [comment removed for export] *)
      unfold rd_ok. replace (0 <? mb_rdn R outl) with true by (symmetry; apply Z.ltb_lt; lia).
      step. if_false.
      (* [comment removed for export] *)
      step. ub_dead. step. ubal_by RBAL. if_lit. zstep. ck8_check RACC1 rbp. zstep. zstep. zstep. ck8_check ACCa (a + 96). st1. st1. zstep.
      change (Z_to_bv 64 (mb_nread R + mb_rdn R outl)) with (wz (mb_nread R + mb_rdn R outl)).
      assert (DJ1 : chunk_disj (mb_bb R) 16 a 128) by (unhide AP1; unfold chunk_disj; lia).
      assert (DJ2 : chunk_disj (mb_bm R) 32 a 128) by (unhide AP2; unfold chunk_disj; lia).
      assert (DJ3 : chunk_disj (mb_rp R) 32 a 128) by (unhide AP3; unfold chunk_disj; lia).
      assert (DJ4 : chunk_disj rbp 8 a 128) by (unhide RF1; unfold chunk_disj; lia).
      unhide OF1; unhide PS1. st1. hide OF1; hide PS1. step.
      (* [comment removed for export] *)
      clear ACCa ACCmt RACC1. pose proof ACCa0 as ACCa; unhide ACCa. pose proof RACC0 as RACC1; unhide RACC1.
      unhide OF1; unhide OF3; unhide RF1; unhide RF3; unhide OUTR; unhide RBR. membio_reacc MU. hide OF1; hide OF3; hide RF1; hide RF3; hide OUTR; hide RBR. unfold id in ACCa, RACC1.
      ck8_check ACCa (a + 16). do 2 step. if_false. zstep. zstep. zstep. ck8_check ACCa (a + 24). st1. step. if_true.
      (* [comment removed for export] *)
      do 2 step. if_false. step. ub_dead. step. ub_dead. zstep. ck8_check RACC1 rbp. st1. step. if_cases K5; zify_cond K5; [| kill K5]. clear K5.
      (* [comment removed for export] *)
      step. do 12 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post. rewrite ?SL.
      match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTCf end.
      match goal with X : rw_cells asegs _ rbp _ |- _ => rename X into RBCf end.
      do 15 eexists. eexists. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [aconst_of AC MU WM|]. split; [exact ST|].
      split. { membio_tac. }
      split. { exact BS2. }
      split. { first [exact OUTCf| rewrite <- SL in OUTCf; exact OUTCf| rewrite SL in OUTCf; exact OUTCf| rewrite SL; exact OUTCf]. }
      exact RBCf.
  Qed.

  (* [comment removed for export] *)
  Lemma abioreadex_mem_spec : bioreadex_mem_stmt H.
  Proof.
    unfold bioreadex_mem_stmt, readintern_mem_stmt_at. intros until junk; intros A0 A1 A2 A3 OUTL MB BL SEP NM BS LEN OUTC MO RBAL RBC MORB RBO SH PAY OSH RSH AC ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_BIO_read_ex, BIOREADEX_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_set_data, FR_bio_read_intern, FR_bread_conv,
      FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, AINTRIN_STACK in *. acb.
    pose proof BL as BL0. pose proof SH as SH0. pose proof MO as MO0. pose proof MORB as MORB0.
    membio_open m a R MB BL SH AC. clear ACCa ACCbb ACCbm ACCrp.
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3.
    cbn [blk_addr blk_size fst snd] in OF1, OF3. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF3. hide OF1; hide OF3. hide OUTR. hide OUTB; hide OUTM. hide OUTF.
    destruct MORB as (RBR & RBP & RBH & RBF & RBB & RBM).
    pose proof (Forall_inv RBF) as RF1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RF3.
    cbn [blk_addr blk_size fst snd] in RF1, RF3. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in RF1, RF3. hide RF1; hide RF3. hide RBR. hide RBB; hide RBM; hide RBO. hide RBF.
    destruct PAY as (PACC & PVIS & PAPP). destruct OSH as (OACC & OVIS & OAPP & OAOK). destruct RSH as (RACC & RAPP & RAOK).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    assert (NSW0 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv)
                          [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (mb_bm R, mb_bm R + 32)]) by nsw_tac.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT. unfold wz in RBC.
    carve_frame 16%nat ST.
    unhide OUTR; unhide RBR. do 4 step. hide RBR; hide OUTR.
    unfold P_bio_read_intern. step.
    pose proof areadintern_mem_spec as RIS. unfold readintern_mem_stmt, readintern_mem_stmt_at, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK,
      FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_BIO_eof, AINTRIN_STACK, P_bio_read_intern in RIS.
    eapply evt_cut.
    { eapply RIS with (lo := lo) (R := R) (LB := LB) (junk := junk) (rbv := rbv); clear RIS;
        [reflexivity| reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL0| exact SEP| unfold METH_mem, O_METH_BREAD, A_mem_buf_method; exact MT
        | exact BS| exact LEN| exact OUTC| | exact RBAL| exact RBC| | exact RBO
        | exact (MEMBIO_shad_across2 H LB _ m m _ a R MB SH0 MU WM NSW0)
        | split; [| split]; [eapply accessible_across2; [exact PACC| exact MU| exact NSW0]| eapply shvis_across2; [exact PVIS| exact MU| exact WM| lia| unfold AAPP_HI in *; lia| exact NSW0]| exact PAPP]
        | pose proof OACC as (_ & OHI & _); split; [| split; [| split]]; [eapply accessible_across2; [exact OACC| exact MU| exact NSW0]| eapply shvis_across2; [exact OVIS| exact MU| exact WM| lia| lia| exact NSW0]| exact OAPP| exact OAOK]
        | split; [| split]; [eapply accessible_across2; [exact RACC| exact MU| exact NSW0]| exact RAPP| exact RAOK]
        | aconst_of AC MU WM
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      - unhide OUTR; unhide OUTB; unhide OUTM; unhide OUTF. unfold memrd_out. rewrite unsigned_lit by lia. repeat split; try assumption. lia.
      - unhide RBR; unhide RBB; unhide RBM; unhide RBF. unfold memrd_out. rewrite unsigned_lit by lia. repeat split; try assumption. lia. }
    clear RIS. intros ms' PO. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in PO. revert ms' PO.
    aland_open MU. carry1 MUc WMc FR using OUTR RBR. aland_close MU WM MUc WMc.
    match goal with X : rw_cells asegs _ out _ |- _ => rename X into OUTCf end.
    match goal with X : rw_cells asegs _ rbp _ |- _ => rename X into RBCf end.
    match goal with X : bytes_at asegs _ (mb_buf _) ds |- _ => rename X into BSf end.
    (* [comment removed for export] *)
    unfold rd_ok in *. destruct (0 <? mb_rdn R outl).
    - zstep. st1. st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post. do 16 eexists. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split; [assumption|]. split; [exact BSf|]. split; [exact OUTCf|]. exact RBCf.
    - zstep. st1. st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold memrd_post. do 16 eexists. split; [reflexivity|].
      split; [unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split; [assumption|]. split; [exact BSf|]. split; [exact OUTCf|]. exact RBCf.
  Qed.
End S.
