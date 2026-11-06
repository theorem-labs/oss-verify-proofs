(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_C7_read ECH_C7_rd.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (Hnn : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|c cs IHc]; cbn; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IHc. }
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    rewrite (Z.land_ones (bv_unsigned b) 8) by lia. rewrite Z.mod_small by lia.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0; [rewrite Z.lor_0_r; reflexivity|].
    symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    + rewrite Z.shiftl_spec_low by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. apply andb_false_r.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_eq_0 (bv_unsigned b) 8); [rewrite Z.lor_0_l; exact IH | lia |].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma bytes_le_to_Z_bound8 : forall bs, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2^64.
Proof.
  intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 8)) with (2^64) in B. lia.
Qed.

Lemma le8_wz_of_bytes : forall bs, length bs = 8%nat -> le8 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, wz. rewrite unsigned_lit by (apply bytes_le_to_Z_bound8; exact L).
  rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma le8_wz_split : forall z, 0 <= z < 2^64 -> le8 (wz z) = le4 (wz z) ++ le4 (wz (Z.shiftr z 32)).
Proof.
  intros z Hz. unfold le8, le4, word_to_le_bytes, wz.
  assert (S32 : 0 <= Z.shiftr z 32 < 2^32).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^32) with (2^64). lia. }
  rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB8_C8 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (wz (bytes_le_to_Z bs)) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  pose proof Hwf as W0. apply cells_wf_app in W0. destruct W0 as [_ [L _]]. cbn in L.
  split; [split|].
  - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_wz_of_bytes by exact L. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_C4C4 : forall segs m A pre z post, 0 <= z < 2^64 ->
  rw_cells segs m A (pre ++ C8 (wz z) :: post) -> rw_cells segs m A (pre ++ C4 (wz z) :: C4 (wz (Z.shiftr z 32)) :: post).
Proof.
  intros segs m A pre z post Hz [[Hwf Hb] Hw].
  split; [split|].
  - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_wz_split in Hb by exact Hz. rewrite <- app_assoc in Hb. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma bioreadex_body : forall (entry stack : Z), entry = P_BIO_read_ex -> stack = BIOREADEX_STACK -> readintern_mem_stmt_at entry stack.
  Proof.
    intros entry stack -> ->. unfold readintern_mem_stmt_at. intros until junk; intros A0 A1 A2 A3 OUTL MB BL SEP METH BS LEN OUTC MO RBC MORB RBO ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_BIO_read_ex, BIOREADEX_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bio_read_intern, FR_bread_conv,
      FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, BIOACC_STACK, FR_BIO_set_data in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & RG1). pose proof RB3 as (BMP & _ & _ & BMH & RG3). hide RB1; hide RB2; hide RB3; hide RB4.
    pose proof BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BL1, BL2, BL3, BL4, AH, BMH, RG1, RG3. hide RG1; hide RG3.
    pose proof MO as MO0. destruct MO0 as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM). hide OUTF; hide OUTB; hide OUTM.
    pose proof MORB as MORB0. destruct MORB0 as (RBR & RBP & RBH & RBF & RBB & RBM). hide RBF; hide RBB; hide RBM; hide RBO.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC. unfold wz in BBC, RBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METH. norm_addr METH.
    carve_frame 16%nat ST.
    st1. st1. st1. hide RBR; hide OUTR. step. unfold P_bio_read_intern. step.
    (* [comment removed for export] *)
    pose proof readintern_mem_spec as RIS. unfold readintern_mem_stmt, readintern_mem_stmt_at, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK,
      FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_BIO_eof, BIOACC_STACK, FR_BIO_set_data, P_bio_read_intern in RIS.
    eapply evt_cut.
    { eapply RIS with (lo := lo) (R := R) (LB := LB) (junk := junk) (rbv := rbv); clear RIS;
        [reflexivity| reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL| exact SEP| exact METH| exact BS| exact LEN| exact OUTC| | exact RBC| | exact RBO
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      - unhide OUTR. unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTF; unhide OUTB; unhide OUTM. repeat split; try assumption. lia.
      - unhide RBR. unfold memrd_out. rewrite unsigned_lit by lia. unhide RBF; unhide RBB; unhide RBM. repeat split; try assumption. lia. }
    clear RIS. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE.
    unhide OUTR; unhide RBR; unhide RG1; unhide RG3. landx MU WM. hide OUTR; hide RBR; hide RG1; hide RG3.
    match goal with H : rw_cells rsegs _ out _ |- _ => rename H into OUTCf end.
    match goal with H : rw_cells rsegs _ rbp _ |- _ => rename H into RBCf end.
    match goal with H : bytes_at rsegs _ (mb_buf _) ds |- _ => rename H into BSf end.
    (* [comment removed for export] *)
    unfold rd_ok in *. destruct (0 <? mb_rdn R outl).
    - zstep. st1. st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [assumption|]. split; [exact BSf|]. split; [exact OUTCf|]. exact RBCf.
    - zstep. st1. st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [assumption|]. split; [exact BSf|]. split; [exact OUTCf|]. exact RBCf.
  Qed.

  Lemma bioreadex_mem_spec : bioreadex_mem_stmt.
  Proof. apply bioreadex_body; reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma bioread_body : bioread_mem_stmt.
  Proof.
    unfold bioread_mem_stmt. intros until junk; intros A0 A1 A2 OUTL MB BL SEP METH BS LEN OUTC MO ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_BIO_read, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bio_read_intern, FR_bread_conv,
      FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, BIOACC_STACK, FR_BIO_set_data, FR_BIO_read in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & RG1). pose proof RB3 as (BMP & _ & _ & BMH & RG3). hide RB1; hide RB2; hide RB3; hide RB4.
    pose proof BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BL1, BL2, BL3, BL4, AH, BMH, RG1, RG3. hide RG1; hide RG3.
    pose proof MO as MO0. destruct MO0 as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM). hide OUTF; hide OUTB; hide OUTM.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC. unfold wz in BBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METH. norm_addr METH.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    destruct (rw_cells_CB_split _ _ _ _ 16 _ FR ltac:(lia)) as [FRlo FRhi]. clear FR.
    destruct (rw_cells_CB_split _ _ _ _ 8 _ FRlo ltac:(lia)) as [FR0 FRrb]. clear FRlo.
    cbn [Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in FRhi, FR0, FRrb.
    replace (bv_unsigned sp + -32 + 16) with (bv_unsigned sp + -16) in FRhi by lia.
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FRrb by lia.
    apply (rw_cells_CB8_C8 _ _ _ [] _ []) in FRrb. cbn [app] in FRrb.
    set (rbv := bytes_le_to_Z (skipn 8 (firstn 16 junk0))) in FRrb.
    st1. st1. st1. hide OUTR. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. unfold P_bio_read_intern. step.
    (* [comment removed for export] *)
    pose proof readintern_mem_spec as RIS. unfold readintern_mem_stmt, readintern_mem_stmt_at, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK,
      FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_BIO_eof, BIOACC_STACK, FR_BIO_set_data, P_bio_read_intern in RIS.
    eapply evt_cut.
    { eapply RIS with (lo := lo) (R := R) (LB := LB) (junk := junk) (rbv := rbv) (rbp := bv_unsigned sp + -24); clear RIS;
        [reflexivity| reflexivity| reflexivity| | exact OUTL| membio_tac| exact BL| exact SEP| exact METH| exact BS| exact LEN| exact OUTC| | exact FRrb| |
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      - reflexivity.
      - unhide OUTR. unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTF; unhide OUTB; unhide OUTM. repeat split; try assumption. lia.
      - unfold memrd_out. rewrite unsigned_lit by lia. split; [lia|]. split; [lia|]. split; [lia|]. split; [| split; [lia| unfold A_mem_buf_method, O_METH_BREAD; lia]].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil.
      - unhide OUTR. lia. }
    clear RIS. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE.
    unhide OUTR; unhide RG1; unhide RG3. landx MU WM. hide OUTR; hide RG1; hide RG3.
    match goal with H : rw_cells rsegs _ out _ |- _ => rename H into OUTCf end.
    match goal with H : rw_cells rsegs _ (bv_unsigned sp + -24) _ |- _ => rename H into RBCf end.
    match goal with H : bytes_at rsegs _ (mb_buf _) ds |- _ => rename H into BSf end.
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (unfold mb_rdn, mb_avail in *; lia).
    unfold rd_ok in *. destruct (0 <? mb_rdn R outl) eqn:KN.
    - (* [comment removed for export] *)
      apply Z.ltb_lt in KN.
      apply (rw_cells_C8_C4C4 _ _ _ [] _ []) in RBCf; [| lia]. cbn [app] in RBCf.
      step. if_false.
      st1. rewrite ?sx32_wz by lia. step. st1. st1. step. step.
      release_frame FR0 ST (bv_unsigned sp + -24). release_frame RBCf ST (bv_unsigned sp + -16). release_frame FRhi ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [assumption|]. split; [exact BSf|]. split; [exact OUTCf|]. exact I.
    - (* [comment removed for export] *)
      apply Z.ltb_ge in KN. assert (KZ : mb_rdn R outl = 0) by lia. rewrite KZ in *.
      step. if_true.
      st1. st1. step. step.
      release_frame FR0 ST (bv_unsigned sp + -24). release_frame RBCf ST (bv_unsigned sp + -16). release_frame FRhi ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [assumption|]. split; [exact BSf|]. split; [exact OUTCf|]. exact I.
  Qed.

  Lemma bioread_mem_spec : bioread_mem_stmt.
  Proof. exact bioread_body. Qed.
End S.
