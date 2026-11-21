(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma icset_next_in_facts : forall c m,
  ic_avail_in (icset_next_in c m) = ic_avail_in c
  /\ ic_next_out (icset_next_in c m) = ic_next_out c
  /\ ic_avail_out (icset_next_in c m) = ic_avail_out c
  /\ ic_input (icset_next_in c m) = ic_input c
  /\ ic_outbuf (icset_next_in c m) = ic_outbuf c
  /\ ic_total_in (icset_next_in c m) = ic_total_in c
  /\ ic_total_out (icset_next_in c m) = ic_total_out c
  /\ ic_msg (icset_next_in c m) = ic_msg c
  /\ ic_data_type (icset_next_in c m) = ic_data_type c
  /\ ic_adler (icset_next_in c m) = ic_adler c
  /\ ic_next_in (icset_next_in c m) = m.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

Section S_next_in.
  Variable v : icv.
  Hypothesis C : ictx v.
  Lemma LMEM_store_next_in : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_next_in c m) r) (wbytes M (zw (cv_ZP v + 0)) (Z_to_le_bytes 8 (cv_I0 v + m))).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_next_in_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6u_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

End S_next_in.

Lemma icset_avail_in_facts : forall c m,
  ic_next_in (icset_avail_in c m) = ic_next_in c
  /\ ic_next_out (icset_avail_in c m) = ic_next_out c
  /\ ic_avail_out (icset_avail_in c m) = ic_avail_out c
  /\ ic_input (icset_avail_in c m) = ic_input c
  /\ ic_outbuf (icset_avail_in c m) = ic_outbuf c
  /\ ic_total_in (icset_avail_in c m) = ic_total_in c
  /\ ic_total_out (icset_avail_in c m) = ic_total_out c
  /\ ic_msg (icset_avail_in c m) = ic_msg c
  /\ ic_data_type (icset_avail_in c m) = ic_data_type c
  /\ ic_adler (icset_avail_in c m) = ic_adler c
  /\ ic_avail_in (icset_avail_in c m) = m.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

Section S_avail_in.
  Variable v : icv.
  Hypothesis C : ictx v.
  Lemma LMEM_store_avail_in : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_avail_in c m) r) (wbytes M (zw (cv_ZP v + 8)) (Z_to_le_bytes 4 m)).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_avail_in_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6u_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

End S_avail_in.

Lemma icset_next_out_facts : forall c m,
  ic_next_in (icset_next_out c m) = ic_next_in c
  /\ ic_avail_in (icset_next_out c m) = ic_avail_in c
  /\ ic_avail_out (icset_next_out c m) = ic_avail_out c
  /\ ic_input (icset_next_out c m) = ic_input c
  /\ ic_outbuf (icset_next_out c m) = ic_outbuf c
  /\ ic_total_in (icset_next_out c m) = ic_total_in c
  /\ ic_total_out (icset_next_out c m) = ic_total_out c
  /\ ic_msg (icset_next_out c m) = ic_msg c
  /\ ic_data_type (icset_next_out c m) = ic_data_type c
  /\ ic_adler (icset_next_out c m) = ic_adler c
  /\ ic_next_out (icset_next_out c m) = m.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

Section S_next_out.
  Variable v : icv.
  Hypothesis C : ictx v.
  Lemma LMEM_store_next_out : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_next_out c m) r) (wbytes M (zw (cv_ZP v + 24)) (Z_to_le_bytes 8 (cv_P0 v + m))).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_next_out_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6u_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

End S_next_out.

Lemma icset_avail_out_facts : forall c m,
  ic_next_in (icset_avail_out c m) = ic_next_in c
  /\ ic_avail_in (icset_avail_out c m) = ic_avail_in c
  /\ ic_next_out (icset_avail_out c m) = ic_next_out c
  /\ ic_input (icset_avail_out c m) = ic_input c
  /\ ic_outbuf (icset_avail_out c m) = ic_outbuf c
  /\ ic_total_in (icset_avail_out c m) = ic_total_in c
  /\ ic_total_out (icset_avail_out c m) = ic_total_out c
  /\ ic_msg (icset_avail_out c m) = ic_msg c
  /\ ic_data_type (icset_avail_out c m) = ic_data_type c
  /\ ic_adler (icset_avail_out c m) = ic_adler c
  /\ ic_avail_out (icset_avail_out c m) = m.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

Section S_avail_out.
  Variable v : icv.
  Hypothesis C : ictx v.
  Lemma LMEM_store_avail_out : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_avail_out c m) r) (wbytes M (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 m)).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_avail_out_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6u_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

End S_avail_out.



Section Restore.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma LMEM_restore : forall s c r M hd bi,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW (iset_bits (iset_hold s hd) bi)
                (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) r)
         (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
            (zw (cv_ZP v)) (Z_to_le_bytes 8 (cv_I0 v + ir_next r)))
            (zw (cv_ZP v + 8)) (Z_to_le_bytes 4 (ir_have r)))
            (zw (cv_ZP v + 24)) (Z_to_le_bytes 8 (cv_P0 v + ir_put r)))
            (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r)))
            (zw (cv_S v + 96)) (Z_to_le_bytes 8 hd))
            (zw (cv_S v + 104)) (Z_to_le_bytes 4 bi)).
  Proof.
    intros s c r M hd bi HM Hput. pose proof (ic_S _ C) as CS.
    pose proof (LMEM_store_next_in v C s c r M (ir_next r) HM Hput) as H1. rewrite (Z.add_0_r (cv_ZP v)) in H1.
    pose proof (LMEM_store_avail_in v C s _ r _ (ir_have r) H1 Hput) as H2.
    pose proof (LMEM_store_next_out v C s _ r _ (ir_put r) H2 Hput) as H3.
    pose proof (LMEM_store_avail_out v C s _ r _ (ir_left r) H3 Hput) as H4.
    match type of H4 with LMEM _ (mkW _ ?c4 _) ?M4 =>
      replace (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) with c4 by (destruct c; reflexivity);
      assert (H5 : LMEM v (mkW (iset_hold s hd) c4 r) (wbytes M4 (zw (cv_S v + 96)) (Z_to_le_bytes 8 hd)))
    end.
    { eapply (LMEM_store_scalar v C s _ r _ _ 96 _ H4); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_hold _ (cv_S v) _ s hd (lm_sc _ _ _ H4)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    eapply (LMEM_store_scalar v C _ _ r _ _ 104 _ H5); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
    apply (is6_upd_bits _ (cv_S v) _ _ bi (lm_sc _ _ _ H5)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia].
  Qed.
End Restore.
End FXG.
