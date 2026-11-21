(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Lemma loop_post_reanchor' : forall v w0 w1 stop w' R' M',
  same_blocks (w_s w0) (w_s w1) -> loop_post v w1 stop w' R' M' -> loop_post v w0 stop w' R' M'.
Proof.
  intros v w0 w1 stop w' R' M' HS (A & B & C & D). split; [exact A|]. split; [exact B|].
  split; [exact (same_blocks_trans _ _ _ HS C) | exact D].
Qed.

Lemma arm_post_chain : forall v w0 w1 M0 M1 res R' M' pc',
  same_blocks (w_s w0) (w_s w1) -> MFRAME v (ir_put (w_r w0)) (ir_put (w_r w1)) M0 M1 ->
  arm_post v w1 M1 res R' M' pc' -> arm_post v w0 M0 res R' M' pc'.
Proof.
  intros v w0 w1 M0 M1 res R' M' pc' HS HF H. destruct res as [u w'|w'|rc w']; cbn [arm_post] in *.
  - destruct H as (A & B & C0 & D). split; [exact A|]. split; [exact B|].
    split; [exact (same_blocks_trans _ _ _ HS C0) | exact (MFRAME_trans v _ _ _ _ _ _ HF D)].
  - destruct H as (A & B & D). split; [exact A|]. split; [exact (loop_post_reanchor' v w0 w1 _ _ _ _ HS B) | exact (MFRAME_trans v _ _ _ _ _ _ HF D)].
  - destruct H as (A & B & D). split; [exact A|]. split; [exact (loop_post_reanchor' v w0 w1 _ _ _ _ HS B) | exact (MFRAME_trans v _ _ _ _ _ _ HF D)].
Qed.

Lemma same_blocks_mode : forall s m, same_blocks s (iset_mode s m).
Proof. intros s m. split; [reflexivity | split; reflexivity]. Qed.
Lemma same_blocks_length : forall s x, same_blocks s (iset_length s x).
Proof. intros s x. split; [reflexivity | split; reflexivity]. Qed.


Section Out.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma LMEM_blit_out : forall s c r r' (n : nat) M,
    LMEM v (mkW s c r) M ->
    0 <= ir_next r -> ir_next r + Z.of_nat n <= cv_NI v ->
    0 <= ir_put r -> ir_put r + Z.of_nat n <= cv_NO v -> arr_len (ic_outbuf c) = cv_NO v ->
    (forall i, 0 <= i < cv_NI v -> 0 <= arr_get (ic_input c) i < 256) ->
    ir_put r' = ir_put r + Z.of_nat n ->
    ir_out r' = ir_out r ->
    LMEM v (mkW s (icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) (Z.of_nat n))) r')
           (wbytes M (zw (cv_P0 v + ir_put r)) (cbytes (arr_get (ic_input c)) (ir_next r) n)).
  Proof.
    intros s c r r' n M HM Hnx0 Hnxn Hpt0 Hptn Hol Hinb Hput' Hout'.
    open_ictx C. open_lmem HM.
    set (a := arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) (Z.of_nat n)).
    pose proof (icset_outbuf_facts c a) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    set (bs := cbytes (arr_get (ic_input c)) (ir_next r) n).
    assert (Hlen : length bs = n) by (subst bs; apply cbytes_length).
    destruct n as [|n'].
    { cbn [cbytes] in bs. subst bs. cbn [wbytes].
      assert (Ea : a = ic_outbuf c) by (subst a; unfold arr_blit; cbn; destruct (ic_outbuf c); reflexivity).
      constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?Hput', ?Hout', ?Ea; try assumption.
      rewrite Z.add_0_r. exact Mout. }
    assert (HNO : 0 < cv_NO v) by lia. assert (HNI : 0 < cv_NI v) by lia.
    specialize (CoP HNO). specialize (CfP HNO). specialize (CSP HNO). specialize (CPW HNO).
    specialize (CoI HNI). specialize (CfI HNI). specialize (CSI HNI). specialize (CIW HNI).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?Hput'.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | rewrite Hlen; lia |]. unfold offimg, IMG6_TOP in CoP. unfold ROD6_LO, ROD6_HI in Hx. rewrite Hlen. clear - Hx CoP Hpt0 Hptn CP0. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | rewrite Hlen; lia |].
      unfold sep in CSP. unfold is6_SIZE. rewrite Hlen. clear - CSP Hpt0 Hptn CP0 CS. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | rewrite Hlen; lia | unfold sep in CSP; rewrite Hlen; clear - CSP Hpt0 Hptn CP0 CS; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | rewrite Hlen; lia | unfold sep in CSP; rewrite Hlen; clear - CSP Hpt0 Hptn CP0 CS; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | rewrite Hlen; lia | unfold sep in CSP; rewrite Hlen; clear - CSP Hpt0 Hptn CP0 CS; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | rewrite Hlen; lia |]. unfold sep in CPW. rewrite Hlen. clear - CPW Hpt0 Hptn CP0 CWB. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | rewrite Hlen; lia |]. unfold sep in CIP. rewrite Hlen. clear - CIP Hpt0 Hptn CP0 CI0. lia.
    -
      intros i Hi. subst a. rewrite arr_get_blit.
      destruct (Z_lt_le_dec i (ir_put r)) as [Hlo|Hge].
      + replace ((ir_put r <=? i) && (i <? ir_put r + Z.max 0 (Z.of_nat (S n'))) && arr_inb (ic_outbuf c) i) with false
          by (destruct (Z.leb_spec (ir_put r) i); [exfalso; lia | reflexivity]).
        apply cell_write_other; [exact (Mout i ltac:(lia)) | lia | cbn; lia | lia | rewrite Hlen; lia | rewrite Hlen; cbn; lia].
      + replace ((ir_put r <=? i) && (i <? ir_put r + Z.max 0 (Z.of_nat (S n'))) && arr_inb (ic_outbuf c) i) with true.
        2:{ symmetry. unfold arr_inb. rewrite Hol. destruct (Z.leb_spec (ir_put r) i); [| exfalso; lia]. destruct (Z.ltb_spec i (ir_put r + Z.max 0 (Z.of_nat (S n')))); [| exfalso; lia].
            destruct (Z.leb_spec 0 i); [| exfalso; lia]. destruct (Z.ltb_spec i (cv_NO v)); [reflexivity | exfalso; lia]. }
        pose proof (memcpy_dst_cells s6_segs M (cv_P0 v + ir_put r) bs ltac:(lia) ltac:(rewrite Hlen; lia) (i - ir_put r) ltac:(rewrite Hlen; lia)) as Hnew.
        replace (cv_P0 v + ir_put r + 1 * (i - ir_put r)) with (cv_P0 v + 1 * i) in Hnew by lia.
        replace (bv_unsigned (nth (Z.to_nat (i - ir_put r)) bs (Z_to_bv 8 0))) with (arr_get (ic_input c) (ir_next r + (i - ir_put r))) in Hnew; [exact Hnew|].
        subst bs. rewrite (cbytes_nth (arr_get (ic_input c)) (S n') (Z.to_nat (i - ir_put r)) (ir_next r)) by lia.
        rewrite Z2Nat.id by lia. rewrite Z_to_bv_small; [reflexivity|]. unfold bv_modulus. cbn. pose proof (Hinb (ir_next r + (i - ir_put r)) ltac:(lia)). lia.
    - apply izs6_outbuf. apply (izs6_other v C); [exact Mzs | lia | rewrite Hlen; lia | unfold sep in CZO; rewrite Hlen; clear - CZO CZP Hpt0 Hptn CP0; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | rewrite Hlen; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfP; rewrite Hlen; clear - CfP Csp Hpt0 Hptn CP0; lia].
    - rewrite Hout'. pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | rewrite Hlen; lia | unfold sep in CfP; rewrite Hlen; clear - CfP Csp Hpt0 Hptn CP0; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.
End Out.


Lemma icset_adler_facts : forall c m,
  ic_next_in (icset_adler c m) = ic_next_in c /\ ic_avail_in (icset_adler c m) = ic_avail_in c
  /\ ic_next_out (icset_adler c m) = ic_next_out c /\ ic_avail_out (icset_adler c m) = ic_avail_out c
  /\ ic_input (icset_adler c m) = ic_input c /\ ic_outbuf (icset_adler c m) = ic_outbuf c
  /\ ic_total_in (icset_adler c m) = ic_total_in c /\ ic_total_out (icset_adler c m) = ic_total_out c
  /\ ic_msg (icset_adler c m) = ic_msg c /\ ic_data_type (icset_adler c m) = ic_data_type c
  /\ ic_adler (icset_adler c m) = m.
Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

Section Adl.
  Variable v : icv.
  Hypothesis C : ictx v.
  Lemma LMEM_store_adler : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_adler c m) r) (wbytes M (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 m)).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_adler_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite F7, F8, F9, ?F10, F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

End Adl.
End FXG.
