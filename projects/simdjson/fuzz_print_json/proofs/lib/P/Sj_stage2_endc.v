(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.

Lemma cword_machine : forall A Wv cv oc, (0 <= Wv + 1 < 2^32)%Z -> (0 <= cv < 2^24)%Z -> (0 <= oc < 256)%Z ->
  Z.lor (Z.shiftr (Z.shiftl (A + 8 * Wv + 8 - A) 29 mod 18446744073709551616) 32)
        (Z.lor (Z.shiftl cv 32 mod 18446744073709551616) (Z.shiftl oc 56 mod 18446744073709551616)) = cword oc (Wv + 1) cv.
Proof.
  intros A Wv cv oc HW Hc Hoc. rewrite (Z.mod_small (Z.shiftl oc 56)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (Z.shiftl_mul_pow2 oc 56) by lia. change (2^56)%Z with 72057594037927936%Z.
  replace (A + 8 * Wv + 8 - A)%Z with ((Wv + 1) * 2^3)%Z by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. change (3 + 29)%Z with 32%Z.
  rewrite (Z.mod_small ((Wv + 1) * 2^32)) by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia.
  rewrite (Z.mod_small (cv * 2^32)) by lia.
  rewrite <- (Z.shiftl_mul_pow2 cv 32) by lia. change 72057594037927936%Z with (2^56)%Z. rewrite <- (Z.shiftl_mul_pow2 oc 56) by lia.
  apply cword_lor; lia.
Qed.

Lemma tword_machine : forall t v, (0 <= t < 256)%Z -> (0 <= v < 2^56)%Z -> Z.lor (Z.shiftl t 56 mod 18446744073709551616) v = tword t v.
Proof. intros t v Ht Hv. rewrite Z.mod_small by (rewrite Z.shiftl_mul_pow2 by lia; lia). apply tword_lor. exact Hv. Qed.
Lemma shl56_small : forall t, (0 <= t < 256)%Z -> (Z.shiftl t 56 mod 18446744073709551616 = t * 72057594037927936)%Z.
Proof. intros t Ht. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.

Section EndC.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Definition endc_env (oc ti Wv cv : Z) : s2env := gapp (gpatch E ti (cword oc (Wv + 1) cv)) [tword (oc + 2) ti] [].

  Lemma endc_tail : forall (Q : machine_state -> Prop) (s : st) (b0 : bool) (ti0 : Z) (rest : list (bool * Z)) (oc cv : Z)
      xra xt0 xt1 xt2 xs1 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    scopes s = (b0, ti0) :: rest -> (oc = 91 \/ oc = 123)%Z -> (0 <= cv <= CNT_MAX)%Z ->
    Z.of_nat (length (e_tws E)) = W s -> (ti0 < W s)%Z ->
    INV ScopeEnd (mkst (k s) (depth s) (W s + 1) (sb s) (scopes s)) -> MEMJ E (scopes s) fc m1 ->
    bytes_at psegs m1 (e_TAPE E + 8 * W s) (le8 (Z_to_bv 64 (tword (oc + 2) ti0))) ->
    (forall sc, scopes s = [sc] -> docend_k (endc_env oc ti0 (W s) cv) Q (mkst (k s) 0 (W s + 1) (sb s) [])) ->
    (forall sc ti rest', scopes s = sc :: (true, ti) :: rest' ->
       lab_k (endc_env oc ti0 (W s) cv) Q 0x481b8 (mkst (k s) (depth s - 1) (W s + 1) (sb s) ((true, ti) :: rest'))) ->
    (forall sc ti rest', scopes s = sc :: (false, ti) :: rest' ->
       lab_k (endc_env oc ti0 (W s) cv) Q 0x47e50 (mkst (k s) (depth s - 1) (W s + 1) (sb s) ((false, ti) :: rest'))) ->
    evt psegs Q (S2R E 0x4815c xra xt0 xt1 xt2 (Z_to_bv 64 (e_THIS E)) xs1 (Z_to_bv 64 (Z.shiftl oc 56)) (Z_to_bv 64 cv) (Z_to_bv 64 ti0) xa3 xa4
                     (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_IDX E + 4 * k s)) xa7 xs2 xs3 (Z_to_bv 64 (e_BUF E)) xs5 xs6 xs7
                     (Z_to_bv 64 (e_TAPE E + 8 * W s + 8)) xs9 xs10 (Z_to_bv 64 (e_SBUF E + sb s)) xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK.
    intros Q s b0 ti0 rest oc cv xra xt0 xt1 xt2 xs1 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 ESC HOC HCV GL HTW HI HM NEWCH KD KA KO.
    unfold CNT_MAX in HCV.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    pose proof (inv_scopes _ _ _ _ HI) as HSC.
    cbn [k depth W sb scopes slackW kind_ok] in *. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    rewrite ESC in HD1, HSC. cbn [length] in HD1.
    inversion HSC as [|? ? HTI HSC']; subst. cbn [snd] in HTI.
    s2_open_memj HM. rewrite ESC in OCR, IAR.
    pose proof (tape_store_ok E m1 ti0 TAPEW ltac:(lia)) as SOK2.
    zstep. zstep. zstep. s2norm. zstep. zstep. zstep. s2norm. zstep. zstep. zstep. zstep. s2norm.
    zstep. s2norm. zstep.
    rewrite (cword_machine (e_TAPE E) (W s) cv oc) by lia.
    apply (tape_img_patchZ E _ _ m1 ti0 (cword oc (W s + 1) cv) OK) in TIMG; [ | lia | apply cword_range; lia].
    store_done. zstep.
    apply (tape_img_app1 E _ _ m (tword (oc + 2) ti0) (e_TAPE E + 8 * W s)%Z OK) in TIMG; [ | exact NEWCH | rewrite zupd_length; lia | rewrite zupd_length; lia | apply tword_range; lia].
    if_cases K; zify_cond K.
    -
      assert (ER : rest = []) by (destruct rest; [reflexivity| cbn [length] in HD1; lia]). subst rest.
      replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
      zstep. zstep. zstep.
      eapply (KD _ ESC). cbn [k W].
      s2_close_mem; [exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].
    -
      destruct rest as [|[b1 ti1] rest']; [cbn [length] in HD1; lia|]. cbn [length] in HD1.
      pose proof (ia_rel_top _ _ _ _ (ia_rel_pop _ _ _ IAR)) as TOP.
      s2_cur_mem ltac:(fun m => pose proof (u8arr_read psegs m (e_IA E) ias (depth s - 1) _ (wa (e_IA E + (depth s + -1))) IAA
                  ltac:(replace (Z.to_nat (depth s - 1)) with (length rest' + 1)%nat by lia; exact TOP) ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD3).
      zstep. zstep. zstep. s2norm. zstep. zstep.
      replace (e_TAPE E + 8 * W s + 8)%Z with (e_TAPE E + 8 * (W s + 1))%Z by lia.
      replace (depth s + -1)%Z with (depth s - 1)%Z by lia.
      destruct b1; s2norm; zstep.
      +
        if_false. zstep.
        eapply (KA _ _ _ ESC). cbn [scopes].
        s2_close_memj; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
      +
        if_true.
        eapply (KO _ _ _ ESC). cbn [scopes].
        s2_close_memj; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
  Qed.

  Lemma seg_endc : forall (Q : machine_state -> Prop) (s : st) (oc : Z) (b0 : bool) (ti0 : Z) (rest : list (bool * Z))
      xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (oc = 91 \/ oc = 123)%Z -> scopes s = (b0, ti0) :: rest ->
    Z.of_nat (length (e_tws E)) = W s -> (ti0 < W s)%Z ->
    INV ScopeEnd (mkst (k s) (depth s) (W s + 1) (sb s) (scopes s)) -> MEMJ E (scopes s) fc m1 ->
    (forall cv sc, (0 <= cv <= CNT_MAX)%Z -> scopes s = [sc] -> docend_k (endc_env oc ti0 (W s) cv) Q (mkst (k s) 0 (W s + 1) (sb s) [])) ->
    (forall cv sc ti rest', (0 <= cv <= CNT_MAX)%Z -> scopes s = sc :: (true, ti) :: rest' ->
       lab_k (endc_env oc ti0 (W s) cv) Q 0x481b8 (mkst (k s) (depth s - 1) (W s + 1) (sb s) ((true, ti) :: rest'))) ->
    (forall cv sc ti rest', (0 <= cv <= CNT_MAX)%Z -> scopes s = sc :: (false, ti) :: rest' ->
       lab_k (endc_env oc ti0 (W s) cv) Q 0x47e50 (mkst (k s) (depth s - 1) (W s + 1) (sb s) ((false, ti) :: rest'))) ->
    evt psegs Q (S2ML E 0x48120 xra xt0 xt1 xt2 xs1 (Z_to_bv 64 oc) (Z_to_bv 64 (oc + 2)) xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6
                      (depth s) (k s) (W s) (sb s) F fc m1).
  Proof using OK.
    intros Q s oc b0 ti0 rest xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HOC ESC GL HTW HI HM KD KA KO.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    pose proof (inv_scopes _ _ _ _ HI) as HSC.
    cbn [k depth W sb scopes slackW kind_ok] in *. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL. s2_env OK.
    rewrite ESC in HD1, HSC, HM.
    cbn [length] in HD1.
    inversion HSC as [|? ? HTI HSC']; subst. cbn [snd] in HTI.
    s2_open_memj HM.
    pose proof (oc_rel_top _ _ _ _ OCR) as TOP.
    assert (DEQ : (2 * (length rest + 1))%nat = Z.to_nat (2 * depth s)) by lia.
    rewrite DEQ in TOP.
    pose proof (u32arr_read psegs m1 (e_OC E) ocs (2 * depth s) (Z_to_bv 64 ti0) (wa (e_OC E + 8 * depth s)) OCA TOP ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD1.
    pose proof (tape_store_ok E m1 (W s) TAPEW ltac:(lia)) as SOK1.
    zstep. zstep. zstep. zstep. zstep. zstep. s2norm.
    zstep. s2norm. zstep.
    zstep. rewrite (tword_machine (oc + 2) ti0) by lia. s2_note_store. store_done.

    destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
    s2_cur_mem ltac:(fun m => pose proof (u32arr_read psegs m (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD2).
    zstep. zstep. zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 64 (sx32 cnt)) as HCR. unfold bv_modulus in HCR. cbn in HCR.
    if_cases K; [ zify_cond K; rewrite <- (Z_to_bv_bv_unsigned (sx32 cnt)) | zstep ].
    1: eapply (endc_tail Q s b0 ti0 rest oc (bv_unsigned (sx32 cnt))).
    12: eapply (endc_tail Q s b0 ti0 rest oc 16777215%Z).
    all: try exact ESC; try exact HOC; try exact GL; try exact HTW; try exact NEWCH; try (unfold CNT_MAX; lia);
      try exact HI; try (rewrite ESC; s2_close_memj0).
    all: intros; first [ eapply KD | eapply KA | eapply KO ]; try eassumption; unfold CNT_MAX; lia.
  Qed.

End EndC.
