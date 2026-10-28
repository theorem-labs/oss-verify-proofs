(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Section ScopeEnd.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Lemma seg_scope_end : forall (Q : machine_state -> Prop) (oc : Z) (s : st) (a1z a2z : Z)
      xra xt1 xt2 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6
      j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    a1z = ((oc + 2) * 72057594037927936)%Z -> a2z = ((oc + 1) * 16777216)%Z ->
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j168; CB 8 j176; CB 8 j208; CB 8 j272]
         (scopes s) fc m1 ->
    INV ScopeEnd s -> (oc = 91 \/ oc = 123)%Z ->
    Z.of_nat (length (e_tws E)) = (W s - 1)%Z -> (forall b ti rest, scopes s = (b, ti) :: rest -> (ti < W s - 1)%Z) ->
    (forall cv sc, (0 <= cv <= CNT_MAX)%Z -> scopes s = [sc] -> docend_k (endc_env E oc (snd sc) (W s - 1) cv) Q (mkst (k s) (depth s - 1) (W s) (sb s) [])) ->
    (forall cv sc ti rest, (0 <= cv <= CNT_MAX)%Z -> scopes s = sc :: (true, ti) :: rest -> arrcont_k (endc_env E oc (snd sc) (W s - 1) cv) Q (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti) :: rest))) ->
    (forall cv sc ti rest, (0 <= cv <= CNT_MAX)%Z -> scopes s = sc :: (false, ti) :: rest -> objcont_k (endc_env E oc (snd sc) (W s - 1) cv) Q (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti) :: rest))) ->
    evt asegs Q (S2R E 0xcf43c xra (Z_to_bv 64 (SHA (e_THIS E + 88))) xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_IDX E + 4 * k s)) (Z_to_bv 64 a1z) (Z_to_bv 64 a2z) (Z_to_bv 64 oc) xa4 xa5 (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_THIS E + 88)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_SBUF E + sb s)) xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (e_TAPE E + 8 * (W s - 1))) xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK SHZ.
    intros Q oc s a1z a2z xra xt1 xt2 xa4 xa5 xs7 xs9 xt3 xt4 xt5 xt6 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j168 j176 j208 j272 F fc m1 -> -> HM.
    intros HI HOC GLT HTW KD KA KO. unfold CNT_MAX in KD, KA, KO.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    pose proof (inv_scopes _ _ _ _ HI) as HSC. pose proof (inv_kind _ _ _ _ HI) as HKD.
    cbn [k depth W sb scopes slackW kind_ok] in *. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. s2_env OK.
    destruct (scopes s) as [|[b0 ti0] rest] eqn:ESC; [congruence|]. clear HKD. specialize (HTW _ _ _ eq_refl).
    cbn [length] in HD1.
    inversion HSC as [|? ? HTI HSC']; subst. cbn [snd] in HTI.
    s2_open_mem HM.
    pose proof (oc_rel_top _ _ _ _ OCR) as TOP.
    assert (DEQ : (2 * (length rest + 1))%nat = Z.to_nat (2 * depth s)) by lia.
    rewrite DEQ in TOP.
    pose proof (u32arr_read asegs m1 (e_OC E) ocs (2 * depth s) (Z_to_bv 64 ti0) (wa (e_OC E + 8 * depth s)) OCA TOP ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD3.
    grun.
    destruct (nth_error_ex ocs (Z.to_nat (2 * depth s + 1)) ltac:(lia)) as [cnt Hcnt].
    s2_cur_mem ltac:(fun m => pose proof (u32arr_read asegs m (e_OC E) ocs (2 * depth s + 1) cnt (wa (e_OC E + 8 * depth s + 4)) OCA Hcnt ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD4).
    grun_to 0xcf4ec%Z.
    pose proof (bv_unsigned_in_range 64 (sx32 cnt)) as HCR. unfold bv_modulus in HCR. cbn in HCR.
    zstep.
    if_cases KC; [ zify_cond KC | zify_cond KC; gstep; gstep ].

    2: pose proof (sx32_hi24_zero cnt KC) as HCV.
    all: clear KC.
    all: grun_to 0xcf514%Z.

    1: zstep; gnorm; s2_endc_patch_a oc ti0 16777215%Z.
    2: zstep; gnorm; s2_endc_patch_a oc ti0 (bv_unsigned (sx32 cnt)).
    all: s2_endc_close_a oc ti0.
    all: zstep.
    all: if_cases K; zify_cond K.

    1,3: assert (ER : rest = []) by (destruct rest; [reflexivity| cbn [length] in HD1; lia]); subst rest.
    1,2: grun_to 0xc2f40%Z.
    1,2: replace (e_TAPE E + 8 * (W s - 1) + 8)%Z with (e_TAPE E + 8 * W s)%Z by lia.
    1: eapply (KD 16777215%Z _ ltac:(lia) eq_refl); cbn [k W scopes]; s2_close_mem; [exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].
    1: eapply (KD (bv_unsigned (sx32 cnt)) _ HCV eq_refl); cbn [k W scopes]; s2_close_mem; [exact OCL | apply oc_rel_nil | exact IAL | apply ia_rel_nil].

    all: destruct rest as [|[b1 ti1] rest']; [cbn [length] in HD1; lia|]; cbn [length] in HD1.
    all: pose proof (ia_rel_top _ _ _ _ (ia_rel_pop _ _ _ IAR)) as TOPI.
    all: grun.
    all: s2_cur_mem ltac:(fun m => pose proof (u8arr_read asegs m (e_IA E) ias (depth s - 1) _ (wa (e_IA E + (depth s + -1))) IAA
                  ltac:(replace (Z.to_nat (depth s - 1)) with (length rest' + 1)%nat by lia; exact TOPI) ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD5).
    all: destruct b1; grun.

    1,3: if_true.
    1,2: replace (depth s + -1)%Z with (depth s - 1)%Z by lia.
    1,2: replace (e_TAPE E + 8 * (W s - 1) + 8)%Z with (e_TAPE E + 8 * W s)%Z by lia.
    1: eapply (KA 16777215%Z _ _ _ ltac:(lia) eq_refl); cbn [scopes k depth W sb];
         s2_close_mem; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
    1: eapply (KA (bv_unsigned (sx32 cnt)) _ _ _ HCV eq_refl); cbn [scopes k depth W sb];
         s2_close_mem; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
    all: if_false.
    all: grun_to 0xca8f8%Z.
    all: replace (depth s + -1)%Z with (depth s - 1)%Z by lia.
    all: replace (e_TAPE E + 8 * (W s - 1) + 8)%Z with (e_TAPE E + 8 * W s)%Z by lia.
    1: eapply (KO 16777215%Z _ _ _ ltac:(lia) eq_refl); cbn [scopes k depth W sb];
         s2_close_mem; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
    1: eapply (KO (bv_unsigned (sx32 cnt)) _ _ _ HCV eq_refl); cbn [scopes k depth W sb];
         s2_close_mem; [exact OCL | exact (oc_rel_pop _ _ _ OCR) | exact IAL | exact (ia_rel_pop _ _ _ IAR)].
  Qed.
End ScopeEnd.
