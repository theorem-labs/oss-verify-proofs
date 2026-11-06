(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs Sj_tables Sj_stage2_auto Sj_stage2_objf Sj_stage2_keya.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section KeyA2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).
  Notation bs := (e_bs E).

  Lemma seg_key_a : forall (Q : machine_state -> Prop) (s : st),
    INV ObjBegin s -> (depth s + 1 < MAXDEPTH)%Z -> e_tok E (k s) = c_quote ->
    Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    (forall h, exit_k (gapp E [h; tword t_str (sb s)] []) Q) ->
    (forall d h, string_ok (e_bs E) (e_idxs E) (k s) d ->
       keyend_k (gapp E [h; tword t_str (sb s)] []) Q (k s) (depth s + 1) (W s + 2) (sb s) d ((false, W s) :: scopes s)) ->
    keya_k E Q s.
  Proof using OK.
    intros Q s HI HDP HQ GLT GLS KX KE. unfold keya_k.
    intros xra xt0 xt1 xt2 xa0 xa2 xa4 xa5 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt5 xt6 j0 j1 j2 j3 j4 j6 j7 j8 j9 F fc m1 HM.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_depth _ _ _ _ HI) as [HD1 HD2].
    destruct (inv_sb _ _ _ _ HI) as [HSB0 HSB]. cbn [slackW slackS] in *. unfold MAXDEPTH in *.
    pose proof (n_bound E OK) as HN. pose proof (n_le_len _ _ (ok_s1 _ OK)) as HNL.
    assert (HKN : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E) (e_idxs E)); [exact HK | rewrite HQ; unfold c_quote; lia]).
    destruct (tok_string _ _ (ok_s1 _ OK) (k s) ltac:(lia) HQ) as (j & HC & HJ1 & HJ2).
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HO. pose proof (off_range _ _ (ok_s1 _ OK) (k s + 1) ltac:(lia)) as HO1.
    s2_env OK.
    s2_open_mem HM.
    pose proof (u32arr_store_ok psegs m1 (e_OC E) ocs (2 * (depth s + 1) + 1) (wa (e_OC E + 8 * (depth s + 1) + 4)) OCA ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as SOK1.
    do 18 zstep.
    s2_old_mem ltac:(fun m =>
      pose proof (u32arr_write psegs m (e_OC E) ocs (2 * (depth s + 1) + 1) (Z_to_bv 64 1) OCA ltac:(lia)) as OCA').
    replace (e_OC E + 4 * (2 * (depth s + 1) + 1))%Z with (e_OC E + 8 * (depth s + 1) + 4)%Z in OCA' by lia.
    store_done.
    do 11 zstep. s2norm.
    zstep. s2norm. rewrite (str_word_machine (e_SBUF E) (sb s)) by lia. s2_note_store. s2_store_done_wr.
    s2_cur_mem ltac:(fun m => destruct (timg_hole8 E _ _ m (W s) TIMG ltac:(lia)) as (hv & HH);
      pose proof (bv_unsigned_in_range 64 hv) as HVR; unfold bv_modulus in HVR; cbn in HVR;
      rewrite <- (Z_to_bv_bv_unsigned hv) in HH;
      apply (tape_img_app2 E _ _ m (bv_unsigned hv) (tword t_str (sb s)) (e_TAPE E + 8 * W s)%Z (e_TAPE E + 8 * W s + 8)%Z OK) in TIMG;
      [ | exact HH | exact NEWCH | lia | lia | lia | lia | apply tword_range; unfold t_str; lia ]).
    do 5 zstep.
    set (E' := gapp E [bv_unsigned hv; tword t_str (sb s)] []) in *.
    specialize (KX (bv_unsigned hv)). fold E' in KX.
    assert (OK' : env_ok E') by (apply env_ok_gapp; exact OK).
    assert (HROOM : (0 <= sb s /\ sb s + (j - e_off E' (k s)) + 4 <= e_scap E')%Z) by (subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs e_sbs] in *; lia).
    assert (KE' : forall d', (0 <= d' <= j - e_off E' (k s) - 1)%Z ->
                   keyend_k E' Q (k s) (depth s + 1) (W s + 2) (sb s) d' ((false, W s) :: scopes s)).
    { intros d' Hd'. apply KE. exists j. split; [exact HC | subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs e_sbs] in *; lia]. }
    pose proof (keya_loop E' OK' Q (k s) (depth s + 1) (W s + 2) (sb s) ((false, W s) :: scopes s) (e_off E' (k s)) j
                  HROOM ltac:(subst E'; cbn [gapp s2_ghost e_scap e_bs e_idxs e_sbs] in *; lia) ltac:(subst E'; cbn [gapp s2_ghost e_sbs]; rewrite length_app; cbn [length]; lia)
                  KX KE' (S (Z.to_nat (j - e_off E' (k s)))) (e_off E' (k s) + 1)%Z 0%Z) as L.
    replace (e_SBUF E' + sb s + 4 + 0)%Z with (e_SBUF E' + sb s + 4)%Z in L by lia.
    replace (e_BUF E' + (e_off E' (k s) + 1))%Z with (e_BUF E' + e_off E' (k s) + 1)%Z in L by lia.
    replace (e_TAPE E' + 8 * (W s + 2))%Z with (e_TAPE E' + 8 * W s + 16)%Z in L by lia.
    eapply L; [apply PS_init; exact HC | subst E'; cbn [gapp s2_ghost e_bs e_idxs]; lia | ].
    s2_close_mem; [rewrite upd_length; exact OCL | | exact IAL | exact IAR].
    apply oc_rel_upd_other; [exact OCR|]. intros jj Hjj. cbn [length] in Hjj. lia.
  Qed.
End KeyA2.
