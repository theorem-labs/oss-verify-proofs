(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs RefMemcpyLib
 Ref_code_26e688_26f1d8 Ref_code_279784_279ef8 Ref_code_dd71c_ddd74            .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section CanaryFacts.
  Variable rnd : EntryDraw.

  (* [comment removed for export] *)
  Lemma lez_rnd4a : bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])).
  Proof. symmetry. apply u_lez4. reflexivity. Qed.
  Lemma lez_rnd4b : bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])).
  Proof. symmetry. apply u_lez4. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rd_guard8_gen : forall segs D (g : Z) (l0 l1 : list byte),
    length l0 = 4%nat -> length l1 = 4%nat -> (0 <= g)%Z -> (g + 8 <= 2^64)%Z ->
    rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) l0) (Z_to_bv 64 (g + 4)) l1) (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0])
        (Z_to_bv 64 g) 8
    = Some (firstn 1 l0 ++ [Z_to_bv 8 0] ++ skipn 2 l0 ++ l1).
  Proof.
    intros segs D g l0 l1 L0 L1 G0 G8.
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite rdn_wbytes_out_Z by (rewrite L1; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      eapply (SeqExec.rdn_firstn segs _ 4); [| lia]. rewrite <- L0. apply rdn_wbytes_hit.
      rewrite L0, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    rewrite word_add_nat, u_Z2bv by lia. change (Z.of_nat 1) with 1%Z.
    apply rdn_app.
    { change 1%nat with (length [Z_to_bv 8 0]). apply rdn_wbytes_hit.
      rewrite u_Z2bv by lia. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    rewrite word_add_nat, u_Z2bv by lia. replace (g + 1 + Z.of_nat 1)%Z with (g + 2)%Z by lia.
    apply rdn_app.
    { rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite rdn_wbytes_out_Z by (rewrite L1; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      replace (Z_to_bv 64 (g + 2)) with (Z_to_bv 64 g + nat_to_word 2)%bv
        by (rewrite word_add_nat, u_Z2bv by lia; reflexivity).
      replace 2%nat with (4 - 2)%nat at 2 by reflexivity. rewrite <- L0.
      apply (SeqExec.rdn_skipn segs _ (length l0)); [| lia]. apply rdn_wbytes_hit.
      rewrite L0, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    rewrite word_add_nat, u_Z2bv by lia. replace (g + 2 + Z.of_nat 2)%Z with (g + 4)%Z by lia.
    rewrite rdn_wbytes_out_Z by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite <- L1. apply rdn_wbytes_hit. rewrite L1, u_Z2bv by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.

  Lemma rd_guard8 : forall D,
    rdn SEGS (wbytes (wbytes (wbytes D (Z_to_bv 64 0x30f4b8) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 0x30f4bc) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])
                (Z_to_bv 64 0x30f4b9) [Z_to_bv 8 0]) (Z_to_bv 64 0x30f4b8) 8
    = Some (canary_bytes rnd).
  Proof.
    intros D.
    exact (rd_guard8_gen SEGS D 0x30f4b8 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]
             eq_refl eq_refl ltac:(lia) ltac:(lia)).
  Qed.

  Lemma lez_canary : bytes_le_to_Z (canary_bytes rnd) = bv_unsigned (canary_w rnd).
  Proof.
    unfold canary_w. symmetry.
    pose proof (lez_bound_len (canary_bytes rnd) 8 eq_refl) as B. change (8 * Z.of_nat 8)%Z with 64%Z in B.
    apply u_Z2bv; lia.
  Qed.
End CanaryFacts.

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rnd av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (rb rnd))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rnd av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). unfold rb. apply E. exact Hjn.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd4a : forall J D,
    rdn SEGS (CM J D) (rnd_w sp0 av ev) 4 = Some [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3].
  Proof.
    intros J D. rewrite <- (firstn4_rb rnd).
    rewrite <- (Z_to_bv_bv_unsigned 64 (rnd_w sp0 av ev)) at 1.
    rewrite <- (Z.add_0_r (bv_unsigned (rnd_w sp0 av ev))). change 0%Z with (Z.of_nat 0).
    exact (rd_rnd J D 0 4 ltac:(lia)).
  Qed.
  Lemma rd_rnd4b : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 4)) 4 = Some [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7].
  Proof.
    intros J D. rewrite <- (firstn4_skipn4_rb rnd). change 4%Z with (Z.of_nat 4) at 1.
    exact (rd_rnd J D 4 4 ltac:(lia)).
  Qed.


  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RNDa := first [ apply rd_rnd4a | eapply rdn_addr; [apply rd_rnd4a | symmetry; apply Z_to_bv_bv_unsigned] ].
  Ltac RD_RNDb := apply rd_rnd4b.

  (* [comment removed for export] *)
  Ltac RD_GUARD := rewrite rdn_cmem_data by region_side; apply rd_guard8.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3077240 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3077240) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x26e7ec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x26e7e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_26e79c D_26e79c (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26e7a0 D_26e7a0.  (* [comment removed for export] *)
      sv F_26ed40 D_26ed40 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_26ed44 D_26ed44 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 2549740) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_26ed48 D_26ed48 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_26ed4c D_26ed4c ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_26ed50 D_26ed50.  (* [comment removed for export] *)
      ld_step F_26ed54 D_26ed54 (word_to_le_bytes 8 (Z_to_bv 64 3208376)) (Z_to_bv 64 3208376) ltac:(rd_img img_2db0e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26ed58 D_26ed58.  (* [comment removed for export] *)
      sn F_26ed5c D_26ed5c.  (* [comment removed for export] *)
      stepiv F_279880 D_279880 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_279884 D_279884 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_279994 D_279994.  (* [comment removed for export] *)
      sn F_279998 D_279998.  (* [comment removed for export] *)
      stepb_ft F_27999c D_27999c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2799a0 D_2799a0.  (* [comment removed for export] *)
      stepb_tk F_2799a4 D_2799a4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2799dc D_2799dc.  (* [comment removed for export] *)
      stepb_ft F_2799e0 D_2799e0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2799e4 D_2799e4 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])) ltac:(RD_RNDa) ltac:(apply lez_rnd4a).  (* [comment removed for export] *)
      ld_step F_2799e8 D_2799e8 [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])) ltac:(RD_RNDb) ltac:(apply lez_rnd4b).  (* [comment removed for export] *)
      stw F_2799ec D_2799ec (Z_to_bv 64 3208376) (LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] eq_refl).
      stw F_2799f0 D_2799f0 (Z_to_bv 64 3208380) (LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] eq_refl).
      sn F_2799f4 D_2799f4.  (* [comment removed for export] *)
      sv F_2799f8 D_2799f8 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_2799fc D_2799fc.  (* [comment removed for export] *)
      stepb_tk F_279a00 D_279a00 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_279c40 D_279c40.  (* [comment removed for export] *)
      stepb_ft F_279c44 D_279c44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_279c48 D_279c48.  (* [comment removed for export] *)
      stepb_ft F_279c4c D_279c4c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_279c50 D_279c50 (0x26ed9c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26ed60 D_26ed60.  (* [comment removed for export] *)
      sn F_26ed7c D_26ed7c.  (* [comment removed for export] *)
      ld_step F_26ed80 D_26ed80 (word_to_le_bytes 8 (Z_to_bv 64 3208376)) (Z_to_bv 64 3208376) ltac:(rd_img img_2db0e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_26ed84 D_26ed84 (Z_to_bv 64 3208377) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_26ed88 D_26ed88 (canary_bytes rnd) (canary_w rnd) ltac:(RD_GUARD) ltac:(apply lez_canary).  (* [comment removed for export] *)
      sn F_26ed8c D_26ed8c.  (* [comment removed for export] *)
      stw F_26ed90 D_26ed90 (Z_to_bv 64 3077224) (canary_w rnd) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_26ed94 D_26ed94 (word_to_le_bytes 8 (Z_to_bv 64 2549740)) (Z_to_bv 64 2549740) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26ed98 D_26ed98 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_26ed9c D_26ed9c (0x26e7ec : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3077240 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 0) ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3077240) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 907448) ->
        getr regs' 11 = (argc_w av) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 18 = (Z_to_bv 64 0) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0x26e9ac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x26e7ec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_26e7a4 D_26e7a4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e7a8 D_26e7a8 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_26e7ac D_26e7ac ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_26e7b0 D_26e7b0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_26e7b4 D_26e7b4 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26e7b8 D_26e7b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26e7bc D_26e7bc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_26e7c0 D_26e7c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26e8a0 D_26e8a0 (word_to_le_bytes 8 (Z_to_bv 64 2550144)) (Z_to_bv 64 2550144) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e8a4 D_26e8a4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e8a8 D_26e8a8 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e8ac D_26e8ac (word_to_le_bytes 8 (Z_to_bv 64 907448)) (Z_to_bv 64 907448) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26e8b0 D_26e8b0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_26e8b4 D_26e8b4 (0x26e980 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26e938 D_26e938.  (* [comment removed for export] *)
      sn F_26e93c D_26e93c.  (* [comment removed for export] *)
      sn F_26e940 D_26e940.  (* [comment removed for export] *)
      sv F_26e944 D_26e944 (argc_w av).  (* [comment removed for export] *)
      sv F_26e948 D_26e948 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_26e94c D_26e94c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e950 D_26e950 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e954 D_26e954 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e958 D_26e958 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26e95c D_26e95c (sp0).  (* [comment removed for export] *)
      stepret F_26e960 D_26e960 (0x26e9ac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3077240 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 907448 ->
    getr regs 11 = argc_w av ->
    getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
    getr regs 18 = Z_to_bv 64 0 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 2550064) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3077240) ->
        getr regs' 8 = (Z_to_bv 64 2617288) ->
        getr regs' 9 = (Z_to_bv 64 2617280) ->
        getr regs' 18 = (Z_to_bv 64 907448) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0xdd7b0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2550240))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x26e9ac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_26e964 D_26e964 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_26e968 D_26e968 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26e96c D_26e96c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26e970 D_26e970 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26e974 D_26e974 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26e978 D_26e978 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_26e97c D_26e97c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_26e980 D_26e980 (argc_w av).  (* [comment removed for export] *)
      sn F_26e984 D_26e984.  (* [comment removed for export] *)
      stepiv F_26e988 D_26e988 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_26e98c D_26e98c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_26e990 D_26e990 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_26e994 D_26e994.  (* [comment removed for export] *)
      sv F_26e8b8 D_26e8b8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_26e8bc D_26e8bc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 2550240) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26e8c0 D_26e8c0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26e8c4 D_26e8c4 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_26e8c8 D_26e8c8.  (* [comment removed for export] *)
      stepret F_26e688 D_26e688 (0x26e914 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26e8cc D_26e8cc.  (* [comment removed for export] *)
      sn F_26e8d0 D_26e8d0.  (* [comment removed for export] *)
      ld_step F_26e8d4 D_26e8d4 (word_to_le_bytes 8 (Z_to_bv 64 2617288)) (Z_to_bv 64 2617288) ltac:(rd_img img_2db108_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e8d8 D_26e8d8 (word_to_le_bytes 8 (Z_to_bv 64 2617280)) (Z_to_bv 64 2617280) ltac:(rd_img img_2db110_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_26e8dc D_26e8dc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26e8e0 D_26e8e0 (word_to_le_bytes 8 (Z_to_bv 64 907184)) (Z_to_bv 64 907184) ltac:(rd_img img_27ef88_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_26e8e4 D_26e8e4 (0xdd7b0 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 2550064 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3077240 ->
    getr regs 8 = Z_to_bv 64 2617288 ->
    getr regs 9 = Z_to_bv 64 2617280 ->
    getr regs 18 = Z_to_bv 64 907448 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 2550256) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3077240) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 907448) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0xdd8b8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2550240))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 2550064))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 2617288))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 3000496) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0xdd7b0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549732))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3208968))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2549740))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2550240))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3208352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208360) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3208992) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3209000) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3077256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3077232) (word_to_le_bytes 8 (Z_to_bv 64 3077256))) (Z_to_bv 64 3077040) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3208968) ([Z_to_bv 8 1])) (Z_to_bv 64 3077080) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3077072) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3077192) (word_to_le_bytes 8 (Z_to_bv 64 3209024))) (Z_to_bv 64 3077160) (word_to_le_bytes 8 (Z_to_bv 64 3077160))) (Z_to_bv 64 3077048) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077056) (word_to_le_bytes 8 (Z_to_bv 64 3077040))) (Z_to_bv 64 3077064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3208376) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3208380) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3208377) ([Z_to_bv 8 0])) (Z_to_bv 64 3077224) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_dd768 D_dd768 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_dd76c D_dd76c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 2550064) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dd770 D_dd770 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 2617288) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_dd774 D_dd774 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_dd778 D_dd778.  (* [comment removed for export] *)
      sn F_dd77c D_dd77c.  (* [comment removed for export] *)
      lb_step F_dd780 D_dd780 (Z_to_bv 8 0) ltac:(rd_img img_2dc870_1).  (* [comment removed for export] *)
      sn F_dd784 D_dd784.  (* [comment removed for export] *)
      stepb_tk F_dd788 D_dd788 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_dd794 D_dd794.  (* [comment removed for export] *)
      sn F_dd798 D_dd798.  (* [comment removed for export] *)
      sn F_dd79c D_dd79c.  (* [comment removed for export] *)
      stw F_dd7a0 D_dd7a0 (Z_to_bv 64 3000496) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_dd7a4 D_dd7a4.  (* [comment removed for export] *)
      ld_step F_dd7a8 D_dd7a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2dab10_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_dd7ac D_dd7ac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_dd7cc D_dd7cc (word_to_le_bytes 8 (Z_to_bv 64 2550064)) (Z_to_bv 64 2550064) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dd7d0 D_dd7d0 (word_to_le_bytes 8 (Z_to_bv 64 2617288)) (Z_to_bv 64 2617288) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_dd7d4 D_dd7d4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_dd7d8 D_dd7d8 (0x26e930 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26e8e8 D_26e8e8.  (* [comment removed for export] *)
      stepb_ft F_26e8ec D_26e8ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26e8f0 D_26e8f0 (word_to_le_bytes 8 (Z_to_bv 64 2550240)) (Z_to_bv 64 2550240) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e8f4 D_26e8f4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26e8f8 D_26e8f8 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26e8fc D_26e8fc (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_26e900 D_26e900 (0x26e9e0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_26e998 D_26e998 (argc_w av).  (* [comment removed for export] *)
      sv F_26e99c D_26e99c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_26e9a0 D_26e9a0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_26e9a4 D_26e9a4 (0xdd8b8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
