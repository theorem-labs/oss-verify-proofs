(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib Ub_code_6b184_6b4a8 Ub_code_6b4a8_6bc18 Ub_code_79454_79c00.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefImg RefStartupDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
    rdn SEGS (wbytes (wbytes (wbytes D (Z_to_bv 64 0xb69b0) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 0xb69b4) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])
                (Z_to_bv 64 0xb69b1) [Z_to_bv 8 0]) (Z_to_bv 64 0xb69b0) 8
    = Some (canary_bytes rnd).
  Proof.
    intros D.
    exact (rd_guard8_gen SEGS D 0xb69b0 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]
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
    getr regs 4 = Z_to_bv 64 616816 ->
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
        getr regs' 4 = (Z_to_bv 64 616816) ->
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
        G (mkst regs' (0x6b2a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x6b298 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_6b298 D_6b298 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_6b29c D_6b29c.  (* [comment removed for export] *)
      sv F_6b830 D_6b830 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_6b834 D_6b834 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 438944) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_6b838 D_6b838 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_6b83c D_6b83c ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_6b840 D_6b840.  (* [comment removed for export] *)
      ld_step F_6b844 D_6b844 (word_to_le_bytes 8 (Z_to_bv 64 747952)) (Z_to_bv 64 747952) ltac:(rd_img img_83b30_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_6b848 D_6b848.  (* [comment removed for export] *)
      sn F_6b84c D_6b84c.  (* [comment removed for export] *)
      stepiv F_79550 D_79550 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_79554 D_79554 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_79664 D_79664.  (* [comment removed for export] *)
      sn F_79668 D_79668.  (* [comment removed for export] *)
      stepb_ft F_7966c D_7966c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_79670 D_79670.  (* [comment removed for export] *)
      stepb_tk F_79674 D_79674 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_796ac D_796ac.  (* [comment removed for export] *)
      stepb_ft F_796b0 D_796b0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_796b4 D_796b4 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])) ltac:(RD_RNDa) ltac:(apply lez_rnd4a).  (* [comment removed for export] *)
      ld_step F_796b8 D_796b8 [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])) ltac:(RD_RNDb) ltac:(apply lez_rnd4b).  (* [comment removed for export] *)
      stw F_796bc D_796bc (Z_to_bv 64 747952) (LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] eq_refl).
      stw F_796c0 D_796c0 (Z_to_bv 64 747956) (LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] eq_refl).
      sn F_796c4 D_796c4.  (* [comment removed for export] *)
      sv F_796c8 D_796c8 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_796cc D_796cc.  (* [comment removed for export] *)
      stepb_tk F_796d0 D_796d0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_79910 D_79910.  (* [comment removed for export] *)
      stepb_ft F_79914 D_79914 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_79918 D_79918.  (* [comment removed for export] *)
      stepb_ft F_7991c D_7991c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_79920 D_79920 (0x6b850 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b850 D_6b850.  (* [comment removed for export] *)
      sn F_6b86c D_6b86c.  (* [comment removed for export] *)
      ld_step F_6b870 D_6b870 (word_to_le_bytes 8 (Z_to_bv 64 747952)) (Z_to_bv 64 747952) ltac:(rd_img img_83b30_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_6b874 D_6b874 (Z_to_bv 64 747953) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_6b878 D_6b878 (canary_bytes rnd) (canary_w rnd) ltac:(RD_GUARD) ltac:(apply lez_canary).  (* [comment removed for export] *)
      sn F_6b87c D_6b87c.  (* [comment removed for export] *)
      stw F_6b880 D_6b880 (Z_to_bv 64 616800) (canary_w rnd) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_6b884 D_6b884 (word_to_le_bytes 8 (Z_to_bv 64 438944)) (Z_to_bv 64 438944) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6b888 D_6b888 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_6b88c D_6b88c (0x6b2a0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 616816 ->
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
        getr regs' 4 = (Z_to_bv 64 616816) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 178924) ->
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
        G (mkst regs' (0x6b460 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x6b2a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_6b2a0 D_6b2a0 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b2a4 D_6b2a4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_6b2a8 D_6b2a8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_6b2ac D_6b2ac (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_6b2b0 D_6b2b0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_6b2b4 D_6b2b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6b2b8 D_6b2b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_6b2bc D_6b2bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6b39c D_6b39c (word_to_le_bytes 8 (Z_to_bv 64 439348)) (Z_to_bv 64 439348) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b3a0 D_6b3a0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b3a4 D_6b3a4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b3a8 D_6b3a8 (word_to_le_bytes 8 (Z_to_bv 64 178924)) (Z_to_bv 64 178924) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6b3ac D_6b3ac (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_6b3b0 D_6b3b0 (0x6b434 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b434 D_6b434.  (* [comment removed for export] *)
      sn F_6b438 D_6b438.  (* [comment removed for export] *)
      sn F_6b43c D_6b43c.  (* [comment removed for export] *)
      sv F_6b440 D_6b440 (argc_w av).  (* [comment removed for export] *)
      sv F_6b444 D_6b444 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_6b448 D_6b448 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b44c D_6b44c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b450 D_6b450 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b454 D_6b454 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6b458 D_6b458 (sp0).  (* [comment removed for export] *)
      stepret F_6b45c D_6b45c (0x6b460 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 616816 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 178924 ->
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
        getr regs' 1 = (Z_to_bv 64 439268) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 616816) ->
        getr regs' 8 = (Z_to_bv 64 517280) ->
        getr regs' 9 = (Z_to_bv 64 517200) ->
        getr regs' 18 = (Z_to_bv 64 178924) ->
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
        G (mkst regs' (0x2b9e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 439444))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x6b460 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_6b460 D_6b460 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_6b464 D_6b464 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6b468 D_6b468 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6b46c D_6b46c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6b470 D_6b470 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6b474 D_6b474 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_6b478 D_6b478 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_6b47c D_6b47c (argc_w av).  (* [comment removed for export] *)
      sn F_6b480 D_6b480.  (* [comment removed for export] *)
      stepiv F_6b484 D_6b484 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_6b488 D_6b488 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_6b48c D_6b48c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_6b490 D_6b490.  (* [comment removed for export] *)
      sv F_6b3b4 D_6b3b4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_6b3b8 D_6b3b8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 439444) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6b3bc D_6b3bc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6b3c0 D_6b3c0 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_6b3c4 D_6b3c4.  (* [comment removed for export] *)
      stepret F_6b184 D_6b184 (0x6b3c8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3c8 D_6b3c8.  (* [comment removed for export] *)
      sn F_6b3cc D_6b3cc.  (* [comment removed for export] *)
      ld_step F_6b3d0 D_6b3d0 (word_to_le_bytes 8 (Z_to_bv 64 517280)) (Z_to_bv 64 517280) ltac:(rd_img img_83b50_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b3d4 D_6b3d4 (word_to_le_bytes 8 (Z_to_bv 64 517200)) (Z_to_bv 64 517200) ltac:(rd_img img_83b58_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_6b3d8 D_6b3d8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 178664)) (Z_to_bv 64 178664) ltac:(rd_img img_7e450_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2b9e8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
