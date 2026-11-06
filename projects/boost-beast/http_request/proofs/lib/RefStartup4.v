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

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs RefMemcpyLib
 Ref_code_2ab1c_2b108 Ref_code_66e58_6717c Ref_code_6717c_678ec Ref_code_75128_758d4.
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
    rdn SEGS (wbytes (wbytes (wbytes D (Z_to_bv 64 0xb2690) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 0xb2694) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])
                (Z_to_bv 64 0xb2691) [Z_to_bv 8 0]) (Z_to_bv 64 0xb2690) 8
    = Some (canary_bytes rnd).
  Proof.
    intros D.
    exact (rd_guard8_gen SEGS D 0xb2690 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]
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
    getr regs 4 = Z_to_bv 64 599632 ->
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
        getr regs' 4 = (Z_to_bv 64 599632) ->
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
        G (mkst regs' (0x66f74 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x66f6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_66f6c D_66f6c (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_66f70 D_66f70.  (* [comment removed for export] *)
      sv F_67504 D_67504 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_67508 D_67508 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 421748) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_6750c D_6750c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_67510 D_67510 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_67514 D_67514.  (* [comment removed for export] *)
      ld_step F_67518 D_67518 (word_to_le_bytes 8 (Z_to_bv 64 730768)) (Z_to_bv 64 730768) ltac:(rd_img img_7f808_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_6751c D_6751c.  (* [comment removed for export] *)
      sn F_67520 D_67520.  (* [comment removed for export] *)
      stepiv F_75224 D_75224 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_75228 D_75228 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_75338 D_75338.  (* [comment removed for export] *)
      sn F_7533c D_7533c.  (* [comment removed for export] *)
      stepb_ft F_75340 D_75340 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_75344 D_75344.  (* [comment removed for export] *)
      stepb_tk F_75348 D_75348 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_75380 D_75380.  (* [comment removed for export] *)
      stepb_ft F_75384 D_75384 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_75388 D_75388 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])) ltac:(RD_RNDa) ltac:(apply lez_rnd4a).  (* [comment removed for export] *)
      ld_step F_7538c D_7538c [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])) ltac:(RD_RNDb) ltac:(apply lez_rnd4b).  (* [comment removed for export] *)
      stw F_75390 D_75390 (Z_to_bv 64 730768) (LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] eq_refl).
      stw F_75394 D_75394 (Z_to_bv 64 730772) (LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] eq_refl).
      sn F_75398 D_75398.  (* [comment removed for export] *)
      sv F_7539c D_7539c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_753a0 D_753a0.  (* [comment removed for export] *)
      stepb_tk F_753a4 D_753a4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_755e4 D_755e4.  (* [comment removed for export] *)
      stepb_ft F_755e8 D_755e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_755ec D_755ec.  (* [comment removed for export] *)
      stepb_ft F_755f0 D_755f0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_755f4 D_755f4 (0x67524 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_67524 D_67524.  (* [comment removed for export] *)
      sn F_67540 D_67540.  (* [comment removed for export] *)
      ld_step F_67544 D_67544 (word_to_le_bytes 8 (Z_to_bv 64 730768)) (Z_to_bv 64 730768) ltac:(rd_img img_7f808_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_67548 D_67548 (Z_to_bv 64 730769) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_6754c D_6754c (canary_bytes rnd) (canary_w rnd) ltac:(RD_GUARD) ltac:(apply lez_canary).  (* [comment removed for export] *)
      sn F_67550 D_67550.  (* [comment removed for export] *)
      stw F_67554 D_67554 (Z_to_bv 64 599616) (canary_w rnd) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_67558 D_67558 (word_to_le_bytes 8 (Z_to_bv 64 421748)) (Z_to_bv 64 421748) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6755c D_6755c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_67560 D_67560 (0x66f74 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 599632 ->
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
        getr regs' 4 = (Z_to_bv 64 599632) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 175208) ->
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
        G (mkst regs' (0x67134 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x66f74 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_66f74 D_66f74 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_66f78 D_66f78 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_66f7c D_66f7c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_66f80 D_66f80 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_66f84 D_66f84 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_66f88 D_66f88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_66f8c D_66f8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_66f90 D_66f90 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_67070 D_67070 (word_to_le_bytes 8 (Z_to_bv 64 422152)) (Z_to_bv 64 422152) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_67074 D_67074 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_67078 D_67078 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6707c D_6707c (word_to_le_bytes 8 (Z_to_bv 64 175208)) (Z_to_bv 64 175208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_67080 D_67080 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_67084 D_67084 (0x67108 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_67108 D_67108.  (* [comment removed for export] *)
      sn F_6710c D_6710c.  (* [comment removed for export] *)
      sn F_67110 D_67110.  (* [comment removed for export] *)
      sv F_67114 D_67114 (argc_w av).  (* [comment removed for export] *)
      sv F_67118 D_67118 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_6711c D_6711c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_67120 D_67120 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_67124 D_67124 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_67128 D_67128 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6712c D_6712c (sp0).  (* [comment removed for export] *)
      stepret F_67130 D_67130 (0x67134 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 599632 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 175208 ->
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
        getr regs' 1 = (Z_to_bv 64 422072) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 599632) ->
        getr regs' 8 = (Z_to_bv 64 500088) ->
        getr regs' 9 = (Z_to_bv 64 500008) ->
        getr regs' 18 = (Z_to_bv 64 175208) ->
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
        G (mkst regs' (0x2ab64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x67134 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_67134 D_67134 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_67138 D_67138 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_6713c D_6713c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_67140 D_67140 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_67144 D_67144 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_67148 D_67148 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_6714c D_6714c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_67150 D_67150 (argc_w av).  (* [comment removed for export] *)
      sn F_67154 D_67154.  (* [comment removed for export] *)
      stepiv F_67158 D_67158 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_6715c D_6715c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_67160 D_67160 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_67164 D_67164.  (* [comment removed for export] *)
      sv F_67088 D_67088 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_6708c D_6708c (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 422248) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_67090 D_67090 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_67094 D_67094 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_67098 D_67098.  (* [comment removed for export] *)
      stepret F_66e58 D_66e58 (0x6709c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6709c D_6709c.  (* [comment removed for export] *)
      sn F_670a0 D_670a0.  (* [comment removed for export] *)
      ld_step F_670a4 D_670a4 (word_to_le_bytes 8 (Z_to_bv 64 500088)) (Z_to_bv 64 500088) ltac:(rd_img img_7f828_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_670a8 D_670a8 (word_to_le_bytes 8 (Z_to_bv 64 500008)) (Z_to_bv 64 500008) ltac:(rd_img img_7f830_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_670ac D_670ac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 174948)) (Z_to_bv 64 174948) ltac:(rd_img img_7a128_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2ab64 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
