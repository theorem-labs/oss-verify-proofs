(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  StartupTac ArgvEnv RefLayout Src0Img Src0StartupDefs
  Src0_code_4aedc_4b18c Src0_code_59b48_59b54.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation RND := (ed_random rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes RND))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
        let H := fresh in
        pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
        cbn [Z.add Pos.add Pos.succ] in H; exact H
    end.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 306380 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = (pn_w sp0 av ev) ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 591560 ->
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
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 5 = Z_to_bv 64 0 ->
        getr regs' 7 = Z_to_bv 64 7 ->
        getr regs' 9 = Z_to_bv 64 591560 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 590912 ->
        getr regs' 13 = Z_to_bv 64 10 ->
        getr regs' 15 = Z_to_bv 64 65600 ->
        getr regs' 16 = Z_to_bv 64 6 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        getr regs' 28 = Z_to_bv 64 1685382481 ->
        getr regs' 29 = Z_to_bv 64 65600 ->
        getr regs' 30 = Z_to_bv 64 131072 ->
        regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
        G (mkst regs' (0x4af64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x4aedc : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_4aedc D_4aedc (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
      stw F_4aee0 D_4aee0 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 306380) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aee4 D_4aee4 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aee8 D_4aee8 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aeec D_4aeec (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 591560) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aef0 D_4aef0 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aef4 D_4aef4 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aef8 D_4aef8 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      ld_step F_4aefc D_4aefc (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4af00 D_4af00.  (* [comment removed for export] *)
      sn F_4af04 D_4af04.  (* [comment removed for export] *)
      sn F_4af08 D_4af08.  (* [comment removed for export] *)
      sn F_4af0c D_4af0c.  (* [comment removed for export] *)
      stepb_ft F_4af10 D_4af10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af14 D_4af14.  (* [comment removed for export] *)
      sn F_4af18 D_4af18.  (* [comment removed for export] *)
      sn F_4af1c D_4af1c.  (* [comment removed for export] *)
      ld_step F_4af20 D_4af20 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4af24 D_4af24 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4af28 D_4af28.  (* [comment removed for export] *)
      sn F_4af2c D_4af2c.  (* [comment removed for export] *)
      ld_step F_4af30 D_4af30 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_5f860_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      ld_step F_4af34 D_4af34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5e4a0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4af38 D_4af38.  (* [comment removed for export] *)
      sn F_4af3c D_4af3c.  (* [comment removed for export] *)
      sn F_4af40 D_4af40.  (* [comment removed for export] *)
      sn F_4af44 D_4af44.  (* [comment removed for export] *)
      sn F_4af48 D_4af48.  (* [comment removed for export] *)
      sn F_4af4c D_4af4c.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 591560 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 590912 ->
    getr regs 13 = Z_to_bv 64 10 ->
    getr regs 15 = Z_to_bv 64 65600 ->
    getr regs 16 = Z_to_bv 64 6 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    getr regs 28 = Z_to_bv 64 1685382481 ->
    getr regs 29 = Z_to_bv 64 65600 ->
    getr regs 30 = Z_to_bv 64 131072 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 5 = Z_to_bv 64 0 ->
        getr regs' 7 = Z_to_bv 64 7 ->
        getr regs' 9 = Z_to_bv 64 591560 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 590912 ->
        getr regs' 13 = Z_to_bv 64 4 ->
        getr regs' 16 = Z_to_bv 64 6 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        getr regs' 28 = Z_to_bv 64 1685382481 ->
        getr regs' 29 = Z_to_bv 64 65936 ->
        getr regs' 30 = Z_to_bv 64 131072 ->
        regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0x4af64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x4af64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af50 D_4af50 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4af54 D_4af54.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 591560 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 590912 ->
    getr regs 13 = Z_to_bv 64 4 ->
    getr regs 16 = Z_to_bv 64 6 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    getr regs 28 = Z_to_bv 64 1685382481 ->
    getr regs 29 = Z_to_bv 64 65936 ->
    getr regs 30 = Z_to_bv 64 131072 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 9 = Z_to_bv 64 591560 ->
        getr regs' 11 = Z_to_bv 64 590912 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0x4afb4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x4af64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_ft F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af90 D_4af90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_4af94 D_4af94 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_ft F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4af64 D_4af64 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4af68 D_4af68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4af6c D_4af6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af80 D_4af80.  (* [comment removed for export] *)
      stepb_ft F_4af84 D_4af84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4af88 D_4af88.  (* [comment removed for export] *)
      stepb_tk F_4af8c D_4af8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4afac D_4afac.  (* [comment removed for export] *)
      sn F_4afb0 D_4afb0.  (* [comment removed for export] *)
      sn F_4af58 D_4af58.  (* [comment removed for export] *)
      sn F_4af5c D_4af5c.  (* [comment removed for export] *)
      stepb_tk F_4af60 D_4af60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 591560 ->
    getr regs 11 = Z_to_bv 64 590912 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 459832 ->
        getr regs' 10 = Z_to_bv 64 590912 ->
        getr regs' 11 = Z_to_bv 64 591616 ->
        getr regs' 12 = Z_to_bv 64 0 ->
        getr regs' 13 = Z_to_bv 64 459624 ->
        getr regs' 14 = Z_to_bv 64 0 ->
        getr regs' 15 = Z_to_bv 64 18446744073709091784 ->
        getr regs' 17 = Z_to_bv 64 96 ->
        getr regs' 18 = Z_to_bv 64 459632 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0x4b138 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0x4afb4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk F_4afb4 D_4afb4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4afec D_4afec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_90450_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4aff0 D_4aff0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_90460_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4aff4 D_4aff4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_90468_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4aff8 D_4aff8.  (* [comment removed for export] *)
      sn F_4affc D_4affc.  (* [comment removed for export] *)
      sn F_4b000 D_4b000.  (* [comment removed for export] *)
      sn F_4b004 D_4b004.  (* [comment removed for export] *)
      sn F_4b008 D_4b008.  (* [comment removed for export] *)
      sn F_4b00c D_4b00c.  (* [comment removed for export] *)
      sn F_4b010 D_4b010.  (* [comment removed for export] *)
      stw F_4b014 D_4b014 (Z_to_bv 64 590944) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b018 D_4b018 (Z_to_bv 64 590960) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_ft F_4b01c D_4b01c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4b020 D_4b020.  (* [comment removed for export] *)
      stw F_4b024 D_4b024 (Z_to_bv 64 590952) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4b028 D_4b028.  (* [comment removed for export] *)
      sn F_4b02c D_4b02c.  (* [comment removed for export] *)
      sn F_4b030 D_4b030.  (* [comment removed for export] *)
      sn F_4b034 D_4b034.  (* [comment removed for export] *)
      sn F_4b038 D_4b038.  (* [comment removed for export] *)
      sn F_4b03c D_4b03c.  (* [comment removed for export] *)
      stw F_4b040 D_4b040 (Z_to_bv 64 591584) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b044 D_4b044 (Z_to_bv 64 591592) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_tk F_4b048 D_4b048 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4b07c D_4b07c.  (* [comment removed for export] *)
      ld_step F_4b080 D_4b080 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_906d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b084 D_4b084 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_906f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4b088 D_4b088.  (* [comment removed for export] *)
      sn F_4b08c D_4b08c.  (* [comment removed for export] *)
      sn F_4b090 D_4b090.  (* [comment removed for export] *)
      sn F_4b094 D_4b094.  (* [comment removed for export] *)
      sn F_4b098 D_4b098.  (* [comment removed for export] *)
      sn F_4b09c D_4b09c.  (* [comment removed for export] *)
      sn F_4b0a0 D_4b0a0.  (* [comment removed for export] *)
      sn F_4b0a4 D_4b0a4.  (* [comment removed for export] *)
      sn F_4b0a8 D_4b0a8.  (* [comment removed for export] *)
      sn F_4b0ac D_4b0ac.  (* [comment removed for export] *)
      sn F_4b0b0 D_4b0b0.  (* [comment removed for export] *)
      stepb_tk F_4b0b4 D_4b0b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stw F_4b0fc D_4b0fc (Z_to_bv 64 459848) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b100 D_4b100 (Z_to_bv 64 459824) (Z_to_bv 64 459848) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b104 D_4b104 (Z_to_bv 64 459632) (Z_to_bv 64 459632) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4b108 D_4b108.  (* [comment removed for export] *)
      sn F_4b10c D_4b10c.  (* [comment removed for export] *)
      sn F_59b48 D_59b48.  (* [comment removed for export] *)
      sn F_59b4c D_59b4c.  (* [comment removed for export] *)
      stepret F_59b50 D_59b50 (0x4b110 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      stepb_ft F_4b110 D_4b110 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_ft F_4b114 D_4b114 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4b118 D_4b118.  (* [comment removed for export] *)
      stw F_4b11c D_4b11c (Z_to_bv 64 591560) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4b120 D_4b120.  (* [comment removed for export] *)
      sn F_4b124 D_4b124.  (* [comment removed for export] *)
      stw F_4b128 D_4b128 (Z_to_bv 64 459672) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4b12c D_4b12c.  (* [comment removed for export] *)
      sn F_4b130 D_4b130.  (* [comment removed for export] *)
      sn F_4b134 D_4b134.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 459832 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 591616 ->
    getr regs 18 = Z_to_bv 64 459632 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 459832 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
        G (mkst regs' (0x4accc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0x4b13c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_4b13c D_4b13c.  (* [comment removed for export] *)
      stw F_4b140 D_4b140 (Z_to_bv 64 459664) tid ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b144 D_4b144 (Z_to_bv 64 459784) (Z_to_bv 64 591616) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b148 D_4b148 (Z_to_bv 64 459752) (Z_to_bv 64 459752) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4b14c D_4b14c.  (* [comment removed for export] *)
      ld_step F_4b150 D_4b150 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_906b0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_4b154 D_4b154 (Z_to_bv 64 459640) (Z_to_bv 64 459632) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b158 D_4b158 (Z_to_bv 64 459648) (Z_to_bv 64 459632) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4b15c D_4b15c (Z_to_bv 64 459656) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4b160 D_4b160.  (* [comment removed for export] *)
      ld_step F_4b168 D_4b168 (word_to_le_bytes 8 (Z_to_bv 64 306380)) (Z_to_bv 64 306380) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b16c D_4b16c (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b170 D_4b170 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b174 D_4b174 (word_to_le_bytes 8 (Z_to_bv 64 591560)) (Z_to_bv 64 591560) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b178 D_4b178 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b17c D_4b17c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b180 D_4b180 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4b184 D_4b184 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_4b188 D_4b188 (0x4accc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
