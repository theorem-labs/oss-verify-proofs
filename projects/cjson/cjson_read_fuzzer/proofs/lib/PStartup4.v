(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PStartupImg PStartupDefs PStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

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
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD _ _) _ _) _ _) _ _ = _ =>
        change (Z_to_bv 64 342780) with (Z_to_bv 64 (342776 + 4));
        change (Z_to_bv 64 342777) with (Z_to_bv 64 (342776 + 1));
        apply (rdn_guard3 SEGS DD 342776); [apply length_N_to_le_bytes | apply length_N_to_le_bytes | lia | lia]
    end.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 211088 ->
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
        getr regs' 4 = (Z_to_bv 64 211088) ->
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
        G (mkst regs' (0x14918 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom)) ->
    G (mkst regs (0x14910 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_14910 D_14910 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_14914 D_14914.  (* [comment removed for export] *)
      sv F_15128 D_15128 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1512c D_1512c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 84248) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_15130 D_15130 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_15134 D_15134 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_15138 D_15138.  (* [comment removed for export] *)
      ld_step F_1513c D_1513c (word_to_le_bytes 8 (Z_to_bv 64 342776)) (Z_to_bv 64 342776) ltac:(rd_img img_224e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_15140 D_15140.  (* [comment removed for export] *)
      sn F_15144 D_15144.  (* [comment removed for export] *)
      stepiv F_209e8 D_209e8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_209ec D_209ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20afc D_20afc.  (* [comment removed for export] *)
      sn F_20b00 D_20b00.  (* [comment removed for export] *)
      stepb_ft F_20b04 D_20b04 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20b08 D_20b08.  (* [comment removed for export] *)
      stepb_tk F_20b0c D_20b0c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20b44 D_20b44.  (* [comment removed for export] *)
      stepb_ft F_20b48 D_20b48 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_20b4c D_20b4c (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) (rnd_lo (ed_random rdraw)) ltac:(RD_RND 0%nat) ltac:(apply rnd_lo_val).  (* [comment removed for export] *)
      ld_step F_20b50 D_20b50 (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) (rnd_hi (ed_random rdraw)) ltac:(RD_RND 4%nat) ltac:(apply rnd_hi_val).  (* [comment removed for export] *)
      stw F_20b54 D_20b54 (Z_to_bv 64 342776) (v_lw (rnd_lo (ed_random rdraw))) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_20b58 D_20b58 (Z_to_bv 64 342780) (v_lw (rnd_hi (ed_random rdraw))) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_20b5c D_20b5c.  (* [comment removed for export] *)
      sv F_20b60 D_20b60 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_20b64 D_20b64.  (* [comment removed for export] *)
      stepb_tk F_20b68 D_20b68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20da8 D_20da8.  (* [comment removed for export] *)
      stepb_ft F_20dac D_20dac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20db0 D_20db0.  (* [comment removed for export] *)
      stepb_ft F_20db4 D_20db4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_20db8 D_20db8 (0x15148 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_15148 D_15148.  (* [comment removed for export] *)
      sn F_15164 D_15164.  (* [comment removed for export] *)
      ld_step F_15168 D_15168 (word_to_le_bytes 8 (Z_to_bv 64 342776)) (Z_to_bv 64 342776) ltac:(rd_img img_224e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1516c D_1516c (Z_to_bv 64 342777) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_15170 D_15170 (guard_bytes (ed_random rdraw)) (canary_w (ed_random rdraw)) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_15174 D_15174.  (* [comment removed for export] *)
      stw F_15178 D_15178 (Z_to_bv 64 211072) (canary_w (ed_random rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1517c D_1517c (word_to_le_bytes 8 (Z_to_bv 64 84248)) (Z_to_bv 64 84248) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_15180 D_15180 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_15184 D_15184 (0x14918 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 211088 ->
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
        getr regs' 4 = (Z_to_bv 64 211088) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 74060) ->
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
        G (mkst regs' (0x14ad8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom)) ->
    G (mkst regs (0x14918 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_14918 D_14918 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1491c D_1491c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_14920 D_14920 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_14924 D_14924 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_14928 D_14928 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_1492c D_1492c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14930 D_14930 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14934 D_14934 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14a14 D_14a14 (word_to_le_bytes 8 (Z_to_bv 64 84652)) (Z_to_bv 64 84652) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14a18 D_14a18 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14a1c D_14a1c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14a20 D_14a20 (word_to_le_bytes 8 (Z_to_bv 64 74060)) (Z_to_bv 64 74060) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_14a24 D_14a24 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_14a28 D_14a28 (0x14aac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_14aac D_14aac.  (* [comment removed for export] *)
      sn F_14ab0 D_14ab0.  (* [comment removed for export] *)
      sn F_14ab4 D_14ab4.  (* [comment removed for export] *)
      sv F_14ab8 D_14ab8 (argc_w av).  (* [comment removed for export] *)
      sv F_14abc D_14abc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_14ac0 D_14ac0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14ac4 D_14ac4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14ac8 D_14ac8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14acc D_14acc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_14ad0 D_14ad0 (sp0).  (* [comment removed for export] *)
      stepret F_14ad4 D_14ad4 (0x14ad8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 211088 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 74060 ->
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
        getr regs' 1 = (Z_to_bv 64 84572) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 211088) ->
        getr regs' 8 = (Z_to_bv 64 140272) ->
        getr regs' 9 = (Z_to_bv 64 140264) ->
        getr regs' 18 = (Z_to_bv 64 74060) ->
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
        G (mkst regs' (0x12048 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 84748))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom)) ->
    G (mkst regs (0x14ad8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_14ad8 D_14ad8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_14adc D_14adc (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14ae0 D_14ae0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14ae4 D_14ae4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14ae8 D_14ae8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14aec D_14aec (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14af0 D_14af0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_14af4 D_14af4 (argc_w av).  (* [comment removed for export] *)
      sn F_14af8 D_14af8.  (* [comment removed for export] *)
      stepiv F_14afc D_14afc (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_14b00 D_14b00 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_14b04 D_14b04 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_14b08 D_14b08.  (* [comment removed for export] *)
      sv F_14a2c D_14a2c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_14a30 D_14a30 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 84748) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14a34 D_14a34 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14a38 D_14a38 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_14a3c D_14a3c.  (* [comment removed for export] *)
      stepret F_147fc D_147fc (0x14a40 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_14a40 D_14a40.  (* [comment removed for export] *)
      sn F_14a44 D_14a44.  (* [comment removed for export] *)
      ld_step F_14a48 D_14a48 (word_to_le_bytes 8 (Z_to_bv 64 140272)) (Z_to_bv 64 140272) ltac:(rd_img img_224d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14a4c D_14a4c (word_to_le_bytes 8 (Z_to_bv 64 140264)) (Z_to_bv 64 140264) ltac:(rd_img img_224e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_14a50 D_14a50 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14a54 D_14a54 (word_to_le_bytes 8 (Z_to_bv 64 73800)) (Z_to_bv 64 73800) ltac:(rd_img img_223e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_14a58 D_14a58 (0x12048 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 84572 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 211088 ->
    getr regs 8 = Z_to_bv 64 140272 ->
    getr regs 9 = Z_to_bv 64 140264 ->
    getr regs 18 = Z_to_bv 64 74060 ->
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
        getr regs' 1 = (Z_to_bv 64 84764) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 211088) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 74060) ->
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
        G (mkst regs' (0x1214c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 84748))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 84572))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 140272))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw)))) (Z_to_bv 64 145200) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x12048 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84240))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 342808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 84248))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 84748))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 342200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 342832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 342840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 211104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 211080) (word_to_le_bytes 8 (Z_to_bv 64 211104))) (Z_to_bv 64 210888) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 342808) ([Z_to_bv 8 1])) (Z_to_bv 64 210928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 210920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 211040) (word_to_le_bytes 8 (Z_to_bv 64 342864))) (Z_to_bv 64 211008) (word_to_le_bytes 8 (Z_to_bv 64 211008))) (Z_to_bv 64 210896) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210904) (word_to_le_bytes 8 (Z_to_bv 64 210888))) (Z_to_bv 64 210912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 342776) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 342780) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 342777) ([Z_to_bv 8 0])) (Z_to_bv 64 211072) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_12048 D_12048 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_1204c D_1204c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 84572) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_12050 D_12050 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 140272) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_12054 D_12054 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_12058 D_12058.  (* [comment removed for export] *)
      sn F_1205c D_1205c.  (* [comment removed for export] *)
      lb_step F_12060 D_12060 (Z_to_bv 8 0) ltac:(rd_img img_23730_1).  (* [comment removed for export] *)
      sn F_12064 D_12064.  (* [comment removed for export] *)
      stepb_tk F_12068 D_12068 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_12074 D_12074.  (* [comment removed for export] *)
      sn F_12078 D_12078.  (* [comment removed for export] *)
      sn F_1207c D_1207c.  (* [comment removed for export] *)
      stw F_12080 D_12080 (Z_to_bv 64 145200) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_12084 D_12084.  (* [comment removed for export] *)
      ld_step F_12088 D_12088 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22490_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_1208c D_1208c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_120ac D_120ac (word_to_le_bytes 8 (Z_to_bv 64 84572)) (Z_to_bv 64 84572) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_120b0 D_120b0 (word_to_le_bytes 8 (Z_to_bv 64 140272)) (Z_to_bv 64 140272) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_120b4 D_120b4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_120b8 D_120b8 (0x14a5c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_14a5c D_14a5c.  (* [comment removed for export] *)
      stepb_ft F_14a60 D_14a60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14a64 D_14a64 (word_to_le_bytes 8 (Z_to_bv 64 84748)) (Z_to_bv 64 84748) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14a68 D_14a68 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14a6c D_14a6c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_14a70 D_14a70 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_14a74 D_14a74 (0x14b0c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_14b0c D_14b0c (argc_w av).  (* [comment removed for export] *)
      sv F_14b10 D_14b10 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_14b14 D_14b14 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_14b18 D_14b18 (0x1214c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
