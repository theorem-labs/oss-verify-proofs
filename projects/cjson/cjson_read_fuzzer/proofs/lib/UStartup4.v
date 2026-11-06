(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupSsp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import UStartupImg UStartupDefs UStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
        change (Z_to_bv 64 347196) with (Z_to_bv 64 (347192 + 4));
        change (Z_to_bv 64 347193) with (Z_to_bv 64 (347192 + 1));
        apply (rdn_guard3 SEGS DD 347192); [apply length_N_to_le_bytes | apply length_N_to_le_bytes | lia | lia]
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
    getr regs 4 = Z_to_bv 64 215504 ->
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
        getr regs' 4 = (Z_to_bv 64 215504) ->
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
        G (mkst regs' (0x15a5c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom)) ->
    G (mkst regs (0x15a54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_15a54 D_15a54 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_15a58 D_15a58.  (* [comment removed for export] *)
      sv F_1626c D_1626c (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_16270 D_16270 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 88668) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_16274 D_16274 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_16278 D_16278 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_1627c D_1627c.  (* [comment removed for export] *)
      ld_step F_16280 D_16280 (word_to_le_bytes 8 (Z_to_bv 64 347192)) (Z_to_bv 64 347192) ltac:(rd_img img_23630_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_16284 D_16284.  (* [comment removed for export] *)
      sn F_16288 D_16288.  (* [comment removed for export] *)
      stepiv F_21b2c D_21b2c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_21b30 D_21b30 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21c40 D_21c40.  (* [comment removed for export] *)
      sn F_21c44 D_21c44.  (* [comment removed for export] *)
      stepb_ft F_21c48 D_21c48 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21c4c D_21c4c.  (* [comment removed for export] *)
      stepb_tk F_21c50 D_21c50 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21c88 D_21c88.  (* [comment removed for export] *)
      stepb_ft F_21c8c D_21c8c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_21c90 D_21c90 (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) (rnd_lo (ed_random rdraw)) ltac:(RD_RND 0%nat) ltac:(apply rnd_lo_val).  (* [comment removed for export] *)
      ld_step F_21c94 D_21c94 (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) (rnd_hi (ed_random rdraw)) ltac:(RD_RND 4%nat) ltac:(apply rnd_hi_val).  (* [comment removed for export] *)
      stw F_21c98 D_21c98 (Z_to_bv 64 347192) (v_lw (rnd_lo (ed_random rdraw))) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_21c9c D_21c9c (Z_to_bv 64 347196) (v_lw (rnd_hi (ed_random rdraw))) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_21ca0 D_21ca0.  (* [comment removed for export] *)
      sv F_21ca4 D_21ca4 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_21ca8 D_21ca8.  (* [comment removed for export] *)
      stepb_tk F_21cac D_21cac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21eec D_21eec.  (* [comment removed for export] *)
      stepb_ft F_21ef0 D_21ef0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21ef4 D_21ef4.  (* [comment removed for export] *)
      stepb_ft F_21ef8 D_21ef8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_21efc D_21efc (0x1628c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1628c D_1628c.  (* [comment removed for export] *)
      sn F_162a8 D_162a8.  (* [comment removed for export] *)
      ld_step F_162ac D_162ac (word_to_le_bytes 8 (Z_to_bv 64 347192)) (Z_to_bv 64 347192) ltac:(rd_img img_23630_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_162b0 D_162b0 (Z_to_bv 64 347193) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_162b4 D_162b4 (guard_bytes (ed_random rdraw)) (canary_w (ed_random rdraw)) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_162b8 D_162b8.  (* [comment removed for export] *)
      stw F_162bc D_162bc (Z_to_bv 64 215488) (canary_w (ed_random rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_162c0 D_162c0 (word_to_le_bytes 8 (Z_to_bv 64 88668)) (Z_to_bv 64 88668) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_162c4 D_162c4 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_162c8 D_162c8 (0x15a5c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 215504 ->
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
        getr regs' 4 = (Z_to_bv 64 215504) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 78188) ->
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
        G (mkst regs' (0x15c1c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom)) ->
    G (mkst regs (0x15a5c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_15a5c D_15a5c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15a60 D_15a60 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_15a64 D_15a64 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_15a68 D_15a68 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_15a6c D_15a6c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_15a70 D_15a70 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_15a74 D_15a74 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_15a78 D_15a78 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_15b58 D_15b58 (word_to_le_bytes 8 (Z_to_bv 64 89072)) (Z_to_bv 64 89072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15b5c D_15b5c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15b60 D_15b60 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15b64 D_15b64 (word_to_le_bytes 8 (Z_to_bv 64 78188)) (Z_to_bv 64 78188) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_15b68 D_15b68 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_15b6c D_15b6c (0x15bf0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_15bf0 D_15bf0.  (* [comment removed for export] *)
      sn F_15bf4 D_15bf4.  (* [comment removed for export] *)
      sn F_15bf8 D_15bf8.  (* [comment removed for export] *)
      sv F_15bfc D_15bfc (argc_w av).  (* [comment removed for export] *)
      sv F_15c00 D_15c00 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_15c04 D_15c04 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15c08 D_15c08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15c0c D_15c0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15c10 D_15c10 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_15c14 D_15c14 (sp0).  (* [comment removed for export] *)
      stepret F_15c18 D_15c18 (0x15c1c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 215504 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 78188 ->
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
        getr regs' 1 = (Z_to_bv 64 88992) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 215504) ->
        getr regs' 8 = (Z_to_bv 64 144696) ->
        getr regs' 9 = (Z_to_bv 64 144688) ->
        getr regs' 18 = (Z_to_bv 64 78188) ->
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
        G (mkst regs' (0x13068 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 89168))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom)) ->
    G (mkst regs (0x15c1c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_15c1c D_15c1c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_15c20 D_15c20 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15c24 D_15c24 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15c28 D_15c28 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15c2c D_15c2c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15c30 D_15c30 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_15c34 D_15c34 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_15c38 D_15c38 (argc_w av).  (* [comment removed for export] *)
      sn F_15c3c D_15c3c.  (* [comment removed for export] *)
      stepiv F_15c40 D_15c40 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_15c44 D_15c44 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_15c48 D_15c48 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_15c4c D_15c4c.  (* [comment removed for export] *)
      sv F_15b70 D_15b70 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_15b74 D_15b74 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 89168) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15b78 D_15b78 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15b7c D_15b7c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_15b80 D_15b80.  (* [comment removed for export] *)
      stepret F_15940 D_15940 (0x15b84 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_15b84 D_15b84.  (* [comment removed for export] *)
      sn F_15b88 D_15b88.  (* [comment removed for export] *)
      ld_step F_15b8c D_15b8c (word_to_le_bytes 8 (Z_to_bv 64 144696)) (Z_to_bv 64 144696) ltac:(rd_img img_23620_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15b90 D_15b90 (word_to_le_bytes 8 (Z_to_bv 64 144688)) (Z_to_bv 64 144688) ltac:(rd_img img_23628_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_15b94 D_15b94 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_15b98 D_15b98 (word_to_le_bytes 8 (Z_to_bv 64 77928)) (Z_to_bv 64 77928) ltac:(rd_img img_23530_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_15b9c D_15b9c (0x13068 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 88992 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 215504 ->
    getr regs 8 = Z_to_bv 64 144696 ->
    getr regs 9 = Z_to_bv 64 144688 ->
    getr regs 18 = Z_to_bv 64 78188 ->
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
        getr regs' 1 = (Z_to_bv 64 89184) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 215504) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 78188) ->
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
        G (mkst regs' (0x1316c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 89168))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 88992))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 144696))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw)))) (Z_to_bv 64 149616) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x13068 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88660))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 347224))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 88668))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 89168))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 346616) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346632) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 346624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 347248) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 347256) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 215520) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 215496) (word_to_le_bytes 8 (Z_to_bv 64 215520))) (Z_to_bv 64 215304) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 347224) ([Z_to_bv 8 1])) (Z_to_bv 64 215344) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 215336) (word_to_le_bytes 4 tid)) (Z_to_bv 64 215456) (word_to_le_bytes 8 (Z_to_bv 64 347280))) (Z_to_bv 64 215424) (word_to_le_bytes 8 (Z_to_bv 64 215424))) (Z_to_bv 64 215312) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215320) (word_to_le_bytes 8 (Z_to_bv 64 215304))) (Z_to_bv 64 215328) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 347192) (word_to_le_bytes 4 (v_lw (rnd_lo (ed_random rdraw))))) (Z_to_bv 64 347196) (word_to_le_bytes 4 (v_lw (rnd_hi (ed_random rdraw))))) (Z_to_bv 64 347193) ([Z_to_bv 8 0])) (Z_to_bv 64 215488) (word_to_le_bytes 8 (canary_w (ed_random rdraw))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_13068 D_13068 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_1306c D_1306c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 88992) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_13070 D_13070 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 144696) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_13074 D_13074 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_13078 D_13078.  (* [comment removed for export] *)
      sn F_1307c D_1307c.  (* [comment removed for export] *)
      lb_step F_13080 D_13080 (Z_to_bv 8 0) ltac:(rd_img img_24870_1).  (* [comment removed for export] *)
      sn F_13084 D_13084.  (* [comment removed for export] *)
      stepb_tk F_13088 D_13088 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_13094 D_13094.  (* [comment removed for export] *)
      sn F_13098 D_13098.  (* [comment removed for export] *)
      sn F_1309c D_1309c.  (* [comment removed for export] *)
      stw F_130a0 D_130a0 (Z_to_bv 64 149616) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_130a4 D_130a4.  (* [comment removed for export] *)
      ld_step F_130a8 D_130a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_235d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_130ac D_130ac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_130cc D_130cc (word_to_le_bytes 8 (Z_to_bv 64 88992)) (Z_to_bv 64 88992) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_130d0 D_130d0 (word_to_le_bytes 8 (Z_to_bv 64 144696)) (Z_to_bv 64 144696) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_130d4 D_130d4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_130d8 D_130d8 (0x15ba0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_15ba0 D_15ba0.  (* [comment removed for export] *)
      stepb_ft F_15ba4 D_15ba4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_15ba8 D_15ba8 (word_to_le_bytes 8 (Z_to_bv 64 89168)) (Z_to_bv 64 89168) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15bac D_15bac (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15bb0 D_15bb0 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_15bb4 D_15bb4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_15bb8 D_15bb8 (0x15c50 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_15c50 D_15c50 (argc_w av).  (* [comment removed for export] *)
      sv F_15c54 D_15c54 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_15c58 D_15c58 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_15c5c D_15c5c (0x1316c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
