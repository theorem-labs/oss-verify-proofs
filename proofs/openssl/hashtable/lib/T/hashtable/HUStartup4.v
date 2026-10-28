(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  StartupTac ArgvEnv RefLayout HUImg HUStartupDefs ClaBytes HU_code_26b000_26c000 HU_code_276000_277000 HU_code_dc000_dd000 HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (rnd16 rdraw))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w, rnd16. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Lemma len_rnd16 : length (rnd16 rdraw) = 16%nat.
  Proof. unfold rnd16. apply length_at_random_bytes. Qed.
  Lemma len_guard_lo : length (guard_lo rdraw) = 4%nat.
  Proof. unfold guard_lo. rewrite length_firstn, len_rnd16. reflexivity. Qed.
  Lemma len_guard_hi : length (guard_hi rdraw) = 4%nat.
  Proof. unfold guard_hi. rewrite length_firstn, length_skipn, len_rnd16. reflexivity. Qed.
  Lemma len_canary8 : length (canary8 rdraw) = 8%nat.
  Proof.
    unfold canary8. rewrite !length_app, !length_firstn, length_skipn, len_rnd16. reflexivity.
  Qed.
  Lemma canary8_eq : firstn 1 (guard_lo rdraw) ++ [Z_to_bv 8 0] ++ skipn 2 (guard_lo rdraw) ++ guard_hi rdraw = canary8 rdraw.
  Proof.
    unfold canary8, guard_lo, guard_hi. pose proof len_rnd16 as L.
    destruct (rnd16 rdraw) as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 l]]]]]]]]]; try discriminate L.
    reflexivity.
  Qed.
  (* [comment removed for export] *)
  Let vlo : word := Z_to_bv 64 (bytes_le_to_Z (guard_lo rdraw)).
  Let vhi : word := Z_to_bv 64 (bytes_le_to_Z (guard_hi rdraw)).
  Let vcan : word := Z_to_bv 64 (bytes_le_to_Z (canary8 rdraw)).

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    rewrite <- canary8_eq;
    apply (rdn_guard8 SEGS _ 3480360 (guard_lo rdraw) (guard_hi rdraw) (Z_to_bv 8 0) len_guard_lo len_guard_hi); lia.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3349224 ->
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
        getr regs' 4 = (Z_to_bv 64 3349224) ->
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
        G (mkst regs' (0x2b0f54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw))) rom)) ->
    G (mkst regs (0x2b0f4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_26b354 D_26b354 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b358 D_26b358.  (* [comment removed for export] *)
      sv F_26b8f8 D_26b8f8 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_26b8fc D_26b8fc (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 2821972) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_26b900 D_26b900 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_26b904 D_26b904 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_26b908 D_26b908.  (* [comment removed for export] *)
      ld_step F_26b90c D_26b90c (word_to_le_bytes 8 (Z_to_bv 64 3480360)) (Z_to_bv 64 3480360) ltac:(rd_img img_2d7b60_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b910 D_26b910.  (* [comment removed for export] *)
      sn F_26b914 D_26b914.  (* [comment removed for export] *)
      stepiv F_276438 D_276438 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_27643c D_27643c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_27654c D_27654c.  (* [comment removed for export] *)
      sn F_276550 D_276550.  (* [comment removed for export] *)
      stepb_ft F_276554 D_276554 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_276558 D_276558.  (* [comment removed for export] *)
      stepb_tk F_27655c D_27655c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_276594 D_276594.  (* [comment removed for export] *)
      stepb_ft F_276598 D_276598 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_27659c D_27659c (guard_lo rdraw) vlo ltac:(unfold guard_lo; RD_RND 0%nat) ltac:(apply bytes_le_to_Z_small64; rewrite len_guard_lo; lia).  (* [comment removed for export] *)
      ld_step F_2765a0 D_2765a0 (guard_hi rdraw) vhi ltac:(unfold guard_hi; RD_RND 4%nat) ltac:(apply bytes_le_to_Z_small64; rewrite len_guard_hi; lia).  (* [comment removed for export] *)
      stw F_2765a4 D_2765a4 (Z_to_bv 64 3480360) (v_lw vlo) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (w4_lw_of_bytes (guard_lo rdraw) len_guard_lo : word_to_le_bytes 4 (v_lw vlo) = guard_lo rdraw).
      stw F_2765a8 D_2765a8 (Z_to_bv 64 3480364) (v_lw vhi) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (w4_lw_of_bytes (guard_hi rdraw) len_guard_hi : word_to_le_bytes 4 (v_lw vhi) = guard_hi rdraw).
      sn F_2765ac D_2765ac.  (* [comment removed for export] *)
      sv F_2765b0 D_2765b0 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_2765b4 D_2765b4.  (* [comment removed for export] *)
      stepb_tk F_2765b8 D_2765b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2767f8 D_2767f8.  (* [comment removed for export] *)
      stepb_ft F_2767fc D_2767fc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_276800 D_276800.  (* [comment removed for export] *)
      stepb_ft F_276804 D_276804 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_276808 D_276808 (0x2b1504 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26b918 D_26b918.  (* [comment removed for export] *)
      sn F_26b934 D_26b934.  (* [comment removed for export] *)
      ld_step F_26b938 D_26b938 (word_to_le_bytes 8 (Z_to_bv 64 3480360)) (Z_to_bv 64 3480360) ltac:(rd_img img_2d7b60_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_26b93c D_26b93c (Z_to_bv 64 3480361) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_26b940 D_26b940 (canary8 rdraw) vcan ltac:(RD_GUARD) ltac:(apply bytes_le_to_Z_small64; rewrite len_canary8; lia).  (* [comment removed for export] *)
      sn F_26b944 D_26b944.  (* [comment removed for export] *)
      stw F_26b948 D_26b948 (Z_to_bv 64 3349208) vcan ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (w8_of_bytes (canary8 rdraw) len_canary8 : word_to_le_bytes 8 vcan = canary8 rdraw).
      ld_step F_26b94c D_26b94c (word_to_le_bytes 8 (Z_to_bv 64 2821972)) (Z_to_bv 64 2821972) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26b950 D_26b950 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_26b954 D_26b954 (0x2b0f54 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3349224 ->
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
        getr regs' 4 = (Z_to_bv 64 3349224) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 924036) ->
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
        G (mkst regs' (0x2b1114 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw))) rom)) ->
    G (mkst regs (0x2b0f54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_26b35c D_26b35c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b360 D_26b360 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_26b364 D_26b364 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_26b368 D_26b368 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_26b36c D_26b36c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b370 D_26b370 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b374 D_26b374 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_26b378 D_26b378 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b458 D_26b458 (word_to_le_bytes 8 (Z_to_bv 64 2822376)) (Z_to_bv 64 2822376) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b45c D_26b45c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b460 D_26b460 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b464 D_26b464 (word_to_le_bytes 8 (Z_to_bv 64 924036)) (Z_to_bv 64 924036) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26b468 D_26b468 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_26b46c D_26b46c (0x2b10e8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26b4f0 D_26b4f0.  (* [comment removed for export] *)
      sn F_26b4f4 D_26b4f4.  (* [comment removed for export] *)
      sn F_26b4f8 D_26b4f8.  (* [comment removed for export] *)
      sv F_26b4fc D_26b4fc (argc_w av).  (* [comment removed for export] *)
      sv F_26b500 D_26b500 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_26b504 D_26b504 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b508 D_26b508 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b50c D_26b50c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b510 D_26b510 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26b514 D_26b514 (sp0).  (* [comment removed for export] *)
      stepret F_26b518 D_26b518 (0x2b1114 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3349224 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 924036 ->
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
        getr regs' 1 = (Z_to_bv 64 2822296) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3349224) ->
        getr regs' 8 = (Z_to_bv 64 2889520) ->
        getr regs' 9 = (Z_to_bv 64 2889512) ->
        getr regs' 18 = (Z_to_bv 64 924036) ->
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
        G (mkst regs' (0xe187c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2822472))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw))) rom)) ->
    G (mkst regs (0x2b1114 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_26b51c D_26b51c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_26b520 D_26b520 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b524 D_26b524 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b528 D_26b528 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b52c D_26b52c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b530 D_26b530 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_26b534 D_26b534 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_26b538 D_26b538 (argc_w av).  (* [comment removed for export] *)
      sn F_26b53c D_26b53c.  (* [comment removed for export] *)
      stepiv F_26b540 D_26b540 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_26b544 D_26b544 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_26b548 D_26b548 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_26b54c D_26b54c.  (* [comment removed for export] *)
      sv F_26b470 D_26b470 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_26b474 D_26b474 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 2822472) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b478 D_26b478 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b47c D_26b47c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_26b480 D_26b480.  (* [comment removed for export] *)
      stepret F_26b240 D_26b240 (0x2b107c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26b484 D_26b484.  (* [comment removed for export] *)
      sn F_26b488 D_26b488.  (* [comment removed for export] *)
      ld_step F_26b48c D_26b48c (word_to_le_bytes 8 (Z_to_bv 64 2889520)) (Z_to_bv 64 2889520) ltac:(rd_img img_2d7b80_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b490 D_26b490 (word_to_le_bytes 8 (Z_to_bv 64 2889512)) (Z_to_bv 64 2889512) ltac:(rd_img img_2d7b88_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_26b494 D_26b494 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b498 D_26b498 (word_to_le_bytes 8 (Z_to_bv 64 923772)) (Z_to_bv 64 923772) ltac:(rd_img img_27bb40_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_26b49c D_26b49c (0xe187c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 2822296 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3349224 ->
    getr regs 8 = Z_to_bv 64 2889520 ->
    getr regs 9 = Z_to_bv 64 2889512 ->
    getr regs 18 = Z_to_bv 64 924036 ->
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
        getr regs' 1 = (Z_to_bv 64 2822488) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3349224) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 924036) ->
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
        G (mkst regs' (0xe1984 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2822472))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 2822296))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 2889520))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw)) (Z_to_bv 64 3272384) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0xe187c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821972))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2822472))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480360) (guard_lo rdraw)) (Z_to_bv 64 3480364) (guard_hi rdraw)) (Z_to_bv 64 3480361) ([Z_to_bv 8 0])) (Z_to_bv 64 3349208) (canary8 rdraw))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_dcf44 D_dcf44 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_dcf48 D_dcf48 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 2822296) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_dcf4c D_dcf4c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 2889520) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_dcf50 D_dcf50 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_dcf54 D_dcf54.  (* [comment removed for export] *)
      sn F_dcf58 D_dcf58.  (* [comment removed for export] *)
      lb_step F_dcf5c D_dcf5c (Z_to_bv 8 0) ltac:(rd_img img_2d92f0_1).  (* [comment removed for export] *)
      sn F_dcf60 D_dcf60.  (* [comment removed for export] *)
      stepb_tk F_dcf64 D_dcf64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_dcf70 D_dcf70.  (* [comment removed for export] *)
      sn F_dcf74 D_dcf74.  (* [comment removed for export] *)
      sn F_dcf78 D_dcf78.  (* [comment removed for export] *)
      stw F_dcf7c D_dcf7c (Z_to_bv 64 3272384) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_dcf80 D_dcf80.  (* [comment removed for export] *)
      ld_step F_dcf84 D_dcf84 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2d75a0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_dcf88 D_dcf88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_dcfa8 D_dcfa8 (word_to_le_bytes 8 (Z_to_bv 64 2822296)) (Z_to_bv 64 2822296) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_dcfac D_dcfac (word_to_le_bytes 8 (Z_to_bv 64 2889520)) (Z_to_bv 64 2889520) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_dcfb0 D_dcfb0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_dcfb4 D_dcfb4 (0x2b1098 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_26b4a0 D_26b4a0.  (* [comment removed for export] *)
      stepb_ft F_26b4a4 D_26b4a4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b4a8 D_26b4a8 (word_to_le_bytes 8 (Z_to_bv 64 2822472)) (Z_to_bv 64 2822472) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b4ac D_26b4ac (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b4b0 D_26b4b0 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26b4b4 D_26b4b4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_26b4b8 D_26b4b8 (0x2b1148 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_26b550 D_26b550 (argc_w av).  (* [comment removed for export] *)
      sv F_26b554 D_26b554 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_26b558 D_26b558 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_26b55c D_26b55c (0xe1984 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
