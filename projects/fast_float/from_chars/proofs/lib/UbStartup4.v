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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbImg UbStartupDefs Ub_code_22780_228cc Ub_code_5233c_52dd8 Ub_code_60628_60720 Ub_code_61234_61240 Ub_code_memcpy.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  #[using="Hlo"] Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0). exact Hlo. Qed.
  #[using="Hhi"] Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. LiaFast.lf_pins (fun (Hhi : LiaFast.U) => LiaFast.u0). exact Hhi. Qed.
  #[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. LiaFast.lf_pins (fun (sp0 Hva : LiaFast.U) => LiaFast.u0). destruct Hva as [[H1 H2] _]. lia. Qed.

  #[using="uid hw rdraw Hva Hve Hlo Hhi Hal"] Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof. LiaFast.lf_pins (fun (uid hw rdraw Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  #[using="Type"] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  #[using="sp0 Hva"] Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof. LiaFast.lf_pins (fun (sp0 Hva : LiaFast.U) => LiaFast.u0).
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.


  (* [comment removed for export] *)
  Ltac rd_J9 R :=
    lazymatch goal with |- rdn _ _ ?a _ = _ =>
      lazymatch type of R with rdn _ _ ?a' _ = _ =>
        first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end end;
    exact R.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 489872 ->
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
        getr regs' 4 = (Z_to_bv 64 489872) ->
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
        G (mkst regs' (0x52458 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336984))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom)) ->
    G (mkst regs (0x52450 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_52450 D_52450 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_52454 D_52454.  (* [comment removed for export] *)
      sv F_52d38 D_52d38 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_52d3c D_52d3c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 336984) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_52d40 D_52d40 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_52d44 D_52d44 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_52d48 D_52d48.  (* [comment removed for export] *)
      ld_step F_52d4c D_52d4c (word_to_le_bytes 8 (Z_to_bv 64 621568)) (Z_to_bv 64 621568) ltac:(rd_img img_65b58_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_52d50 D_52d50.  (* [comment removed for export] *)
      sn F_52d54 D_52d54.  (* [comment removed for export] *)
      stepiv F_600a8 D_600a8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_600ac D_600ac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_601bc D_601bc.  (* [comment removed for export] *)
      sn F_601c0 D_601c0.  (* [comment removed for export] *)
      stepb_ft F_601c4 D_601c4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_601c8 D_601c8.  (* [comment removed for export] *)
      stepb_tk F_601cc D_601cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_60204 D_60204.  (* [comment removed for export] *)
      stepb_ft F_60208 D_60208 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_6020c D_6020c (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) (rnd_lo rdraw) ltac:(RD_RND 0%nat) ltac:(apply rnd_lo_val).  (* [comment removed for export] *)
      ld_step F_60210 D_60210 (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) (rnd_hi rdraw) ltac:(RD_RND 4%nat) ltac:(apply rnd_hi_val).  (* [comment removed for export] *)
      stw F_60214 D_60214 (Z_to_bv 64 621568) (v_lw (rnd_lo rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_60218 D_60218 (Z_to_bv 64 621572) (v_lw (rnd_hi rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_6021c D_6021c.  (* [comment removed for export] *)
      sv F_60220 D_60220 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_60224 D_60224.  (* [comment removed for export] *)
      stepb_tk F_60228 D_60228 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_60468 D_60468.  (* [comment removed for export] *)
      stepb_ft F_6046c D_6046c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_60470 D_60470.  (* [comment removed for export] *)
      stepb_ft F_60474 D_60474 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_60478 D_60478 (0x52d58 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_52d58 D_52d58.  (* [comment removed for export] *)
      sn F_52d74 D_52d74.  (* [comment removed for export] *)
      ld_step F_52d78 D_52d78 (word_to_le_bytes 8 (Z_to_bv 64 621568)) (Z_to_bv 64 621568) ltac:(rd_img img_65b58_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_52d7c D_52d7c (Z_to_bv 64 621569) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_52d80 D_52d80 (canary_bytes rdraw) (canary rdraw) ltac:(rewrite rdn_cmem_data by region_side; apply rd_guard) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_52d84 D_52d84.  (* [comment removed for export] *)
      stw F_52d88 D_52d88 (Z_to_bv 64 489856) (canary rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_52d8c D_52d8c (word_to_le_bytes 8 (Z_to_bv 64 336984)) (Z_to_bv 64 336984) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_52d90 D_52d90 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_52d94 D_52d94 (0x52458 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 489872 ->
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
        getr regs' 4 = (Z_to_bv 64 489872) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 141516) ->
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
        G (mkst regs' (0x52618 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336984))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom)) ->
    G (mkst regs (0x52458 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336984))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, D_ssp, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_52458 D_52458 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_5245c D_5245c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_52460 D_52460 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_52464 D_52464 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_52468 D_52468 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_5246c D_5246c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_52470 D_52470 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_52474 D_52474 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_52554 D_52554 (word_to_le_bytes 8 (Z_to_bv 64 337388)) (Z_to_bv 64 337388) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_52558 D_52558 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_5255c D_5255c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_52560 D_52560 (word_to_le_bytes 8 (Z_to_bv 64 141516)) (Z_to_bv 64 141516) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_52564 D_52564 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_52568 D_52568 (0x525ec : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_525ec D_525ec.  (* [comment removed for export] *)
      sn F_525f0 D_525f0.  (* [comment removed for export] *)
      sn F_525f4 D_525f4.  (* [comment removed for export] *)
      sv F_525f8 D_525f8 (argc_w av).  (* [comment removed for export] *)
      sv F_525fc D_525fc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_52600 D_52600 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_52604 D_52604 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_52608 D_52608 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_5260c D_5260c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_52610 D_52610 (sp0).  (* [comment removed for export] *)
      stepret F_52614 D_52614 (0x52618 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 489872 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 141516 ->
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
        getr regs' 1 = (Z_to_bv 64 337308) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 489872) ->
        getr regs' 8 = (Z_to_bv 64 403664) ->
        getr regs' 9 = (Z_to_bv 64 403656) ->
        getr regs' 18 = (Z_to_bv 64 141516) ->
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
        G (mkst regs' (0x227c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336984))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 337484))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom)) ->
    G (mkst regs (0x52618 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336976))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 621600))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 336984))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, D_ssp, aux_base, argv_w in *.
    eapply HG.
    { sv F_52618 D_52618 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_5261c D_5261c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_52620 D_52620 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_52624 D_52624 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_52628 D_52628 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_5262c D_5262c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_52630 D_52630 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_52634 D_52634 (argc_w av).  (* [comment removed for export] *)
      sn F_52638 D_52638.  (* [comment removed for export] *)
      stepiv F_5263c D_5263c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_52640 D_52640 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_52644 D_52644 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_52648 D_52648.  (* [comment removed for export] *)
      sv F_5256c D_5256c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_52570 D_52570 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 337484) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_52574 D_52574 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_52578 D_52578 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_5257c D_5257c.  (* [comment removed for export] *)
      stepret F_5233c D_5233c (0x52580 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_52580 D_52580.  (* [comment removed for export] *)
      sn F_52584 D_52584.  (* [comment removed for export] *)
      ld_step F_52588 D_52588 (word_to_le_bytes 8 (Z_to_bv 64 403664)) (Z_to_bv 64 403664) ltac:(rd_img img_65b48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_5258c D_5258c (word_to_le_bytes 8 (Z_to_bv 64 403656)) (Z_to_bv 64 403656) ltac:(rd_img img_65b50_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_52590 D_52590 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_52594 D_52594 (word_to_le_bytes 8 (Z_to_bv 64 141256)) (Z_to_bv 64 141256) ltac:(rd_img img_628c8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_52598 D_52598 (0x227c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word) (J9 : word -> option byte),
    wfJ sp0 J9 ->
    rdn SEGS J9 (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 337484)) ->
    rdn SEGS J9 (Z_to_bv 64 (bv_unsigned sp0 - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) ->
    rdn SEGS J9 (Z_to_bv 64 (bv_unsigned sp0 - 72)) 8 = Some (word_to_le_bytes 8 (argc_w av)) ->
    getr regs 1 = Z_to_bv 64 337308 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 489872 ->
    getr regs 8 = Z_to_bv 64 403664 ->
    getr regs 9 = Z_to_bv 64 403656 ->
    getr regs 18 = Z_to_bv 64 141516 ->
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
        getr regs' 1 = (Z_to_bv 64 337500) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 489872) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 141516) ->
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
        G (mkst regs' (0x228cc : word) (CM (wbytes (wbytes J9 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 337308))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 403664))) (wbytes ((D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0))))) (Z_to_bv 64 421328) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x227c8 : word) (CM J9 ((D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 620984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 621000) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 620992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 621624) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 621632) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 489888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 489864) (word_to_le_bytes 8 (Z_to_bv 64 489888))) (Z_to_bv 64 489672) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 621600) ([Z_to_bv 8 1])) (Z_to_bv 64 489712) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 489704) (word_to_le_bytes 4 tid)) (Z_to_bv 64 489824) (word_to_le_bytes 8 (Z_to_bv 64 621656))) (Z_to_bv 64 489792) (word_to_le_bytes 8 (Z_to_bv 64 489792))) (Z_to_bv 64 489680) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489688) (word_to_le_bytes 8 (Z_to_bv 64 489672))) (Z_to_bv 64 489696) (word_to_le_bytes 8 (Z_to_bv 64 0)))))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid J9 HJ R56 R64 R72 H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, D_ssp, aux_base, argv_w in *.
    eapply HG.
    { sv F_227c8 D_227c8 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_227cc D_227cc (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 337308) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_227d0 D_227d0 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 403664) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_227d4 D_227d4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_227d8 D_227d8.  (* [comment removed for export] *)
      sn F_227dc D_227dc.  (* [comment removed for export] *)
      lb_step F_227e0 D_227e0 (Z_to_bv 8 0) ltac:(rd_img img_66dd0_1).  (* [comment removed for export] *)
      sn F_227e4 D_227e4.  (* [comment removed for export] *)
      stepb_tk F_227e8 D_227e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_227f4 D_227f4.  (* [comment removed for export] *)
      sn F_227f8 D_227f8.  (* [comment removed for export] *)
      sn F_227fc D_227fc.  (* [comment removed for export] *)
      stw F_22800 D_22800 (Z_to_bv 64 421328) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_22804 D_22804.  (* [comment removed for export] *)
      ld_step F_22808 D_22808 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_65a40_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_2280c D_2280c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2282c D_2282c (word_to_le_bytes 8 (Z_to_bv 64 337308)) (Z_to_bv 64 337308) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_22830 D_22830 (word_to_le_bytes 8 (Z_to_bv 64 403664)) (Z_to_bv 64 403664) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_22834 D_22834 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_22838 D_22838 (0x5259c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_5259c D_5259c.  (* [comment removed for export] *)
      stepb_ft F_525a0 D_525a0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_525a4 D_525a4 (word_to_le_bytes 8 (Z_to_bv 64 337484)) (Z_to_bv 64 337484) ltac:(rewrite rdn_cmem_win by region_side; peel; rd_J9 R56) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_525a8 D_525a8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; peel; rd_J9 R64) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_525ac D_525ac (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; peel; rd_J9 R72) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_525b0 D_525b0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_525b4 D_525b4 (0x5264c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_5264c D_5264c (argc_w av).  (* [comment removed for export] *)
      sv F_52650 D_52650 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_52654 D_52654 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_52658 D_52658 (0x228cc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
