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
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import StartupTac ArgvEnv RefLayout UbImg UbStartupDefs RefMemcpyLib Ub_code_2b52bc_2b5e0c Ub_code_2c03b8_2c0b2c Ub_code_e214c_e27a4.
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
    rdn SEGS (wbytes (wbytes (wbytes D (Z_to_bv 64 0x3560d8) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 0x3560dc) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])
                (Z_to_bv 64 0x3560d9) [Z_to_bv 8 0]) (Z_to_bv 64 0x3560d8) 8
    = Some (canary_bytes rnd).
  Proof.
    intros D.
    exact (rd_guard8_gen SEGS D 0x3560d8 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]
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
    getr regs 4 = Z_to_bv 64 3367064 ->
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
        getr regs' 4 = (Z_to_bv 64 3367064) ->
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
        G (mkst regs' (0x2b5420 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x2b5418 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_2b53d0 D_2b53d0 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_2b53d4 D_2b53d4.  (* [comment removed for export] *)
      sv F_2b5974 D_2b5974 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_2b5978 D_2b5978 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 2839584) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_2b597c D_2b597c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_2b5980 D_2b5980 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_2b5984 D_2b5984.  (* [comment removed for export] *)
      ld_step F_2b5988 D_2b5988 (word_to_le_bytes 8 (Z_to_bv 64 3498200)) (Z_to_bv 64 3498200) ltac:(rd_img img_321b58_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_2b598c D_2b598c.  (* [comment removed for export] *)
      sn F_2b5990 D_2b5990.  (* [comment removed for export] *)
      stepiv F_2c04b4 D_2c04b4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_2c04b8 D_2c04b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2c05c8 D_2c05c8.  (* [comment removed for export] *)
      sn F_2c05cc D_2c05cc.  (* [comment removed for export] *)
      stepb_ft F_2c05d0 D_2c05d0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2c05d4 D_2c05d4.  (* [comment removed for export] *)
      stepb_tk F_2c05d8 D_2c05d8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2c0610 D_2c0610.  (* [comment removed for export] *)
      stepb_ft F_2c0614 D_2c0614 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2c0618 D_2c0618 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3])) ltac:(RD_RNDa) ltac:(apply lez_rnd4a).  (* [comment removed for export] *)
      ld_step F_2c061c D_2c061c [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] (Z_to_bv 64 (bytes_le_to_Z [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7])) ltac:(RD_RNDb) ltac:(apply lez_rnd4b).  (* [comment removed for export] *)
      stw F_2c0620 D_2c0620 (Z_to_bv 64 3498200) (LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] eq_refl).
      stw F_2c0624 D_2c0624 (Z_to_bv 64 3498204) (LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite (sw_bytes_LWv [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7] eq_refl).
      sn F_2c0628 D_2c0628.  (* [comment removed for export] *)
      sv F_2c062c D_2c062c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_2c0630 D_2c0630.  (* [comment removed for export] *)
      stepb_tk F_2c0634 D_2c0634 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2c0874 D_2c0874.  (* [comment removed for export] *)
      stepb_ft F_2c0878 D_2c0878 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2c087c D_2c087c.  (* [comment removed for export] *)
      stepb_ft F_2c0880 D_2c0880 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_2c0884 D_2c0884 (0x2b59d0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b5994 D_2b5994.  (* [comment removed for export] *)
      sn F_2b59b0 D_2b59b0.  (* [comment removed for export] *)
      ld_step F_2b59b4 D_2b59b4 (word_to_le_bytes 8 (Z_to_bv 64 3498200)) (Z_to_bv 64 3498200) ltac:(rd_img img_321b58_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_2b59b8 D_2b59b8 (Z_to_bv 64 3498201) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_2b59bc D_2b59bc (canary_bytes rnd) (canary_w rnd) ltac:(RD_GUARD) ltac:(apply lez_canary).  (* [comment removed for export] *)
      sn F_2b59c0 D_2b59c0.  (* [comment removed for export] *)
      stw F_2b59c4 D_2b59c4 (Z_to_bv 64 3367048) (canary_w rnd) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_2b59c8 D_2b59c8 (word_to_le_bytes 8 (Z_to_bv 64 2839584)) (Z_to_bv 64 2839584) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b59cc D_2b59cc (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_2b59d0 D_2b59d0 (0x2b5420 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3367064 ->
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
        getr regs' 4 = (Z_to_bv 64 3367064) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 926440) ->
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
        G (mkst regs' (0x2b55e0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x2b5420 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_2b53d8 D_2b53d8 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b53dc D_2b53dc (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_2b53e0 D_2b53e0 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_2b53e4 D_2b53e4 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_2b53e8 D_2b53e8 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_2b53ec D_2b53ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2b53f0 D_2b53f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_2b53f4 D_2b53f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2b54d4 D_2b54d4 (word_to_le_bytes 8 (Z_to_bv 64 2839988)) (Z_to_bv 64 2839988) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b54d8 D_2b54d8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b54dc D_2b54dc (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b54e0 D_2b54e0 (word_to_le_bytes 8 (Z_to_bv 64 926440)) (Z_to_bv 64 926440) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b54e4 D_2b54e4 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_2b54e8 D_2b54e8 (0x2b55b4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b556c D_2b556c.  (* [comment removed for export] *)
      sn F_2b5570 D_2b5570.  (* [comment removed for export] *)
      sn F_2b5574 D_2b5574.  (* [comment removed for export] *)
      sv F_2b5578 D_2b5578 (argc_w av).  (* [comment removed for export] *)
      sv F_2b557c D_2b557c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_2b5580 D_2b5580 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b5584 D_2b5584 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b5588 D_2b5588 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b558c D_2b558c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b5590 D_2b5590 (sp0).  (* [comment removed for export] *)
      stepret F_2b5594 D_2b5594 (0x2b55e0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3367064 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 926440 ->
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
        getr regs' 1 = (Z_to_bv 64 2839908) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3367064) ->
        getr regs' 8 = (Z_to_bv 64 2907136) ->
        getr regs' 9 = (Z_to_bv 64 2907128) ->
        getr regs' 18 = (Z_to_bv 64 926440) ->
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
        G (mkst regs' (0xe21e0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2840084))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd)))) rom)) ->
    G (mkst regs (0x2b55e0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_2b5598 D_2b5598 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_2b559c D_2b559c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2b55a0 D_2b55a0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2b55a4 D_2b55a4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2b55a8 D_2b55a8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2b55ac D_2b55ac (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_2b55b0 D_2b55b0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_2b55b4 D_2b55b4 (argc_w av).  (* [comment removed for export] *)
      sn F_2b55b8 D_2b55b8.  (* [comment removed for export] *)
      stepiv F_2b55bc D_2b55bc (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_2b55c0 D_2b55c0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_2b55c4 D_2b55c4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_2b55c8 D_2b55c8.  (* [comment removed for export] *)
      sv F_2b54ec D_2b54ec (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_2b54f0 D_2b54f0 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 2840084) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2b54f4 D_2b54f4 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2b54f8 D_2b54f8 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2b54fc D_2b54fc.  (* [comment removed for export] *)
      stepret F_2b52bc D_2b52bc (0x2b5548 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b5500 D_2b5500.  (* [comment removed for export] *)
      sn F_2b5504 D_2b5504.  (* [comment removed for export] *)
      ld_step F_2b5508 D_2b5508 (word_to_le_bytes 8 (Z_to_bv 64 2907136)) (Z_to_bv 64 2907136) ltac:(rd_img img_321b78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b550c D_2b550c (word_to_le_bytes 8 (Z_to_bv 64 2907128)) (Z_to_bv 64 2907128) ltac:(rd_img img_321b80_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_2b5510 D_2b5510 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2b5514 D_2b5514 (word_to_le_bytes 8 (Z_to_bv 64 926176)) (Z_to_bv 64 926176) ltac:(rd_img img_2c5bb8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_2b5518 D_2b5518 (0xe21e0 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 2839908 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3367064 ->
    getr regs 8 = Z_to_bv 64 2907136 ->
    getr regs 9 = Z_to_bv 64 2907128 ->
    getr regs 18 = Z_to_bv 64 926440 ->
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
        getr regs' 1 = (Z_to_bv 64 2840100) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3367064) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 926440) ->
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
        G (mkst regs' (0xe22e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2840084))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 2839908))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 2907136))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 3290320) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0xe21e0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839576))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3498792))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2839584))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 2840084))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3498176) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498192) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498184) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3498816) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3498824) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3367080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3367056) (word_to_le_bytes 8 (Z_to_bv 64 3367080))) (Z_to_bv 64 3366864) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3498792) ([Z_to_bv 8 1])) (Z_to_bv 64 3366904) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3366896) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3367016) (word_to_le_bytes 8 (Z_to_bv 64 3498848))) (Z_to_bv 64 3366984) (word_to_le_bytes 8 (Z_to_bv 64 3366984))) (Z_to_bv 64 3366872) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366880) (word_to_le_bytes 8 (Z_to_bv 64 3366864))) (Z_to_bv 64 3366888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3498200) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 3498204) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 3498201) ([Z_to_bv 8 0])) (Z_to_bv 64 3367048) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_e2198 D_e2198 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_e219c D_e219c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 2839908) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_e21a0 D_e21a0 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 2907136) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_e21a4 D_e21a4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_e21a8 D_e21a8.  (* [comment removed for export] *)
      sn F_e21ac D_e21ac.  (* [comment removed for export] *)
      lb_step F_e21b0 D_e21b0 (Z_to_bv 8 0) ltac:(rd_img img_323490_1).  (* [comment removed for export] *)
      sn F_e21b4 D_e21b4.  (* [comment removed for export] *)
      stepb_tk F_e21b8 D_e21b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_e21c4 D_e21c4.  (* [comment removed for export] *)
      sn F_e21c8 D_e21c8.  (* [comment removed for export] *)
      sn F_e21cc D_e21cc.  (* [comment removed for export] *)
      stw F_e21d0 D_e21d0 (Z_to_bv 64 3290320) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_e21d4 D_e21d4.  (* [comment removed for export] *)
      ld_step F_e21d8 D_e21d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_321590_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_e21dc D_e21dc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_e21fc D_e21fc (word_to_le_bytes 8 (Z_to_bv 64 2839908)) (Z_to_bv 64 2839908) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_e2200 D_e2200 (word_to_le_bytes 8 (Z_to_bv 64 2907136)) (Z_to_bv 64 2907136) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_e2204 D_e2204 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_e2208 D_e2208 (0x2b5564 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b551c D_2b551c.  (* [comment removed for export] *)
      stepb_ft F_2b5520 D_2b5520 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_2b5524 D_2b5524 (word_to_le_bytes 8 (Z_to_bv 64 2840084)) (Z_to_bv 64 2840084) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b5528 D_2b5528 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2b552c D_2b552c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b5530 D_2b5530 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_2b5534 D_2b5534 (0x2b5614 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_2b55cc D_2b55cc (argc_w av).  (* [comment removed for export] *)
      sv F_2b55d0 D_2b55d0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_2b55d4 D_2b55d4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_2b55d8 D_2b55d8 (0xe22e8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
