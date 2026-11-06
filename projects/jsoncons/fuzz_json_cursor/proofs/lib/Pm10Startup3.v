(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  StartupTac ArgvEnv RefLayout Pm10Img Pm10StartupDefs
  Pm10_code_a4d64_a5014 Pm10_code_b8100_b810c     .
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

Section P.
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

  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

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

Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 674644 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 1002560 ->
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
getr regs' 9 = Z_to_bv 64 1002560 ->
getr regs' 10 = Z_to_bv 64 56 ->
getr regs' 11 = Z_to_bv 64 1001912 ->
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
G (mkst regs' (0xa4dec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xa4d64 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_a4d64 D_a4d64 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_a4d68 D_a4d68 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 674644) ltac:(ok_win HJ).
stw F_a4d6c D_a4d6c (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_a4d70 D_a4d70 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_a4d74 D_a4d74 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 1002560) ltac:(ok_win HJ).
stw F_a4d78 D_a4d78 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a4d7c D_a4d7c (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a4d80 D_a4d80 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_a4d84 D_a4d84 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_a4d88 D_a4d88.
sn F_a4d8c D_a4d8c.
sn F_a4d90 D_a4d90.
sn F_a4d94 D_a4d94.
stepb_ft F_a4d98 D_a4d98 ltac:(pin; cond_compute).
sn F_a4d9c D_a4d9c.
sn F_a4da0 D_a4da0.
sn F_a4da4 D_a4da4.
ld_step F_a4da8 D_a4da8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4dac D_a4dac (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_a4db0 D_a4db0.
sn F_a4db4 D_a4db4.
ld_step F_a4db8 D_a4db8 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_c2ef8_4) ltac:(vm_compute; reflexivity).
ld_step F_a4dbc D_a4dbc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c1a50_8) ltac:(apply bytes_le_to_Z_8).
sn F_a4dc0 D_a4dc0.
sn F_a4dc4 D_a4dc4.
sn F_a4dc8 D_a4dc8.
sn F_a4dcc D_a4dcc.
sn F_a4dd0 D_a4dd0.
sn F_a4dd4 D_a4dd4.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 1002560 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 1001912 ->
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
getr regs' 9 = Z_to_bv 64 1002560 ->
getr regs' 10 = Z_to_bv 64 56 ->
getr regs' 11 = Z_to_bv 64 1001912 ->
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
G (mkst regs' (0xa4dec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xa4dec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_a4df0 D_a4df0 ltac:(pin; cond_compute).
ld_step F_a4dd8 D_a4dd8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_a4ddc D_a4ddc.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 1002560 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 1001912 ->
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
getr regs' 9 = Z_to_bv 64 1002560 ->
getr regs' 11 = Z_to_bv 64 1001912 ->
getr regs' 17 = Z_to_bv 64 0 ->
getr regs' 22 = Z_to_bv 64 0 ->
getr regs' 23 = Z_to_bv 64 0 ->
getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 25 = Z_to_bv 64 0 ->
getr regs' 26 = Z_to_bv 64 0 ->
getr regs' 27 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0xa4e3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0xa4dec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_ft F_a4e14 D_a4e14 ltac:(pin; cond_compute).
ld_step F_a4e18 D_a4e18 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_a4e1c D_a4e1c ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_ft F_a4de8 D_a4de8 ltac:(pin; cond_compute).
ld_step F_a4dec D_a4dec (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a4df0 D_a4df0 ltac:(pin; cond_compute).
stepb_tk F_a4df4 D_a4df4 ltac:(pin; cond_compute).
sn F_a4e08 D_a4e08.
stepb_ft F_a4e0c D_a4e0c ltac:(pin; cond_compute).
sn F_a4e10 D_a4e10.
stepb_tk F_a4e14 D_a4e14 ltac:(pin; cond_compute).
sn F_a4e34 D_a4e34.
sn F_a4e38 D_a4e38.
sn F_a4de0 D_a4de0.
sn F_a4de4 D_a4de4.
stepb_tk F_a4de8 D_a4de8 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 1002560 ->
getr regs 11 = Z_to_bv 64 1001912 ->
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
getr regs' 4 = Z_to_bv 64 870832 ->
getr regs' 10 = Z_to_bv 64 1001912 ->
getr regs' 11 = Z_to_bv 64 1002616 ->
getr regs' 12 = Z_to_bv 64 0 ->
getr regs' 13 = Z_to_bv 64 870624 ->
getr regs' 14 = Z_to_bv 64 0 ->
getr regs' 15 = Z_to_bv 64 18446744073708680784 ->
getr regs' 17 = Z_to_bv 64 96 ->
getr regs' 18 = Z_to_bv 64 870632 ->
getr regs' 22 = Z_to_bv 64 0 ->
getr regs' 23 = Z_to_bv 64 0 ->
getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 25 = Z_to_bv 64 0 ->
getr regs' 26 = Z_to_bv 64 0 ->
getr regs' 27 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0xa4fc0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1001944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1001960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1001952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1002584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1002592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 870848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 870824) (word_to_le_bytes 8 (Z_to_bv 64 870848))) (Z_to_bv 64 870632) (word_to_le_bytes 8 (Z_to_bv 64 870632))) (Z_to_bv 64 1002560) ([Z_to_bv 8 1])) (Z_to_bv 64 870672) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0xa4e3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_a4e3c D_a4e3c ltac:(pin; cond_compute).
ld_step F_a4e74 D_a4e74 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f49c8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4e78 D_a4e78 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f49d8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4e7c D_a4e7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f49e0_8) ltac:(apply bytes_le_to_Z_8).
sn F_a4e80 D_a4e80.
sn F_a4e84 D_a4e84.
sn F_a4e88 D_a4e88.
sn F_a4e8c D_a4e8c.
sn F_a4e90 D_a4e90.
sn F_a4e94 D_a4e94.
sn F_a4e98 D_a4e98.
stw F_a4e9c D_a4e9c (Z_to_bv 64 1001944) (Z_to_bv 64 0) ltac:(ok_data).
stw F_a4ea0 D_a4ea0 (Z_to_bv 64 1001960) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_a4ea4 D_a4ea4 ltac:(pin; cond_compute).
sn F_a4ea8 D_a4ea8.
stw F_a4eac D_a4eac (Z_to_bv 64 1001952) (Z_to_bv 64 8) ltac:(ok_data).
sn F_a4eb0 D_a4eb0.
sn F_a4eb4 D_a4eb4.
sn F_a4eb8 D_a4eb8.
sn F_a4ebc D_a4ebc.
sn F_a4ec0 D_a4ec0.
sn F_a4ec4 D_a4ec4.
stw F_a4ec8 D_a4ec8 (Z_to_bv 64 1002584) (Z_to_bv 64 224) ltac:(ok_data).
stw F_a4ecc D_a4ecc (Z_to_bv 64 1002592) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_a4ed0 D_a4ed0 ltac:(pin; cond_compute).
sn F_a4f04 D_a4f04.
ld_step F_a4f08 D_a4f08 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f4c50_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4f0c D_a4f0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f4c68_8) ltac:(apply bytes_le_to_Z_8).
sn F_a4f10 D_a4f10.
sn F_a4f14 D_a4f14.
sn F_a4f18 D_a4f18.
sn F_a4f1c D_a4f1c.
sn F_a4f20 D_a4f20.
sn F_a4f24 D_a4f24.
sn F_a4f28 D_a4f28.
sn F_a4f2c D_a4f2c.
sn F_a4f30 D_a4f30.
sn F_a4f34 D_a4f34.
sn F_a4f38 D_a4f38.
stepb_tk F_a4f3c D_a4f3c ltac:(pin; cond_compute).
stw F_a4f84 D_a4f84 (Z_to_bv 64 870848) (Z_to_bv 64 0) ltac:(ok_data).
stw F_a4f88 D_a4f88 (Z_to_bv 64 870824) (Z_to_bv 64 870848) ltac:(ok_data).
stw F_a4f8c D_a4f8c (Z_to_bv 64 870632) (Z_to_bv 64 870632) ltac:(ok_data).
sn F_a4f90 D_a4f90.
sn F_a4f94 D_a4f94.
sn F_b8100 D_b8100.
sn F_b8104 D_b8104.
stepret F_b8108 D_b8108 (0xa4f98 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_a4f98 D_a4f98 ltac:(pin; cond_compute).
stepb_ft F_a4f9c D_a4f9c ltac:(pin; cond_compute).
sn F_a4fa0 D_a4fa0.
stw F_a4fa4 D_a4fa4 (Z_to_bv 64 1002560) (Z_to_bv 64 1) ltac:(ok_data).
sn F_a4fa8 D_a4fa8.
sn F_a4fac D_a4fac.
stw F_a4fb0 D_a4fb0 (Z_to_bv 64 870672) (Z_to_bv 64 2) ltac:(ok_data).
sn F_a4fb4 D_a4fb4.
sn F_a4fb8 D_a4fb8.
sn F_a4fbc D_a4fbc.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 870832 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 1002616 ->
getr regs 18 = Z_to_bv 64 870632 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 870832 ->
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
G (mkst regs' (0xa4b54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1001944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1001960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1001952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1002584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1002592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 870848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 870824) (word_to_le_bytes 8 (Z_to_bv 64 870848))) (Z_to_bv 64 870632) (word_to_le_bytes 8 (Z_to_bv 64 870632))) (Z_to_bv 64 1002560) ([Z_to_bv 8 1])) (Z_to_bv 64 870672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 870664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 870784) (word_to_le_bytes 8 (Z_to_bv 64 1002616))) (Z_to_bv 64 870752) (word_to_le_bytes 8 (Z_to_bv 64 870752))) (Z_to_bv 64 870640) (word_to_le_bytes 8 (Z_to_bv 64 870632))) (Z_to_bv 64 870648) (word_to_le_bytes 8 (Z_to_bv 64 870632))) (Z_to_bv 64 870656) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0xa4fc4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 674644))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1002560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1001944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1001960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1001952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1002584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1002592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 870848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 870824) (word_to_le_bytes 8 (Z_to_bv 64 870848))) (Z_to_bv 64 870632) (word_to_le_bytes 8 (Z_to_bv 64 870632))) (Z_to_bv 64 1002560) ([Z_to_bv 8 1])) (Z_to_bv 64 870672) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_a4fc4 D_a4fc4.
stw F_a4fc8 D_a4fc8 (Z_to_bv 64 870664) tid ltac:(ok_data).
stw F_a4fcc D_a4fcc (Z_to_bv 64 870784) (Z_to_bv 64 1002616) ltac:(ok_data).
stw F_a4fd0 D_a4fd0 (Z_to_bv 64 870752) (Z_to_bv 64 870752) ltac:(ok_data).
sn F_a4fd4 D_a4fd4.
ld_step F_a4fd8 D_a4fd8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_f4c28_8) ltac:(apply bytes_le_to_Z_8).
stw F_a4fdc D_a4fdc (Z_to_bv 64 870640) (Z_to_bv 64 870632) ltac:(ok_data).
stw F_a4fe0 D_a4fe0 (Z_to_bv 64 870648) (Z_to_bv 64 870632) ltac:(ok_data).
stw F_a4fe4 D_a4fe4 (Z_to_bv 64 870656) (Z_to_bv 64 0) ltac:(ok_data).
sn F_a4fe8 D_a4fe8.
ld_step F_a4ff0 D_a4ff0 (word_to_le_bytes 8 (Z_to_bv 64 674644)) (Z_to_bv 64 674644) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4ff4 D_a4ff4 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4ff8 D_a4ff8 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a4ffc D_a4ffc (word_to_le_bytes 8 (Z_to_bv 64 1002560)) (Z_to_bv 64 1002560) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a5000 D_a5000 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a5004 D_a5004 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a5008 D_a5008 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_a500c D_a500c (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_a5010 D_a5010 (0xa4b54 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
