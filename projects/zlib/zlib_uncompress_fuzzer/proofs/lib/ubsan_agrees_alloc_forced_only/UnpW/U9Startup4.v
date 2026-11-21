(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac ArgvEnv RefLayout DrawDefs. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U9Img U9StartupDefs U9_code_14730_15000 U9_code_19000_1a000 U9_code_1a000_1b000 U9_code_21000_21d44.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
(* [comment removed for export] *)

Abbreviation SEGS := TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := TgtO_zlib_uncompress_fuzzer_ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  (* a worker port727 (): the launch as Common/ArgvEnv's Scaffold has it (a worker's VLAUNCH +
     LOK); av / ev / uid / hw / gid / rseq are notations of inp. *)
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.  (* a worker (A1) tool *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N TgtO_zlib_uncompress_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N TgtO_zlib_uncompress_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N TgtO_zlib_uncompress_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). rewrite <- rnd_sub4 by exact Hjn. apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side; apply rdn_guard; [reflexivity | reflexivity | lia | lia].

  Lemma slli_argc : v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. change (len_word av) with (argcN inp); rewrite (u_argcN inp Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475728 ->
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
        getr regs' 4 = (Z_to_bv 64 475728) ->
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
        G (mkst regs' (0x19cec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19ce4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_19bf0 D_19bf0 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19bf4 D_19bf4.  (* [comment removed for export] *)
      sv F_1a414 D_1a414 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1a418 D_1a418 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105708) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1a41c D_1a41c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_1a420 D_1a420 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_1a424 D_1a424.  (* [comment removed for export] *)
      ld_step F_1a428 D_1a428 (word_to_le_bytes 8 (Z_to_bv 64 607416)) (Z_to_bv 64 607416) ltac:(rd_img img_22df8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1a42c D_1a42c.  (* [comment removed for export] *)
      sn F_1a430 D_1a430.  (* [comment removed for export] *)
      stepiv F_21368 D_21368 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_2136c D_2136c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2147c D_2147c.  (* [comment removed for export] *)
      sn F_21480 D_21480.  (* [comment removed for export] *)
      stepb_ft F_21484 D_21484 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21488 D_21488.  (* [comment removed for export] *)
      stepb_tk F_2148c D_2148c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_214c4 D_214c4.  (* [comment removed for export] *)
      stepb_ft F_214c8 D_214c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_214cc D_214cc (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_214d0 D_214d0 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_214d4 D_214d4 (Z_to_bv 64 607416) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_214d8 D_214d8 (Z_to_bv 64 607420) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_214dc D_214dc.  (* [comment removed for export] *)
      sv F_214e0 D_214e0 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_214e4 D_214e4.  (* [comment removed for export] *)
      stepb_tk F_214e8 D_214e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21728 D_21728.  (* [comment removed for export] *)
      stepb_ft F_2172c D_2172c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21730 D_21730.  (* [comment removed for export] *)
      stepb_ft F_21734 D_21734 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_21738 D_21738 (0x1a51c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1a434 D_1a434.  (* [comment removed for export] *)
      sn F_1a450 D_1a450.  (* [comment removed for export] *)
      ld_step F_1a454 D_1a454 (word_to_le_bytes 8 (Z_to_bv 64 607416)) (Z_to_bv 64 607416) ltac:(rd_img img_22df8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1a458 D_1a458 (Z_to_bv 64 607417) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a45c D_1a45c (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_1a460 D_1a460.  (* [comment removed for export] *)
      stw F_1a464 D_1a464 (Z_to_bv 64 475712) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a468 D_1a468 (word_to_le_bytes 8 (Z_to_bv 64 105708)) (Z_to_bv 64 105708) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1a46c D_1a46c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1a470 D_1a470 (0x19cec : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_19bf0 D_19bf0 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19bf4 D_19bf4.  (* [comment removed for export] *)
      sv F_1a414 D_1a414 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1a418 D_1a418 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105708) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1a41c D_1a41c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_1a420 D_1a420 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_1a424 D_1a424.  (* [comment removed for export] *)
      ld_step F_1a428 D_1a428 (word_to_le_bytes 8 (Z_to_bv 64 607416)) (Z_to_bv 64 607416) ltac:(rd_img img_22df8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1a42c D_1a42c.  (* [comment removed for export] *)
      sn F_1a430 D_1a430.  (* [comment removed for export] *)
      stepiv F_21368 D_21368 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_2136c D_2136c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2147c D_2147c.  (* [comment removed for export] *)
      sn F_21480 D_21480.  (* [comment removed for export] *)
      stepb_ft F_21484 D_21484 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21488 D_21488.  (* [comment removed for export] *)
      stepb_tk F_2148c D_2148c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_214c4 D_214c4.  (* [comment removed for export] *)
      stepb_ft F_214c8 D_214c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_214cc D_214cc (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_214d0 D_214d0 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_214d4 D_214d4 (Z_to_bv 64 607416) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_214d8 D_214d8 (Z_to_bv 64 607420) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_214dc D_214dc.  (* [comment removed for export] *)
      sv F_214e0 D_214e0 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_214e4 D_214e4.  (* [comment removed for export] *)
      stepb_tk F_214e8 D_214e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21728 D_21728.  (* [comment removed for export] *)
      stepb_ft F_2172c D_2172c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21730 D_21730.  (* [comment removed for export] *)
      stepb_ft F_21734 D_21734 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_21738 D_21738 (0x1a51c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1a434 D_1a434.  (* [comment removed for export] *)
      sn F_1a450 D_1a450.  (* [comment removed for export] *)
      ld_step F_1a454 D_1a454 (word_to_le_bytes 8 (Z_to_bv 64 607416)) (Z_to_bv 64 607416) ltac:(rd_img img_22df8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1a458 D_1a458 (Z_to_bv 64 607417) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a45c D_1a45c (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_1a460 D_1a460.  (* [comment removed for export] *)
      stw F_1a464 D_1a464 (Z_to_bv 64 475712) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a468 D_1a468 (word_to_le_bytes 8 (Z_to_bv 64 105708)) (Z_to_bv 64 105708) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1a46c D_1a46c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1a470 D_1a470 (0x19cec : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475728 ->
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
        getr regs' 4 = (Z_to_bv 64 475728) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 84216) ->
        getr regs' 11 = (argc_w inp) ->
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
        G (mkst regs' (0x19eac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19cec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_19bf8 D_19bf8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19bfc D_19bfc (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19c00 D_19c00 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19c04 D_19c04 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19c08 D_19c08 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19c0c D_19c0c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19c10 D_19c10 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_19c14 D_19c14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19cf4 D_19cf4 (word_to_le_bytes 8 (Z_to_bv 64 106112)) (Z_to_bv 64 106112) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cf8 D_19cf8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cfc D_19cfc (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d00 D_19d00 (word_to_le_bytes 8 (Z_to_bv 64 84216)) (Z_to_bv 64 84216) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d04 D_19d04 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_19d08 D_19d08 (0x19e80 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d8c D_19d8c.  (* [comment removed for export] *)
      sn F_19d90 D_19d90.  (* [comment removed for export] *)
      sn F_19d94 D_19d94.  (* [comment removed for export] *)
      sv F_19d98 D_19d98 (argc_w inp).  (* [comment removed for export] *)
      sv F_19d9c D_19d9c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_19da0 D_19da0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19da4 D_19da4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19da8 D_19da8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19dac D_19dac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19db0 D_19db0 (sp0).  (* [comment removed for export] *)
      stepret F_19db4 D_19db4 (0x19eac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_19bf8 D_19bf8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19bfc D_19bfc (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19c00 D_19c00 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19c04 D_19c04 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19c08 D_19c08 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19c0c D_19c0c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19c10 D_19c10 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_19c14 D_19c14 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19cf4 D_19cf4 (word_to_le_bytes 8 (Z_to_bv 64 106112)) (Z_to_bv 64 106112) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cf8 D_19cf8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cfc D_19cfc (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d00 D_19d00 (word_to_le_bytes 8 (Z_to_bv 64 84216)) (Z_to_bv 64 84216) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d04 D_19d04 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_19d08 D_19d08 (0x19e80 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d8c D_19d8c.  (* [comment removed for export] *)
      sn F_19d90 D_19d90.  (* [comment removed for export] *)
      sn F_19d94 D_19d94.  (* [comment removed for export] *)
      sv F_19d98 D_19d98 (argc_w inp).  (* [comment removed for export] *)
      sv F_19d9c D_19d9c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_19da0 D_19da0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19da4 D_19da4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19da8 D_19da8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19dac D_19dac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19db0 D_19db0 (sp0).  (* [comment removed for export] *)
      stepret F_19db4 D_19db4 (0x19eac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475728 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 84216 ->
    getr regs 11 = argc_w inp ->
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
        getr regs' 1 = (Z_to_bv 64 106032) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475728) ->
        getr regs' 8 = (Z_to_bv 64 142904) ->
        getr regs' 9 = (Z_to_bv 64 142896) ->
        getr regs' 18 = (Z_to_bv 64 84216) ->
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
        G (mkst regs' (0x147f4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106208))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19eac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_19db8 D_19db8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_19dbc D_19dbc (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dc0 D_19dc0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dc4 D_19dc4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dc8 D_19dc8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dcc D_19dcc (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_19dd0 D_19dd0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19dd4 D_19dd4 (argc_w inp).  (* [comment removed for export] *)
      sn F_19dd8 D_19dd8.  (* [comment removed for export] *)
      stepiv F_19ddc D_19ddc (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_19de0 D_19de0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_19de4 D_19de4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_19de8 D_19de8.  (* [comment removed for export] *)
      sv F_19d0c D_19d0c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_19d10 D_19d10 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 106208) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d14 D_19d14 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d18 D_19d18 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_19d1c D_19d1c.  (* [comment removed for export] *)
      stepret F_19adc D_19adc (0x19e14 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d20 D_19d20.  (* [comment removed for export] *)
      sn F_19d24 D_19d24.  (* [comment removed for export] *)
      ld_step F_19d28 D_19d28 (word_to_le_bytes 8 (Z_to_bv 64 142904)) (Z_to_bv 64 142904) ltac:(rd_img img_22de8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d2c D_19d2c (word_to_le_bytes 8 (Z_to_bv 64 142896)) (Z_to_bv 64 142896) ltac:(rd_img img_22df0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19d30 D_19d30 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19d34 D_19d34 (word_to_le_bytes 8 (Z_to_bv 64 83956)) (Z_to_bv 64 83956) ltac:(rd_img img_22d48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_19d38 D_19d38 (0x147f4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_19db8 D_19db8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_19dbc D_19dbc (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dc0 D_19dc0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dc4 D_19dc4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dc8 D_19dc8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19dcc D_19dcc (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_19dd0 D_19dd0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19dd4 D_19dd4 (argc_w inp).  (* [comment removed for export] *)
      sn F_19dd8 D_19dd8.  (* [comment removed for export] *)
      stepiv F_19ddc D_19ddc (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_19de0 D_19de0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_19de4 D_19de4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_19de8 D_19de8.  (* [comment removed for export] *)
      sv F_19d0c D_19d0c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_19d10 D_19d10 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 106208) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d14 D_19d14 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d18 D_19d18 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_19d1c D_19d1c.  (* [comment removed for export] *)
      stepret F_19adc D_19adc (0x19e14 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d20 D_19d20.  (* [comment removed for export] *)
      sn F_19d24 D_19d24.  (* [comment removed for export] *)
      ld_step F_19d28 D_19d28 (word_to_le_bytes 8 (Z_to_bv 64 142904)) (Z_to_bv 64 142904) ltac:(rd_img img_22de8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d2c D_19d2c (word_to_le_bytes 8 (Z_to_bv 64 142896)) (Z_to_bv 64 142896) ltac:(rd_img img_22df0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19d30 D_19d30 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19d34 D_19d34 (word_to_le_bytes 8 (Z_to_bv 64 83956)) (Z_to_bv 64 83956) ltac:(rd_img img_22d48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_19d38 D_19d38 (0x147f4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 106032 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475728 ->
    getr regs 8 = Z_to_bv 64 142904 ->
    getr regs 9 = Z_to_bv 64 142896 ->
    getr regs 18 = Z_to_bv 64 84216 ->
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
        getr regs' 1 = (Z_to_bv 64 106224) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475728) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 84216) ->
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
        G (mkst regs' (0x148f8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106208))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 106032))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 142904))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 147712) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x147f4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105700))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607448))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105708))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106208))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606840) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606856) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606848) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607472) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607480) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475744) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475744))) (Z_to_bv 64 475528) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 607448) ([Z_to_bv 8 1])) (Z_to_bv 64 475568) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475560) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 607504))) (Z_to_bv 64 475648) (word_to_le_bytes 8 (Z_to_bv 64 475648))) (Z_to_bv 64 475536) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475544) (word_to_le_bytes 8 (Z_to_bv 64 475528))) (Z_to_bv 64 475552) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607416) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607420) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607417) ([Z_to_bv 8 0])) (Z_to_bv 64 475712) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_14778 D_14778 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_1477c D_1477c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 106032) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14780 D_14780 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 142904) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14784 D_14784 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14788 D_14788.  (* [comment removed for export] *)
      sn F_1478c D_1478c.  (* [comment removed for export] *)
      lb_step F_14790 D_14790 (Z_to_bv 8 0) ltac:(rd_img img_24020_1).  (* [comment removed for export] *)
      sn F_14794 D_14794.  (* [comment removed for export] *)
      stepb_tk F_14798 D_14798 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_147a4 D_147a4.  (* [comment removed for export] *)
      sn F_147a8 D_147a8.  (* [comment removed for export] *)
      sn F_147ac D_147ac.  (* [comment removed for export] *)
      stw F_147b0 D_147b0 (Z_to_bv 64 147712) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_147b4 D_147b4.  (* [comment removed for export] *)
      ld_step F_147b8 D_147b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22d90_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_147bc D_147bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_147dc D_147dc (word_to_le_bytes 8 (Z_to_bv 64 106032)) (Z_to_bv 64 106032) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_147e0 D_147e0 (word_to_le_bytes 8 (Z_to_bv 64 142904)) (Z_to_bv 64 142904) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147e4 D_147e4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147e8 D_147e8 (0x19e30 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d3c D_19d3c.  (* [comment removed for export] *)
      stepb_ft F_19d40 D_19d40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19d44 D_19d44 (word_to_le_bytes 8 (Z_to_bv 64 106208)) (Z_to_bv 64 106208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d48 D_19d48 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d4c D_19d4c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d50 D_19d50 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_19d54 D_19d54 (0x19ee0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_19dec D_19dec (argc_w inp).  (* [comment removed for export] *)
      sv F_19df0 D_19df0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19df4 D_19df4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_19df8 D_19df8 (0x148f8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_14778 D_14778 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_1477c D_1477c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 106032) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14780 D_14780 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 142904) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14784 D_14784 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14788 D_14788.  (* [comment removed for export] *)
      sn F_1478c D_1478c.  (* [comment removed for export] *)
      lb_step F_14790 D_14790 (Z_to_bv 8 0) ltac:(rd_img img_24020_1).  (* [comment removed for export] *)
      sn F_14794 D_14794.  (* [comment removed for export] *)
      stepb_tk F_14798 D_14798 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_147a4 D_147a4.  (* [comment removed for export] *)
      sn F_147a8 D_147a8.  (* [comment removed for export] *)
      sn F_147ac D_147ac.  (* [comment removed for export] *)
      stw F_147b0 D_147b0 (Z_to_bv 64 147712) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_147b4 D_147b4.  (* [comment removed for export] *)
      ld_step F_147b8 D_147b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22d90_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_147bc D_147bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_147dc D_147dc (word_to_le_bytes 8 (Z_to_bv 64 106032)) (Z_to_bv 64 106032) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_147e0 D_147e0 (word_to_le_bytes 8 (Z_to_bv 64 142904)) (Z_to_bv 64 142904) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147e4 D_147e4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147e8 D_147e8 (0x19e30 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d3c D_19d3c.  (* [comment removed for export] *)
      stepb_ft F_19d40 D_19d40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19d44 D_19d44 (word_to_le_bytes 8 (Z_to_bv 64 106208)) (Z_to_bv 64 106208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d48 D_19d48 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d4c D_19d4c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d50 D_19d50 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_19d54 D_19d54 (0x19ee0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_19dec D_19dec (argc_w inp).  (* [comment removed for export] *)
      sv F_19df0 D_19df0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19df4 D_19df4 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_19df8 D_19df8 (0x148f8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
