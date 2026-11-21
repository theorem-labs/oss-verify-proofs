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

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac ArgvEnv RefLayout DrawDefs. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U7Img U7StartupDefs U7_code_14708_15000 U7_code_19000_1a000 U7_code_1a000_1b000 U7_code_21000_21d00.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
(* [comment removed for export] *)

Abbreviation SEGS := TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := TgtO_zlib_uncompress2_fuzzer_ubsan.M.phdrs.

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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 475760 ->
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
        getr regs' 4 = (Z_to_bv 64 475760) ->
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
        G (mkst regs' (0x19d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19d10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_19bac D_19bac (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19bb0 D_19bb0.  (* [comment removed for export] *)
      sv F_1a3d0 D_1a3d0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1a3d4 D_1a3d4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105752) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1a3d8 D_1a3d8 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_1a3dc D_1a3dc ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_1a3e0 D_1a3e0.  (* [comment removed for export] *)
      ld_step F_1a3e4 D_1a3e4 (word_to_le_bytes 8 (Z_to_bv 64 607448)) (Z_to_bv 64 607448) ltac:(rd_img img_22db0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1a3e8 D_1a3e8.  (* [comment removed for export] *)
      sn F_1a3ec D_1a3ec.  (* [comment removed for export] *)
      stepiv F_21324 D_21324 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_21328 D_21328 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21438 D_21438.  (* [comment removed for export] *)
      sn F_2143c D_2143c.  (* [comment removed for export] *)
      stepb_ft F_21440 D_21440 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21444 D_21444.  (* [comment removed for export] *)
      stepb_tk F_21448 D_21448 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21480 D_21480.  (* [comment removed for export] *)
      stepb_ft F_21484 D_21484 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_21488 D_21488 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_2148c D_2148c (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_21490 D_21490 (Z_to_bv 64 607448) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_21494 D_21494 (Z_to_bv 64 607452) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_21498 D_21498.  (* [comment removed for export] *)
      sv F_2149c D_2149c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_214a0 D_214a0.  (* [comment removed for export] *)
      stepb_tk F_214a4 D_214a4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_216e4 D_216e4.  (* [comment removed for export] *)
      stepb_ft F_216e8 D_216e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_216ec D_216ec.  (* [comment removed for export] *)
      stepb_ft F_216f0 D_216f0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_216f4 D_216f4 (0x1a548 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1a3f0 D_1a3f0.  (* [comment removed for export] *)
      sn F_1a40c D_1a40c.  (* [comment removed for export] *)
      ld_step F_1a410 D_1a410 (word_to_le_bytes 8 (Z_to_bv 64 607448)) (Z_to_bv 64 607448) ltac:(rd_img img_22db0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1a414 D_1a414 (Z_to_bv 64 607449) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a418 D_1a418 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_1a41c D_1a41c.  (* [comment removed for export] *)
      stw F_1a420 D_1a420 (Z_to_bv 64 475744) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a424 D_1a424 (word_to_le_bytes 8 (Z_to_bv 64 105752)) (Z_to_bv 64 105752) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1a428 D_1a428 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1a42c D_1a42c (0x19d18 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_19bac D_19bac (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19bb0 D_19bb0.  (* [comment removed for export] *)
      sv F_1a3d0 D_1a3d0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1a3d4 D_1a3d4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105752) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1a3d8 D_1a3d8 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_1a3dc D_1a3dc ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_1a3e0 D_1a3e0.  (* [comment removed for export] *)
      ld_step F_1a3e4 D_1a3e4 (word_to_le_bytes 8 (Z_to_bv 64 607448)) (Z_to_bv 64 607448) ltac:(rd_img img_22db0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1a3e8 D_1a3e8.  (* [comment removed for export] *)
      sn F_1a3ec D_1a3ec.  (* [comment removed for export] *)
      stepiv F_21324 D_21324 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_21328 D_21328 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21438 D_21438.  (* [comment removed for export] *)
      sn F_2143c D_2143c.  (* [comment removed for export] *)
      stepb_ft F_21440 D_21440 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21444 D_21444.  (* [comment removed for export] *)
      stepb_tk F_21448 D_21448 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_21480 D_21480.  (* [comment removed for export] *)
      stepb_ft F_21484 D_21484 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_21488 D_21488 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_2148c D_2148c (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_21490 D_21490 (Z_to_bv 64 607448) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_21494 D_21494 (Z_to_bv 64 607452) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_21498 D_21498.  (* [comment removed for export] *)
      sv F_2149c D_2149c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_214a0 D_214a0.  (* [comment removed for export] *)
      stepb_tk F_214a4 D_214a4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_216e4 D_216e4.  (* [comment removed for export] *)
      stepb_ft F_216e8 D_216e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_216ec D_216ec.  (* [comment removed for export] *)
      stepb_ft F_216f0 D_216f0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_216f4 D_216f4 (0x1a548 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1a3f0 D_1a3f0.  (* [comment removed for export] *)
      sn F_1a40c D_1a40c.  (* [comment removed for export] *)
      ld_step F_1a410 D_1a410 (word_to_le_bytes 8 (Z_to_bv 64 607448)) (Z_to_bv 64 607448) ltac:(rd_img img_22db0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1a414 D_1a414 (Z_to_bv 64 607449) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a418 D_1a418 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_1a41c D_1a41c.  (* [comment removed for export] *)
      stw F_1a420 D_1a420 (Z_to_bv 64 475744) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1a424 D_1a424 (word_to_le_bytes 8 (Z_to_bv 64 105752)) (Z_to_bv 64 105752) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1a428 D_1a428 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1a42c D_1a42c (0x19d18 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475760 ->
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
        getr regs' 4 = (Z_to_bv 64 475760) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 84220) ->
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
        G (mkst regs' (0x19ed8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_19bb4 D_19bb4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19bb8 D_19bb8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19bbc D_19bbc ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19bc0 D_19bc0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19bc4 D_19bc4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19bc8 D_19bc8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19bcc D_19bcc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_19bd0 D_19bd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19cb0 D_19cb0 (word_to_le_bytes 8 (Z_to_bv 64 106156)) (Z_to_bv 64 106156) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cb4 D_19cb4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cb8 D_19cb8 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cbc D_19cbc (word_to_le_bytes 8 (Z_to_bv 64 84220)) (Z_to_bv 64 84220) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19cc0 D_19cc0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_19cc4 D_19cc4 (0x19eac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d48 D_19d48.  (* [comment removed for export] *)
      sn F_19d4c D_19d4c.  (* [comment removed for export] *)
      sn F_19d50 D_19d50.  (* [comment removed for export] *)
      sv F_19d54 D_19d54 (argc_w inp).  (* [comment removed for export] *)
      sv F_19d58 D_19d58 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_19d5c D_19d5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d60 D_19d60 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d64 D_19d64 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d68 D_19d68 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d6c D_19d6c (sp0).  (* [comment removed for export] *)
      stepret F_19d70 D_19d70 (0x19ed8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_19bb4 D_19bb4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19bb8 D_19bb8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19bbc D_19bbc ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19bc0 D_19bc0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19bc4 D_19bc4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19bc8 D_19bc8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_19bcc D_19bcc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_19bd0 D_19bd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19cb0 D_19cb0 (word_to_le_bytes 8 (Z_to_bv 64 106156)) (Z_to_bv 64 106156) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cb4 D_19cb4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cb8 D_19cb8 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19cbc D_19cbc (word_to_le_bytes 8 (Z_to_bv 64 84220)) (Z_to_bv 64 84220) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19cc0 D_19cc0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_19cc4 D_19cc4 (0x19eac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19d48 D_19d48.  (* [comment removed for export] *)
      sn F_19d4c D_19d4c.  (* [comment removed for export] *)
      sn F_19d50 D_19d50.  (* [comment removed for export] *)
      sv F_19d54 D_19d54 (argc_w inp).  (* [comment removed for export] *)
      sv F_19d58 D_19d58 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_19d5c D_19d5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d60 D_19d60 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d64 D_19d64 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d68 D_19d68 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d6c D_19d6c (sp0).  (* [comment removed for export] *)
      stepret F_19d70 D_19d70 (0x19ed8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475760 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 84220 ->
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
        getr regs' 1 = (Z_to_bv 64 106076) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475760) ->
        getr regs' 8 = (Z_to_bv 64 142944) ->
        getr regs' 9 = (Z_to_bv 64 142936) ->
        getr regs' 18 = (Z_to_bv 64 84220) ->
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
        G (mkst regs' (0x147f8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106252))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19ed8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_19d74 D_19d74 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_19d78 D_19d78 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d7c D_19d7c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d80 D_19d80 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d84 D_19d84 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d88 D_19d88 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_19d8c D_19d8c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19d90 D_19d90 (argc_w inp).  (* [comment removed for export] *)
      sn F_19d94 D_19d94.  (* [comment removed for export] *)
      stepiv F_19d98 D_19d98 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_19d9c D_19d9c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_19da0 D_19da0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_19da4 D_19da4.  (* [comment removed for export] *)
      sv F_19cc8 D_19cc8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_19ccc D_19ccc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 106252) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19cd0 D_19cd0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19cd4 D_19cd4 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_19cd8 D_19cd8.  (* [comment removed for export] *)
      stepret F_19a98 D_19a98 (0x19e40 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19cdc D_19cdc.  (* [comment removed for export] *)
      sn F_19ce0 D_19ce0.  (* [comment removed for export] *)
      ld_step F_19ce4 D_19ce4 (word_to_le_bytes 8 (Z_to_bv 64 142944)) (Z_to_bv 64 142944) ltac:(rd_img img_22da0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19ce8 D_19ce8 (word_to_le_bytes 8 (Z_to_bv 64 142936)) (Z_to_bv 64 142936) ltac:(rd_img img_22da8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19cec D_19cec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19cf0 D_19cf0 (word_to_le_bytes 8 (Z_to_bv 64 83960)) (Z_to_bv 64 83960) ltac:(rd_img img_22d00_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_19cf4 D_19cf4 (0x147f8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_19d74 D_19d74 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_19d78 D_19d78 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d7c D_19d7c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d80 D_19d80 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d84 D_19d84 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19d88 D_19d88 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_19d8c D_19d8c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19d90 D_19d90 (argc_w inp).  (* [comment removed for export] *)
      sn F_19d94 D_19d94.  (* [comment removed for export] *)
      stepiv F_19d98 D_19d98 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_19d9c D_19d9c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_19da0 D_19da0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_19da4 D_19da4.  (* [comment removed for export] *)
      sv F_19cc8 D_19cc8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_19ccc D_19ccc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 106252) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19cd0 D_19cd0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_19cd4 D_19cd4 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_19cd8 D_19cd8.  (* [comment removed for export] *)
      stepret F_19a98 D_19a98 (0x19e40 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19cdc D_19cdc.  (* [comment removed for export] *)
      sn F_19ce0 D_19ce0.  (* [comment removed for export] *)
      ld_step F_19ce4 D_19ce4 (word_to_le_bytes 8 (Z_to_bv 64 142944)) (Z_to_bv 64 142944) ltac:(rd_img img_22da0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19ce8 D_19ce8 (word_to_le_bytes 8 (Z_to_bv 64 142936)) (Z_to_bv 64 142936) ltac:(rd_img img_22da8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_19cec D_19cec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19cf0 D_19cf0 (word_to_le_bytes 8 (Z_to_bv 64 83960)) (Z_to_bv 64 83960) ltac:(rd_img img_22d00_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_19cf4 D_19cf4 (0x147f8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 106076 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475760 ->
    getr regs 8 = Z_to_bv 64 142944 ->
    getr regs 9 = Z_to_bv 64 142936 ->
    getr regs 18 = Z_to_bv 64 84220 ->
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
        getr regs' 1 = (Z_to_bv 64 106268) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475760) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 84220) ->
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
        G (mkst regs' (0x148fc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106252))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 106076))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 142944))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 147744) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x147f8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105744))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607480))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105752))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106252))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 606872) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606888) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 606880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607504) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607512) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475752) (word_to_le_bytes 8 (Z_to_bv 64 475776))) (Z_to_bv 64 475560) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 607480) ([Z_to_bv 8 1])) (Z_to_bv 64 475600) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475592) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 607536))) (Z_to_bv 64 475680) (word_to_le_bytes 8 (Z_to_bv 64 475680))) (Z_to_bv 64 475568) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475576) (word_to_le_bytes 8 (Z_to_bv 64 475560))) (Z_to_bv 64 475584) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607448) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607452) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607449) ([Z_to_bv 8 0])) (Z_to_bv 64 475744) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_14750 D_14750 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14754 D_14754 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 106076) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14758 D_14758 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 142944) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_1475c D_1475c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14760 D_14760.  (* [comment removed for export] *)
      sn F_14764 D_14764.  (* [comment removed for export] *)
      lb_step F_14768 D_14768 (Z_to_bv 8 0) ltac:(rd_img img_23fe0_1).  (* [comment removed for export] *)
      sn F_1476c D_1476c.  (* [comment removed for export] *)
      stepb_tk F_14770 D_14770 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1477c D_1477c.  (* [comment removed for export] *)
      sn F_14780 D_14780.  (* [comment removed for export] *)
      sn F_14784 D_14784.  (* [comment removed for export] *)
      stw F_14788 D_14788 (Z_to_bv 64 147744) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_1478c D_1478c.  (* [comment removed for export] *)
      ld_step F_14790 D_14790 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22d48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14794 D_14794 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_147b4 D_147b4 (word_to_le_bytes 8 (Z_to_bv 64 106076)) (Z_to_bv 64 106076) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_147b8 D_147b8 (word_to_le_bytes 8 (Z_to_bv 64 142944)) (Z_to_bv 64 142944) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147bc D_147bc (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147c0 D_147c0 (0x19e5c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19cf8 D_19cf8.  (* [comment removed for export] *)
      stepb_ft F_19cfc D_19cfc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19d00 D_19d00 (word_to_le_bytes 8 (Z_to_bv 64 106252)) (Z_to_bv 64 106252) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d04 D_19d04 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d08 D_19d08 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d0c D_19d0c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_19d10 D_19d10 (0x19f0c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_19da8 D_19da8 (argc_w inp).  (* [comment removed for export] *)
      sv F_19dac D_19dac (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19db0 D_19db0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_19db4 D_19db4 (0x148fc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_14750 D_14750 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14754 D_14754 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 106076) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14758 D_14758 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 142944) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_1475c D_1475c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14760 D_14760.  (* [comment removed for export] *)
      sn F_14764 D_14764.  (* [comment removed for export] *)
      lb_step F_14768 D_14768 (Z_to_bv 8 0) ltac:(rd_img img_23fe0_1).  (* [comment removed for export] *)
      sn F_1476c D_1476c.  (* [comment removed for export] *)
      stepb_tk F_14770 D_14770 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1477c D_1477c.  (* [comment removed for export] *)
      sn F_14780 D_14780.  (* [comment removed for export] *)
      sn F_14784 D_14784.  (* [comment removed for export] *)
      stw F_14788 D_14788 (Z_to_bv 64 147744) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_1478c D_1478c.  (* [comment removed for export] *)
      ld_step F_14790 D_14790 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22d48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14794 D_14794 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_147b4 D_147b4 (word_to_le_bytes 8 (Z_to_bv 64 106076)) (Z_to_bv 64 106076) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_147b8 D_147b8 (word_to_le_bytes 8 (Z_to_bv 64 142944)) (Z_to_bv 64 142944) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147bc D_147bc (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147c0 D_147c0 (0x19e5c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19cf8 D_19cf8.  (* [comment removed for export] *)
      stepb_ft F_19cfc D_19cfc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_19d00 D_19d00 (word_to_le_bytes 8 (Z_to_bv 64 106252)) (Z_to_bv 64 106252) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d04 D_19d04 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_19d08 D_19d08 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19d0c D_19d0c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_19d10 D_19d10 (0x19f0c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_19da8 D_19da8 (argc_w inp).  (* [comment removed for export] *)
      sv F_19dac D_19dac (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_19db0 D_19db0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_19db4 D_19db4 (0x148fc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
