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

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ArgvEnv OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefLayout OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.DrawDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8Img OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8StartupDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_146ec_15000 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_18000_19000 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_19000_1a000 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8_code_20000_20a98.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
(* [comment removed for export] *)

Abbreviation SEGS := SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs.

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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 471088 ->
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
        getr regs' 4 = (Z_to_bv 64 471088) ->
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
        G (mkst regs' (0x18ad0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18ac8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_18944 D_18944 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_18948 D_18948.  (* [comment removed for export] *)
      sv F_19168 D_19168 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1916c D_1916c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 101072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_19170 D_19170 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_19174 D_19174 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_19178 D_19178.  (* [comment removed for export] *)
      ld_step F_1917c D_1917c (word_to_le_bytes 8 (Z_to_bv 64 602776)) (Z_to_bv 64 602776) ltac:(rd_img img_21b48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19180 D_19180.  (* [comment removed for export] *)
      sn F_19184 D_19184.  (* [comment removed for export] *)
      stepiv F_200bc D_200bc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_200c0 D_200c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201d0 D_201d0.  (* [comment removed for export] *)
      sn F_201d4 D_201d4.  (* [comment removed for export] *)
      stepb_ft F_201d8 D_201d8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201dc D_201dc.  (* [comment removed for export] *)
      stepb_tk F_201e0 D_201e0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20218 D_20218.  (* [comment removed for export] *)
      stepb_ft F_2021c D_2021c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_20220 D_20220 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_20224 D_20224 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_20228 D_20228 (Z_to_bv 64 602776) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_2022c D_2022c (Z_to_bv 64 602780) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_20230 D_20230.  (* [comment removed for export] *)
      sv F_20234 D_20234 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_20238 D_20238.  (* [comment removed for export] *)
      stepb_tk F_2023c D_2023c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2047c D_2047c.  (* [comment removed for export] *)
      stepb_ft F_20480 D_20480 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20484 D_20484.  (* [comment removed for export] *)
      stepb_ft F_20488 D_20488 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_2048c D_2048c (0x19300 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19188 D_19188.  (* [comment removed for export] *)
      sn F_191a4 D_191a4.  (* [comment removed for export] *)
      ld_step F_191a8 D_191a8 (word_to_le_bytes 8 (Z_to_bv 64 602776)) (Z_to_bv 64 602776) ltac:(rd_img img_21b48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_191ac D_191ac (Z_to_bv 64 602777) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_191b0 D_191b0 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_191b4 D_191b4.  (* [comment removed for export] *)
      stw F_191b8 D_191b8 (Z_to_bv 64 471072) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_191bc D_191bc (word_to_le_bytes 8 (Z_to_bv 64 101072)) (Z_to_bv 64 101072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_191c0 D_191c0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_191c4 D_191c4 (0x18ad0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_18944 D_18944 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_18948 D_18948.  (* [comment removed for export] *)
      sv F_19168 D_19168 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1916c D_1916c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 101072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_19170 D_19170 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_19174 D_19174 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_19178 D_19178.  (* [comment removed for export] *)
      ld_step F_1917c D_1917c (word_to_le_bytes 8 (Z_to_bv 64 602776)) (Z_to_bv 64 602776) ltac:(rd_img img_21b48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19180 D_19180.  (* [comment removed for export] *)
      sn F_19184 D_19184.  (* [comment removed for export] *)
      stepiv F_200bc D_200bc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_200c0 D_200c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201d0 D_201d0.  (* [comment removed for export] *)
      sn F_201d4 D_201d4.  (* [comment removed for export] *)
      stepb_ft F_201d8 D_201d8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201dc D_201dc.  (* [comment removed for export] *)
      stepb_tk F_201e0 D_201e0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20218 D_20218.  (* [comment removed for export] *)
      stepb_ft F_2021c D_2021c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_20220 D_20220 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_20224 D_20224 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_20228 D_20228 (Z_to_bv 64 602776) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_2022c D_2022c (Z_to_bv 64 602780) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_20230 D_20230.  (* [comment removed for export] *)
      sv F_20234 D_20234 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_20238 D_20238.  (* [comment removed for export] *)
      stepb_tk F_2023c D_2023c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2047c D_2047c.  (* [comment removed for export] *)
      stepb_ft F_20480 D_20480 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20484 D_20484.  (* [comment removed for export] *)
      stepb_ft F_20488 D_20488 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_2048c D_2048c (0x19300 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19188 D_19188.  (* [comment removed for export] *)
      sn F_191a4 D_191a4.  (* [comment removed for export] *)
      ld_step F_191a8 D_191a8 (word_to_le_bytes 8 (Z_to_bv 64 602776)) (Z_to_bv 64 602776) ltac:(rd_img img_21b48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_191ac D_191ac (Z_to_bv 64 602777) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_191b0 D_191b0 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_191b4 D_191b4.  (* [comment removed for export] *)
      stw F_191b8 D_191b8 (Z_to_bv 64 471072) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_191bc D_191bc (word_to_le_bytes 8 (Z_to_bv 64 101072)) (Z_to_bv 64 101072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_191c0 D_191c0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_191c4 D_191c4 (0x18ad0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 471088 ->
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
        getr regs' 4 = (Z_to_bv 64 471088) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 84180) ->
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
        G (mkst regs' (0x18c90 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18ad0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_1894c D_1894c (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18950 D_18950 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18954 D_18954 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18958 D_18958 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1895c D_1895c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18960 D_18960 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18964 D_18964 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_18968 D_18968 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a48 D_18a48 (word_to_le_bytes 8 (Z_to_bv 64 101476)) (Z_to_bv 64 101476) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a4c D_18a4c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a50 D_18a50 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a54 D_18a54 (word_to_le_bytes 8 (Z_to_bv 64 84180)) (Z_to_bv 64 84180) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a58 D_18a58 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_18a5c D_18a5c (0x18c64 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18ae0 D_18ae0.  (* [comment removed for export] *)
      sn F_18ae4 D_18ae4.  (* [comment removed for export] *)
      sn F_18ae8 D_18ae8.  (* [comment removed for export] *)
      sv F_18aec D_18aec (argc_w inp).  (* [comment removed for export] *)
      sv F_18af0 D_18af0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_18af4 D_18af4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18af8 D_18af8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18afc D_18afc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18b00 D_18b00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18b04 D_18b04 (sp0).  (* [comment removed for export] *)
      stepret F_18b08 D_18b08 (0x18c90 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_1894c D_1894c (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18950 D_18950 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18954 D_18954 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18958 D_18958 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1895c D_1895c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18960 D_18960 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18964 D_18964 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_18968 D_18968 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a48 D_18a48 (word_to_le_bytes 8 (Z_to_bv 64 101476)) (Z_to_bv 64 101476) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a4c D_18a4c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a50 D_18a50 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a54 D_18a54 (word_to_le_bytes 8 (Z_to_bv 64 84180)) (Z_to_bv 64 84180) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a58 D_18a58 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_18a5c D_18a5c (0x18c64 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18ae0 D_18ae0.  (* [comment removed for export] *)
      sn F_18ae4 D_18ae4.  (* [comment removed for export] *)
      sn F_18ae8 D_18ae8.  (* [comment removed for export] *)
      sv F_18aec D_18aec (argc_w inp).  (* [comment removed for export] *)
      sv F_18af0 D_18af0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_18af4 D_18af4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18af8 D_18af8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18afc D_18afc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18b00 D_18b00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18b04 D_18b04 (sp0).  (* [comment removed for export] *)
      stepret F_18b08 D_18b08 (0x18c90 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 471088 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 84180 ->
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
        getr regs' 1 = (Z_to_bv 64 101396) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 471088) ->
        getr regs' 8 = (Z_to_bv 64 138264) ->
        getr regs' 9 = (Z_to_bv 64 138256) ->
        getr regs' 18 = (Z_to_bv 64 84180) ->
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
        G (mkst regs' (0x147d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101572))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18c90 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_18b0c D_18b0c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_18b10 D_18b10 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b14 D_18b14 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b18 D_18b18 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b1c D_18b1c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b20 D_18b20 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_18b24 D_18b24 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b28 D_18b28 (argc_w inp).  (* [comment removed for export] *)
      sn F_18b2c D_18b2c.  (* [comment removed for export] *)
      stepiv F_18b30 D_18b30 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_18b34 D_18b34 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_18b38 D_18b38 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_18b3c D_18b3c.  (* [comment removed for export] *)
      sv F_18a60 D_18a60 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_18a64 D_18a64 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101572) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a68 D_18a68 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a6c D_18a6c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_18a70 D_18a70.  (* [comment removed for export] *)
      stepret F_18830 D_18830 (0x18bf8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a74 D_18a74.  (* [comment removed for export] *)
      sn F_18a78 D_18a78.  (* [comment removed for export] *)
      ld_step F_18a7c D_18a7c (word_to_le_bytes 8 (Z_to_bv 64 138264)) (Z_to_bv 64 138264) ltac:(rd_img img_21b38_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a80 D_18a80 (word_to_le_bytes 8 (Z_to_bv 64 138256)) (Z_to_bv 64 138256) ltac:(rd_img img_21b40_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18a84 D_18a84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a88 D_18a88 (word_to_le_bytes 8 (Z_to_bv 64 83920)) (Z_to_bv 64 83920) ltac:(rd_img img_21a98_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_18a8c D_18a8c (0x147d0 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_18b0c D_18b0c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_18b10 D_18b10 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b14 D_18b14 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b18 D_18b18 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b1c D_18b1c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18b20 D_18b20 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_18b24 D_18b24 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b28 D_18b28 (argc_w inp).  (* [comment removed for export] *)
      sn F_18b2c D_18b2c.  (* [comment removed for export] *)
      stepiv F_18b30 D_18b30 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_18b34 D_18b34 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_18b38 D_18b38 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_18b3c D_18b3c.  (* [comment removed for export] *)
      sv F_18a60 D_18a60 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_18a64 D_18a64 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101572) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a68 D_18a68 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a6c D_18a6c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_18a70 D_18a70.  (* [comment removed for export] *)
      stepret F_18830 D_18830 (0x18bf8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a74 D_18a74.  (* [comment removed for export] *)
      sn F_18a78 D_18a78.  (* [comment removed for export] *)
      ld_step F_18a7c D_18a7c (word_to_le_bytes 8 (Z_to_bv 64 138264)) (Z_to_bv 64 138264) ltac:(rd_img img_21b38_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a80 D_18a80 (word_to_le_bytes 8 (Z_to_bv 64 138256)) (Z_to_bv 64 138256) ltac:(rd_img img_21b40_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18a84 D_18a84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a88 D_18a88 (word_to_le_bytes 8 (Z_to_bv 64 83920)) (Z_to_bv 64 83920) ltac:(rd_img img_21a98_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_18a8c D_18a8c (0x147d0 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 101396 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 471088 ->
    getr regs 8 = Z_to_bv 64 138264 ->
    getr regs 9 = Z_to_bv 64 138256 ->
    getr regs 18 = Z_to_bv 64 84180 ->
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
        getr regs' 1 = (Z_to_bv 64 101588) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 471088) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 84180) ->
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
        G (mkst regs' (0x148d4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101572))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 101396))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 138264))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 143072) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x147d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101064))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602808))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 101072))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101572))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602200) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602216) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602832) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602840) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 471104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 471080) (word_to_le_bytes 8 (Z_to_bv 64 471104))) (Z_to_bv 64 470888) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 602808) ([Z_to_bv 8 1])) (Z_to_bv 64 470928) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470920) (word_to_le_bytes 4 tid)) (Z_to_bv 64 471040) (word_to_le_bytes 8 (Z_to_bv 64 602864))) (Z_to_bv 64 471008) (word_to_le_bytes 8 (Z_to_bv 64 471008))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470888))) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602776) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602780) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602777) ([Z_to_bv 8 0])) (Z_to_bv 64 471072) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_14734 D_14734 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14738 D_14738 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101396) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1473c D_1473c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138264) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14740 D_14740 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14744 D_14744.  (* [comment removed for export] *)
      sn F_14748 D_14748.  (* [comment removed for export] *)
      lb_step F_1474c D_1474c (Z_to_bv 8 0) ltac:(rd_img img_22d70_1).  (* [comment removed for export] *)
      sn F_14750 D_14750.  (* [comment removed for export] *)
      stepb_tk F_14754 D_14754 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_14760 D_14760.  (* [comment removed for export] *)
      sn F_14764 D_14764.  (* [comment removed for export] *)
      sn F_14768 D_14768.  (* [comment removed for export] *)
      stw F_1476c D_1476c (Z_to_bv 64 143072) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_14770 D_14770.  (* [comment removed for export] *)
      ld_step F_14774 D_14774 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14778 D_14778 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14798 D_14798 (word_to_le_bytes 8 (Z_to_bv 64 101396)) (Z_to_bv 64 101396) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1479c D_1479c (word_to_le_bytes 8 (Z_to_bv 64 138264)) (Z_to_bv 64 138264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147a0 D_147a0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147a4 D_147a4 (0x18c14 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a90 D_18a90.  (* [comment removed for export] *)
      stepb_ft F_18a94 D_18a94 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a98 D_18a98 (word_to_le_bytes 8 (Z_to_bv 64 101572)) (Z_to_bv 64 101572) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a9c D_18a9c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18aa0 D_18aa0 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18aa4 D_18aa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_18aa8 D_18aa8 (0x18cc4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_18b40 D_18b40 (argc_w inp).  (* [comment removed for export] *)
      sv F_18b44 D_18b44 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b48 D_18b48 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_18b4c D_18b4c (0x148d4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_14734 D_14734 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14738 D_14738 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101396) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1473c D_1473c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138264) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14740 D_14740 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14744 D_14744.  (* [comment removed for export] *)
      sn F_14748 D_14748.  (* [comment removed for export] *)
      lb_step F_1474c D_1474c (Z_to_bv 8 0) ltac:(rd_img img_22d70_1).  (* [comment removed for export] *)
      sn F_14750 D_14750.  (* [comment removed for export] *)
      stepb_tk F_14754 D_14754 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_14760 D_14760.  (* [comment removed for export] *)
      sn F_14764 D_14764.  (* [comment removed for export] *)
      sn F_14768 D_14768.  (* [comment removed for export] *)
      stw F_1476c D_1476c (Z_to_bv 64 143072) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_14770 D_14770.  (* [comment removed for export] *)
      ld_step F_14774 D_14774 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14778 D_14778 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14798 D_14798 (word_to_le_bytes 8 (Z_to_bv 64 101396)) (Z_to_bv 64 101396) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1479c D_1479c (word_to_le_bytes 8 (Z_to_bv 64 138264)) (Z_to_bv 64 138264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147a0 D_147a0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147a4 D_147a4 (0x18c14 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a90 D_18a90.  (* [comment removed for export] *)
      stepb_ft F_18a94 D_18a94 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a98 D_18a98 (word_to_le_bytes 8 (Z_to_bv 64 101572)) (Z_to_bv 64 101572) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a9c D_18a9c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18aa0 D_18aa0 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18aa4 D_18aa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_18aa8 D_18aa8 (0x18cc4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_18b40 D_18b40 (argc_w inp).  (* [comment removed for export] *)
      sv F_18b44 D_18b44 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b48 D_18b48 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_18b4c D_18b4c (0x148d4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
