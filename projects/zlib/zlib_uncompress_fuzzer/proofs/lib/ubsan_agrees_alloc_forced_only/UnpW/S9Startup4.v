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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac ArgvEnv RefLayout DrawDefs. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S9Img S9StartupDefs S9_code_1470c_15000 S9_code_18000_19000 S9_code_19000_1a000 S9_code_20000_20a74.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
(* [comment removed for export] *)

Abbreviation SEGS := SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := SrcO_zlib_zlib_uncompress_fuzzer_repro.M.phdrs.

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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 470960 ->
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
        getr regs' 4 = (Z_to_bv 64 470960) ->
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
        G (mkst regs' (0x18a4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18a44 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_18920 D_18920 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_18924 D_18924.  (* [comment removed for export] *)
      sv F_19144 D_19144 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_19148 D_19148 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100940) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1914c D_1914c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_19150 D_19150 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_19154 D_19154.  (* [comment removed for export] *)
      ld_step F_19158 D_19158 (word_to_le_bytes 8 (Z_to_bv 64 602648)) (Z_to_bv 64 602648) ltac:(rd_img img_21b28_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1915c D_1915c.  (* [comment removed for export] *)
      sn F_19160 D_19160.  (* [comment removed for export] *)
      stepiv F_20098 D_20098 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_2009c D_2009c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201ac D_201ac.  (* [comment removed for export] *)
      sn F_201b0 D_201b0.  (* [comment removed for export] *)
      stepb_ft F_201b4 D_201b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201b8 D_201b8.  (* [comment removed for export] *)
      stepb_tk F_201bc D_201bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201f4 D_201f4.  (* [comment removed for export] *)
      stepb_ft F_201f8 D_201f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_201fc D_201fc (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_20200 D_20200 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_20204 D_20204 (Z_to_bv 64 602648) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_20208 D_20208 (Z_to_bv 64 602652) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2020c D_2020c.  (* [comment removed for export] *)
      sv F_20210 D_20210 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_20214 D_20214.  (* [comment removed for export] *)
      stepb_tk F_20218 D_20218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20458 D_20458.  (* [comment removed for export] *)
      stepb_ft F_2045c D_2045c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20460 D_20460.  (* [comment removed for export] *)
      stepb_ft F_20464 D_20464 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_20468 D_20468 (0x1927c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19164 D_19164.  (* [comment removed for export] *)
      sn F_19180 D_19180.  (* [comment removed for export] *)
      ld_step F_19184 D_19184 (word_to_le_bytes 8 (Z_to_bv 64 602648)) (Z_to_bv 64 602648) ltac:(rd_img img_21b28_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_19188 D_19188 (Z_to_bv 64 602649) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1918c D_1918c (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_19190 D_19190.  (* [comment removed for export] *)
      stw F_19194 D_19194 (Z_to_bv 64 470944) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_19198 D_19198 (word_to_le_bytes 8 (Z_to_bv 64 100940)) (Z_to_bv 64 100940) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1919c D_1919c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_191a0 D_191a0 (0x18a4c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_18920 D_18920 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_18924 D_18924.  (* [comment removed for export] *)
      sv F_19144 D_19144 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_19148 D_19148 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100940) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1914c D_1914c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_19150 D_19150 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_19154 D_19154.  (* [comment removed for export] *)
      ld_step F_19158 D_19158 (word_to_le_bytes 8 (Z_to_bv 64 602648)) (Z_to_bv 64 602648) ltac:(rd_img img_21b28_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1915c D_1915c.  (* [comment removed for export] *)
      sn F_19160 D_19160.  (* [comment removed for export] *)
      stepiv F_20098 D_20098 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_2009c D_2009c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201ac D_201ac.  (* [comment removed for export] *)
      sn F_201b0 D_201b0.  (* [comment removed for export] *)
      stepb_ft F_201b4 D_201b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201b8 D_201b8.  (* [comment removed for export] *)
      stepb_tk F_201bc D_201bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201f4 D_201f4.  (* [comment removed for export] *)
      stepb_ft F_201f8 D_201f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_201fc D_201fc (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_20200 D_20200 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_20204 D_20204 (Z_to_bv 64 602648) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_20208 D_20208 (Z_to_bv 64 602652) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2020c D_2020c.  (* [comment removed for export] *)
      sv F_20210 D_20210 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_20214 D_20214.  (* [comment removed for export] *)
      stepb_tk F_20218 D_20218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20458 D_20458.  (* [comment removed for export] *)
      stepb_ft F_2045c D_2045c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20460 D_20460.  (* [comment removed for export] *)
      stepb_ft F_20464 D_20464 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_20468 D_20468 (0x1927c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19164 D_19164.  (* [comment removed for export] *)
      sn F_19180 D_19180.  (* [comment removed for export] *)
      ld_step F_19184 D_19184 (word_to_le_bytes 8 (Z_to_bv 64 602648)) (Z_to_bv 64 602648) ltac:(rd_img img_21b28_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_19188 D_19188 (Z_to_bv 64 602649) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1918c D_1918c (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_19190 D_19190.  (* [comment removed for export] *)
      stw F_19194 D_19194 (Z_to_bv 64 470944) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_19198 D_19198 (word_to_le_bytes 8 (Z_to_bv 64 100940)) (Z_to_bv 64 100940) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1919c D_1919c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_191a0 D_191a0 (0x18a4c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470960 ->
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
        getr regs' 4 = (Z_to_bv 64 470960) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 84172) ->
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
        G (mkst regs' (0x18c0c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18a4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_18928 D_18928 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1892c D_1892c (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18930 D_18930 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18934 D_18934 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18938 D_18938 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_1893c D_1893c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18940 D_18940 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_18944 D_18944 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a24 D_18a24 (word_to_le_bytes 8 (Z_to_bv 64 101344)) (Z_to_bv 64 101344) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a28 D_18a28 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a2c D_18a2c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a30 D_18a30 (word_to_le_bytes 8 (Z_to_bv 64 84172)) (Z_to_bv 64 84172) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a34 D_18a34 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_18a38 D_18a38 (0x18be0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18abc D_18abc.  (* [comment removed for export] *)
      sn F_18ac0 D_18ac0.  (* [comment removed for export] *)
      sn F_18ac4 D_18ac4.  (* [comment removed for export] *)
      sv F_18ac8 D_18ac8 (argc_w inp).  (* [comment removed for export] *)
      sv F_18acc D_18acc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_18ad0 D_18ad0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18ad4 D_18ad4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18ad8 D_18ad8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18adc D_18adc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18ae0 D_18ae0 (sp0).  (* [comment removed for export] *)
      stepret F_18ae4 D_18ae4 (0x18c0c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_18928 D_18928 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1892c D_1892c (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18930 D_18930 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18934 D_18934 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18938 D_18938 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_1893c D_1893c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_18940 D_18940 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_18944 D_18944 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a24 D_18a24 (word_to_le_bytes 8 (Z_to_bv 64 101344)) (Z_to_bv 64 101344) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a28 D_18a28 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a2c D_18a2c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a30 D_18a30 (word_to_le_bytes 8 (Z_to_bv 64 84172)) (Z_to_bv 64 84172) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a34 D_18a34 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_18a38 D_18a38 (0x18be0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18abc D_18abc.  (* [comment removed for export] *)
      sn F_18ac0 D_18ac0.  (* [comment removed for export] *)
      sn F_18ac4 D_18ac4.  (* [comment removed for export] *)
      sv F_18ac8 D_18ac8 (argc_w inp).  (* [comment removed for export] *)
      sv F_18acc D_18acc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_18ad0 D_18ad0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18ad4 D_18ad4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18ad8 D_18ad8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18adc D_18adc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18ae0 D_18ae0 (sp0).  (* [comment removed for export] *)
      stepret F_18ae4 D_18ae4 (0x18c0c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
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
    getr regs 4 = Z_to_bv 64 470960 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 84172 ->
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
        getr regs' 1 = (Z_to_bv 64 101264) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 470960) ->
        getr regs' 8 = (Z_to_bv 64 138136) ->
        getr regs' 9 = (Z_to_bv 64 138128) ->
        getr regs' 18 = (Z_to_bv 64 84172) ->
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
        G (mkst regs' (0x147c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101440))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18c0c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_18ae8 D_18ae8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_18aec D_18aec (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18af0 D_18af0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18af4 D_18af4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18af8 D_18af8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18afc D_18afc (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_18b00 D_18b00 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b04 D_18b04 (argc_w inp).  (* [comment removed for export] *)
      sn F_18b08 D_18b08.  (* [comment removed for export] *)
      stepiv F_18b0c D_18b0c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_18b10 D_18b10 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_18b14 D_18b14 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_18b18 D_18b18.  (* [comment removed for export] *)
      sv F_18a3c D_18a3c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_18a40 D_18a40 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101440) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a44 D_18a44 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a48 D_18a48 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_18a4c D_18a4c.  (* [comment removed for export] *)
      stepret F_1880c D_1880c (0x18b74 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a50 D_18a50.  (* [comment removed for export] *)
      sn F_18a54 D_18a54.  (* [comment removed for export] *)
      ld_step F_18a58 D_18a58 (word_to_le_bytes 8 (Z_to_bv 64 138136)) (Z_to_bv 64 138136) ltac:(rd_img img_21b18_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a5c D_18a5c (word_to_le_bytes 8 (Z_to_bv 64 138128)) (Z_to_bv 64 138128) ltac:(rd_img img_21b20_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18a60 D_18a60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a64 D_18a64 (word_to_le_bytes 8 (Z_to_bv 64 83912)) (Z_to_bv 64 83912) ltac:(rd_img img_21a78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_18a68 D_18a68 (0x147c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_18ae8 D_18ae8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_18aec D_18aec (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18af0 D_18af0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18af4 D_18af4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18af8 D_18af8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18afc D_18afc (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_18b00 D_18b00 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b04 D_18b04 (argc_w inp).  (* [comment removed for export] *)
      sn F_18b08 D_18b08.  (* [comment removed for export] *)
      stepiv F_18b0c D_18b0c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_18b10 D_18b10 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_18b14 D_18b14 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_18b18 D_18b18.  (* [comment removed for export] *)
      sv F_18a3c D_18a3c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_18a40 D_18a40 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101440) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a44 D_18a44 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a48 D_18a48 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_18a4c D_18a4c.  (* [comment removed for export] *)
      stepret F_1880c D_1880c (0x18b74 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a50 D_18a50.  (* [comment removed for export] *)
      sn F_18a54 D_18a54.  (* [comment removed for export] *)
      ld_step F_18a58 D_18a58 (word_to_le_bytes 8 (Z_to_bv 64 138136)) (Z_to_bv 64 138136) ltac:(rd_img img_21b18_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a5c D_18a5c (word_to_le_bytes 8 (Z_to_bv 64 138128)) (Z_to_bv 64 138128) ltac:(rd_img img_21b20_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18a60 D_18a60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a64 D_18a64 (word_to_le_bytes 8 (Z_to_bv 64 83912)) (Z_to_bv 64 83912) ltac:(rd_img img_21a78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_18a68 D_18a68 (0x147c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 101264 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470960 ->
    getr regs 8 = Z_to_bv 64 138136 ->
    getr regs 9 = Z_to_bv 64 138128 ->
    getr regs 18 = Z_to_bv 64 84172 ->
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
        getr regs' 1 = (Z_to_bv 64 101456) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 470960) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 84172) ->
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
        G (mkst regs' (0x148cc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101440))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 101264))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 138136))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 142944) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x147c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100932))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602680))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100940))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101440))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602080) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602704) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470952) (word_to_le_bytes 8 (Z_to_bv 64 470976))) (Z_to_bv 64 470760) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 602680) ([Z_to_bv 8 1])) (Z_to_bv 64 470800) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470792) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470912) (word_to_le_bytes 8 (Z_to_bv 64 602736))) (Z_to_bv 64 470880) (word_to_le_bytes 8 (Z_to_bv 64 470880))) (Z_to_bv 64 470768) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470760))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602648) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602652) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602649) ([Z_to_bv 8 0])) (Z_to_bv 64 470944) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_14754 D_14754 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14758 D_14758 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101264) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1475c D_1475c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138136) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14760 D_14760 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14764 D_14764.  (* [comment removed for export] *)
      sn F_14768 D_14768.  (* [comment removed for export] *)
      lb_step F_1476c D_1476c (Z_to_bv 8 0) ltac:(rd_img img_22d50_1).  (* [comment removed for export] *)
      sn F_14770 D_14770.  (* [comment removed for export] *)
      stepb_tk F_14774 D_14774 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_14780 D_14780.  (* [comment removed for export] *)
      sn F_14784 D_14784.  (* [comment removed for export] *)
      sn F_14788 D_14788.  (* [comment removed for export] *)
      stw F_1478c D_1478c (Z_to_bv 64 142944) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_14790 D_14790.  (* [comment removed for export] *)
      ld_step F_14794 D_14794 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21ac0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14798 D_14798 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_147b8 D_147b8 (word_to_le_bytes 8 (Z_to_bv 64 101264)) (Z_to_bv 64 101264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_147bc D_147bc (word_to_le_bytes 8 (Z_to_bv 64 138136)) (Z_to_bv 64 138136) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147c0 D_147c0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147c4 D_147c4 (0x18b90 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a6c D_18a6c.  (* [comment removed for export] *)
      stepb_ft F_18a70 D_18a70 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a74 D_18a74 (word_to_le_bytes 8 (Z_to_bv 64 101440)) (Z_to_bv 64 101440) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a78 D_18a78 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a7c D_18a7c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a80 D_18a80 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_18a84 D_18a84 (0x18c40 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_18b1c D_18b1c (argc_w inp).  (* [comment removed for export] *)
      sv F_18b20 D_18b20 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b24 D_18b24 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_18b28 D_18b28 (0x148cc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_14754 D_14754 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14758 D_14758 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101264) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1475c D_1475c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138136) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14760 D_14760 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_14764 D_14764.  (* [comment removed for export] *)
      sn F_14768 D_14768.  (* [comment removed for export] *)
      lb_step F_1476c D_1476c (Z_to_bv 8 0) ltac:(rd_img img_22d50_1).  (* [comment removed for export] *)
      sn F_14770 D_14770.  (* [comment removed for export] *)
      stepb_tk F_14774 D_14774 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_14780 D_14780.  (* [comment removed for export] *)
      sn F_14784 D_14784.  (* [comment removed for export] *)
      sn F_14788 D_14788.  (* [comment removed for export] *)
      stw F_1478c D_1478c (Z_to_bv 64 142944) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_14790 D_14790.  (* [comment removed for export] *)
      ld_step F_14794 D_14794 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21ac0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14798 D_14798 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_147b8 D_147b8 (word_to_le_bytes 8 (Z_to_bv 64 101264)) (Z_to_bv 64 101264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_147bc D_147bc (word_to_le_bytes 8 (Z_to_bv 64 138136)) (Z_to_bv 64 138136) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_147c0 D_147c0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_147c4 D_147c4 (0x18b90 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a6c D_18a6c.  (* [comment removed for export] *)
      stepb_ft F_18a70 D_18a70 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a74 D_18a74 (word_to_le_bytes 8 (Z_to_bv 64 101440)) (Z_to_bv 64 101440) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a78 D_18a78 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a7c D_18a7c (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a80 D_18a80 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_18a84 D_18a84 (0x18c40 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_18b1c D_18b1c (argc_w inp).  (* [comment removed for export] *)
      sv F_18b20 D_18b20 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18b24 D_18b24 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_18b28 D_18b28 (0x148cc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
