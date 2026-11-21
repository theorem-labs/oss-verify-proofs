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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac ArgvEnv RefLayout DrawDefs. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7Img S7StartupDefs S7_code_146e4_15000 S7_code_18000_19000 S7_code_19000_1a000 S7_code_20000_20a30.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
(* [comment removed for export] *)

Abbreviation SEGS := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs.

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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 470976 ->
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
        getr regs' 4 = (Z_to_bv 64 470976) ->
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
        G (mkst regs' (0x18a68 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18a60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_188dc D_188dc (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_188e0 D_188e0.  (* [comment removed for export] *)
      sv F_19100 D_19100 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_19104 D_19104 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100968) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_19108 D_19108 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_1910c D_1910c ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_19110 D_19110.  (* [comment removed for export] *)
      ld_step F_19114 D_19114 (word_to_le_bytes 8 (Z_to_bv 64 602664)) (Z_to_bv 64 602664) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19118 D_19118.  (* [comment removed for export] *)
      sn F_1911c D_1911c.  (* [comment removed for export] *)
      stepiv F_20054 D_20054 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_20058 D_20058 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20168 D_20168.  (* [comment removed for export] *)
      sn F_2016c D_2016c.  (* [comment removed for export] *)
      stepb_ft F_20170 D_20170 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20174 D_20174.  (* [comment removed for export] *)
      stepb_tk F_20178 D_20178 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201b0 D_201b0.  (* [comment removed for export] *)
      stepb_ft F_201b4 D_201b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_201b8 D_201b8 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_201bc D_201bc (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_201c0 D_201c0 (Z_to_bv 64 602664) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_201c4 D_201c4 (Z_to_bv 64 602668) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_201c8 D_201c8.  (* [comment removed for export] *)
      sv F_201cc D_201cc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_201d0 D_201d0.  (* [comment removed for export] *)
      stepb_tk F_201d4 D_201d4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20414 D_20414.  (* [comment removed for export] *)
      stepb_ft F_20418 D_20418 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2041c D_2041c.  (* [comment removed for export] *)
      stepb_ft F_20420 D_20420 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_20424 D_20424 (0x19298 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19120 D_19120.  (* [comment removed for export] *)
      sn F_1913c D_1913c.  (* [comment removed for export] *)
      ld_step F_19140 D_19140 (word_to_le_bytes 8 (Z_to_bv 64 602664)) (Z_to_bv 64 602664) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_19144 D_19144 (Z_to_bv 64 602665) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_19148 D_19148 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_1914c D_1914c.  (* [comment removed for export] *)
      stw F_19150 D_19150 (Z_to_bv 64 470960) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_19154 D_19154 (word_to_le_bytes 8 (Z_to_bv 64 100968)) (Z_to_bv 64 100968) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19158 D_19158 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1915c D_1915c (0x18a68 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_188dc D_188dc (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_188e0 D_188e0.  (* [comment removed for export] *)
      sv F_19100 D_19100 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_19104 D_19104 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100968) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_19108 D_19108 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_1910c D_1910c ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_19110 D_19110.  (* [comment removed for export] *)
      ld_step F_19114 D_19114 (word_to_le_bytes 8 (Z_to_bv 64 602664)) (Z_to_bv 64 602664) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_19118 D_19118.  (* [comment removed for export] *)
      sn F_1911c D_1911c.  (* [comment removed for export] *)
      stepiv F_20054 D_20054 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_20058 D_20058 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20168 D_20168.  (* [comment removed for export] *)
      sn F_2016c D_2016c.  (* [comment removed for export] *)
      stepb_ft F_20170 D_20170 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20174 D_20174.  (* [comment removed for export] *)
      stepb_tk F_20178 D_20178 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_201b0 D_201b0.  (* [comment removed for export] *)
      stepb_ft F_201b4 D_201b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_201b8 D_201b8 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      ld_step F_201bc D_201bc (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).  (* [comment removed for export] *)
      stw F_201c0 D_201c0 (Z_to_bv 64 602664) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_201c4 D_201c4 (Z_to_bv 64 602668) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_201c8 D_201c8.  (* [comment removed for export] *)
      sv F_201cc D_201cc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_201d0 D_201d0.  (* [comment removed for export] *)
      stepb_tk F_201d4 D_201d4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20414 D_20414.  (* [comment removed for export] *)
      stepb_ft F_20418 D_20418 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_2041c D_2041c.  (* [comment removed for export] *)
      stepb_ft F_20420 D_20420 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_20424 D_20424 (0x19298 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_19120 D_19120.  (* [comment removed for export] *)
      sn F_1913c D_1913c.  (* [comment removed for export] *)
      ld_step F_19140 D_19140 (word_to_le_bytes 8 (Z_to_bv 64 602664)) (Z_to_bv 64 602664) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_19144 D_19144 (Z_to_bv 64 602665) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_19148 D_19148 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).  (* [comment removed for export] *)
      sn F_1914c D_1914c.  (* [comment removed for export] *)
      stw F_19150 D_19150 (Z_to_bv 64 470960) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_19154 D_19154 (word_to_le_bytes 8 (Z_to_bv 64 100968)) (Z_to_bv 64 100968) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_19158 D_19158 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1915c D_1915c (0x18a68 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470976 ->
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
        getr regs' 4 = (Z_to_bv 64 470976) ->
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
        G (mkst regs' (0x18c28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18a68 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_188e4 D_188e4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_188e8 D_188e8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_188ec D_188ec ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_188f0 D_188f0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_188f4 D_188f4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_188f8 D_188f8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_188fc D_188fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_18900 D_18900 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_189e0 D_189e0 (word_to_le_bytes 8 (Z_to_bv 64 101372)) (Z_to_bv 64 101372) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_189e4 D_189e4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_189e8 D_189e8 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_189ec D_189ec (word_to_le_bytes 8 (Z_to_bv 64 84172)) (Z_to_bv 64 84172) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_189f0 D_189f0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_189f4 D_189f4 (0x18bfc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a78 D_18a78.  (* [comment removed for export] *)
      sn F_18a7c D_18a7c.  (* [comment removed for export] *)
      sn F_18a80 D_18a80.  (* [comment removed for export] *)
      sv F_18a84 D_18a84 (argc_w inp).  (* [comment removed for export] *)
      sv F_18a88 D_18a88 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_18a8c D_18a8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a90 D_18a90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a94 D_18a94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a98 D_18a98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a9c D_18a9c (sp0).  (* [comment removed for export] *)
      stepret F_18aa0 D_18aa0 (0x18c28 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_188e4 D_188e4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_188e8 D_188e8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_188ec D_188ec ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_188f0 D_188f0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_188f4 D_188f4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_188f8 D_188f8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_188fc D_188fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_18900 D_18900 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_189e0 D_189e0 (word_to_le_bytes 8 (Z_to_bv 64 101372)) (Z_to_bv 64 101372) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_189e4 D_189e4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_189e8 D_189e8 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_189ec D_189ec (word_to_le_bytes 8 (Z_to_bv 64 84172)) (Z_to_bv 64 84172) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_189f0 D_189f0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_189f4 D_189f4 (0x18bfc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a78 D_18a78.  (* [comment removed for export] *)
      sn F_18a7c D_18a7c.  (* [comment removed for export] *)
      sn F_18a80 D_18a80.  (* [comment removed for export] *)
      sv F_18a84 D_18a84 (argc_w inp).  (* [comment removed for export] *)
      sv F_18a88 D_18a88 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_18a8c D_18a8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a90 D_18a90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a94 D_18a94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a98 D_18a98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a9c D_18a9c (sp0).  (* [comment removed for export] *)
      stepret F_18aa0 D_18aa0 (0x18c28 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
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
    getr regs 4 = Z_to_bv 64 470976 ->
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
        getr regs' 1 = (Z_to_bv 64 101292) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 470976) ->
        getr regs' 8 = (Z_to_bv 64 138160) ->
        getr regs' 9 = (Z_to_bv 64 138152) ->
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
        G (mkst regs' (0x147c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101468))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18c28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_18aa4 D_18aa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_18aa8 D_18aa8 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18aac D_18aac (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18ab0 D_18ab0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18ab4 D_18ab4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18ab8 D_18ab8 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_18abc D_18abc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18ac0 D_18ac0 (argc_w inp).  (* [comment removed for export] *)
      sn F_18ac4 D_18ac4.  (* [comment removed for export] *)
      stepiv F_18ac8 D_18ac8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_18acc D_18acc (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_18ad0 D_18ad0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_18ad4 D_18ad4.  (* [comment removed for export] *)
      sv F_189f8 D_189f8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_189fc D_189fc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101468) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a00 D_18a00 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a04 D_18a04 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_18a08 D_18a08.  (* [comment removed for export] *)
      stepret F_187c8 D_187c8 (0x18b90 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a0c D_18a0c.  (* [comment removed for export] *)
      sn F_18a10 D_18a10.  (* [comment removed for export] *)
      ld_step F_18a14 D_18a14 (word_to_le_bytes 8 (Z_to_bv 64 138160)) (Z_to_bv 64 138160) ltac:(rd_img img_21ad0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a18 D_18a18 (word_to_le_bytes 8 (Z_to_bv 64 138152)) (Z_to_bv 64 138152) ltac:(rd_img img_21ad8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18a1c D_18a1c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a20 D_18a20 (word_to_le_bytes 8 (Z_to_bv 64 83912)) (Z_to_bv 64 83912) ltac:(rd_img img_21a30_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_18a24 D_18a24 (0x147c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_18aa4 D_18aa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_18aa8 D_18aa8 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18aac D_18aac (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18ab0 D_18ab0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18ab4 D_18ab4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18ab8 D_18ab8 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_18abc D_18abc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18ac0 D_18ac0 (argc_w inp).  (* [comment removed for export] *)
      sn F_18ac4 D_18ac4.  (* [comment removed for export] *)
      stepiv F_18ac8 D_18ac8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_18acc D_18acc (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_18ad0 D_18ad0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_18ad4 D_18ad4.  (* [comment removed for export] *)
      sv F_189f8 D_189f8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_189fc D_189fc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101468) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a00 D_18a00 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_18a04 D_18a04 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_18a08 D_18a08.  (* [comment removed for export] *)
      stepret F_187c8 D_187c8 (0x18b90 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a0c D_18a0c.  (* [comment removed for export] *)
      sn F_18a10 D_18a10.  (* [comment removed for export] *)
      ld_step F_18a14 D_18a14 (word_to_le_bytes 8 (Z_to_bv 64 138160)) (Z_to_bv 64 138160) ltac:(rd_img img_21ad0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a18 D_18a18 (word_to_le_bytes 8 (Z_to_bv 64 138152)) (Z_to_bv 64 138152) ltac:(rd_img img_21ad8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_18a1c D_18a1c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a20 D_18a20 (word_to_le_bytes 8 (Z_to_bv 64 83912)) (Z_to_bv 64 83912) ltac:(rd_img img_21a30_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_18a24 D_18a24 (0x147c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 101292 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470976 ->
    getr regs 8 = Z_to_bv 64 138160 ->
    getr regs 9 = Z_to_bv 64 138152 ->
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
        getr regs' 1 = (Z_to_bv 64 101484) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 470976) ->
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
        G (mkst regs' (0x148cc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101468))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 101292))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 138160))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 142960) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x147c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100960))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100968))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101468))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602088) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602104) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602096) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470968) (word_to_le_bytes 8 (Z_to_bv 64 470992))) (Z_to_bv 64 470776) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 602696) ([Z_to_bv 8 1])) (Z_to_bv 64 470816) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470808) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 602752))) (Z_to_bv 64 470896) (word_to_le_bytes 8 (Z_to_bv 64 470896))) (Z_to_bv 64 470784) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470792) (word_to_le_bytes 8 (Z_to_bv 64 470776))) (Z_to_bv 64 470800) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602665) ([Z_to_bv 8 0])) (Z_to_bv 64 470960) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* a worker port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_1472c D_1472c (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14730 D_14730 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101292) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14734 D_14734 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138160) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14738 D_14738 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_1473c D_1473c.  (* [comment removed for export] *)
      sn F_14740 D_14740.  (* [comment removed for export] *)
      lb_step F_14744 D_14744 (Z_to_bv 8 0) ltac:(rd_img img_22d10_1).  (* [comment removed for export] *)
      sn F_14748 D_14748.  (* [comment removed for export] *)
      stepb_tk F_1474c D_1474c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_14758 D_14758.  (* [comment removed for export] *)
      sn F_1475c D_1475c.  (* [comment removed for export] *)
      sn F_14760 D_14760.  (* [comment removed for export] *)
      stw F_14764 D_14764 (Z_to_bv 64 142960) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_14768 D_14768.  (* [comment removed for export] *)
      ld_step F_1476c D_1476c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21a78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14770 D_14770 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14790 D_14790 (word_to_le_bytes 8 (Z_to_bv 64 101292)) (Z_to_bv 64 101292) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14794 D_14794 (word_to_le_bytes 8 (Z_to_bv 64 138160)) (Z_to_bv 64 138160) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_14798 D_14798 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_1479c D_1479c (0x18bac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a28 D_18a28.  (* [comment removed for export] *)
      stepb_ft F_18a2c D_18a2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a30 D_18a30 (word_to_le_bytes 8 (Z_to_bv 64 101468)) (Z_to_bv 64 101468) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a34 D_18a34 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a38 D_18a38 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a3c D_18a3c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_18a40 D_18a40 (0x18c5c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_18ad8 D_18ad8 (argc_w inp).  (* [comment removed for export] *)
      sv F_18adc D_18adc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18ae0 D_18ae0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_18ae4 D_18ae4 (0x148cc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_1472c D_1472c (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_14730 D_14730 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101292) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_14734 D_14734 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138160) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_14738 D_14738 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_1473c D_1473c.  (* [comment removed for export] *)
      sn F_14740 D_14740.  (* [comment removed for export] *)
      lb_step F_14744 D_14744 (Z_to_bv 8 0) ltac:(rd_img img_22d10_1).  (* [comment removed for export] *)
      sn F_14748 D_14748.  (* [comment removed for export] *)
      stepb_tk F_1474c D_1474c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_14758 D_14758.  (* [comment removed for export] *)
      sn F_1475c D_1475c.  (* [comment removed for export] *)
      sn F_14760 D_14760.  (* [comment removed for export] *)
      stw F_14764 D_14764 (Z_to_bv 64 142960) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_14768 D_14768.  (* [comment removed for export] *)
      ld_step F_1476c D_1476c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21a78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_14770 D_14770 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_14790 D_14790 (word_to_le_bytes 8 (Z_to_bv 64 101292)) (Z_to_bv 64 101292) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_14794 D_14794 (word_to_le_bytes 8 (Z_to_bv 64 138160)) (Z_to_bv 64 138160) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_14798 D_14798 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_1479c D_1479c (0x18bac : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_18a28 D_18a28.  (* [comment removed for export] *)
      stepb_ft F_18a2c D_18a2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_18a30 D_18a30 (word_to_le_bytes 8 (Z_to_bv 64 101468)) (Z_to_bv 64 101468) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a34 D_18a34 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_18a38 D_18a38 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_18a3c D_18a3c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_18a40 D_18a40 (0x18c5c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_18ad8 D_18ad8 (argc_w inp).  (* [comment removed for export] *)
      sv F_18adc D_18adc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_18ae0 D_18ae0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_18ae4 D_18ae4 (0x148cc : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
