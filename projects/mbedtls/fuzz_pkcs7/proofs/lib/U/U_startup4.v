(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section is over the launch's ProcInput, mmap base, entry point and break with the valid_launch and entry_launch_ok_va premises; new lemma rnd_facts_here; rnd_bounds, rd_rnd, rdn_addr and fin_c6 to fin_c9 written out in plain text from their encoded (CDefT) form; fin_c7 reads the group id from the input; the CDefT name table, recorded LiaOrc tables and using annotations removed). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup_defs U_code_1cc20_1d000 U_code_3b000_3c000 U_code_3c000_3d000 U_code_43000_43c04           .
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.
Local Set Default Proof Using "All".

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section P6.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variable rdraw : EntryDraw.
  Variable Jb : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Lemma rnd_facts_here :
    (bv_unsigned sp0
     <= bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev))%Z
    /\ (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) + 16
        <= bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)))%Z
    /\ (bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn SEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
            (Z_to_bv 64 (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)
                         + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    eapply rnd_facts;
      first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal].
  Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct rnd_facts_here as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    intros J D j n Hjn.
    destruct rnd_facts_here as (A & B & C & D' & E).
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
    rewrite rdn_cmem_data by region_side; apply guard_read.

  Lemma slli_argc : v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN inp Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 381128 ->
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
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 381128 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x3f0a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x3f09c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. dpose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_3b944 D_3b944 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3b948 D_3b948.  (* [comment removed for export] *)
      sv F_3c174 D_3c174 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_3c178 D_3c178 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 258212) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_3c17c D_3c17c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_3c180 D_3c180 ((rnd_w sp0 inp)).  (* [comment removed for export] *)
      sn F_3c184 D_3c184.  (* [comment removed for export] *)
      ld_step F_3c188 D_3c188 (word_to_le_bytes 8 (Z_to_bv 64 512816)) (Z_to_bv 64 512816) ltac:(rd_img img_48590_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_3c18c D_3c18c.  (* [comment removed for export] *)
      sn F_3c190 D_3c190.  (* [comment removed for export] *)
      stepiv F_432f4 D_432f4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; dpose rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_432f8 D_432f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_43408 D_43408.  (* [comment removed for export] *)
      sn F_4340c D_4340c.  (* [comment removed for export] *)
      stepb_ft F_43410 D_43410 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_43414 D_43414.  (* [comment removed for export] *)
      stepb_tk F_43418 D_43418 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_43450 D_43450.  (* [comment removed for export] *)
      stepb_ft F_43454 D_43454 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_43458 D_43458 (guard_lo_bytes rdraw) (Z_to_bv 64 (bytes_le_to_Z (guard_lo_bytes rdraw))) ltac:(RD_RND 0%nat) ltac:(apply guard_lo_val).  (* [comment removed for export] *)
      ld_step F_4345c D_4345c (guard_hi_bytes rdraw) (Z_to_bv 64 (bytes_le_to_Z (guard_hi_bytes rdraw))) ltac:(RD_RND 4%nat) ltac:(apply guard_hi_val).  (* [comment removed for export] *)
      stw F_43460 D_43460 (Z_to_bv 64 512816) (guard_lo rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_43464 D_43464 (Z_to_bv 64 512820) (guard_hi rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_43468 D_43468.  (* [comment removed for export] *)
      sv F_4346c D_4346c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).  (* [comment removed for export] *)
      sn F_43470 D_43470.  (* [comment removed for export] *)
      stepb_tk F_43474 D_43474 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_436b4 D_436b4.  (* [comment removed for export] *)
      stepb_ft F_436b8 D_436b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_436bc D_436bc.  (* [comment removed for export] *)
      stepb_ft F_436c0 D_436c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_436c4 D_436c4 (0x3f8e0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_3c194 D_3c194.  (* [comment removed for export] *)
      sn F_3c1b0 D_3c1b0.  (* [comment removed for export] *)
      ld_step F_3c1b4 D_3c1b4 (word_to_le_bytes 8 (Z_to_bv 64 512816)) (Z_to_bv 64 512816) ltac:(rd_img img_48590_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_3c1b8 D_3c1b8 (Z_to_bv 64 512817) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_3c1bc D_3c1bc (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_3c1c0 D_3c1c0.  (* [comment removed for export] *)
      stw F_3c1c4 D_3c1c4 (Z_to_bv 64 381112) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_3c1c8 D_3c1c8 (word_to_le_bytes 8 (Z_to_bv 64 258212)) (Z_to_bv 64 258212) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3c1cc D_3c1cc (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_3c1d0 D_3c1d0 (0x3f0a4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 381128 ->
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
        getr regs' 1 = Z_to_bv 64 0 ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 381128 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 119372 ->
        getr regs' 11 = (argc_w inp) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 18 = Z_to_bv 64 0 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0x3f264 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x3f0a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. dpose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_3b94c D_3b94c (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3b950 D_3b950 (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_3b954 D_3b954 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_3b958 D_3b958 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3b95c D_3b95c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_3b960 D_3b960 ltac:(pin; first [apply c_eq_refl | cond_compute]).  (* [comment removed for export] *)
      ld_step F_3b964 D_3b964 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_3b968 D_3b968 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3ba48 D_3ba48 (word_to_le_bytes 8 (Z_to_bv 64 258616)) (Z_to_bv 64 258616) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3ba4c D_3ba4c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3ba50 D_3ba50 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3ba54 D_3ba54 (word_to_le_bytes 8 (Z_to_bv 64 119372)) (Z_to_bv 64 119372) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3ba58 D_3ba58 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_3ba5c D_3ba5c (0x3f238 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_3bae0 D_3bae0.  (* [comment removed for export] *)
      sn F_3bae4 D_3bae4.  (* [comment removed for export] *)
      sn F_3bae8 D_3bae8.  (* [comment removed for export] *)
      sv F_3baec D_3baec (argc_w inp).  (* [comment removed for export] *)
      sv F_3baf0 D_3baf0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_3baf4 D_3baf4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3baf8 D_3baf8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3bafc D_3bafc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3bb00 D_3bb00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3bb04 D_3bb04 (sp0).  (* [comment removed for export] *)
      stepret F_3bb08 D_3bb08 (0x3f264 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 381128 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 119372 ->
    getr regs 11 = (argc_w inp) ->
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
        getr regs' 1 = Z_to_bv 64 258536 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 381128 ->
        getr regs' 8 = Z_to_bv 64 295768 ->
        getr regs' 9 = Z_to_bv 64 295760 ->
        getr regs' 18 = Z_to_bv 64 119372 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x1d148 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 258712))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x3f264 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. dpose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_3bb0c D_3bb0c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_3bb10 D_3bb10 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bb14 D_3bb14 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bb18 D_3bb18 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bb1c D_3bb1c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3bb20 D_3bb20 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_3bb24 D_3bb24 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_3bb28 D_3bb28 (argc_w inp).  (* [comment removed for export] *)
      sn F_3bb2c D_3bb2c.  (* [comment removed for export] *)
      stepiv F_3bb30 D_3bb30 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_3bb34 D_3bb34 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_3bb38 D_3bb38 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_3bb3c D_3bb3c.  (* [comment removed for export] *)
      sv F_3ba60 D_3ba60 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_3ba64 D_3ba64 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 258712) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3ba68 D_3ba68 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_3ba6c D_3ba6c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_3ba70 D_3ba70.  (* [comment removed for export] *)
      stepret F_3b830 D_3b830 (0x3f1cc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_3ba74 D_3ba74.  (* [comment removed for export] *)
      sn F_3ba78 D_3ba78.  (* [comment removed for export] *)
      ld_step F_3ba7c D_3ba7c (word_to_le_bytes 8 (Z_to_bv 64 295768)) (Z_to_bv 64 295768) ltac:(rd_img img_48580_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3ba80 D_3ba80 (word_to_le_bytes 8 (Z_to_bv 64 295760)) (Z_to_bv 64 295760) ltac:(rd_img img_48588_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_3ba84 D_3ba84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3ba88 D_3ba88 (word_to_le_bytes 8 (Z_to_bv 64 119112)) (Z_to_bv 64 119112) ltac:(rd_img img_44c08_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_3ba8c D_3ba8c (0x1d148 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 258536 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 381128 ->
    getr regs 8 = Z_to_bv 64 295768 ->
    getr regs 9 = Z_to_bv 64 295760 ->
    getr regs 18 = Z_to_bv 64 119372 ->
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
        getr regs' 1 = Z_to_bv 64 258728 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 381128 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 119372 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x1d24c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 258712))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 258536))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 295768))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 315168) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x1d148 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase entry rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258204))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 512848))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 258212))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 258712))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 512240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512248) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 512872) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 512880) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 381144) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 381120) (word_to_le_bytes 8 (Z_to_bv 64 381144))) (Z_to_bv 64 380928) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 512848) ([Z_to_bv 8 1])) (Z_to_bv 64 380968) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 380960) (word_to_le_bytes 4 tid)) (Z_to_bv 64 381080) (word_to_le_bytes 8 (Z_to_bv 64 512904))) (Z_to_bv 64 381048) (word_to_le_bytes 8 (Z_to_bv 64 381048))) (Z_to_bv 64 380936) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380944) (word_to_le_bytes 8 (Z_to_bv 64 380928))) (Z_to_bv 64 380952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 512816) (word_to_le_bytes 4 (guard_lo rdraw))) (Z_to_bv 64 512820) (word_to_le_bytes 4 (guard_hi rdraw))) (Z_to_bv 64 512817) ([Z_to_bv 8 0])) (Z_to_bv 64 381112) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. dpose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_1cc68 D_1cc68 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_1cc6c D_1cc6c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 258536) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1cc70 D_1cc70 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 295768) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_1cc74 D_1cc74 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_1cc78 D_1cc78.  (* [comment removed for export] *)
      sn F_1cc7c D_1cc7c.  (* [comment removed for export] *)
      lb_step F_1cc80 D_1cc80 (Z_to_bv 8 0) ltac:(rd_img img_497d0_1).  (* [comment removed for export] *)
      sn F_1cc84 D_1cc84.  (* [comment removed for export] *)
      stepb_tk F_1cc88 D_1cc88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1cc94 D_1cc94.  (* [comment removed for export] *)
      sn F_1cc98 D_1cc98.  (* [comment removed for export] *)
      sn F_1cc9c D_1cc9c.  (* [comment removed for export] *)
      stw F_1cca0 D_1cca0 (Z_to_bv 64 315168) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_1cca4 D_1cca4.  (* [comment removed for export] *)
      ld_step F_1cca8 D_1cca8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_48530_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_1ccac D_1ccac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_1cccc D_1cccc (word_to_le_bytes 8 (Z_to_bv 64 258536)) (Z_to_bv 64 258536) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1ccd0 D_1ccd0 (word_to_le_bytes 8 (Z_to_bv 64 295768)) (Z_to_bv 64 295768) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1ccd4 D_1ccd4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_1ccd8 D_1ccd8 (0x3f1e8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_3ba90 D_3ba90.  (* [comment removed for export] *)
      stepb_ft F_3ba94 D_3ba94 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_3ba98 D_3ba98 (word_to_le_bytes 8 (Z_to_bv 64 258712)) (Z_to_bv 64 258712) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3ba9c D_3ba9c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_3baa0 D_3baa0 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3baa4 D_3baa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_3baa8 D_3baa8 (0x3f298 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_3bb40 D_3bb40 (argc_w inp).  (* [comment removed for export] *)
      sv F_3bb44 D_3bb44 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_3bb48 D_3bb48 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_3bb4c D_3bb4c (0x1d24c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
