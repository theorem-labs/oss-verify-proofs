(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "eval"; "SVar"; "obj_range"; "valuation"; "soff"; "SAlu"; "rl"; "rw"; "rm"; "smatch"; "sstate"; "DList"; "cell"; "enc_bytes"; "image_byte"; "mkObj"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "rd"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "of_nat"; "lt"; "pow"; "sub"; "modulo"; "opp"; "to_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "length"; "app"; "list"; "nat"; "nil"; "option"; "None"; "bool"; "Some"; "true"; "false"; "@Corelib.Lists.ListDef"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "obj_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs.Strs"; "strs_tail"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "find_segment"; "wview"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "rand_bytes"; "pad_len"; "tab"; "region"; "str_off"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "STK_FREE"; "aux_base"; "env_base"; "segs_top"; "sll3"; "O_rand"; "O_str0"; "Jinit"; "data_ok_b"; "ms0"; "rnd0"; "rnd1"; "@Stdlib.PArith.BinPos.Pos"; "le"; "succ"; "@Corelib.Init.Nat"; "add"; "mul"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.StackLayout"; "flatten_strings"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "rho_set_rw"; "state_has_rl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs"; "O_strs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition O_strs (nv nl : positive) : sobj := ltac2:(tb__ "0|0|
S17S9P4A1S7Z0A1S9Vnv;A1S3bS14A1S13Vnl;A1A5").

Section Strs.
Variable segs : list Segment.
Variable pc0 : N.
Variable ph : PhdrInfo.
Variable data_lo data_hi : Z.
Hypothesis Hdata : ltac2:(tb__ "0|0|
S0S3eS5aVsegs;Vdata_lo;Vdata_hi;A3S40A3").
Hypothesis Hdata_hi : data_hi <= 2 ^ 40.
Hypothesis Htop : segs_top segs <= 2 ^ 40.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hinp : valid_input_either inp.

Let argv := in_argv inp.
Let envp := in_envp inp.
Let uid := in_uid inp.
Let hwcap := in_hwcap inp.
Let ARGC := Z.of_nat (length argv).
Let ENVC := Z.of_nat (length envp).
Let STR := Z.of_nat (str_off argv envp).
Let RND := Z.of_nat (rand_off argv envp).
Let LEN := Z.of_nat (img_len argv envp).
Let argv0 : list byte := nth 0 argv [].
Let ms0 : ltac2:(tb__ "0|0|
S48") := ltac2:(tb__ "0|0|
S5bVsegs;Vpc0;Vph;Vsp;Vdraw;Vinp;A6").
Let JI : ltac2:(tb__ "0|0|
SbOFrho;") := ltac2:(tb__ "0|0|
S59Vsegs;Vpc0;Vph;Vsp;Vdraw;Vinp;A6").

Definition strs_tail : list byte := ltac2:(tb__ "0|2|
S38S32Q8M0A1M1S65Vargv;A1S38G1S65Venvp;A1S38G1S43G1S33G0Z0A2S4eVargv;Venvp;A2A3S4dVdraw;A1A3A3A3").

Lemma region_tail : ltac2:(tb__ "0|0|
S50Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;S51Vargv;Venvp;A2S45A9").
Proof using .
  exists (hdr_bytes sp argv envp ++ env_bytes sp argv envp ++ auxv ph sp argv envp uid hwcap), [].
  split.
  - rewrite (bsb_decomp ph sp argv envp uid). unfold strs_tail. rewrite <- !app_assoc, app_nil_r. reflexivity.
  - rewrite !length_app, length_hdr_bytes, length_env_bytes, length_auxv. unfold str_off, aux_off. lia.
Qed.

Lemma length_tail : ltac2:(tb__ "0|0|
S0S3S2aS37S32Q8A1S45A2A1S2dVLEN;VSTR;A2A3").
Proof using .
  unfold strs_tail. rewrite !length_app, !length_flatten_strings, !repeat_length.
  unfold rand_bytes. rewrite length_at_random_bytes.
  subst LEN STR. unfold img_len, rand_off, raw_len, env_str_off. lia.
Qed.

Lemma NUMS : ltac2:(tb__ "0|9|
S1S1S28Z7fff80000000S31Q40Vsp;A2M0A2S28G0Z800000000000A2A2S1S0S3S2eG0Z10M1A2Z0M2A3S1S1S28Z1M3VARGC;A2S28VARGC;Z400A2A2S1S1S28G2VENVC;A2S28VENVC;Z100A2A2S1S0S3VSTR;S27S27Zb8S29Z8M4VARGC;A2A2S29G4VENVC;A2A2A3S1S28S27S2aS37S32Q8A1Vargv0;A2A1M5G3A2S2aS4fVargv;A1A1M6A2S1S28G5Z1ffffA2S1S0S3VRND;S27S27S27VSTR;G6A2S2aS4fVenvp;A1A1M7A2S2aS4eVargv;Venvp;A2A1M8A2A3S1S2bG8G4A2S1S28G6Z200000A2S1S28G7Z20000A2S1S0S3VLEN;S27VRND;G1A2A3S1S0S3S2eVRND;G4A2G2A3S0S3S2eVSTR;G4A2G2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using Hinp Hsp. exact (nums sp inp Hsp Hinp). Qed.

Lemma tail_nth_str0 : ltac2:(tb__ "0|3|
S3aS47R1S37S32Q8M0A1M1Vargv0;A2A2S0G1S42G1R2S45S33G0Z0A2M2A4S42G1R2S38G1Vargv0;S36G1G2S3bG1A1A3A3G2A4A3F_;Fj;").
Proof using Hinp Hsp.
  intros j Hj. unfold strs_tail. pose proof NUMS. subst argv0 ARGC.
  destruct argv as [|a r] eqn:Ea; [cbn in *; lia|].
  rewrite flatten_strings_cons. cbn [nth]. rewrite <- app_assoc. apply app_nth1.
  rewrite length_app. cbn [length]. cbn in Hj. lia.
Qed.

Lemma tail_nth_rand : ltac2:(tb__ "0|3|
S3aS46R1U10A2S0S32Q8M0A1M1S42G1S60S30S2dVRND;VSTR;A2A1R2A2S45S33G0Z0A2M2A4S42G1R2S4dVdraw;A1G2A4A3F_;Fj;").
Proof using Hinp Hsp.
  intros j Hj. pose proof NUMS. unfold strs_tail.
  rewrite !app_assoc. rewrite app_nth2.
  - f_equal. rewrite !length_app, !length_flatten_strings, repeat_length. lia.
  - rewrite !length_app, !length_flatten_strings, repeat_length. lia.
Qed.

Lemma rand_bytes_nth : ltac2:(tb__ "0|7|
S3aS3aS46R2U2A2S46R2U8M0A2S0S32Q8M1A1M2S42G2S60S61G0R4A2R3A2S4dVdraw;A1S33G1Z0M3A2M4A4S42G2R3S15G0S42S32Q40M5A1M6R4S36G6S5cVdraw;A1S36G6S5dVdraw;A1S3bG6A1A3A3S33G5G3A2A4A2G4A4A3F_;F_;Fi;Fk;").
Proof using ARGC ENVC LEN RND STR argv draw envp inp.
  intros k i Hk Hi. unfold rand_bytes. rewrite at_random_bytes_words.
  rewrite nth_flat_map_le8 by (cbn; lia). rewrite word_le8_enc. reflexivity.
Qed.

Section J.
Variable rho : valuation.
Hypothesis HJ : JI rho.

Lemma J_v1 : ltac2:(tb__ "0|1|
S0S3S31Q40M0S8Vrho;S9P1A1A2A2S31G0Vsp;A2A3").
Proof using HJ. cbn [eval]. rewrite (ji_sp _ _ _ _ _ _ _ HJ). reflexivity. Qed.
Lemma J_v2 : ltac2:(tb__ "0|0|
S0S3S31Q40S8Vrho;S9P2A1A2A2VARGC;A3").
Proof using ENVC HJ Hinp Hsp LEN RND STR argv0. cbn [eval]. rewrite (ji_argc _ _ _ _ _ _ _ HJ). pose proof NUMS. apply U_addr. lia. Qed.
Lemma J_v3 : ltac2:(tb__ "0|0|
S0S3S31Q40S8Vrho;S9P3A1A2A2VENVC;A3").
Proof using ARGC HJ Hinp Hsp LEN RND STR argv0. cbn [eval]. rewrite (ji_envc _ _ _ _ _ _ _ HJ). pose proof NUMS. apply U_addr. lia. Qed.
Lemma J_v4 : ltac2:(tb__ "0|1|
S0S3S31Q40M0S8Vrho;S9P4A1A2A2S27S31G0Vsp;A2VSTR;A2A3").
Proof using ARGC ENVC HJ Hinp Hsp LEN RND argv0. cbn [eval]. rewrite (ji_argv0 _ _ _ _ _ _ _ HJ). pose proof NUMS. apply U_addr. lia. Qed.
Lemma J_v5 : ltac2:(tb__ "0|0|
S0S3S31Q40S8Vrho;S9P5A1A2A2S2aS37S32Q8A1Vargv0;A2A1A3").
Proof using ARGC ENVC HJ Hinp Hsp LEN RND STR. cbn [eval]. rewrite (ji_len0 _ _ _ _ _ _ _ HJ). pose proof NUMS. apply U_addr. lia. Qed.
Lemma J_v6 : ltac2:(tb__ "0|1|
S0S3S31Q40M0S8Vrho;S9P6A1A2A2S27S31G0Vsp;A2VRND;A2A3").
Proof using ARGC ENVC HJ Hinp Hsp LEN STR argv0. cbn [eval]. rewrite (ji_rand _ _ _ _ _ _ _ HJ). pose proof NUMS. apply U_addr. lia. Qed.
Lemma J_lit : ltac2:(tb__ "0|0|
S3S1S28Z0R1A2S2bR1S2cZ2Z40A2A2A2S0S3S31Q40S8Vrho;S7R2A1A2A2R2A3F_;Fz;").
Proof using . intros. cbn [eval]. apply U_addr. assumption. Qed.

Lemma J_add : ltac2:(tb__ "0|3|
S5S5S3S3S0S3S31Q40M0S8Vrho;R4A2A2R2A3M1G1S28Z0R4A2M2G2S2bS27R6R5A2S2cZ2Z40A2A2S0S3S31G0S8Vrho;SdS4cR9R8A3A2A2S27R7R6A2A3F_;F_;F_;F_;F_;Fy;Fx;Fb;Fa;").
Proof using ARGC ENVC LEN RND STR.
  intros a b x y Hx Hy H1 H2 H3. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. lia.
Qed.

Lemma J_sll3 : ltac2:(tb__ "0|1|
S4S3S0S3S31Q40M0S8Vrho;S9R2A1A2A2R1A3S1S28Z0R2A2S2bR2S2cZ2Z32A2A2A2S0S3S31G0S8Vrho;S56R4A1A2A2S29Z8R3A2A3F_;F_;Fx;Fi;").
Proof using ARGC ENVC LEN RND STR.
  intros i x Hx Hr. unfold sll3. cbn [eval]. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  cbn [eval] in Hx. rewrite Hx. rewrite Z.mod_small; [lia|]. rewrite pow64. lia.
Qed.

Lemma J_env_base : ltac2:(tb__ "0|1|
S0S3S31Q40M0S8Vrho;S54A2A2S27S27S31G0Vsp;A2S29Z8VARGC;A2A2Z10A2A3").
Proof using ENVC HJ Hinp Hsp LEN RND STR argv0.
  pose proof NUMS. unfold env_base.
  erewrite J_add; [reflexivity| | apply J_lit; lia | | |lia]; try lia.
  erewrite J_add; [reflexivity| apply J_v1 | apply (J_sll3 2 ARGC J_v2); lia | | |]; lia.
Qed.

Lemma J_aux_base : ltac2:(tb__ "0|2|
S0S3S31Q40M0S8Vrho;S53A2A2S27S27S27S31G0Vsp;A2S29Z8M1VARGC;A2A2S29G1VENVC;A2A2Z18A2A3").
Proof using HJ Hinp Hsp LEN RND STR argv0.
  pose proof NUMS. unfold aux_base.
  erewrite J_add; [reflexivity| | apply J_lit; lia | | |lia]; try lia.
  erewrite J_add; [reflexivity| | apply (J_sll3 3 ENVC J_v3); lia | | |]; try lia.
  erewrite J_add; [reflexivity| apply J_v1 | apply (J_sll3 2 ARGC J_v2); lia | | |]; lia.
Qed.

Lemma J_soff_small : ltac2:(tb__ "0|0|
S5S3S0S3S31Q40S8Vrho;R2A2A2R1A3S2bR2S2cZ2Z3fA2A2S0S3ScVrho;R4A2R3A3F_;F_;Fx;Fe;").
Proof using ARGC ENVC LEN RND STR.
  intros e x Hx Hr. rewrite soff_snorm. unfold U. rewrite Hx. pose proof (urange (eval rho e)).
  apply snorm_id. unfold smin, smax. lia.
Qed.

Lemma J_soff_lit : ltac2:(tb__ "0|1|
S3S1S28S2fS2cZ2Z3fA2M0A1R1A2S2bR1G0A2A2S0S3ScVrho;S7R2A1A2R2A3F_;Fz;").
Proof using . intros. apply soff_lit_small. assumption. Qed.

Lemma range_of_rng : ltac2:(tb__ "0|0|
S6S3S3S3S0S3S31Q40S8Vrho;S19R4A1A2A2R3A3S0S3ScVrho;S1bR5A1A2R3A3S0S3ScVrho;S1aR6A1A2R3A3S0S35S3S3A2SaVrho;R7A2S34S3S3S27R6R5A2S27R6R4A2A4A3F_;F_;F_;Fhi;Flo;Fb;Fo;").
Proof using . intros o b lo hi Hb Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hlo, Hhi. reflexivity. Qed.

Lemma rng_stk : ltac2:(tb__ "0|2|
S6S0S35S35S5S5A2M0S5A2S44R1A1S34G0S5S34S5S5S9P1A1S7S2fS52A1A1A4S7Z0A1A4A3S0S35S3S3A2SaVrho;R2A2S34S3S3S2dS31Q40Vsp;A2M1S52A2G1A4A3F_;Fo;").
Proof using ARGC ENVC HJ LEN RND STR.
  intros o Ho. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp) (- STK_FREE) 0); [f_equal; lia| | |].
  - rewrite Hb. apply J_v1. - rewrite Hl. apply J_soff_lit. unfold STK_FREE. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma rng_hdr : ltac2:(tb__ "0|3|
S6S0S35S35S5S5A2M0S5A2S44R1A1S34G0S5S34S5S5S9P1A1S7Z0A1A4S7Z10M1A1A4A3S0S35S3S3A2SaVrho;R2A2S34S3S3S31Q40Vsp;A2M2S27G2G1A2A4A3F_;Fo;").
Proof using ARGC ENVC HJ LEN RND STR.
  intros o Ho. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp) 0 16); [f_equal; lia| | |].
  - rewrite Hb. apply J_v1. - rewrite Hl. apply J_soff_lit. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma rng_env : ltac2:(tb__ "0|3|
S6S0S35S35S5S5A2M0S5A2S44R1A1S34G0S5S34S5S5S54S7Z0A1A4SdS4cS56P3A1S7Z8M1A1A3A4A3S0S35S3S3A2SaVrho;R2A2S34S3S3S27S27S31Q40Vsp;A2S29G1VARGC;A2A2Z10A2M2S27S27G2S29G1VENVC;A2A2G1A2A4A3F_;Fo;").
Proof using HJ Hinp Hsp LEN RND STR argv0.
  intros o Ho. pose proof NUMS. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp + 8 * ARGC + 16) 0 (8 * ENVC + 8)); [f_equal; lia| | |].
  - rewrite Hb. apply J_env_base. - rewrite Hl. apply J_soff_lit. lia.
  - rewrite Hh. apply J_soff_small; [|lia].
    erewrite J_add; [reflexivity | apply (J_sll3 3 ENVC J_v3); lia | apply J_lit; lia | | |]; lia.
Qed.

Lemma rng_aux : ltac2:(tb__ "0|4|
S6S0S35S35S5S5A2M0S5A2S44R1A1S34G0S5S34S5S5S53S7Z0A1A4S7Za0M1A1A4A3S0S35S3S3A2SaVrho;R2A2S34S3S3S27S27S27S31Q40Vsp;A2S29Z8M2VARGC;A2A2S29G2VENVC;A2A2Z18A2M3S27G3G1A2A4A3F_;Fo;").
Proof using HJ Hinp Hsp LEN RND STR argv0.
  intros o Ho. pose proof NUMS. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24) 0 160); [f_equal; lia| | |].
  - rewrite Hb. apply J_aux_base. - rewrite Hl. apply J_soff_lit. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma data_lo_hi' : 0 <= data_lo <= data_hi.
Proof using ARGC ENVC Hdata LEN RND STR.
  pose proof Hdata as Hd. unfold data_ok_b in Hd. apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hd1 Hd2].
  apply Z.leb_le in Hd1. apply Z.leb_le in Hd2. lia.
Qed.

Lemma rng_data : ltac2:(tb__ "0|1|
S6S0S35S35S5S5A2M0S5A2S44R1A1S34G0S5S34S5S5S7Z0A1S7Vdata_lo;A1A4S7Vdata_hi;A1A4A3S0S35S3S3A2SaVrho;R2A2S34S3S3Vdata_lo;Vdata_hi;A4A3F_;Fo;").
Proof using ARGC ENVC Hdata Hdata_hi LEN RND STR.
  intros o Ho. pose proof data_lo_hi'. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o 0 data_lo data_hi); [f_equal; lia| | |].
  - rewrite Hb. apply J_lit. lia. - rewrite Hl. apply J_soff_lit. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma rng_str0 : ltac2:(tb__ "0|1|
S0S35S3S3A2SaVrho;S58A2S34S3S3S27S31Q40Vsp;A2VSTR;A2M0S27S27G0S2aS37S32Q8A1Vargv0;A2A1A2Z1A2A4A3").
Proof using ARGC ENVC HJ Hinp Hsp LEN RND.
  pose proof NUMS.
  rewrite (range_of_rng O_str0 (bv_unsigned sp + STR) 0 (Z.of_nat (length argv0) + 1)); [f_equal; lia| | |].
  - apply J_v4. - apply J_soff_lit. lia.
  - cbn [ob_hi O_str0]. apply J_soff_small; [|lia].
    erewrite J_add; [reflexivity | apply J_v5 | apply J_lit; lia | | |]; lia.
Qed.

Lemma rng_rand : ltac2:(tb__ "0|1|
S0S35S3S3A2SaVrho;S57A2S34S3S3S27S31Q40Vsp;A2VRND;A2M0S27G0Z10A2A4A3").
Proof using ARGC ENVC HJ Hinp Hsp LEN STR argv0.
  pose proof NUMS.
  rewrite (range_of_rng O_rand (bv_unsigned sp + RND) 0 16); [f_equal; lia| | |].
  - apply J_v6. - apply J_soff_lit. lia. - apply J_soff_lit. lia.
Qed.
End J.

Lemma find_segment_none_high : ltac2:(tb__ "0|1|
S32Q40M0A1S28S55Vsegs;A1S31G0R1A2A2S0S3cS62A1S4aVsegs;S31G0R2A2Z1A3S3dS62A1A3F_;Fa;").
Proof using ARGC ENVC LEN RND STR.
  intros a Ha. destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (find_segment_top segs (bv_unsigned a) 1 seg ltac:(lia) E). lia.
Qed.

Lemma image_byte_none_high : ltac2:(tb__ "0|2|
S32Q40M0A1S28S55Vsegs;A1S31G0R1A2A2S0S3cS32Q8A1M1A1S16Vsegs;R2A2S3dG1A1A3F_;Fa;").
Proof using ARGC ENVC LEN RND STR.
  intros a Ha. unfold image_byte, memory_read. rewrite find_segment_none_high by exact Ha. reflexivity.
Qed.

Lemma Jinit_set_rl : ltac2:(tb__ "0|0|
SbS4S39S32Q8A1A1VJI;R3A1S2S0S4R3P1A3A1S2S0S4R4P2A3A1VJI;S66R6R5R4A3A1F_;F_;F_;FL;Fl;Frho;").
Proof using inp pc0 ph segs sp.
  intros rho l L HJ H1 H2. destruct HJ; constructor; auto.
  - rewrite rho_set_rl_other; auto.
  - rewrite rho_set_rl_other; auto.
Qed.

Lemma Jinit_set_rw : ltac2:(tb__ "0|0|
SbS4S32Q40A1VJI;R3A1S5ePbR3A2VJI;S67R5R4R3A3A1F_;F_;Fv;Fn;Frho;").
Proof using ARGC ENVC LEN RND STR pc0 ph segs sp.
  intros rho n v HJ Hn. destruct HJ; constructor; auto; rewrite rho_set_rw_other; auto; lia.
Qed.

Lemma ms_mem_some_high : ltac2:(tb__ "0|3|
S48S32Q40M0A1S32Q8A1M1S28S55Vsegs;A1S31G0R2A2A2S2S0S3cG1A1M2S4bVsegs;S49R4A1R3A3S3dG1A1A3A1S0G2S1cR5R4A2S3fG1R3A2A3S0G2S49R6R5A2S3fG1R4A2A3F_;F_;F_;Fb;Fa;Fms;").
Proof using ARGC ENVC LEN RND STR.
  intros ms a b Ha Hw Hr. unfold wview in Hw. unfold rd, ms_read_byte in Hr.
  destruct (ms_mem ms a) as [b'|] eqn:E; [exact Hr|].
  rewrite find_segment_none_high in Hw by exact Ha. exfalso. apply Hw. reflexivity.
Qed.

Ltac fwd H := match type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] end.

Theorem recarve_strs : ltac2:(tb__ "0|d|
SbS12S39S6aA1M0S48S69S6S6S6S6S6S4S4S11Vsegs;RcRbS34G0S63RaS64R9R8A2A4A4VJI;RdA1S0S39S6A1S22RdA1S36S6R9S36S6R8S36S6R7S36S6R6S36S6S58S36S6S57S36S6R5S3bS6A1M1A3A3A3A3A3A3A3A3S0S35S35S5S5A2M2S5A2M3S44RaA1M4S34G2S5S34S5S5S9P1M5A1M6S7S2fS52A1A1A4S7Z0A1M7A4A3S0G3G4S34G2S5S34S5S5G6G7A4S7Z10A1A4A3S0G3G4S34G2S5S34S5S5S54G7A4SdS4cS56P3A1S7Z8A1A3A4A3S0G3G4S34G2S5S34S5S5S53G7A4S7Za0A1A4A3S0G3G4S34G2S5S34S5S5G7S7Vdata_lo;A1A4S7Vdata_hi;A1A4A3S0S3eS68R9R13A2S41A3S2S0S4RaG5A3A1S2S0S4RbP2A3A1S5eS21R16A1RdA2S5ePbReA2S67S66R19ReS45A3RfS33Q40M8S2dVLEN;VSTR;A2A2M9A3SbS18S23R19A1S24R19A1S1fR19A1S1eR19A1S25R19A1S36S6R15S36S6R14S36S6R13S36S6R12S36S6S6bR10RfA2S36S6R11G1A3A3A3A3A3A3S1dR19A1S5fR10A1S20R19A1A9S12S0S3eS26R1A1S40A3S1S11Vsegs;R3R2S34G0S63R1aS64R19R18A2A4A4S1VJI;R3A1S1S0S39S32Q8A1MaA1MbSeR3R11A2S45A3S1S0S32G8A1McSfR3R12A2G9A3S1S4S2S0S4R1R13A3A1S0GcSfR5R2A2SfR1eR2A2A3F_;Fi;S1S4S2S0S4R1R12A3A1S0GbSeR5R2A2SeR1eR2A2A3F_;Fl;GcS0S3cGaA1S10R4R1A2S10R1dR1A2A3Fa;A2A2A2A2A2A2F_;TS';Trho';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnl;Fnv;FE;FD;FC;FB;FA;Fmd;Fms;Ftr;FS;Frho;").
Proof using Hdata Hdata_hi Hinp Hsp Htop pc0 ph.
  intros rho S tr ms md A B C D E nv nl Hsm HJ Hobjs HA HB HC HD HE Hrl Hn1 Hn2 Hnv H7 rho' S' Hwf'.
  pose proof NUMS as NU. pose proof (LEN_bound inp Hinp) as HLEN. pose proof stack_max_size_val as SMS.
  pose proof data_lo_hi' as DLH.

  set (rho1 := rho_set_rl rho nl strs_tail).
  assert (Hsm1 : smatch segs rho1 S (tr, mkCfg ms md)) by (apply smatch_set_rl; assumption).
  assert (HJ1 : JI rho1) by (apply Jinit_set_rl; assumption).

  assert (Hag : agree_below (ss_next S) rho1 rho') by (apply agree_below_set_rw; exact Hnv).
  assert (Hsm2 : smatch segs rho' S (tr, mkCfg ms md)) by (eapply smatch_agree; [exact Hag | exact Hsm1]).
  assert (HJ' : JI rho') by (apply Jinit_set_rw; assumption).
  assert (Hrl' : rl rho' nl = strs_tail) by (subst rho' rho1; rewrite rho_set_rw_rl, rho_set_rl_at; reflexivity).
  assert (Hrw' : rw rho' nv = Z_to_bv 64 (LEN - STR)) by (subst rho'; apply rho_set_rw_at).
  split; [| split; [exact HJ'|]; split; [exact Hrl'|]; split; [exact Hrw'|]].
  2:{ subst rho' rho1. split; [|split].
      - intros i Hi. rewrite rho_set_rw_other by exact Hi. reflexivity.
      - intros l Hl. rewrite rho_set_rw_rl, rho_set_rl_other by exact Hl. reflexivity.
      - intros a. rewrite rho_set_rw_rm, rho_set_rl_rm. reflexivity. }

  pose proof Hsm2 as (_ & _ & _ & _ & Hrom & Hroc & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms cfg_model] in Hmm, Hrom, Hroc.
  rewrite Hobjs in Hmm. destruct Hmm as (Hall & Hpd & Hfr).
  pose proof Hall as Hall0.
  fwd Hall. fwd Hall. fwd Hall. fwd Hall. fwd Hall. fwd Hall. fwd Hall. clear Hall.
  rename H into HoA. rename H0 into HoB. rename H1 into HoC. rename H2 into HoD.
  rename H3 into Ho0. rename H4 into HoR. rename H5 into HoE.
  pose proof (rng_stk rho' HJ' A HA) as RA. pose proof (rng_hdr rho' HJ' B HB) as RB.
  pose proof (rng_env rho' HJ' C HC) as RC. pose proof (rng_aux rho' HJ' D HD) as RD.
  pose proof (rng_data rho' E HE) as RE.
  pose proof (rng_str0 rho' HJ') as R0. pose proof (rng_rand rho' HJ') as RR.
  assert (Hb4 : bv_unsigned (eval rho' (SVar 4)) = bv_unsigned sp + STR) by (apply J_v4; exact HJ').
  assert (Hhi : soff rho' (SVar nv) = LEN - STR).
  { apply (J_soff_small rho'); [|lia]. cbn [eval]. rewrite Hrw'. apply U_addr. lia. }
  assert (RS : obj_range rho' (O_strs nv nl) = (bv_unsigned sp + STR, bv_unsigned sp + LEN)).
  { rewrite (range_of_rng rho' (O_strs nv nl) (bv_unsigned sp + STR) 0 (LEN - STR)); [f_equal; lia | exact Hb4 | apply soff_lit_small; lia | exact Hhi]. }

  assert (PR : forall off, 0 <= off < LEN - STR ->
            ms_mem ms (Z_to_bv 64 (bv_unsigned sp + STR + off)) = Some (nth (Z.to_nat off) strs_tail (Z_to_bv 8 0))).
  { intros off Hoff.
    assert (Htopa : segs_top segs <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + STR + off))) by (rewrite U_addr by lia; lia).
    destruct (Z_lt_le_dec off (Z.of_nat (length argv0) + 1)) as [Hlt|Hge].
    -
      pose proof Ho0 as (_ & Hw & _ & Hd & _).
      unfold obj_lo_of, obj_hi_of in Hw, Hd. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells O_str0] in Hw, Hd.
      rewrite Hb4 in Hw, Hd.
      assert (Hlo0 : soff rho' (SLit 0) = 0) by (apply soff_lit_small; lia).
      assert (Hhi0 : soff rho' (SAlu ALU_ADD (SVar 5) (SLit 1)) = Z.of_nat (length argv0) + 1).
      { apply (J_soff_small rho'); [|lia]. erewrite (J_add rho'); [reflexivity | apply J_v5; exact HJ' | apply (J_lit rho'); lia | | |]; lia. }
      rewrite Hlo0, Hhi0 in Hw, Hd.
      apply ms_mem_some_high; [exact Htopa | apply Hw; [lia|reflexivity] |].
      cbn [dflt_holds] in Hd. rewrite (Hd off ltac:(lia) ltac:(intros HC0; inversion HC0)).
      rewrite (ji_str0 _ _ _ _ _ _ _ HJ'). rewrite Z.sub_0_r. f_equal. symmetry. apply tail_nth_str0. lia.
    - destruct (Z_lt_le_dec off (RND - STR)) as [Hlt2|Hge2].
      +
        rewrite Hfr.
        * subst rho' rho1. rewrite rho_set_rw_rm, rho_set_rl_rm. rewrite (ji_mem _ _ _ _ _ _ _ HJ).
          replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + (Z.of_nat (str_off argv envp) + Z.of_nat (Z.to_nat off))) by (subst STR; lia).
          apply (ms0_mem_region segs pc0 ph sp draw inp Hsp Hinp _ strs_tail (Z.to_nat off) region_tail).
          pose proof length_tail. lia.
        * unfold outside_all. repeat apply Forall_cons; try apply Forall_nil;
            rewrite ?RA, ?RB, ?RC, ?RD, ?RE, ?R0, ?RR; cbn [fst snd]; rewrite U_addr by lia; unfold STK_FREE; lia.
      +
        pose proof HoR as (_ & Hw & Hc & _ & _).
        unfold obj_lo_of, obj_hi_of in Hw, Hc. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells O_rand] in Hw, Hc.
        rewrite (J_v6 rho' HJ') in Hw.
        rewrite !soff_lit_small in Hw by lia.
        replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + RND + (off - (RND - STR))) by lia.
        replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + RND + (off - (RND - STR))) in Htopa by lia.
        set (d := off - (RND - STR)) in *.
        assert (Hd16 : 0 <= d < 16) by lia.

        set (k := Z.to_nat (d / 8)). set (i := Z.to_nat (d mod 8)).
        assert (Hk : (k < 2)%nat) by (subst k; clear - Hd16; Z.to_euclidean_division_equations; lia).
        assert (Hi8 : (i < 8)%nat) by (subst i; pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
        assert (Hdki : d = 8 * Z.of_nat k + Z.of_nat i).
        { subst k i. rewrite !Z2Nat.id by (try apply Z.div_pos; try apply Z.mod_pos_bound; lia).
          rewrite <- Z.div_mod; lia. }
        apply Forall_cons_iff in Hc as [Hc0 Hc]. apply Forall_cons_iff in Hc as [Hc1 _].
        assert (HCK : cell_holds rho' (SVar 6) 0 16 ms (cell8 (8 * Z.of_nat k) (SVar (Pos.of_nat (9 + k))))).
        { destruct k as [|[|k]]; [exact Hc0 | exact Hc1 | lia]. }
        destruct HCK as (_ & _ & HR). unfold cell8 in HR. cbn [c_off c_width c_val eval] in HR.
        rewrite soff_lit_small in HR by lia. change (Z.to_nat 8) with 8%nat in HR.
        unfold oaddr in HR. cbn [eval] in HR. rewrite (ji_rand _ _ _ _ _ _ _ HJ') in HR.
        change (Z.of_nat (rand_off (in_argv inp) (in_envp inp))) with RND in HR.
        rewrite (U_addr (bv_unsigned sp + RND)) in HR by lia.
        apply ms_mem_some_high; [exact Htopa | apply Hw; [lia|reflexivity] |].
        rewrite Hdki.
        replace (bv_unsigned sp + RND + (8 * Z.of_nat k + Z.of_nat i))
          with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + RND + 8 * Z.of_nat k)) + Z.of_nat i)
          by (rewrite U_addr by lia; lia).
        rewrite (rd_bytes_nth ms 8 _ _ i HR Hi8) by (rewrite U_addr by lia; lia).
        f_equal. symmetry.
        replace (Z.to_nat off) with (Z.to_nat (RND - STR) + (8 * k + i))%nat by lia.
        rewrite tail_nth_rand by lia. rewrite (rand_bytes_nth k i Hk Hi8).
        do 3 f_equal. symmetry.
        destruct k as [|[|k]]; [ | | lia]; cbn [nth Nat.add Pos.of_nat];
          [exact (ji_rnd0 _ _ _ _ _ _ _ HJ') | exact (ji_rnd1 _ _ _ _ _ _ _ HJ')]. }
  apply (smatch_set_objs_next segs rho' S (tr, mkCfg ms md) [A; B; C; D; O_strs nv nl; E] (Pos.succ nv) (ss_lenient S) Hsm2); [|exact Hwf'].
  cbn [snd cfg_ms].
  split; [|split].
  -
    repeat apply Forall_cons; try assumption; try apply Forall_nil.
    apply (obj_holds_of segs rho' ms (O_strs nv nl) (bv_unsigned sp + STR) 0 (LEN - STR));
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_strs].
    + exact Hb4.
    + apply soff_lit_small. lia.
    + exact Hhi.
    + lia.
    + intros off Hoff _. unfold wview. rewrite (PR off Hoff). discriminate.
    + constructor.
    + intros off Hoff _. cbn [dflt_holds]. unfold rd, ms_read_byte. rewrite (PR off Hoff), Hrl', Z.sub_0_r. reflexivity.
    + cbn [dflt_inv]. rewrite Hrl', length_tail. lia.
  -
    unfold pairwise_disjoint.
    repeat split; repeat (apply Forall_cons || apply Forall_nil);
      rewrite ?RA, ?RB, ?RC, ?RD, ?RE, ?RS; unfold ranges_disjoint, STK_FREE; cbn [fst snd]; try lia.
  -
    intros a Ha. apply Hfr. unfold outside_all in Ha |- *.
    fwd Ha. fwd Ha. fwd Ha. fwd Ha. fwd Ha. fwd Ha. clear Ha.
    rewrite RS in H3. cbn [fst snd] in H3.
    repeat apply Forall_cons; try apply Forall_nil; try assumption;
      rewrite ?R0, ?RR; cbn [fst snd]; lia.
Qed.
End Strs.
