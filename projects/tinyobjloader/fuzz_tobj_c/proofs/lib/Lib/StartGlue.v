(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "iff"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "length"; "list"; "nat"; "cons"; "nil"; "app"; "false"; "@Corelib.Lists.ListDef"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "word_le8"; "le_bytes_to_word"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sublist"; "ext_low"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "envp_ptrs"; "env_bytes"; "@Stdlib.Lists.List"; "flat_map"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "of_nat"; "modulo"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma sublist_word : ltac2:(tb__ "0|4|
S9S0Q40M0A1M1A1SaS12R1S8G1R2A2A2S3S9S0Q8A1M2A1S14S1aZ8M3S1bR2A1A2G3S18G1G2S10R3A4A3S10SfG1R2R3S1G0Z0A2A4A1A3F_;Fk;Fws;").
Proof.
  induction ws as [|w ws IH]; intros k Hk; [cbn in Hk; lia|].
  unfold sublist in *. cbn [flat_map].
  destruct k as [|k].
  - cbn [Z.of_nat Z.mul Z.to_nat nth]. rewrite skipn_O, firstn_app, length_word_le8.
    replace (Z.to_nat 8 - 8)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_word_le8; lia). reflexivity.
  - replace (Z.to_nat (8 * Z.of_nat (S k))) with (length (word_le8 w) + Z.to_nat (8 * Z.of_nat k))%nat
      by (rewrite length_word_le8; lia).
    rewrite skipn_app, skipn_all2 by lia. cbn [app nth].
    replace (length (word_le8 w) + Z.to_nat (8 * Z.of_nat k) - length (word_le8 w))%nat
      with (Z.to_nat (8 * Z.of_nat k)) by lia.
    apply IH. cbn in Hk; lia.
Qed.

Lemma le_bytes_word_le8 : ltac2:(tb__ "0|1|
S0Q40A1M0S3G0S11S10R1A1A1R1A3Fw;").
Proof.
  intros w. rewrite word_le8_enc. unfold enc_bytes, le_bytes_to_word.
  rewrite bytes_le_to_Z_Z_to_le_bytes by apply (proj1 (urange w)).
  change (8 * Z.of_nat 8) with 64. pose proof (urange w).
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma sublist_byte : ltac2:(tb__ "0|3|
S9S0Q8M0A1M1A1M2SaS12R1S8G1R2A2A2S3G2S14S1bR2A1Z1R3A3SbG1SfG1R2R3S1G0Z0A2A4ScG1A1A3A3F_;Fi;Fl;").
Proof.
  intros l i Hi. unfold sublist. rewrite Nat2Z.id. change (Z.to_nat 1) with 1%nat.
  revert i Hi. induction l as [|b l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hi; lia.
Qed.

Lemma byte_val : ltac2:(tb__ "0|2|
S0Q8M0A1M1S3S7S2Q40S15SeG0S11SbG1R1ScG1A1A3A1A3A2S2G0R1A2A3Fb;").
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  unfold le_bytes_to_word. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned, Z_to_bv_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite two64.
  rewrite (Z.mod_small (bv_unsigned b) (2 ^ 64)) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  apply Z.mod_small. lia.
Qed.

Section Env.
Variable sp : word.
Variable argv envp : list (list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hargv : valid_argv argv.
Hypothesis Henvp : valid_envp envp.

Let ENVC := Z.of_nat (length envp).

Lemma env_bytes_flat : ltac2:(tb__ "0|3|
S3S9S0Q8A1M0A1S17Vsp;Vargv;Venvp;A3S18S0Q40M1A1M2G0S10SdG2S16Vsp;Vargv;Venvp;A3SbG2S1G1Z0A2ScG2A1A3A3A4A3").
Proof using . unfold env_bytes. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma envp_ptrs_length : ltac2:(tb__ "0|0|
S3SaS8S0Q40A1S16Vsp;Vargv;Venvp;A3A2S8S9S0Q8A1A1Venvp;A2A3").
Proof using . unfold envp_ptrs. apply string_addrs_fst_length. Qed.

Lemma envp_ptr_nz : ltac2:(tb__ "0|2|
SaS12R1S8S9S0Q8A1A1Venvp;A2A2S6S3S7S2Q40M0SfS0G0A1R2S16Vsp;Vargv;Venvp;A3S1G0Z0M1A2A4A2G1A3A1F_;Fk;").
Proof using Hargv Henvp Hsp.
  intros k Hk. unfold envp_ptrs. rewrite string_addrs_nth by exact Hk.
  unfold env_str_base. rewrite string_addrs_snd. unfold str_base, nat_to_word.
  pose proof Hsp as (Hlo & Hhi & _). unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi.
  pose proof Hargv as (_ & Ha & _). pose proof Henvp as (_ & He & _).
  rewrite total_arg_bytes_tab in Ha, He.
  assert (Htf : Z.of_nat (tab (firstn k envp)) <= Z.of_nat (tab envp)).
  { rewrite <- (firstn_skipn k envp) at 2. rewrite tab_app. lia. }
  assert (Hso : Z.of_nat (str_off argv envp) <= 184 + 8 * 1024 + 8 * 256).
  { unfold str_off, aux_off, argc, envc. pose proof (proj1 Hargv). pose proof (proj1 Henvp). lia. }
  rewrite !Z_to_bv_unsigned, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite (Z.mod_small (Z.of_nat (str_off argv envp))) by lia.
  rewrite (Z.mod_small (bv_unsigned sp + _)) by lia.
  rewrite (Z.mod_small (_ + Z.of_nat (tab argv))) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma env_word : ltac2:(tb__ "0|4|
S7S5S19Z0M0R1A2S19R1S1aZ8M1VENVC;A2M2A2A2S3S7S1cR2G1A2G0A3S11S14R3G1S17Vsp;Vargv;Venvp;A3A3A1S0Q40M3A1S4S3S7S2G3R1A2G0A3S3S7R4G2A3A2Tw;F_;F_;Fo;").
Proof using Hargv Henvp Hsp.
  intros o Ho Hm. cbv zeta.
  apply Z.mod_divide in Hm; [|lia]. destruct Hm as [k Hk].
  assert (Hk0 : 0 <= k <= ENVC) by lia.
  replace o with (8 * Z.of_nat (Z.to_nat k)) by lia.
  rewrite env_bytes_flat, sublist_word by (rewrite length_app, envp_ptrs_length; cbn; lia).
  rewrite le_bytes_word_le8.
  destruct (Z.eq_dec k ENVC) as [E|E].
  - rewrite app_nth2 by (rewrite envp_ptrs_length; lia).
    rewrite envp_ptrs_length. replace (Z.to_nat k - length envp)%nat with 0%nat by lia. cbn [nth].
    rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. split; intros; lia.
  - rewrite app_nth1 by (rewrite envp_ptrs_length; lia).
    pose proof (envp_ptr_nz (Z.to_nat k) ltac:(lia)). split; intros; lia.
Qed.
End Env.

Section Str0.
Variable argv : list (list byte).
Hypothesis Hargv : valid_argv argv.
Let argv0 : list byte := nth 0 argv [].

Lemma argv0_no_nul : ~ In (Z_to_bv 8 0) argv0.
Proof using Hargv.
  pose proof Hargv as (H1 & _ & _ & H4 & _). subst argv0.
  destruct argv as [|a r]; [cbn in H1; lia|]. cbn. inversion H4. assumption.
Qed.

Lemma str0_byte : ltac2:(tb__ "0|5|
SaS13R1S8S0Q8M0A1M1Vargv0;A2M2A2S4S3S7S2G0SfG1R2SdG1Vargv0;SbG1S1G0Z0M3A2M4ScG1A1A3A3G4A4A2G3A3S3SaR2G2A3A2F_;Fi;").
Proof using Hargv.
  intros i Hi. destruct (Nat.eq_dec i (length argv0)) as [->|Hne].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite Z_to_bv_unsigned. cbn. tauto.
  - rewrite app_nth1 by lia. split; [|lia]. intros H0. exfalso. apply argv0_no_nul.
    replace (Z_to_bv 8 0) with (nth i argv0 (Z_to_bv 8 0)); [apply nth_In; lia|].
    apply bv_eq. rewrite H0, Z_to_bv_unsigned. reflexivity.
Qed.
End Str0.
