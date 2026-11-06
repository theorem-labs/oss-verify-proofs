(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "holds"; "sv_below"; "sprop_below"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV"; "U"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "modulo"; "mul"; "pow"; "add"; "le"; "@Corelib.Init.Datatypes"; "Some"; "option"; "pair"; "prod"; "bool"; "list"; "true"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "lin_decomp"; "atom_index"; "lin_decomp_facts"; "lin_decomp_syn"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mul_mod_idemp : ltac2:(tb__ "0|1|
S0S0S8S0ScSdR2ScR1SeZ2Z40A2M0A2A2G0A2ScSdR2R1A2G0A2A3Fa;Fesz;").
Proof. intros. rewrite <- (Zmult_mod_idemp_r (a mod 2 ^ 64)), Z.mod_mod by lia. apply Zmult_mod_idemp_r. Qed.

Lemma atom_index_sound : ltac2:(tb__ "0|0|
S4S2S0S2SbZ0R2A2S8S12S2A1S1aR4R3A2S11S2R2A2A3S8S0SaR6R5A2ScSdR4SaR6R3A2A2SeZ2Z40A2A2A3F_;F_;Fx;Fesz;Ft;Frho;").
Proof.
  intros rho t esz x Hesz H. unfold atom_index in H.
  destruct t as [| |op a b|op a b|op a b|op a b| |]; try discriminate.
  - destruct op; try discriminate. destruct b as [sh| | | | | | |]; try discriminate.
    destruct ((0 <=? sh) && (sh <? 64) && (2 ^ sh =? esz))%bool eqn:E; [|discriminate].
    injection H as <-.
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3. subst esz.
    unfold U. cbn [eval]. rewrite sll_val. rewrite (Z.mod_small sh 64) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
  - destruct op; try discriminate.
    destruct a as [e| | | | | | |].
    1:{ destruct (e mod 2 ^ 64 =? esz) eqn:E.
      * injection H as <-. apply Z.eqb_eq in E. unfold U. cbn [eval]. rewrite mul_val.
        rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, E. f_equal.
      * destruct b as [e'| | | | | | |]; try discriminate.
        destruct (e' mod 2 ^ 64 =? esz) eqn:E'; [|discriminate]. injection H as <-.
        apply Z.eqb_eq in E'. unfold U. cbn [eval]. rewrite mul_val.
        rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, E'. f_equal. lia. }
    all: (destruct b as [e'| | | | | | |]; try discriminate;
                destruct (e' mod 2 ^ 64 =? esz) eqn:E'; [|discriminate]; injection H as <-;
                apply Z.eqb_eq in E'; unfold U; cbn [eval]; rewrite mul_val;
                rewrite Z_to_bv_unsigned; unfold bv_wrap; rewrite two64, E'; f_equal; lia).
Qed.

Lemma lin_decomp_syn_sound : ltac2:(tb__ "0|2|
S4S2S0S2S0SbZ0M0R3A2S8S12S14S2S0A2M1A1S1cR5R4A2S11G1S13S2S0R3R2A4A2A3S9S9S10G0R3A2SbR3R5A2A2S8S0SaR7R6A2ScSfSdR5SaR7R4A2A2R3A2SeZ2Z40A2A2A3A2F_;F_;Fc;Fidx;Fesz;Fd;Frho;").
Proof.
  intros rho d esz idx c Hesz H. unfold lin_decomp_syn in H.
  destruct (atoms_of d [] 0) as [atoms c0] eqn:Ea.
  pose proof (atoms_of_sound0 rho d atoms c0 Ea) as Hd.
  destruct atoms as [|t [|t2 rest]]; try discriminate.
  - injection H as <- <-.
    pose proof (Z.mod_pos_bound c0 (2 ^ 64) ltac:(lia)) as Hc0.
    pose proof (Z.mod_pos_bound (c0 mod 2 ^ 64) esz Hesz) as Hr.
    split; [lia|].
    cbn [sumZ fold_right] in Hd. rewrite Z.add_0_l in Hd. rewrite Hd.
    unfold U. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    assert (Hq : 0 <= c0 mod 2 ^ 64 / esz <= c0 mod 2 ^ 64).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
    rewrite (Z.mod_small (c0 mod 2 ^ 64 / esz)) by lia.
    rewrite <- (Z_div_mod_eq_full (c0 mod 2 ^ 64) esz). symmetry. apply Z.mod_small. lia.
  - destruct (if esz =? 1 then Some t else atom_index t esz) as [x|] eqn:Ex; [|discriminate].
    injection H as <- <-.
    pose proof (Z.mod_pos_bound c0 esz Hesz) as Hr. split; [lia|].
    cbn [sumZ fold_right] in Hd. rewrite Z.add_0_r in Hd.
    assert (Ht : U rho t = (esz * U rho x) mod 2 ^ 64).
    { destruct (Z.eqb_spec esz 1).
      - injection Ex as <-. subst esz. rewrite Z.mul_1_l. symmetry. apply Z.mod_small. apply U_range.
      - eapply atom_index_sound; eauto. }
    unfold U in *. rewrite Hd, Ht.
    rewrite mk_addk_sound, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l.
    set (X := bv_unsigned (eval rho x)).
    transitivity ((esz * ((X + c0 / esz) mod 2 ^ 64) mod 2 ^ 64 + c0 mod esz) mod 2 ^ 64).
    2:{ apply Zplus_mod_idemp_l. }
    rewrite mul_mod_idemp, Zplus_mod_idemp_l. f_equal. rewrite (Z_div_mod_eq_full c0 esz) at 1. lia.
Qed.

Lemma lin_decomp_facts_sound : ltac2:(tb__ "0|2|
S4S16S3A1S2S0S2S0SbZ0M0R3A2S18S3S5R7A1R6A3S8S12S14S2S0A2M1A1S1bR7R6R5A3S11G1S13S2S0R4R3A4A2A3S9S9S10G0R4A2SbR4R6A2A2S8S0SaR9R7A2ScSfSdR6SaR9R5A2A2R4A2SeZ2Z40A2A2A3A2F_;F_;F_;Fc;Fidx;Fesz;Fd;Ffacts;Frho;").
Proof.
  intros rho facts d esz idx c Hesz Hf. induction facts as [|f rest IH]; intros H; [discriminate|].
  inversion Hf as [|f' rest' Hf1 Hrest]; subst.
  cbn [lin_decomp_facts] in H.
  assert (SHIFT : forall a b delta, eval rho a = eval rho b -> same_atoms d a = Some delta ->
            lin_decomp_syn (mk_addk b delta) esz = Some (idx, c) ->
            0 <= c < esz /\ U rho d = (esz * U rho idx + c) mod 2 ^ 64).
  { intros a b delta Hab Hsa Hl.
    destruct (lin_decomp_syn_sound rho _ esz idx c Hesz Hl) as [Hc Hv]. split; [exact Hc|].
    rewrite <- Hv. rewrite (same_atoms_sound rho d a delta Hsa).
    unfold U. rewrite mk_addk_sound, bv_add_unsigned, Z_to_bv_unsigned, Hab. unfold bv_wrap. rewrite two64.
    rewrite Zplus_mod_idemp_r. reflexivity. }
  destruct f; try (apply IH; assumption).
  cbn in Hf1.
  destruct (same_atoms d a) as [delta|] eqn:Hsa.
  - destruct (lin_decomp_syn (mk_addk b delta) esz) as [r|] eqn:Hl.
    + injection H as ->. eapply SHIFT; eauto.
    + destruct (same_atoms d b) as [delta'|] eqn:Hsb.
      * destruct (lin_decomp_syn (mk_addk a delta') esz) as [r'|] eqn:Hl'.
        -- injection H as ->. eapply (SHIFT b a); eauto.
        -- apply IH; assumption.
      * apply IH; assumption.
  - destruct (same_atoms d b) as [delta'|] eqn:Hsb.
    + destruct (lin_decomp_syn (mk_addk a delta') esz) as [r'|] eqn:Hl'.
      * injection H as ->. eapply (SHIFT b a); eauto.
      * apply IH; assumption.
    + apply IH; assumption.
Qed.

Theorem lin_decomp_sound : ltac2:(tb__ "0|3|
S4S16S3A1S2S0S2S0S18S3S5R6A1R5A3S8S12S14S2S0A2M0A1S19R6R5R4A3S11G0S13S2S0R3R2A4A2A3S9S9SbZ0M1R5A2SbR5SeZ2M2Z3eA2A2A2S9S9S10G1R3A2SbR3R5A2A2S8S0SaR8R6A2ScSfSdR5SaR8R4A2A2R3A2SeG2Z40A2A2A3A2A2F_;F_;Fc;Fidx;Fesz;Fd;Ffacts;Frho;").
Proof.
  intros rho facts d esz idx c Hf H. unfold lin_decomp in H.
  destruct ((0 <? esz) && (esz <? 2 ^ 62))%bool eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
  split; [lia|].
  destruct (lin_decomp_syn d esz) as [r|] eqn:Hs.
  - injection H as ->. eapply lin_decomp_syn_sound; eauto.
  - eapply lin_decomp_facts_sound; eauto.
Qed.

Lemma lin_decomp_below : ltac2:(tb__ "0|1|
S1S16S3A1S2S0S2S0S8S15S6R6R4A2S17A3S8S15S1dS3S7R7A1R6A3S17A3S8S12S14S2S0A2M0A1S19R7R6R5A3S11G0S13S2S0R4R3A4A2A3S8S15S6R9R5A2S17A3F_;F_;F_;Fc;Fidx;Fesz;Fd;Ffacts;Fn;").
Proof.
  intros n facts d esz idx c Hd Hf H. unfold lin_decomp in H.
  destruct ((0 <? esz) && (esz <? 2 ^ 62))%bool; [|discriminate].
  assert (SYN : forall d', sv_below n d' = true -> lin_decomp_syn d' esz = Some (idx, c) -> sv_below n idx = true).
  { intros d' Hd' Hs. unfold lin_decomp_syn in Hs.
    destruct (atoms_of d' [] 0) as [atoms c0] eqn:Ea.
    pose proof (atoms_of_below n d' [] 0 atoms c0 Hd' ltac:(reflexivity) Ea) as Hab.
    destruct atoms as [|t [|t2 rest]]; try discriminate.
    - injection Hs as <- _. reflexivity.
    - destruct (if esz =? 1 then Some t else atom_index t esz) as [x|] eqn:Ex; [|discriminate].
      injection Hs as <- _. apply mk_addk_below.
      cbn in Hab. apply andb_prop in Hab as [Ht _].
      destruct (esz =? 1); [injection Ex as <-; exact Ht|].
      unfold atom_index in Ex. destruct t as [| |op a b|op a b|op a b|op a b| |]; try discriminate;
        destruct op; try discriminate; cbn in Ht; apply andb_prop in Ht as [Hta Htb].
      + destruct b; try discriminate. destruct (_ && _)%bool; [|discriminate]. injection Ex as <-. exact Hta.
      + destruct a as [e| | | | | | |].
        1:{ destruct (e mod 2 ^ 64 =? esz); [injection Ex as <-; exact Htb|].
          destruct b as [e'| | | | | | |]; try discriminate. destruct (e' mod 2 ^ 64 =? esz); [|discriminate].
          injection Ex as <-. reflexivity. }
        all: destruct b as [e'| | | | | | |]; try discriminate; destruct (e' mod 2 ^ 64 =? esz); try discriminate;
               injection Ex as <-; exact Hta. }
  destruct (lin_decomp_syn d esz) as [r|] eqn:Hs.
  - injection H as ->. eapply SYN; eauto.
  - revert H. induction facts as [|f rest IH]; intros H; [discriminate|].
    cbn in Hf. apply andb_prop in Hf as [Hf1 Hrest].
    cbn [lin_decomp_facts] in H.
    destruct f; try (apply IH; assumption).
    cbn in Hf1. apply andb_prop in Hf1 as [Ha Hb].
    destruct (same_atoms d a) as [delta|].
    + destruct (lin_decomp_syn (mk_addk b delta) esz) as [r|] eqn:Hl.
      * injection H as ->. eapply SYN; [apply mk_addk_below; exact Hb | exact Hl].
      * destruct (same_atoms d b) as [delta'|].
        -- destruct (lin_decomp_syn (mk_addk a delta') esz) as [r'|] eqn:Hl'.
           ++ injection H as ->. eapply SYN; [apply mk_addk_below; exact Ha | exact Hl'].
           ++ apply IH; assumption.
        -- apply IH; assumption.
    + destruct (same_atoms d b) as [delta'|].
      * destruct (lin_decomp_syn (mk_addk a delta') esz) as [r'|] eqn:Hl'.
        -- injection H as ->. eapply SYN; [apply mk_addk_below; exact Ha | exact Hl'].
        -- apply IH; assumption.
      * apply IH; assumption.
Qed.
