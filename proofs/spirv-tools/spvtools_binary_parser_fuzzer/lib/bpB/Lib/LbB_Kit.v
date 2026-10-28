(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim StoreOk MemSplit RefMemcpyLib LibIface SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition SHBASE : Z := 0x7fff8000.
Definition SHCELL : Z := 0x191038.
Definition GOT_SH : Z := 0x1850a0.

Definition UARCELL : Z := 0x191040.
Definition GOT_UAR : Z := 0x1850f8.

Definition shk (M : mem) (x k : Z) : Prop :=
  rdn ASEGS M (Z_to_bv 64 (x / 8 + SHBASE)) 1 = Some [Z_to_bv 8 k].
Definition sh0 (M : mem) (x : Z) : Prop := shk M x 0.

Definition gz (M : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> sh0 M (a + i).

Lemma gz_at : forall M a n i, gz M a n -> 0 <= i < n -> sh0 M (a + i).
Proof. intros M a n i H Hi. exact (H i Hi). Qed.

Definition KN_A : list kentry := [KImg GOT_SH (GOT_SH + 8); KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE)].

Lemma word_to_le_bytes_1 : forall k, 0 <= k < 256 ->
  word_to_le_bytes 1 (Z_to_bv 64 k) = [Z_to_bv 8 k].
Proof.
  intros k Hk. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small k (2 ^ 64)) by lia.
  first [ rewrite bv_extract_unsigned, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
          rewrite Z.shiftr_0_r, (Z.mod_small k (2 ^ 64)) by lia; reflexivity
        | reflexivity ].
Qed.

Lemma kshadow : forall E M e (x k : Z) (ek : expr),
  edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= k < 256 -> edenot E ek = Z_to_bv 64 k ->
  shk M x k ->
  kentry_ok ASEGS E M (KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 ek).
Proof.
  intros E M e x k ek He Hx Hk Hek Hs. cbn [kentry_ok].
  assert (Hsh : bv_unsigned (edenot E (EAlu ALU_SRL e (ELit 3))) = x / 8).
  { cbn [edenot]. rewrite He. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small x) by lia.
    replace (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3 by (vm_compute; reflexivity).
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  split; [lia|]. split.
  - unfold flat, estart. cbn [a_base a_off]. rewrite Hsh. unfold SHBASE.
    assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
  - unfold adenot. cbn [a_base a_off]. rewrite Hek, word_to_le_bytes_1 by lia.
    unfold v_addi. rewrite Hsh. exact Hs.
Qed.

Lemma kshadow0 : forall E M e (x : Z),
  edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> sh0 M x ->
  kentry_ok ASEGS E M (KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 (ELit 0)).
Proof. intros E M e x He Hx Hs. exact (kshadow E M e x 0 (ELit 0) He Hx ltac:(lia) eq_refl Hs). Qed.

Definition non_argT : list reg :=
  [1; 2; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition aonlyT (R R' : bvmap 5 word) : Prop := forall r, In r non_argT -> getr R' r = getr R r.
Lemma aonlyT_trans : forall R1 R2 R3, aonlyT R1 R2 -> aonlyT R2 R3 -> aonlyT R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Ltac sc_dj := cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off a_base]; lia.

Definition is_shadow_addr (a : saddr) : bool :=
  (a_off a =? SHBASE) && match a_base a with EAlu ALU_SRL _ (ELit 3) => true | _ => false end.

Fixpoint last_sh_req (scs : list sidecond) (acc : option saddr) : option saddr :=
  match scs with
  | [] => acc
  | SCReadBase a 1 _ _ :: t => if is_shadow_addr a then last_sh_req t (Some a) else last_sh_req t acc
  | _ :: t => last_sh_req t acc
  end.

Fixpoint kn_fix (fuel : nat) (stops : list Z) (scr : scripts) (pc : Z) (sr : list expr)
         (kn : list kentry) (nx : N) : list kentry :=
  match fuel with
  | O => kn
  | S f =>
      let '(_, scs, _) := sym_exec ASEGS 200 true stops scr (SS pc sr [] kn nx) [] in
      match last_sh_req scs None with
      | None => kn
      | Some a => kn_fix f stops scr pc sr (kn ++ [KWord a 1 (ELit 0)]) nx
      end
  end.

Ltac sh0_from_gz :=
  lazymatch goal with
  | |- sh0 ?M ?x =>
      first [ unfold sh0; assumption
            | match goal with H : gz M ?a ?n |- _ =>
                replace x with (a + (x - a)) by lia; apply H; lia end
            | match goal with H : forall _ _ _, _ -> gz M _ _ |- _ =>
                eapply H; [eassumption|]; lia end ]
  end.

Ltac kshadow_tac :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord (SA (EAlu ALU_SRL ?e (ELit 3)) _) 1 (ELit 0)) =>
      eapply kshadow0;
      [ evs; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia; reflexivity
      | lia
      | sh0_from_gz ]
  end.

Lemma srl3_val : forall E e x, edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_SRL e (ELit 3))) = x / 8.
Proof.
  intros E e x He Hx. cbn [edenot]. rewrite He. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x) by lia.
  replace (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma shk_wbytes : forall M (d : word) bs x k,
  shk M x k -> 0 <= x < 2 ^ 64 -> bv_unsigned d + Z.of_nat (length bs) <= 2 ^ 64 ->
  (x / 8 + SHBASE + 1 <= bv_unsigned d \/ bv_unsigned d + Z.of_nat (length bs) <= x / 8 + SHBASE) ->
  shk (wbytes M d bs) x k.
Proof.
  intros M d bs x k Hs Hx Hd Hap. unfold shk in *. rewrite <- Hs.
  assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply rdn_ext; rewrite ?u64_of_Z by (unfold SHBASE; lia); [unfold SHBASE; lia|].
  intros y Hy. apply wbytes_outside; [exact Hd|]. unfold SHBASE in *. lia.
Qed.

Lemma gz_wbytes : forall M (d : word) bs a n,
  gz M a n -> 0 <= a -> a + n <= 2 ^ 47 -> 2 ^ 45 <= bv_unsigned d -> bv_unsigned d + Z.of_nat (length bs) <= 2 ^ 64 ->
  gz (wbytes M d bs) a n.
Proof.
  intros M d bs a n Hg Ha Han Hd Hdb i Hi. apply shk_wbytes; [apply Hg; exact Hi | lia | exact Hdb |].
  left. assert ((a + i) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SHBASE. lia.
Qed.

Lemma div8_bound : forall x, 0 <= x < 2 ^ 47 -> 0 <= x / 8 < 2 ^ 44.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma estart_sh : forall E e x, edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  estart E (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) = x / 8 + SHBASE.
Proof. intros E e x He Hx. unfold estart. cbn [a_base a_off]. rewrite (srl3_val E e x He Hx). reflexivity. Qed.

Ltac sc_shdj :=
  cbn [sc_denot]; unfold flat, elenZ;
  repeat (erewrite estart_sh; [| evs; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia; reflexivity | lia]);
  unfold estart; cbn [a_base a_off]; evs; rewrite ?u64_of_Z by lia; cbn [edenot];
  repeat match goal with
  | |- context [?a / 8] =>
      let t := fresh "t" in let Ht := fresh "Ht" in
      pose proof (div8_bound a ltac:(lia)) as Ht; set (t := a / 8) in *; clearbody t
  end;
  rewrite ?u64_of_Z by lia;
  unfold SHBASE; lia.

Ltac kentry_tac :=
  first [ kshadow_tac
        | match goal with H : forall i, GOT_SH <= i < GOT_SH + 8 -> ?M _ = None |- kentry_ok _ _ ?M (KImg _ _) =>
            apply kimg_abs; [unfold GOT_SH; lia | unfold GOT_SH; lia | exact H] end
        | match goal with H : cell8 _ ?M SHCELL SHBASE |- kentry_ok _ ?E ?M (KWord (SA (ELit 0) _) 8 _) =>
            exact (kword_abs ASEGS E M SHCELL 8%N SHBASE (ELit SHBASE) H ltac:(lia) ltac:(unfold SHCELL; lia) ltac:(unfold SHCELL; lia) eq_refl) end
        | match goal with H : stack_room _ ?M ?sp ?S |- kentry_ok _ ?E ?M (KWr (SA (EVar ?n) _) (ELit _)) =>
            eapply (kwr_stack _ E M n sp S);
            [ evs; first [ reflexivity
                         | match goal with Hs : getr ?R ?r = Z_to_bv 64 sp |- getr ?R ?r' = _ =>
                             replace r' with r by (apply bv_eq; reflexivity); exact Hs end ]
            | reflexivity | lia | lia | exact H ] end ].
Ltac know_tac :=
  lazymatch goal with
  | |- know_ok _ _ _ _ => unfold know_ok; know_tac
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [kentry_tac | know_tac]
  end.

Ltac kn_eval :=
  lazymatch goal with |- know_ok ?s ?E ?M ?kn =>
    let l := eval vm_compute in kn in
    let H := fresh "Hkn" in
    assert (H : kn = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite H; clear H end.

Lemma ext_shadow_small : forall k, 0 <= k < 8 -> ext_val true 0 1 (Z_to_bv 64 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. f_equal.
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_small by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus (8 * N.of_nat 1)) with 128. change (bv_modulus (8 * N.of_nat 1)) with 256.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma br_lts_small : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite !Z.mod_small by lia. replace (a + 2 ^ 63 - 2 ^ 63) with a by lia. replace (b + 2 ^ 63 - 2 ^ 63) with b by lia.
  reflexivity.
Qed.

Lemma land7_val : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7) = Z_to_bv 64 (x mod 8).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x), (Z.mod_small 7) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2 ^ 3) with 8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  rewrite ?(Z.mod_small (x mod 8) (2 ^ 64)) by lia. reflexivity.
Qed.

Ltac sc_slow :=
  cbn [sc_denot]; evs; cbn [edenot];
  rewrite ?ext_shadow_small by lia; rewrite ?land7_val by lia; rewrite ?w_add by lia;
  first [ rewrite br_ne by lia; bool_lia
        | rewrite br_lts_small by lia; bool_lia ].
