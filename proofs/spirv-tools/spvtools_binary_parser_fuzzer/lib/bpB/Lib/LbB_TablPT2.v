(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_DStat LbB_RGb2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RGl LbB_ContStmt LbB_TablStmt LbB_TablLO LbB_TablOS1 LbB_TablPT1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition PT_H2 : Z := 0xfec70.
Definition PT_Z : Z := 0xfecd4.

Definition PTX (R : bvmap 5 word) (SP S1 ff ps v n i : Z) : Prop :=
  getr R 2 = Z_to_bv 64 S1 /\ getr R 8 = Z_to_bv 64 SP /\ getr R 9 = Z_to_bv 64 S1
  /\ getr R 16 = Z_to_bv 64 v /\ getr R 18 = Z_to_bv 64 0x7fff8000 /\ getr R 20 = Z_to_bv 64 (i + 1)
  /\ getr R 21 = Z_to_bv 64 (v + 8) /\ getr R 22 = Z_to_bv 64 (sh (v + 8)) /\ getr R 23 = Z_to_bv 64 (ff + 32)
  /\ getr R 24 = Z_to_bv 64 ps /\ getr R 26 = Z_to_bv 64 (sh ff) /\ getr R 27 = Z_to_bv 64 n.
Definition PTH (R : bvmap 5 word) (SP S1 ff ps v n i : Z) : Prop :=
  PTX R SP S1 ff ps v n i /\ getr R 10 = Z_to_bv 64 i /\ getr R 11 = Z_to_bv 64 (sh ps).

Definition KPT : list reg := [1; 3; 4]%bv.

Definition PTXREGS : list reg := [2; 8; 9; 16; 18; 20; 21; 22; 23; 24; 26; 27]%bv.
Lemma PTX_kept : forall R R' SP S1 ff ps v n i (ks : list reg),
  PTX R SP S1 ff ps v n i -> kept_in ks R R' ->
  forallb (fun r => existsb (fun y => bv_eqb r y) ks) PTXREGS = true ->
  PTX R' SP S1 ff ps v n i.
Proof.
  intros R R' SP S1 ff ps v n i ks P K Hb.
  assert (KK : kept_in PTXREGS R R') by (eapply kept_in_incl; [exact K | exact Hb]).
  destruct P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
  unfold PTX. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)), (KK 16%bv ltac:(inb)),
    (KK 18%bv ltac:(inb)), (KK 20%bv ltac:(inb)), (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)), (KK 23%bv ltac:(inb)),
    (KK 24%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
  repeat (split; [assumption|]). assumption.
Qed.

Lemma zext32_val : forall x, 0 <= x < 2 ^ 32 ->
  alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 x) (Z_to_bv 64 32)) (Z_to_bv 64 32) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite pt_sllk by lia.
  assert (B : 0 <= x * 2 ^ 32 < 2 ^ 64) by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
  rewrite HWord.w_srl by lia. f_equal. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma pt_shk_word : forall M c n a, accessible M c n -> c <= a -> a + 4 <= c + n -> a mod 4 = 0 ->
  exists k, LbB_Kit.shk M a k /\ (k = 0 \/ a mod 8 + 4 <= k < 8).
Proof.
  intros M c n a (A0 & A1 & AC) H1 H2 H4.
  destruct (AC (a + 3) ltac:(lia)) as (v & Hv & Hrd & Hok).
  assert (E : (a + 3) / 8 = a / 8) by (clear - H4 A0 H1; Z.div_mod_to_equations; lia).
  replace (sh (a + 3)) with (sh a) in Hrd by (unfold sh; rewrite E; reflexivity).
  pose proof (shk_of_mrd M a (b8 v) ltac:(lia) Hrd) as K. unfold b8 in K. rewrite Z_to_bv_unsigned in K.
  rewrite bv_wrap_small in K by (change (bv_modulus 8) with 256; lia).
  exists v. split; [exact K|].
  unfold byte_ok in Hok. destruct Hok as [Hv0|Hv1]; [left; exact Hv0|right].
  assert (M8 : (a + 3) mod 8 = a mod 8 + 3) by (clear - H4 A0 H1; Z.div_mod_to_equations; lia). lia.
Qed.

Section PT2.
  Context {HCEIL : HeapCeil}.

  Definition KR0 : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.

  Lemma pt_r0 : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i : Z),
    PTX R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 i -> getr R 11 = Z_to_bv 64 4 ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> wr_at asegs m (sh ff) 8 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh ps))] ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_HEAD) fc None m ro) (MS R' F (Z_to_bv 64 PT_H2) fc None M' ro)
      /\ PTH R' SP S1 ff ps v n i /\ kept_in KPT R R'
      /\ munch [(sh ff + 4, sh ff + 5)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' (sh ff + 4) [C1 (b8 4)].
  Proof.
    intros R F fc m ro SP S1 ff ps v n i P P10 P11 F64 FLO FHI WS S45 SS SPH C48.
    pose proof P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
    assert (QS : 8 * (ff / 64) + SHBASE = sh ff) by (apply q8sh; lia).
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 (sh ps)]).
    assert (HR : regs_ok E (srs sr_id [(11%bv, ELit 4); (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs.
      - exact P11.
      - rewrite P26. rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
        f_equal. unfold SHBASE in QS. lia. }
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64))
      by (evs; rewrite w_mul by (Z.div_mod_to_equations; lia); rewrite u64_of_Z by (Z.div_mod_to_equations; lia); reflexivity).
    assert (HK : know_ok asegs E m [KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8);
                                    KWord (SA (EVar 9) 56) 8 (EVar 33);
                                    KRange (EVar 9) (2 ^ 45) (2 ^ 47); KRange (EVar 32) (0x6e8000 / 64) (2 ^ 41)]).
    { unfold know_ok. apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
          | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
          | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 8%nat (C8 (Z_to_bv 64 (sh ps)))); [exact C48 | reflexivity | reflexivity | lia
          | unfold estart; evs; change (getr R (Z_to_bv 5 (Z.of_N 9))) with (getr R 9%bv); rewrite P9, u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; change (getr R (Z_to_bv 5 (Z.of_N 9))) with (getr R 9%bv); rewrite P9, u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R PT_HEAD m ro HR HK 10%nat [PT_H2] (SCR [] [] []) 34%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (KK : kept_in KR0 R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR0 HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    rreg HR' 11%bv L11. rreg HR' 26%bv L26.
    split.
    { split; [|split; [rewrite (KK 10%bv ltac:(inb)); exact P10 | rewrite L11; first [reflexivity | evs; reflexivity]]].
      apply (PTX_kept R R' SP S1 ff ps v n i (26%bv :: KR0)); [exact P | | vm_cast_no_check (@eq_refl bool true)].
      intros rr Hrr. destruct Hrr as [<-|Hrr]; [| exact (KK rr Hrr)].
      rewrite L26, P26. rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
      f_equal. unfold SHBASE in QS. lia. }
    split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ES; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ];
                          unfold SHBASE in *; lia | apply Forall_nil]. }
    split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
    split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
      | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
      | destruct WS as (W0 & W1 & W); split; [lia|]; split; [lia|]; intros j Hj; replace (sh ff + 4 + j) with (sh ff + (4 + j)) by lia; apply W; cbn in Hj; lia
      | reflexivity | exact I | reflexivity].
  Qed.

  Definition KR2k : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 28; 29; 30; 31]%bv.

  Lemma pt_r2k : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i : Z),
    PTX R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 (-8) -> 0 <= i -> i + 1 <= n -> n <= 48 ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> wr_at asegs m (sh ff) 8 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh ps))] ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_SKIP) fc None m ro)
                          (MS R' F (Z_to_bv 64 (if i + 1 =? n then PT_EXIT else PT_H2)) fc None M' ro)
      /\ PTX R' SP S1 ff ps v n (i + 1) /\ getr R' 10 = Z_to_bv 64 (i + 1)
      /\ (i + 1 < n -> getr R' 11 = Z_to_bv 64 (sh ps)) /\ kept_in KPT R R'
      /\ munch [(sh ff + 4, sh ff + 5)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' (sh ff + 4) [C1 (b8 (if i + 1 =? n then 0xf8 else 4))].
  Proof.
    intros R F fc m ro SP S1 ff ps v n i P P10 I0 I1 N48 F64 FLO FHI WS S45 SS SPH C48.
    pose proof P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
    assert (QS : 8 * (ff / 64) + SHBASE = sh ff) by (apply q8sh; lia).
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 (sh ps)]).
    set (SR0 := srs sr_id [(10%bv, ELit (-8)); (20%bv, EAlu ALU_ADD (EVar 33) (ELit 1)); (27%bv, EVar 34);
                           (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880))]).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs.
      - exact P10.
      - rewrite P20, TablLib.zbv_add. reflexivity.
      - exact P27.
      - rewrite P26. rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
        f_equal. unfold SHBASE in QS. lia. }
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64))
      by (evs; rewrite w_mul by (Z.div_mod_to_equations; lia); rewrite u64_of_Z by (Z.div_mod_to_equations; lia); reflexivity).
    assert (HK : know_ok asegs E m [KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8); KRange (EVar 33) 0 47; KRange (EVar 34) 1 48;
                                    KWord (SA (EVar 9) 56) 8 (EVar 35);
                                    KRange (EVar 9) (2 ^ 45) (2 ^ 47); KRange (EVar 32) (0x6e8000 / 64) (2 ^ 41)]).
    { unfold know_ok. apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
          | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
          | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 8%nat (C8 (Z_to_bv 64 (sh ps)))); [exact C48 | reflexivity | reflexivity | lia
          | unfold estart; evs; change (getr R (Z_to_bv 5 (Z.of_N 9))) with (getr R 9%bv); rewrite P9, u64_of_Z by lia; cbn [a_off]; lia
          | lia | lia | evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; change (getr R (Z_to_bv 5 (Z.of_N 9))) with (getr R 9%bv); rewrite P9, u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia|].
      apply Forall_nil. }
    assert (BR : forall b : bool, (if b then n <= i + 1 else i + 1 < n) -> forall e, edenot E e = Z_to_bv 64 (i + 1) ->
                 sc_denot asegs m E (SCBr b BC_GEU e (EVar 34))).
    { intros b Hb e He. cbn [sc_denot]. rewrite He. evs. rewrite br_geu by lia. destruct b; bool_lia. }
    assert (WS4 : wr_at asegs m (sh ff + 4) (Z.of_nat 1)).
    { destruct WS as (W0 & W1 & W); split; [lia|]; split; [lia|]; intros j Hj; replace (sh ff + 4 + j) with (sh ff + (4 + j)) by lia; apply W; cbn in Hj; lia. }
    destruct (Z.eqb_spec (i + 1) n) as [X|X].
    - xrun_at (PropExec.mkFP F fc) asegs R PT_SKIP m ro HR HK 20%nat [PT_H2; PT_EXIT] (SCR [true] [] []) 36%N.
      { split_scs. apply BR; [lia | evs; rewrite TablLib.zbv_add; reflexivity]. }
      replace (i + 1 =? n) with true by (symmetry; apply Z.eqb_eq; exact X).
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KR2k R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR2k HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(sh ff + 4, sh ff + 5)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ES;
                                    cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]).
        apply Forall_nil. }
      assert (CL1 : rw_cells asegs M1 (sh ff + 4) [C1 (b8 0xf8)]).
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia | exact WS4
        | reflexivity | exact I | first [reflexivity | evs; cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity]]. }
      rreg HR' 10%bv L10. rreg HR' 20%bv L20. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
      split.
      { unfold PTX. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)), (KK 16%bv ltac:(inb)), (KK 18%bv ltac:(inb)),
          (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)), (KK 23%bv ltac:(inb)), (KK 24%bv ltac:(inb)).
        rewrite L20, L26, L27.
        split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P16|]. split; [exact P18|].
        split; [rewrite !TablLib.zbv_add; f_equal; lia|].
        split; [exact P21|]. split; [exact P22|]. split; [exact P23|]. split; [exact P24|].
        split; [|reflexivity].
        rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
        f_equal. unfold SHBASE in QS. lia. }
      split; [rewrite L10, TablLib.zbv_add; reflexivity|].
      split; [intros Hlt; exfalso; lia|].
      split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
      split; [exact MU1|].
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      exact CL1.
    - xrun_at (PropExec.mkFP F fc) asegs R PT_SKIP m ro HR HK 20%nat [PT_H2; PT_EXIT] (SCR [false] [] []) 36%N.
      { split_scs. apply BR; [lia | evs; rewrite TablLib.zbv_add; reflexivity]. }
      replace (i + 1 =? n) with false by (symmetry; apply Z.eqb_neq; exact X).
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KR2k R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR2k HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(sh ff + 4, sh ff + 5)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ES;
                                    cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]).
        apply Forall_nil. }
      assert (CL1 : rw_cells asegs M1 (sh ff + 4) [C1 (b8 4)]).
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia | exact WS4
        | reflexivity | exact I | first [reflexivity | evs; cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity]]. }
      rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 20%bv L20. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
      split.
      { unfold PTX. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)), (KK 16%bv ltac:(inb)), (KK 18%bv ltac:(inb)),
          (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)), (KK 23%bv ltac:(inb)), (KK 24%bv ltac:(inb)).
        rewrite L20, L26, L27.
        split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P16|]. split; [exact P18|].
        split; [rewrite !TablLib.zbv_add; f_equal; lia|].
        split; [exact P21|]. split; [exact P22|]. split; [exact P23|]. split; [exact P24|].
        split; [|reflexivity].
        rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
        f_equal. unfold SHBASE in QS. lia. }
      split; [rewrite L10, TablLib.zbv_add; reflexivity|].
      split; [intros _; rewrite L11; first [reflexivity | evs; reflexivity]|].
      split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
      split; [exact MU1|].
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      exact CL1.
  Qed.

  Definition KR1a : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 19; 20; 21; 22; 25; 26; 28; 29; 30; 31]%bv.

  Lemma pt_r1a : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i p t k : Z),
    PTH R SP S1 ff ps v n i -> 0 <= i -> i + 1 <= n -> n <= 48 ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> wr_at asegs m (ff + 32) 4 ->
    0 <= ps -> ps + 16 <= 2 ^ 47 -> ps mod 8 = 0 -> rw_cells asegs m ps [C8 (Z_to_bv 64 p)] -> sh0 m ps ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh ps))] ->
    0x10000 <= p -> p + 4 * n <= 0x91000 -> p mod 4 = 0 ->
    cell4 ASEGS m (p + 4 * (n - 1 - i)) t -> 0 <= t < 2 ^ 31 ->
    LbB_Kit.shk m (p + 4 * (n - 1 - i)) k -> (k = 0 \/ ((p + 4 * (n - 1 - i)) mod 8 = 0 /\ 4 <= k < 8)) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_H2) fc None m ro) (MS R' F (Z_to_bv 64 PT_Z) fc None M' ro)
      /\ PTX R' SP S1 ff ps v n i /\ getr R' 10 = Z_to_bv 64 t /\ kept_in KPT R R'
      /\ munch [(ff + 32, ff + 36)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' (ff + 32) [C4 (Z_to_bv 64 t)].
  Proof.
    intros R F fc m ro SP S1 ff ps v n i p t k [P [P10 P11]] I0 I1 N48 F64 FLO FHI WL PS0 PS1 PS8 CP SHP S45 SS SPH C48 PL PH P4 CE TR SK KC.
    pose proof P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    set (a := p + 4 * (n - 1 - i)) in *.
    pose (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 ps; Z_to_bv 64 p; Z_to_bv 64 (ff / 64); Z_to_bv 64 t; Z_to_bv 64 k]).
    set (SR0 := srs sr_id [(10%bv, EVar 32); (27%bv, EVar 33); (24%bv, EVar 34);
                           (11%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 34) (ELit 3)) (ELit 2147450880)); (18%bv, ELit 2147450880);
                           (23%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 36)) (ELit 32))]).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs.
      - exact P10.
      - exact P27.
      - exact P24.
      - rewrite P11, sh_word by lia. reflexivity.
      - exact P18.
      - rewrite P23, Q, TablLib.zbv_add. reflexivity. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 36))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    set (EL := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4)) (EVar 32)) (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (EVar 35))) (ELit (-4))).
    assert (ELV : edenot E EL = Z_to_bv 64 a).
    { subst EL a. evs. rewrite !TablLib.zbv_mul, !TablLib.zbv_add. f_equal. lia. }
    assert (HK : know_ok asegs E m
          [ KWord (SA (EVar 34) 0) 8 (EVar 35);
            KWord (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) 2147450880) 1 (ELit 0);
            KWord (SA (EAlu ALU_SRL EL (ELit 3)) 2147450880) 1 (EVar 38);
            KWr (SA (EMd M_MUL (ELit 64) (EVar 36)) 32) (ELit 4);
            KRange (EVar 32) 0 47; KRange (EVar 33) 1 48; KRange (EVar 34) 0 (2 ^ 47 - 16);
            KRange (EVar 35) 0x10000 0x91000; KAlign (EVar 35) 4; KRange (EVar 36) (0x6e8000 / 64) (2 ^ 41);
            KRange (EVar 38) 0 7; KWord (SA (EVar 9) 48) 8 (ELit (2 ^ 61)); KRange (EVar 37) 0 (2 ^ 31 - 1);
            KRange (EVar 9) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m ps _ 0%nat (C8 (Z_to_bv 64 p))); [exact CP | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ ps); [evs; reflexivity | lia | exact SHP]. }
      apply Forall_cons. { eapply (kshadow _ _ _ a k); [exact ELV | subst a; lia | destruct KC; lia | evs; reflexivity | exact SK]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WL | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact P4]|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (destruct KC; lia); destruct KC; lia|].
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 0%nat (C8 (Z_to_bv 64 (2 ^ 61)))); [exact C48 | reflexivity | reflexivity | lia
          | unfold estart; evs; change (getr R (Z_to_bv 5 (Z.of_N 9))) with (getr R 9%bv); rewrite P9, u64_of_Z by lia; cbn [a_off]; lia
          | lia | lia | evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; change (getr R (Z_to_bv 5 (Z.of_N 9))) with (getr R 9%bv); rewrite P9, u64_of_Z by lia; lia|].
      apply Forall_nil. }
    set (EB0 := EAlu ALU_ADD (EMd M_MUL (ELit (-4)) (EVar 32)) (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (EVar 35))).
    assert (EBV : edenot E EB0 = Z_to_bv 64 (a + 4)).
    { subst EB0 a. evs. rewrite !TablLib.zbv_mul, !TablLib.zbv_add. f_equal. lia. }
    assert (RD : sc_denot asegs m E (SCReadBase (SA EB0 (-4)) 4 true (EVar 37))).
    { eapply (sc_read_cell4_sx asegs _ _ _ _ _ _ CE); [| evs; rewrite TablLib.sxw_small by lia; reflexivity].
      unfold adenot. cbn [a_base a_off]. rewrite EBV. rewrite v_addi_Z by (subst a; lia). f_equal. lia. }
    assert (EF0 : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 36))) + 32 = ff + 32) by (rewrite EF; reflexivity).
    assert (LTU : sc_denot asegs m E (SCBr false BC_LTU EL (EVar 35))).
    { cbn [sc_denot]. rewrite ELV. evs. rewrite br_ltu by (subst a; lia). apply Z.ltb_ge. subst a; lia. }
    destruct KC as [K0|(KA & K1)].
    - subst k. xrun_at (PropExec.mkFP F fc) asegs R PT_H2 m ro HR HK 40%nat [PT_Z] (SCR [false; false] [EVar 37] []) 39%N.
      { split_scs; [exact RD | cbn [sc_denot]; evs; rewrite br_ne by lia; reflexivity | exact LTU]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KR1a R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR1a HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(ff + 32, ff + 36)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite EF;
                            cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]. }
      assert (CL1 : rw_cells asegs M1 (ff + 32) [C4 (Z_to_bv 64 t)]).
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; cbn [a_base a_off]; exact EF0 | exact WL | reflexivity | exact I | evs; reflexivity]. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (SK1 : forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi) by (intros lo hi S; subst M1; apply stk_mem_denot; exact S).
      rreg HR' 10%bv L10. rreg HR' 18%bv L18. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 27%bv L27.
      split.
      { unfold PTX. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)), (KK 16%bv ltac:(inb)), (KK 20%bv ltac:(inb)),
          (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)), (KK 26%bv ltac:(inb)).
        rewrite L18, L23, L24, L27.
        split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P16|]. split; [reflexivity|].
        split; [exact P20|]. split; [exact P21|]. split; [exact P22|].
        split; [rewrite Q, TablLib.zbv_add; reflexivity|]. split; [reflexivity|]. split; [exact P26|].
        reflexivity. }
      split; [exact L10|].
      split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact SK1|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      exact CL1.
    - assert (SL : sc_denot asegs m E (SCBr true BC_LT (EAlu ALU_ADD (EAlu ALU_AND EL (ELit 7)) (ELit 3)) (EVar 38))).
      { cbn [sc_denot].
        change (edenot E (EAlu ALU_ADD (EAlu ALU_AND EL (ELit 7)) (ELit 3)))
          with (alu64 ALU_ADD (alu64 ALU_AND (edenot E EL) (Z_to_bv 64 7)) (Z_to_bv 64 3)).
        rewrite ELV, land7_val by (subst a; lia). rewrite KA. rewrite TablLib.zbv_add.
        evs. rewrite br_lts_small by lia. apply Z.ltb_lt. lia. }
      assert (SN : sc_denot asegs m E (SCBr true BC_NE (EVar 38) (ELit 0))).
      { cbn [sc_denot]. evs. rewrite br_ne by lia. apply negb_true_iff, Z.eqb_neq. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R PT_H2 m ro HR HK 40%nat [PT_Z] (SCR [false; true; true] [EVar 37] []) 39%N.
      { split_scs; first [exact RD | exact SL | exact SN | exact LTU]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KR1a R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR1a HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(ff + 32, ff + 36)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite EF;
                            cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]. }
      assert (CL1 : rw_cells asegs M1 (ff + 32) [C4 (Z_to_bv 64 t)]).
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; cbn [a_base a_off]; exact EF0 | exact WL | reflexivity | exact I | evs; reflexivity]. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (SK1 : forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi) by (intros lo hi S; subst M1; apply stk_mem_denot; exact S).
      rreg HR' 10%bv L10. rreg HR' 18%bv L18. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 27%bv L27.
      split.
      { unfold PTX. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)), (KK 16%bv ltac:(inb)), (KK 20%bv ltac:(inb)),
          (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)), (KK 26%bv ltac:(inb)).
        rewrite L18, L23, L24, L27.
        split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P16|]. split; [reflexivity|].
        split; [exact P20|]. split; [exact P21|]. split; [exact P22|].
        split; [rewrite Q, TablLib.zbv_add; reflexivity|]. split; [reflexivity|]. split; [exact P26|].
        reflexivity. }
      split; [exact L10|].
      split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact SK1|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      exact CL1.
  Qed.

  Lemma pt_r1z : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i : Z),
    PTX R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 0 ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_Z) fc None m ro) (MS R' F (Z_to_bv 64 PT_SKIP) fc None m ro)
      /\ PTX R' SP S1 ff ps v n i /\ getr R' 10 = Z_to_bv 64 (-8) /\ kept_in KPT R R'.
  Proof.
    intros R F fc m ro SP S1 ff ps v n i P P10.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs. exact P10. }
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R PT_Z m ro HR HK 4%nat [PT_SKIP] (SCR [] [] []) 32%N.
    { first [apply Forall_nil | split_scs]. }
    exists R'. split; [exact Hms|].
    assert (KK : kept_in [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv R R')
      by (intros rr Hrr; eapply (syms_id_sound R _ _ R' _ HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    rreg HR' 10%bv L10.
    split; [exact (PTX_kept R R' SP S1 ff ps v n i _ P KK ltac:(vm_cast_no_check (@eq_refl bool true)))|].
    split; [rewrite L10; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
    eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)].
  Qed.

  Definition PTC (R : bvmap 5 word) (SP S1 ff ps v n i : Z) : Prop :=
    getr R 2 = Z_to_bv 64 S1 /\ getr R 8 = Z_to_bv 64 SP /\ getr R 9 = Z_to_bv 64 S1
    /\ getr R 18 = Z_to_bv 64 0x7fff8000 /\ getr R 19 = Z_to_bv 64 ps /\ getr R 20 = Z_to_bv 64 (i + 1)
    /\ getr R 21 = Z_to_bv 64 (v + 8) /\ getr R 22 = Z_to_bv 64 (sh (v + 8)) /\ getr R 23 = Z_to_bv 64 (ff + 32)
    /\ getr R 26 = Z_to_bv 64 (sh ff) /\ getr R 27 = Z_to_bv 64 n.

  Definition PTCREGS : list reg := [2; 8; 9; 18; 19; 20; 21; 22; 23; 26; 27]%bv.

  Lemma pt_kword_of_fld : forall E M (a : saddr) (e : expr) (k : nat) (p x : Z),
    fld ASEGS M p k x -> (k <= 8)%nat -> estart E a = p -> 0 <= p -> p + Z.of_nat k < 2 ^ 64 -> edenot E e = Z_to_bv 64 x ->
    kentry_ok ASEGS E M (KWord a k e).
  Proof.
    intros E M a e k p x HF Hk Ha Hp Hpk He. cbn [kentry_ok]. split; [exact Hk|]. split.
    - unfold SymExec3Sound.SX2S.flat. rewrite Ha. lia.
    - unfold fld in HF. rewrite He. rewrite <- HF. f_equal.
      apply bv_eq. rewrite (flat_u E a (Z.of_nat k)) by (unfold SymExec3Sound.SX2S.flat; rewrite Ha; lia). rewrite Ha, u64_of_Z by lia. reflexivity.
  Qed.

  Definition pt_kn1b (bl : Z) : list kentry :=
    [ KWord (SA (EVar 37) 16) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EVar 35) (ELit 3)) (ELit 2147450880));
      KWord (SA (EVar 37) 24) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 16)) (ELit 3)) (ELit 2147450880));
      KWord (SA (EVar 37) 32) 8 (EAlu ALU_ADD (EVar 35) (ELit 16));
      KWord (SA (EVar 35) 0) 8 (EVar 38); KWord (SA (EVar 35) 8) 8 (EVar 39); KWord (SA (EVar 35) 16) 8 (EVar 40);
      KWord (SA (EAlu ALU_SRL (EVar 35) (ELit 3)) 2147450880) 1 (ELit 0);
      KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
      KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 16)) (ELit 3)) 2147450880) 1 (ELit 0);
      KRange (EVar 41) 1 (2 ^ 31 - 1); KRange (EVar 38) bl (2 ^ 47); KRange (EVar 39) bl (2 ^ 47); KRange (EVar 40) 0 (2 ^ 47);
      KRange (EVar 35) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 37) (2 ^ 45) (2 ^ 47) ].
  Definition pt_sr1b : list expr :=
    srs sr_id [(9%bv, EVar 37); (10%bv, EVar 41); (16%bv, EVar 35); (21%bv, EAlu ALU_ADD (EVar 35) (ELit 8));
               (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 35) (ELit 8)) (ELit 3)) (ELit 2147450880))].

  Lemma pt_kn1b_ok : forall (R : bvmap 5 word) (m : mem) (SP S1 ff ps v n i t bi e c bl : Z),
    PTX R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 t -> 0 < t < 2 ^ 31 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> 0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 ->
    rw_cells asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh v)); C8 (Z_to_bv 64 (sh (v + 16))); C8 (Z_to_bv 64 (v + 16))] ->
    fldA m v 8 bi -> fldA m (v + 8) 8 e -> fldA m (v + 16) 8 c -> gz m v 24 ->
    0 <= bl -> bl <= bi <= 2 ^ 47 -> bl <= e <= 2 ^ 47 -> 0 <= c <= 2 ^ 47 ->
    regs_ok (Eseed R [Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 (ff / 64); Z_to_bv 64 S1;
                      Z_to_bv 64 bi; Z_to_bv 64 e; Z_to_bv 64 c; Z_to_bv 64 t]) pt_sr1b R
    /\ know_ok asegs (Eseed R [Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 (ff / 64); Z_to_bv 64 S1;
                      Z_to_bv 64 bi; Z_to_bv 64 e; Z_to_bv 64 c; Z_to_bv 64 t]) m (pt_kn1b bl).
  Proof.
    intros R m SP S1 ff ps v n i t bi e c bl P P10 T0 S45 SS SPH V0 V24 V8 C16 F0 F8 F16 GZ BL0 BL E0 C0.
    pose proof P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
    set (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 (ff / 64); Z_to_bv 64 S1;
                      Z_to_bv 64 bi; Z_to_bv 64 e; Z_to_bv 64 c; Z_to_bv 64 t]).
    split.
    { unfold pt_sr1b. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs.
      - exact P9.
      - exact P10.
      - exact P16.
      - rewrite P21, TablLib.zbv_add. reflexivity.
      - rewrite P22, TablLib.zbv_add, sh_word by lia. reflexivity. }
    assert (ES1 : forall o, estart E (SA (EVar 37) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EV : forall o, estart E (SA (EVar 35) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (G0 : sh0 m v) by (replace v with (v + 0) by lia; apply GZ; lia).
    assert (G8 : sh0 m (v + 8)) by (apply GZ; lia).
    assert (G16 : sh0 m (v + 16)) by (apply GZ; lia).
    unfold pt_kn1b, know_ok.
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 (sh v)))); [exact C16 | reflexivity | reflexivity | lia
        | rewrite ES1; lia | lia | lia | subst E; evs; rewrite sh_word by lia; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 8%nat (C8 (Z_to_bv 64 (sh (v + 16))))); [exact C16 | reflexivity | reflexivity | lia
        | rewrite ES1; cbn; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add, sh_word by lia; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 16%nat (C8 (Z_to_bv 64 (v + 16)))); [exact C16 | reflexivity | reflexivity | lia
        | rewrite ES1; cbn; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
    apply Forall_cons. { eapply (pt_kword_of_fld E m _ _ 8%nat); [exact F0 | lia | rewrite EV; lia | lia | cbn; lia | subst E; evs; reflexivity]. }
    apply Forall_cons. { eapply (pt_kword_of_fld E m _ _ 8%nat); [exact F8 | lia | rewrite EV; lia | lia | cbn; lia | subst E; evs; reflexivity]. }
    apply Forall_cons. { eapply (pt_kword_of_fld E m _ _ 8%nat); [exact F16 | lia | rewrite EV; lia | lia | cbn; lia | subst E; evs; reflexivity]. }
    apply Forall_cons. { eapply (kshadow0 _ _ _ v); [subst E; evs; reflexivity | lia | exact G0]. }
    apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact G8]. }
    apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 16)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact G16]. }
    do 6 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
    apply Forall_nil.
  Qed.

  Definition KR1b : list reg := [2; 3; 4; 5; 6; 7; 8; 14; 15; 17; 18; 20; 23; 26; 27; 28; 29; 30; 31]%bv.

  Lemma pt_r1f : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i t bi e c : Z),
    PTX R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 t -> 0 < t < 2 ^ 31 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> 0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 ->
    rw_cells asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh v)); C8 (Z_to_bv 64 (sh (v + 16))); C8 (Z_to_bv 64 (v + 16))] ->
    fldA m v 8 bi -> fldA m (v + 8) 8 e -> fldA m (v + 16) 8 c -> gz m v 24 ->
    16 <= bi -> bi <= e -> e < c -> c <= 2 ^ 47 ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_Z) fc None m ro) (MS R' F (Z_to_bv 64 AANNOTATE_CC) fc None m ro)
      /\ PTC R' SP S1 ff ps v n i /\ kept_in [3; 4]%bv R R'
      /\ getr R' 1 = Z_to_bv 64 PT_AN_RET /\ getr R' 10 = Z_to_bv 64 bi /\ getr R' 11 = Z_to_bv 64 c
      /\ getr R' 12 = Z_to_bv 64 e /\ getr R' 13 = Z_to_bv 64 (e + 4) /\ getr R' 24 = Z_to_bv 64 (e + 4) /\ getr R' 25 = Z_to_bv 64 e.
  Proof.
    intros R F fc m ro SP S1 ff ps v n i t bi e c P P10 T0 S45 SS SPH V0 V24 V8 C16 F0 F8 F16 GZ B16 BE EC CH.
    destruct (pt_kn1b_ok R m SP S1 ff ps v n i t bi e c 16 P P10 T0 S45 SS SPH V0 V24 V8 C16 F0 F8 F16 GZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as [HR HK].
    set (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 (ff / 64); Z_to_bv 64 S1;
                      Z_to_bv 64 bi; Z_to_bv 64 e; Z_to_bv 64 c; Z_to_bv 64 t]) in HR, HK.
    xrun_at (PropExec.mkFP F fc) asegs R PT_Z m ro HR HK 40%nat [AANNOTATE_CC; 0x100040] (SCR [false; false] [] []) 42%N.
    { split_scs; cbn [sc_denot]; subst E; evs; [rewrite br_ltu by lia | rewrite br_geu by lia]; bool_lia. }
    exists R'. split; [exact Hms|].
    assert (KK : kept_in KR1b R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR1b HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12. rreg HR' 13%bv L13.
    rreg HR' 19%bv L19. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    pose proof P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
    split.
    { unfold PTC. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 18%bv ltac:(inb)), (KK 20%bv ltac:(inb)),
        (KK 23%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      rewrite L9, L19, L21, L22.
      split; [exact P2|]. split; [exact P8|]. split; [reflexivity|]. split; [exact P18|]. split; [exact P24|].
      split; [exact P20|]. split; [rewrite TablLib.zbv_add; reflexivity|].
      split; [rewrite TablLib.zbv_add, sh_word by lia; reflexivity|].
      split; [exact P23|]. split; [exact P26 | exact P27]. }
    split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
    rewrite L1, L10, L11, L12, L13, L24, L25. rewrite !TablLib.zbv_add.
    repeat (split; [reflexivity|]). reflexivity.
  Qed.

  Lemma pt_r1s : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i t bi e c : Z),
    PTX R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 t -> 0 < t < 2 ^ 31 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> 0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 ->
    rw_cells asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh v)); C8 (Z_to_bv 64 (sh (v + 16))); C8 (Z_to_bv 64 (v + 16))] ->
    fldA m v 8 bi -> fldA m (v + 8) 8 e -> fldA m (v + 16) 8 c -> gz m v 24 ->
    0 <= bi <= 2 ^ 47 -> 0 <= e <= 2 ^ 47 -> c <= e -> 0 <= c ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_Z) fc None m ro) (MS R' F (Z_to_bv 64 0x100040) fc None m ro)
      /\ PTC R' SP S1 ff ps v n i /\ kept_in [3; 4]%bv R R'
      /\ getr R' 1 = Z_to_bv 64 PT_SL_RET /\ getr R' 10 = Z_to_bv 64 v /\ getr R' 11 = Z_to_bv 64 (ff + 32).
  Proof.
    intros R F fc m ro SP S1 ff ps v n i t bi e c P P10 T0 S45 SS SPH V0 V24 V8 C16 F0 F8 F16 GZ B0 E0 CE C0.
    destruct (pt_kn1b_ok R m SP S1 ff ps v n i t bi e c 0 P P10 T0 S45 SS SPH V0 V24 V8 C16 F0 F8 F16 GZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as [HR HK].
    set (E := Eseed R [Z_to_bv 64 i; Z_to_bv 64 n; Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 (ff / 64); Z_to_bv 64 S1;
                      Z_to_bv 64 bi; Z_to_bv 64 e; Z_to_bv 64 c; Z_to_bv 64 t]) in HR, HK.
    xrun_at (PropExec.mkFP F fc) asegs R PT_Z m ro HR HK 40%nat [AANNOTATE_CC; 0x100040] (SCR [true] [] []) 42%N.
    { split_scs. cbn [sc_denot]. subst E. evs. rewrite br_geu by lia. bool_lia. }
    exists R'. split; [exact Hms|].
    assert (KK : kept_in KR1b R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR1b HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 19%bv L19. rreg HR' 21%bv L21. rreg HR' 22%bv L22.
    pose proof P as (P2 & P8 & P9 & P16 & P18 & P20 & P21 & P22 & P23 & P24 & P26 & P27).
    split.
    { unfold PTC. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 18%bv ltac:(inb)), (KK 20%bv ltac:(inb)),
        (KK 23%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      rewrite L9, L19, L21, L22.
      split; [exact P2|]. split; [exact P8|]. split; [reflexivity|]. split; [exact P18|]. split; [exact P24|].
      split; [exact P20|]. split; [rewrite TablLib.zbv_add; reflexivity|].
      split; [rewrite TablLib.zbv_add, sh_word by lia; reflexivity|].
      split; [exact P23|]. split; [exact P26 | exact P27]. }
    split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
    rewrite L1, L10. split; [reflexivity|]. split; [reflexivity|].
    rewrite L11. exact P23.
  Qed.

  Definition KR2 : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 17; 18; 19; 22; 26; 27; 28; 29; 30; 31]%bv.

  Ltac pt_r2f_fin :=
    lazymatch goal with
    | Hlf : log_flat ?E ?lg, Hms : CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _), HR' : regs_ok ?E _ ?R',
      P : PTC ?R ?SP ?S1 ?ff ?ps ?v ?n ?i, EV : forall o, estart ?E (SA (EVar 33) o) = ?v + o, EE : estart ?E (SA (EVar 36) 0) = ?e,
      WE : wr_at asegs ?m ?e 4, WV : wr_at asegs ?m (?v + 8) 8, DJ : (?e + 4 <= ?v + 8 \/ ?v + 16 <= ?e),
      Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (?ff / 64)) = Z_to_bv 64 ?ff,
      CLx : rw_cells asegs ?m (?ff + 32) [C4 (Z_to_bv 64 ?t)] |- _ =>
      change mm with (mem_denot E m lg) in Hms;
      let M1 := fresh "M1" in set (M1 := mem_denot E m lg) in Hms;
      exists R', M1; split; [exact Hms|];
      let KK0 := fresh "KK0" in
      assert (KK0 : kept_in [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 17; 19; 20; 26; 27; 28; 29; 30; 31]%bv R R')
        by (intros rr Hrr; eapply (syms_id_sound R _ _ R' _ HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]);
      let MU1 := fresh "MU1" in
      assert (MU1 : munch [(e, e + 4); (v + 8, v + 16)] m M1)
        by (subst M1; apply munch_mem_denot; [exact Hlf|];
            apply Forall_cons; [cbn [e_addr e_width]; rewrite EV; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|];
            apply Forall_cons; [cbn [e_addr e_width]; rewrite EE; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|];
            apply Forall_nil);
      let CL1 := fresh "CL1" in
      assert (CL1 : rw_cells asegs M1 e [C4 (Z_to_bv 64 t)])
        by (subst M1; eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
              | apply Forall_cons; [cbn [e_addr e_width]; rewrite EV, EE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]
              | exact EE | exact WE | reflexivity | exact I | subst E; evs; reflexivity]);
      let CL2 := fresh "CL2" in
      assert (CL2 : rw_cells asegs M1 (v + 8) [C8 (Z_to_bv 64 (e + 4))])
        by (subst M1; eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
              | rewrite EV; reflexivity | exact WV | reflexivity | exact I | subst E; evs; rewrite TablLib.zbv_add; reflexivity]);
      let WM1 := fresh "WM1" in assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot);
      let SK1 := fresh "SK1" in
      assert (SK1 : forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi) by (intros lo hi S; subst M1; apply stk_mem_denot; exact S);
      let MI1 := fresh "MI1" in assert (MI1 : mem_inv asegs m -> mem_inv asegs M1) by (intros MI; exact (msteps_mem_inv asegs _ _ Hms MI));
      let L9 := fresh "L9" in let L10 := fresh "L10" in let L16 := fresh "L16" in let L18 := fresh "L18" in
      let L21 := fresh "L21" in let L22 := fresh "L22" in let L23 := fresh "L23" in let L24 := fresh "L24" in
      rreg HR' 9%bv L9; rreg HR' 10%bv L10; rreg HR' 16%bv L16; rreg HR' 18%bv L18;
      rreg HR' 21%bv L21; rreg HR' 22%bv L22; rreg HR' 23%bv L23; rreg HR' 24%bv L24;
      let P2 := fresh "P2" in let P8 := fresh "P8" in let P9 := fresh "P9" in let P18 := fresh "P18" in
      let P19 := fresh "P19" in let P20 := fresh "P20" in let P21 := fresh "P21" in let P22 := fresh "P22" in
      let P23 := fresh "P23" in let P26 := fresh "P26" in let P27 := fresh "P27" in
      destruct P as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P26 & P27);
      let KK := fresh "KK" in
      assert (KK : kept_in KR2 R R')
        by (intros rr Hrr; unfold KR2 in Hrr;
            repeat (destruct Hrr as [<-|Hrr]; [first [ apply KK0; apply inb_In; vm_compute; reflexivity | rewrite L18, P18; reflexivity
                                                    | rewrite L22, P22, TablLib.zbv_add, sh_word by lia; reflexivity ] |]);
            destruct Hrr);
      split;
      [ unfold PTX; rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK0 20%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb));
        rewrite L9, L16, L18, L21, L22, L23, L24;
        split; [exact P2|]; split; [exact P8|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
        split; [exact P20|]; split; [rewrite TablLib.zbv_add; reflexivity|];
        split; [rewrite TablLib.zbv_add, sh_word by lia; reflexivity|]; split; [rewrite Q, TablLib.zbv_add; reflexivity|];
        split; [exact P19|]; split; [exact P26 | exact P27]
      | split; [rewrite L10; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|];
        split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|];
        split; [exact MU1|]; split; [exact WM1|]; split; [exact SK1|]; split; [exact MI1|];
        split; [exact CL1 | exact CL2] ]
    end.

  Lemma pt_r2f : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i t e j : Z),
    PTC R SP S1 ff ps v n i -> getr R 24 = Z_to_bv 64 (e + 4) -> getr R 25 = Z_to_bv 64 e ->
    0 <= i -> i + 1 <= n -> n <= 48 -> ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> 0 <= ps -> ps + 16 <= 2 ^ 47 ->
    0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 -> 16 <= e -> e + 4 <= 2 ^ 47 -> e mod 4 = 0 ->
    rw_cells asegs m (S1 + 40) [C8 (Z_to_bv 64 v)] ->
    rw_cells asegs m (ff + 32) [C4 (Z_to_bv 64 t)] -> 0 < t < 2 ^ 31 ->
    LbB_Kit.shk m e j -> (j = 0 \/ (e mod 8 = 0 /\ 4 <= j < 8)) ->
    sh0 m (v + 8) -> wr_at asegs m e 4 -> wr_at asegs m (v + 8) 8 ->
    (e + 4 <= v + 8 \/ v + 16 <= e) -> (e + 4 <= sh (v + 8) \/ sh (v + 8) + 1 <= e) ->
    (v + 24 <= S1 \/ S1 + 192 <= v) -> (e + 4 <= S1 \/ S1 + 192 <= e) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_AN_RET) fc None m ro) (MS R' F (Z_to_bv 64 PT_SKIP) fc None M' ro)
      /\ PTX R' SP S1 ff ps v n i /\ getr R' 10 = Z_to_bv 64 (-8) /\ kept_in KPT R R'
      /\ munch [(e, e + 4); (v + 8, v + 16)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' e [C4 (Z_to_bv 64 t)] /\ rw_cells asegs M' (v + 8) [C8 (Z_to_bv 64 (e + 4))].
  Proof.
    intros R F fc m ro SP S1 ff ps v n i t e j P P24 P25 I0 I1 N48 F64 FLO FHI S45 SS SPH PS0 PS1 V0 V24 V8 E16 EH E4
      C40 CL T0 SJ JC S8 WE WV DJ DJS DV DE.
    pose proof P as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P26 & P27).
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    pose (E := Eseed R [Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 (ff / 64); Z_to_bv 64 S1; Z_to_bv 64 e; Z_to_bv 64 t; Z_to_bv 64 j]).
    set (SR0 := srs sr_id [(9%bv, EVar 35); (18%bv, ELit 2147450880);
                           (21%bv, EAlu ALU_ADD (EVar 33) (ELit 8));
                           (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit 2147450880));
                           (23%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 34)) (ELit 32));
                           (24%bv, EAlu ALU_ADD (EVar 36) (ELit 4)); (25%bv, EVar 36)]).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs.
      - exact P9.
      - exact P18.
      - rewrite P21, TablLib.zbv_add. reflexivity.
      - rewrite P22, TablLib.zbv_add, sh_word by lia. reflexivity.
      - rewrite P23, Q, TablLib.zbv_add. reflexivity.
      - rewrite P24, TablLib.zbv_add. reflexivity.
      - exact P25. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 34))) = ff) by (subst E; evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES1 : forall o, estart E (SA (EVar 35) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EV : forall o, estart E (SA (EVar 33) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EE : estart E (SA (EVar 36) 0) = e) by (unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK0 : know_ok asegs E m
          [ KWord (SA (EVar 35) 40) 8 (EVar 33);
            KWord (SA (EMd M_MUL (ELit 64) (EVar 34)) 32) 4 (EVar 37);
            KWord (SA (EAlu ALU_SRL (EVar 36) (ELit 3)) 2147450880) 1 (EVar 38);
            KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
            KWr (SA (EVar 36) 0) (ELit 4); KWr (SA (EVar 33) 8) (ELit 8);
            KRange (EVar 37) 1 (2 ^ 31 - 1); KRange (EVar 38) 0 7; KRange (EVar 36) 16 (2 ^ 47 - 4); KAlign (EVar 36) 4;
            KRange (EVar 33) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 35) (2 ^ 45) (2 ^ 47); KRange (EVar 34) (0x6e8000 / 64) (2 ^ 41);
            KDisj (SA (EVar 36) 0) (ELit 4) (SA (EVar 33) 8) (ELit 8);
            KDisj (SA (EVar 35) 40) (ELit 8) (SA (EVar 33) 8) (ELit 8); KDisj (SA (EVar 35) 40) (ELit 8) (SA (EVar 36) 0) (ELit 4) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (S1 + 40) _ 0%nat (C8 (Z_to_bv 64 v))); [exact C40 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (ff + 32) _ 0%nat (C4 (Z_to_bv 64 t))); [exact CL | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kshadow _ _ _ e j); [subst E; evs; reflexivity | lia | destruct JC; lia | subst E; evs; reflexivity | exact SJ]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact S8]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WE | rewrite EE; reflexivity | unfold elenZ; rewrite EE; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; reflexivity | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by (destruct JC; lia); destruct JC; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact E4]|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite EE, EV; subst E; evs; rewrite !u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite ES1, EV; subst E; evs; rewrite !u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite ES1, EE; subst E; evs; rewrite !u64_of_Z by lia; lia|].
      apply Forall_nil. }
    assert (SHV : estart E (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) 2147450880) = sh (v + 8)).
    { unfold estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
      rewrite u64_of_Z by (Z.div_mod_to_equations; lia). unfold sh. rewrite ASHADOW_BASE_val. change (2 ^ 3) with 8. lia. }
    assert (SD : sc_denot asegs m E (SCDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) 2147450880) (ELit 1) (SA (EVar 36) 0) (ELit 4))).
    { cbn [sc_denot]. unfold flat, elenZ. rewrite SHV, EE. cbn [edenot]. rewrite !u64_of_Z by lia.
      assert (0x7fff8000 <= sh (v + 8) < 2 ^ 45) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      lia. }
    destruct JC as [J0|(JA & J1)].
    - subst j. xrun_at (PropExec.mkFP F fc) asegs R PT_AN_RET m ro HR HK0 40%nat [PT_SKIP] (SCR [false] [] []) 39%N.
      { split_scs; [exact SD | cbn [sc_denot]; subst E; evs; rewrite br_ne by lia; reflexivity]. }
      pt_r2f_fin.
    - assert (SL : sc_denot asegs m E (SCBr true BC_LT (EAlu ALU_ADD (EAlu ALU_AND (EVar 36) (ELit 7)) (ELit 3)) (EVar 38))).
      { cbn [sc_denot]. subst E; evs. rewrite land7_val by lia. rewrite JA, TablLib.zbv_add. rewrite br_lts_small by lia. apply Z.ltb_lt. lia. }
      assert (SN : sc_denot asegs m E (SCBr true BC_NE (EVar 38) (ELit 0))).
      { cbn [sc_denot]. subst E; evs. rewrite br_ne by lia. apply negb_true_iff, Z.eqb_neq. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R PT_AN_RET m ro HR HK0 40%nat [PT_SKIP] (SCR [true; true] [] []) 39%N.
      { split_scs; first [exact SD | exact SL | exact SN]. }
      pt_r2f_fin.
  Qed.

  Definition KR2s : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 11; 12; 13; 14; 15; 17; 18; 20; 23; 25; 26; 27; 28; 29; 30; 31]%bv.

  Lemma pt_r2s : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (SP S1 ff ps v n i e' : Z),
    PTC R SP S1 ff ps v n i -> getr R 10 = Z_to_bv 64 e' -> 16 <= e' < 2 ^ 64 -> e' mod 4 = 0 ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> 0 <= ps -> ps + 16 <= 2 ^ 47 ->
    0x6e8000 <= v -> v + 24 <= 2 ^ 47 -> v mod 8 = 0 ->
    rw_cells asegs m (S1 + 40) [C8 (Z_to_bv 64 v)] ->
    sh0 m (v + 8) -> wr_at asegs m (v + 8) 8 -> (v + 24 <= S1 \/ S1 + 192 <= v) ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_SL_RET) fc None m ro) (MS R' F (Z_to_bv 64 PT_SKIP) fc None M' ro)
      /\ PTX R' SP S1 ff ps v n i /\ getr R' 10 = Z_to_bv 64 (-8) /\ kept_in KPT R R'
      /\ munch [(v + 8, v + 16)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' (v + 8) [C8 (Z_to_bv 64 e')].
  Proof.
    intros R F fc m ro SP S1 ff ps v n i e' P P10 E0 E4 S45 SS SPH PS0 PS1 V0 V24 V8 C40 S8 WV DJ.
    pose proof P as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P26 & P27).
    pose (E := Eseed R [Z_to_bv 64 ps; Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 e']).
    set (SR0 := srs sr_id [(9%bv, EVar 34); (10%bv, EVar 35); (19%bv, EVar 32); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 8));
                           (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit 2147450880))]).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs.
      - exact P9.
      - exact P10.
      - exact P19.
      - rewrite P21, TablLib.zbv_add. reflexivity.
      - rewrite P22, TablLib.zbv_add, sh_word by lia. reflexivity. }
    assert (ES1 : forall o, estart E (SA (EVar 34) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EV : forall o, estart E (SA (EVar 33) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK0 : know_ok asegs E m
          [ KWord (SA (EVar 34) 40) 8 (EVar 33);
            KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
            KWr (SA (EVar 33) 8) (ELit 8);
            KRange (EVar 33) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 34) (2 ^ 45) (2 ^ 47);
            KRange (EVar 35) 16 (2 ^ 64 - 1); KAlign (EVar 35) 4; KDisj (SA (EVar 34) 40) (ELit 8) (SA (EVar 33) 8) (ELit 8) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (S1 + 40) _ 0%nat (C8 (Z_to_bv 64 v))); [exact C40 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact S8]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; reflexivity | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact E4]|].
      apply Forall_cons; [cbn [kentry_ok]; rewrite ES1, EV; unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R PT_SL_RET m ro HR HK0 40%nat [PT_SKIP] (SCR [] [] []) 36%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (KK : kept_in KR2s R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KR2s HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    assert (MU1 : munch [(v + 8, v + 16)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      apply Forall_cons; [cbn [e_addr e_width]; rewrite EV; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply Forall_nil]. }
    assert (CL2 : rw_cells asegs M1 (v + 8) [C8 (Z_to_bv 64 e')]).
    { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | rewrite EV; reflexivity | exact WV | reflexivity | exact I | subst E; evs; reflexivity]. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (SK1 : forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi) by (intros lo hi S; subst M1; apply stk_mem_denot; exact S).
    assert (MI1 : mem_inv asegs m -> mem_inv asegs M1) by (intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)).
    rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 16%bv L16. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 24%bv L24.
    split.
    { unfold PTX. rewrite (KK 2%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 18%bv ltac:(inb)), (KK 20%bv ltac:(inb)),
        (KK 23%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      rewrite L9, L16, L21, L22, L24.
      split; [exact P2|]. split; [exact P8|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact P18|].
      split; [exact P20|]. split; [rewrite TablLib.zbv_add; reflexivity|].
      split; [rewrite TablLib.zbv_add, sh_word by lia; reflexivity|].
      split; [exact P23|]. split; [reflexivity|]. split; [exact P26 | exact P27]. }
    split; [rewrite L10; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
    split; [eapply kept_in_incl; [exact KK | vm_cast_no_check (@eq_refl bool true)]|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact SK1|]. split; [exact MI1|]. exact CL2.
  Qed.

End PT2.
