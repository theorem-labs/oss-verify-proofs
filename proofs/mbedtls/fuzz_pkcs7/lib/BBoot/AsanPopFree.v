(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound.
From Stdlib Require Import FunctionalExtensionality.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanPopFree () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "Corelib.Lists.ListDef.nth"; "Corelib.Init.Nat.add"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.mul"; "pf_bytes"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.list"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.regupd"; "Corelib.Init.Datatypes.S"; "pf_mem"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "Stdlib.ZArith.BinInt.Z.divide"; "Stdlib.ZArith.BinInt.Z.opp"].


(* [comment removed for export] *)
Definition PW0 : bv 32 := 0x00465713.  (* [comment removed for export] *)
Definition PW1 : bv 32 := 0xfff54793.  (* [comment removed for export] *)
Definition PW2 : bv 32 := 0x00150513.  (* [comment removed for export] *)
Definition PW3 : bv 32 := 0x00279793.  (* [comment removed for export] *)
Definition PW4 : bv 32 := 0x00f587b3.  (* [comment removed for export] *)
Definition PW5 : bv 32 := 0x00e7a023.  (* [comment removed for export] *)
Definition PW6 : bv 32 := 0x01560633.  (* [comment removed for export] *)
Definition PW7 : bv 32 := 0xff3562e3.  (* [comment removed for export] *)

Lemma PD0 : decode_any PW0 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z). Proof. vm_refl. Qed.
Lemma PD1 : decode_any PW1 = Some (OpImm ALU_XOR 15 10 4095, 4%Z). Proof. vm_refl. Qed.
Lemma PD2 : decode_any PW2 = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl. Qed.
Lemma PD3 : decode_any PW3 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z). Proof. vm_refl. Qed.
Lemma PD4 : decode_any PW4 = Some (Op ALU_ADD 15 11 15, 4%Z). Proof. vm_refl. Qed.
Lemma PD5 : decode_any PW5 = Some (Store SZ4 15 14 0, 4%Z). Proof. vm_refl. Qed.
Lemma PD6 : decode_any PW6 = Some (Op ALU_ADD 12 12 21, 4%Z). Proof. vm_refl. Qed.
Lemma PD7 : decode_any PW7 = Some (Branch BC_LTU 10 19 8164, 4%Z). Proof. vm_refl. Qed.

(* [comment removed for export] *)
Fixpoint pf_mem (mem : word -> option byte) (e c s i : Z) (k : nat) : word -> option byte :=
  match k with
  | O => mem
  | S k' => pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))))
                   e (c + s) s (i + 1) k'
  end.

(* [comment removed for export] *)
Fixpoint pf_bytes (c s : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => Z_to_le_bytes 4 ((c + Z.of_nat k' * s) / 16) ++ pf_bytes c s k'
  end.

Lemma pf_bytes_length : forall c s k, length (pf_bytes c s k) = (4 * k)%nat.
Proof. intros c s k. induction k as [|k IH]; cbn [pf_bytes length]; [reflexivity|]. rewrite length_app, length_Z_to_le_bytes, IH. lia. Qed.

Lemma pf_bytes_nth : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pc,$0.Ps,$0.Pk,$1.Pj,$0.Pt,$1.P,(2.(3.=R2.)(4.R2.(5.R3.)))P,(6.R2.#4.)(7.(8.&8.)(9.(8.&8.)(:.(;.(<.+4.R4.))R3.)(=.R7.R6.R5.)(>.&8.=))(9.(8.&8.)R3.(?.#4.(10.(11.R7.(<.(12.(12.(5.R5.)+1.)R4.)R6.))+10.))(>.&8.=)))")
(* [comment removed for export] *).
Proof.
  intros c s k. induction k as [|k IH]; intros j t Hj Ht; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite app_nth1 by (rewrite length_Z_to_le_bytes; lia). replace (Z.to_nat (4 * 0) + t)%nat with t by lia. f_equal. f_equal. f_equal. lia.
  - rewrite app_nth2 by (rewrite length_Z_to_le_bytes; lia). rewrite length_Z_to_le_bytes.
    replace (Z.to_nat (4 * j) + t - 4)%nat with (Z.to_nat (4 * (j - 1)) + t)%nat by lia.
    rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pf_bytes_cell : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pc,$0.Ps,$0.Pk,$1.Pj,$0.P,(2.(3.=R1.)(4.R1.(5.R2.)))(7.(13.(8.&8.))(14.(8.&8.)#4.(15.(8.&8.)(;.(<.+4.R2.))(=.R5.R4.R3.)))(?.#4.(10.(11.R5.(<.(12.(12.(5.R3.)+1.)R2.)R4.))+10.)))")
(* [comment removed for export] *).
Proof.
  intros c s k. induction k as [|k IH]; intros j Hj; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - replace (Z.to_nat (4 * 0)) with 0%nat by lia. rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). f_equal. f_equal. lia.
  - rewrite skipn_app, length_Z_to_le_bytes. rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
    replace (Z.to_nat (4 * j) - 4)%nat with (Z.to_nat (4 * (j - 1)))%nat by lia.
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition popfree_spec (SEGS : list Segment) (p : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pregs,(16.&5.(8.&40.))Pmem,P,(8.&40.)(17.(8.&8.))Pi,$0.Pe,$0.Pc,$0.Ps,$0.Pn,$0.P,(7.(8.&40.)(18.R7.(19.&5.+:.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R8.(19.&5.+;.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R9.(19.&5.+<.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R:.(19.&5.+15.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R;.(19.&5.+13.$1:.))(>.&40.R5.))P,(2.(3.=R:.)(4.R:.R6.))P,(2.(3.(<.+4.R7.)R:.)(4.R:.(1;.+2.+40.)))P,(3.=R:.)P,(3.=R:.)P,(4.(11.R<.(<.(12.R:.R>.)R;.))(1;.+2.+40.))P,(7.$1<.(1=.O2.R10.(>.&40.(12.R>.(<.+4.R;.)))(;.(<.+4.(12.R;.R?.))))$1>.)(1?.(16.&5.(8.&40.))Lregs',(16.&5.(8.&40.))(2.(20.O2.(21.$22.R13.(>.&40.O1.)R12.(23.O2.))(21.$22.R1.(>.&40.(11.O1.+20.))(24.R12.(>.&40.(12.R10.(<.+4.R=.)))(=.R?.R>.(;.(12.R=.R11.))))(23.O2.)))(2.(7.(8.&40.)(18.R1.(19.&5.+:.$1:.))(>.&40.R=.))(2.(7.(8.&40.)(18.R1.(19.&5.+<.$1:.))(>.&40.(11.R?.(<.(12.R=.R11.)R>.))))(2.(7.(8.&40.)(18.R1.(19.&5.+>.$1:.))(>.&40.(10.(11.R?.(<.(12.(12.R=.R11.)+1.)R>.))+10.)))(2.(7.(8.&40.)(18.R1.(19.&5.+?.$1:.))(>.&40.(12.R10.(<.+4.R=.))))Pr,(8.&5.)P,(25.(7.(8.&5.)R1.(19.&5.+:.$1:.)))P,(25.(7.(8.&5.)R2.(19.&5.+<.$1:.)))P,(25.(7.(8.&5.)R3.(19.&5.+>.$1:.)))P,(25.(7.(8.&5.)R4.(19.&5.+?.$1:.)))(7.(8.&40.)(18.R6.R5.)(18.R18.R5.))))))))")
(* [comment removed for export] *).

Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.                       (* [comment removed for export] *)
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.

(* [comment removed for export] *)
Definition iter_regs (regs : bvmap 5 word) (i e c s : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "(26.(26.(26.(26.O5.(19.&5.+>.$1:.)(>.&40.(10.O2.+10.)))(19.&5.+:.$1:.)(>.&40.(11.O4.+1.)))(19.&5.+?.$1:.)(>.&40.(12.O3.(<.+4.(11.O4.+1.)))))(19.&5.+<.$1:.)(>.&40.(11.O2.O1.)))")
(* [comment removed for export] *).

Ltac red_if :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (if bv_eqb a b then x else y) with x
      | false => change (if bv_eqb a b then x else y) with y
      end
  end.

#[using="Type"] Lemma u64_of_Z : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

#[using="Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7"] Lemma pf_iter : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i + 1 <= n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + s < 2 ^ 64)%Z ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (if (i + 1 <? n)%Z then p else p + 32))
                      (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
    /\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 e /\ getr regs' 12 = Z_to_bv 64 (c + s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 (c / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hok.
  destruct Hp as [Hp0 Hp1].
  (* [comment removed for export] *)
  assert (V14 : v_srli (Z_to_bv 64 c) (bv_unsigned (4 : bv 6)) = Z_to_bv 64 (c / 16)).
  { unfold v_srli. rewrite u64_of_Z by lia. change (bv_unsigned (4 : bv 6)) with 4%Z.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (V15a : v_xori (Z_to_bv 64 i) (bv_signed (4095 : bv 12)) = Z_to_bv 64 (2 ^ 64 - 1 - i)).
  { unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (bv_signed (4095 : bv 12))) with (2 ^ 64 - 1)%Z.
    rewrite AX2S.lxor_ones64 by lia. reflexivity. }
  assert (V10 : v_addi (Z_to_bv 64 i) (bv_signed (1 : bv 12)) = Z_to_bv 64 (i + 1)).
  { change (bv_signed (1 : bv 12)) with 1%Z. apply v_addi_lit. }
  assert (V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) (bv_unsigned (2 : bv 6)) = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)).
  { unfold v_slli. rewrite u64_of_Z by lia. change (bv_unsigned (2 : bv 6)) with 2%Z.
    rewrite Z.shiftl_mul_pow2 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal. lia. }
  assert (V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { unfold v_add. rewrite u64_of_Z by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    rewrite Z.add_mod_idemp_r by lia.
    replace (e + (2 ^ 66 - 4 - 4 * i))%Z with ((e - 4 * (i + 1)) + 4 * 2 ^ 64)%Z by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) (bv_signed (0 : bv 12)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_lit. f_equal. lia. }
  assert (V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s)).
  { unfold v_add. rewrite !u64_of_Z by lia. reflexivity. }
  eexists. split.
  - eapply mst_step; [reflexivity | eapply (step_srli segs); [exact HF0 | reflexivity | exact PD0] |].
    red_if. rewrite v_addi_lit, H12, V14.
    eapply mst_step; [reflexivity | eapply (step_xori segs); [exact HF1 | reflexivity | exact PD1] |].
    red_if. rewrite v_addi_lit. replace (p + 4 + 4)%Z with (p + 8)%Z by lia. gr. rewrite H10, V15a.
    eapply mst_step; [reflexivity | eapply (step_addi segs); [exact HF2 | reflexivity | exact PD2] |].
    red_if. rewrite v_addi_lit. replace (p + 8 + 4)%Z with (p + 12)%Z by lia. gr. rewrite H10, V10.
    eapply mst_step; [reflexivity | eapply (step_slli segs); [exact HF3 | reflexivity | exact PD3] |].
    red_if. rewrite v_addi_lit. replace (p + 12 + 4)%Z with (p + 16)%Z by lia. gr. rewrite V15b.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF4 | reflexivity | exact PD4] |].
    red_if. rewrite v_addi_lit. replace (p + 16 + 4)%Z with (p + 20)%Z by lia. gr. rewrite H11, V15c.
    eapply mst_step; [reflexivity | eapply (step_sw_val segs); [exact HF5 | reflexivity | exact PD5 | gr; rewrite Vst; exact Hok] |].
    rewrite v_addi_lit. replace (p + 20 + 4)%Z with (p + 24)%Z by lia. gr. rewrite Vst.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF6 | reflexivity | exact PD6] |].
    red_if. rewrite v_addi_lit. replace (p + 24 + 4)%Z with (p + 28)%Z by lia. gr. rewrite H12, H21, V12.
    destruct (Z.ltb (i + 1) n) eqn:Hlt.
    + eapply mst_step; [reflexivity | eapply (step_bltu_tk segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite btgt_lit. change (bv_signed (8164 : bv 13)) with (-28)%Z.
      replace (p + 28 + -28)%Z with p by lia. apply mst_refl.
    + eapply mst_step; [reflexivity | eapply (step_bltu_ft segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite v_addi_lit. replace (p + 28 + 4)%Z with (p + 32)%Z by lia. apply mst_refl.
  - gr. rewrite H11, H21, H19.
    repeat (split; [reflexivity|]).
    intros r Hr10 Hr12 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.

#[using="Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7"] Lemma pf_loop : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pk,$1.Pregs,(16.&5.(8.&40.))Pmem,P,(8.&40.)(17.(8.&8.))Prom,P,(8.&40.)(17.(8.&8.))Pi,$0.Pe,$0.Pc,$0.Ps,$0.Pn,$0.P,(7.$0.R1.(11.R5.(5.(27.R9.))))P,(7.(8.&40.)(18.R9.(19.&5.+:.$1:.))(>.&40.R6.))P,(7.(8.&40.)(18.R:.(19.&5.+;.$1:.))(>.&40.R6.))P,(7.(8.&40.)(18.R;.(19.&5.+<.$1:.))(>.&40.R6.))P,(7.(8.&40.)(18.R<.(19.&5.+15.$1:.))(>.&40.R6.))P,(7.(8.&40.)(18.R=.(19.&5.+13.$1:.))(>.&40.R6.))P,(3.=R;.)P,(3.(<.+4.R8.)R;.)P,(4.R<.(1;.+2.+40.))P,(3.=R<.)P,(3.=R<.)P,(4.(11.R>.(<.(5.(27.R14.))R=.))(1;.+2.+40.))P,Pj,$0.P,(2.(3.R12.R1.)(4.R1.R>.))(7.$1<.(1=.Vsegs,R15.(>.&40.(12.R12.(<.+4.(11.R2.+1.))))#4.)$1>.)(1?.(16.&5.(8.&40.))Lregs',(16.&5.(8.&40.))(2.(20.Vsegs,(21.$22.R16.(>.&40.Vp,)R15.R14.)(21.$22.R1.(>.&40.(11.Vp,+20.))(28.R15.R12.R11.R10.R13.(27.R17.))R14.))(2.(7.(8.&40.)(18.R1.(19.&5.+:.$1:.))(>.&40.R?.))(2.(7.(8.&40.)(18.R1.(19.&5.+;.$1:.))(>.&40.R12.))(2.(7.(8.&40.)(18.R1.(19.&5.+<.$1:.))(>.&40.(11.R11.(<.(5.(27.R17.))R10.))))(2.(7.(8.&40.)(18.R1.(19.&5.+15.$1:.))(>.&40.R10.))(2.(7.(8.&40.)(18.R1.(19.&5.+13.$1:.))(>.&40.R?.))(2.(7.(8.&40.)(18.R1.(19.&5.+>.$1:.))(>.&40.(10.(11.R11.(<.(5.R17.)R10.))+10.)))(2.(7.(8.&40.)(18.R1.(19.&5.+?.$1:.))(>.&40.(12.R12.(<.+4.R?.))))Pr,(8.&5.)P,(25.(7.(8.&5.)R1.(19.&5.+:.$1:.)))P,(25.(7.(8.&5.)R2.(19.&5.+<.$1:.)))P,(25.(7.(8.&5.)R3.(19.&5.+>.$1:.)))P,(25.(7.(8.&5.)R4.(19.&5.+?.$1:.)))(7.(8.&40.)(18.R6.R5.)(18.R1;.R5.)))))))))))")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok.
  - (* [comment removed for export] *)
    change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
    cbn [pf_mem].
    split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
    repeat (split; [reflexivity|]). exact Rothers.
  - (* [comment removed for export] *)
    rewrite Nat2Z.inj_succ in Hn, Hcs |- *. rewrite Nat2Z.inj_succ in Hcs |- *.
    assert (Hks : (0 <= Z.of_nat k * s)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs1 & Hms1 & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    destruct (Z.ltb_spec (i + 1) n); [|lia].
    destruct (IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
                 (i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
                 ltac:(rewrite Nat2Z.inj_succ; lia))
      as (regs2 & Hms2 & S10 & S11 & S12 & S21 & S19 & S14 & S15 & Sothers).
    { intros j Hj. eapply store_ok_mono; [apply wbytes_grows | apply Hok; lia]. }
    exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    rewrite S10, S11, S12, S21, S19, S14, S15.
    split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; f_equal; lia|]. split; [reflexivity|].
    intros r A B C D. rewrite (Sothers r A B C D). apply Rothers; assumption.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma pf_wbytes_inside : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pbs,(13.(8.&8.))Pm,P,(8.&40.)(17.(8.&8.))Pa,(8.&40.)Px,(8.&40.)P,(3.(11.(29.&40.R2.)(5.(2:.(8.&8.)R4.)))(1;.+2.+40.))P,(2.(3.(29.&40.R3.)(29.&40.R2.))(4.(29.&40.R2.)(11.(29.&40.R3.)(5.(2:.(8.&8.)R5.)))))(7.(17.(8.&8.))(24.R5.R4.R6.R3.)(2;.(8.&8.)(9.(8.&8.)(;.(12.(29.&40.R3.)(29.&40.R4.)))R6.(>.&8.=))))")
(* [comment removed for export] *).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

#[using="Type"] Lemma pf_wbytes_outside : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pbs,(13.(8.&8.))Pm,P,(8.&40.)(17.(8.&8.))Pa,(8.&40.)Px,(8.&40.)P,(3.(11.(29.&40.R2.)(5.(2:.(8.&8.)R4.)))(1;.+2.+40.))P,(2<.(4.(29.&40.R2.)(29.&40.R3.))(3.(11.(29.&40.R3.)(5.(2:.(8.&8.)R5.)))(29.&40.R2.)))(7.(17.(8.&8.))(24.R5.R4.R6.R3.)A1.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pf_mem_frame : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pk,$1.Pmem,P,(8.&40.)(17.(8.&8.))Pe,$0.Pc,$0.Ps,$0.Pi,$0.Pa,(8.&40.)P,(3.=R2.)P,(3.(<.+4.(11.R3.(5.R8.)))R6.)P,(4.R7.(1;.+2.+40.))P,(2<.(4.(29.&40.R4.)(12.R8.(<.+4.(11.R5.(5.R:.)))))(3.(12.R8.(<.+4.R5.))(29.&40.R4.)))(7.(17.(8.&8.))(28.R:.R9.R8.R7.R6.R;.R5.)A1.R:.R5.)")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros mem e c s i a Hi Hk He Ha; [reflexivity|].
  cbn [pf_mem]. rewrite IH by lia.
  apply pf_wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; cbn [Z.of_nat]; lia.
Qed.

#[using="Type"] Lemma word_to_le_bytes4_Z : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof. intros v. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. apply Z_to_le_bytes_wrap. cbn; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pf_mem_cell : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pk,$1.Pmem,P,(8.&40.)(17.(8.&8.))Pe,$0.Pc,$0.Ps,$0.Pi,$0.Pj,$0.Pt,$1.P,(3.=R3.)P,(3.(<.+4.(11.R4.(5.R9.)))R7.)P,(4.R8.(1;.+2.+40.))P,(2.(3.=R5.)(4.R5.(5.R;.)))P,(6.R5.#4.)(7.(17.(8.&8.))(28.R<.R;.R:.R9.R8.R=.(>.&40.(11.(11.(12.R;.(<.+4.(11.R8.(5.R=.))))(<.+4.R7.))(5.R6.))))(2;.(8.&8.)(9.(8.&8.)R6.(?.#4.(10.(11.R:.(<.(12.(12.(5.R=.)+1.)R7.)R9.))+10.))(>.&8.=))))")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros mem e c s i j t Hi Hk He Hj Ht; [lia|].
  rewrite Nat2Z.inj_succ in *.
  cbn [pf_mem].
  destruct (Z.eq_dec j (Z.of_nat k)) as [->|Hne].
  - (* [comment removed for export] *)
    rewrite pf_mem_frame; [| lia | lia | lia | rewrite u64_of_Z by lia; lia].
    rewrite pf_wbytes_inside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
    rewrite word_to_le_bytes4_Z. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
  - replace (e - 4 * (i + Z.succ (Z.of_nat k)) + 4 * j + Z.of_nat t)%Z
      with (e - 4 * ((i + 1) + Z.of_nat k) + 4 * j + Z.of_nat t)%Z by lia.
    rewrite (IH _ e (c + s)%Z s (i + 1)%Z j t) by lia.
    f_equal. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pf_mem_rdn : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pk,$1.Pmem,P,(8.&40.)(17.(8.&8.))Pe,$0.Pc,$0.Ps,$0.Pi,$0.Pj,$0.P,(3.=R2.)P,(3.(<.+4.(11.R3.(5.R8.)))R6.)P,(4.R7.(1;.+2.+40.))P,(2.(3.=R4.)(4.R4.(5.R:.)))(7.(17.(13.(8.&8.)))(2=.Vsegs,(28.R:.R9.R8.R7.R6.R;.)(>.&40.(11.(12.R9.(<.+4.(11.R6.(5.R;.))))(<.+4.R5.)))#4.)(2;.(13.(8.&8.))(?.#4.(10.(11.R8.(<.(12.(12.(5.R;.)+1.)R5.)R7.))+10.))))")
(* [comment removed for export] *).
Proof.
  intros k mem e c s i j Hi Hk He Hj.
  apply AX2S.rdn_pointwise; [apply length_Z_to_le_bytes | rewrite u64_of_Z by lia; cbn [Z.of_nat]; lia |].
  intros t Ht. rewrite u64_of_Z by lia. apply pf_mem_cell; assumption.
Qed.

#[using="Type"] Lemma pf_cell_linear : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pc,$0.Ps,$0.Pk,$0.Pj,$0.P,(2>.+10.R3.)(7.$0.(10.(11.R5.(<.(12.(12.R3.+1.)R2.)R4.))+10.)(11.(10.(11.R5.(<.(12.R3.+1.)R4.))+10.)(<.R2.(2?.(10.R4.+10.)))))")
(* [comment removed for export] *).
Proof.
  intros c s k j [q ->].
  replace (c + (k - 1 - j) * (q * 16))%Z with ((c + (k - 1) * (q * 16)) + (- (j * q)) * 16)%Z by lia.
  rewrite Z.div_add by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7"] Theorem popfree_loop_run : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pregs,(16.&5.(8.&40.))Pmem,P,(8.&40.)(17.(8.&8.))Prom,P,(8.&40.)(17.(8.&8.))Pi,$0.Pe,$0.Pc,$0.Ps,$0.Pn,$0.P,(7.(8.&40.)(18.R8.(19.&5.+:.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R9.(19.&5.+;.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R:.(19.&5.+<.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R;.(19.&5.+15.$1:.))(>.&40.R5.))P,(7.(8.&40.)(18.R<.(19.&5.+13.$1:.))(>.&40.R5.))P,(3.=R:.)P,(4.R;.R7.)P,(3.(<.+4.R8.)R;.)P,(4.R<.(1;.+2.+40.))P,(3.=R<.)P,(3.=R<.)P,(4.(11.R>.(<.(12.R<.R10.)R=.))(1;.+2.+40.))P,Pd,$0.Pm,$1.P,(3.=R2.)P,(3.(11.R3.(5.R2.))(<.+4.(12.R10.R14.)))(7.$1<.(1=.Vsegs,R17.(>.&40.(11.(12.R14.(<.+4.R11.))R4.))R3.)$1>.)(1?.(16.&5.(8.&40.))Lregs',(16.&5.(8.&40.))(2.(20.Vsegs,(21.$22.R16.(>.&40.Vp,)R15.R14.)(21.$22.R1.(>.&40.(11.Vp,+20.))(28.R15.R12.R11.R10.R13.(;.(12.R?.R13.)))R14.))(2.(7.(8.&40.)(18.R1.(19.&5.+:.$1:.))(>.&40.R?.))(2.(7.(8.&40.)(18.R1.(19.&5.+;.$1:.))(>.&40.R12.))(2.(7.(8.&40.)(18.R1.(19.&5.+<.$1:.))(>.&40.(11.R11.(<.(12.R?.R13.)R10.))))(2.(7.(8.&40.)(18.R1.(19.&5.+15.$1:.))(>.&40.R10.))(2.(7.(8.&40.)(18.R1.(19.&5.+13.$1:.))(>.&40.R?.))(2.(7.(8.&40.)(18.R1.(19.&5.+>.$1:.))(>.&40.(10.(11.R11.(<.(12.(12.R?.R13.)+1.)R10.))+10.)))(2.(7.(8.&40.)(18.R1.(19.&5.+?.$1:.))(>.&40.(12.R12.(<.+4.R?.))))Pr,(8.&5.)P,(25.(7.(8.&5.)R1.(19.&5.+:.$1:.)))P,(25.(7.(8.&5.)R2.(19.&5.+<.$1:.)))P,(25.(7.(8.&5.)R3.(19.&5.+>.$1:.)))P,(25.(7.(8.&5.)R4.(19.&5.+?.$1:.)))(7.(8.&40.)(18.R6.R5.)(18.R1;.R5.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hwr.
  destruct (Z.to_nat (n - i)) as [|k] eqn:Hk; [lia|].
  assert (Hkz : (Z.of_nat (S k) = n - i)%Z) by lia.
  destruct (pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))
    as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
  { intros j Hj. replace (e - 4 * (j + 1))%Z with (e - 4 * n + 4 * (n - j - 1))%Z by lia. apply Hwr; lia. }
  exists regs'. rewrite R10, R11, R12, R21, R19, R14, R15, Hkz.
  replace (Z.of_nat k) with (n - i - 1)%Z by lia.
  repeat (split; [first [exact Hms | reflexivity]|]). exact Ro.
Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma pf_mem_wbytes : ltac2:(CDefT.buildp (gd_tbl_AsanPopFree ()) "Pk,$1.Pmem,P,(8.&40.)(17.(8.&8.))Pe,$0.Pc,$0.Ps,$0.Pi,$0.P,(3.=R1.)P,(3.(<.+4.(11.R2.(5.R7.)))R5.)P,(4.R6.(1;.+2.+40.))(7.P,(8.&40.)(17.(8.&8.))(28.R8.R7.R6.R5.R4.R9.)(24.R8.(>.&40.(12.R7.(<.+4.(11.R4.(5.R9.)))))(=.R6.R5.R9.)))")
(* [comment removed for export] *).
Proof.
  intros k mem e c s i Hi Hk He. apply functional_extensionality. intros a.
  pose proof (u64_range a) as Ra. pose proof (pf_bytes_length c s k) as L.
  destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * (i + Z.of_nat k))) as [Hlt|Hge];
    [|destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * i)) as [Hlt2|Hge2]].
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
  - set (base := (e - 4 * (i + Z.of_nat k))%Z) in *.
    set (j := ((bv_unsigned a - base) / 4)%Z). set (t := Z.to_nat ((bv_unsigned a - base) mod 4)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hj : (0 <= j < Z.of_nat k)%Z) by (subst j base; lia).
    assert (Ht : (t < 4)%nat) by (subst t; lia).
    assert (Ha : a = Z_to_bv 64 (base + 4 * j + Z.of_nat t)).
    { apply bv_eq. rewrite u64_of_Z by (subst j t base; lia). subst j t base. lia. }
    rewrite Ha. subst base. rewrite (pf_mem_cell k mem e c s i j t Hi Hk He Hj Ht).
    rewrite pf_wbytes_inside; rewrite ?L, ?u64_of_Z by lia; [|lia|lia].
    replace (Z.to_nat (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t - (e - 4 * (i + Z.of_nat k)))) with (Z.to_nat (4 * j) + t)%nat by lia.
    symmetry. f_equal. apply pf_bytes_nth; assumption.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
Qed.

#[using="Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7"] Theorem popfree_spec_of_code : popfree_spec segs p.
Proof.
  intros regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok.
  destruct (popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
  { intros d m Hd Hdm. eapply (store_ok_sub segs mem _ _ (Z.to_nat (4 * (n - i))) m); [| exact Hok | |]; rewrite !u64_of_Z by lia; lia. }
  exists regs'. rewrite (pf_mem_wbytes (Z.to_nat (n - i)) mem e c s i) in Hms by lia.
  replace (i + Z.of_nat (Z.to_nat (n - i)))%Z with n in Hms by lia.
  split; [exact Hms|]. split; [exact R10|]. split; [exact R12|]. split; [exact R14|]. split; [exact R15|]. exact Ro.
Qed.

End PopFreeLoop.
