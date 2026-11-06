(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export Walk AStep Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AEvtA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export ALazy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export AEvtS AEvtA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export AShadow.
(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export DietDestruct.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac destruct_exs PO ::= destruct_exs_diet PO.
Ltac destruct_ands PO ::= destruct_ands_diet PO.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_StepA () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.ALazy.asan_layout"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.LibA.ALazy.acc_ok"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.LibA.ALazy.shadow_of"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Peano.le"; "OSSVerify.KrLib.LibA.ALazy.al_img_lo"; "OSSVerify.KrLib.LibA.ALazy.al_img_hi"; "Stdlib.Arith.PeanoNat.Nat.leb"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "OSSVerify.KrLib.Lib.Step.fetch_dec"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Lib.Step.reads_imp"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "OSSVerify.KrLib.LibA.AEvtA.liftA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.interp_eff_accesses"; "LinuxProcessSemantics.Riscv.Sem.exec"; "LinuxProcessSemantics.Riscv.Sem.Core"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "OSSVerify.KrLib.Lib.Step.reads_all"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "OSSVerify.KrLib.Lib.MState.MS"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "OSSVerify.KrLib.LibA.AShadow.shadow_val_okN"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Mem.sxb"; "Stdlib.ZArith.BinInt.Z.land"; "LinuxProcessSemantics.Riscv.Prelude.bv_lts"].


Lemma dt_apart_sb_11 : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PX,$0.Pc2,$0.Pn2,$0.Pc1,$0.Plen,$0.P,(1.$2.(3.(4.(5.R4.R3.)R2.)(4.(5.R2.R1.)R4.))$6.)(7.(8.(5.(5.R6.R5.)R4.)(5.R6.R3.))(8.(5.(5.R6.R3.)R2.)(5.R6.R5.)))")
(* [comment removed for export] *).
Proof. intros X c2 n2 c1 len H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.
Lemma dt_apart_sb_01 : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PX,$0.Pn2,$0.Pc1,$0.Plen,$0.P,(1.$2.(3.(4.R3.R2.)(4.(5.R2.R1.)=))$6.)(7.(8.(5.R5.R4.)(5.R5.R3.))(8.(5.(5.R5.R3.)R2.)R5.))")
(* [comment removed for export] *).
Proof. intros X n2 c1 len H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.
Lemma dt_apart_sb_10 : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PX,$0.Pc2,$0.Pn2,$0.Plen,$0.P,(1.$2.(3.(4.(5.R3.R2.)=)(4.R1.R3.))$6.)(7.(8.(5.(5.R5.R4.)R3.)R5.)(8.(5.R5.R2.)(5.R5.R4.)))")
(* [comment removed for export] *).
Proof. intros X c2 n2 len H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.
Lemma dt_apart_sb_12 : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PX,$0.Pc2,$0.Pn2,$0.Pc1,$0.Pd1,$0.Plen,$0.P,(1.$2.(3.(4.(5.R5.R4.)(5.R3.R2.))(4.(5.(5.R3.R2.)R1.)R5.))$6.)(7.(8.(5.(5.R7.R6.)R5.)(5.(5.R7.R4.)R3.))(8.(5.(5.(5.R7.R4.)R3.)R2.)(5.R7.R6.)))")
(* [comment removed for export] *).
Proof. intros X c2 n2 c1 d1 len H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.
Lemma dt_apart_sb_02 : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PX,$0.Pn2,$0.Pc1,$0.Pd1,$0.Plen,$0.P,(1.$2.(3.(4.R4.(5.R3.R2.))(4.(5.(5.R3.R2.)R1.)=))$6.)(7.(8.(5.R6.R5.)(5.(5.R6.R4.)R3.))(8.(5.(5.(5.R6.R4.)R3.)R2.)R6.))")
(* [comment removed for export] *).
Proof. intros X n2 c1 d1 len H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.
Lemma dt_apart_lit : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PA2,$0.Pn2,$0.Pa,$0.Plen,$0.P,(1.$2.(3.(4.(5.R4.R3.)R2.)(4.(5.R2.R1.)R4.))$6.)(7.(8.(5.R5.R4.)R3.)(8.(5.R3.R2.)R5.))")
(* [comment removed for export] *).
Proof. intros A2 n2 a len H. apply orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia. Qed.

Lemma dt_le_lit : forall a b : Z, (a <=? b) = true -> a <= b.  Proof. intros a b H. apply Z.leb_le, H. Qed.

(* [comment removed for export] *)
Ltac dt_closed_true :=
  lazymatch goal with
  | |- ?b = true => let v := eval vm_compute in b in
                    lazymatch v with true => exact (@eq_refl bool true) end
  end.
(* [comment removed for export] *)
Ltac dt_apart_sb :=
  lazymatch goal with
  | |- ?X + ?c2 + ?n2 <= ?X + ?c1 + ?d1 \/ _ => is_Zlit c2; is_Zlit n2; is_Zlit c1; is_Zlit d1; apply (dt_apart_sb_12 X c2 n2 c1 d1); dt_closed_true
  | |- ?X + ?c2 + ?n2 <= ?X + ?c1 \/ _ => is_Zlit c2; is_Zlit n2; is_Zlit c1; apply (dt_apart_sb_11 X c2 n2 c1); dt_closed_true
  | |- ?X + ?n2 <= ?X + ?c1 + ?d1 \/ _ => is_Zlit n2; is_Zlit c1; is_Zlit d1; apply (dt_apart_sb_02 X n2 c1 d1); dt_closed_true
  | |- ?X + ?n2 <= ?X + ?c1 \/ _ => is_Zlit n2; is_Zlit c1; apply (dt_apart_sb_01 X n2 c1); dt_closed_true
  | |- ?X + ?c2 + ?n2 <= ?X \/ _ => is_Zlit c2; is_Zlit n2; apply (dt_apart_sb_10 X c2 n2); dt_closed_true
  | |- ?A2 + ?n2 <= ?a \/ _ => is_Zlit A2; is_Zlit n2; is_Zlit a; apply (dt_apart_lit A2 n2 a); dt_closed_true
  end.

(* [comment removed for export] *)
Ltac dt_pos_lit :=
  lazymatch goal with
  | |- (0 < ?n)%Z => is_Zlit n; exact (@eq_refl comparison Lt)
  | |- (0 < S ?n)%nat => exact (Nat.lt_0_succ n)
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac addr_diff_raw E A ::=
  match constr:(tt) with
  | _ => let chk := match goal with _ => constr_eq E A end in constr:(0%Z)
  | _ =>
    lazymatch E with
    | Z.add ?X ?c1 =>
        lazymatch A with
        | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => zlit c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | E => constr:(0%Z)
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end
  end.

(* [comment removed for export] *)
Ltac addr_diff E A ::=
  let k := addr_diff_raw E A in
  lazymatch eval vm_compute in (Z.leb 0 k && Z.ltb k 4096)%bool with true => k end.

(* [comment removed for export] *)
Ltac show_hyps := try (match reverse goal with H : ?T |- _ => idtac H ":" T; fail end).
Ltac show_goal := match goal with |- ?g => idtac g end.

(* [comment removed for export] *)
Lemma zb8_norm : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 (z mod 2^8).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2^8). change (2 ^ Z.of_N 64) with (2^8 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^8)), Z_mod_plus_full. reflexivity.
Qed.
Ltac norm_b8 H :=
  rewrite ?zb8_norm in H;
  repeat match type of H with
  | context [Z_to_bv 8 (?z mod 2^8)] =>
      let k := eval vm_compute in (Z.modulo z (2^8)) in
      change (Z.modulo z (2^8)) with k in H
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_mods :=
  lazymatch goal with
  | |- context [Z.modulo _ _] => idtac
  | _ => repeat match goal with
         | H : Z.modulo _ _ = _ |- _ => clear H
         | H : _ = Z.modulo _ _ |- _ => clear H
         | H : Z.modulo _ _ <> _ |- _ => clear H
         | H : Z.modulo _ _ < _ |- _ => clear H
         end
  end.
Ltac qlia := clear_disj; clear_mods; lia.
(* [comment removed for export] *)
Ltac pqlia := prune_disj; clear_mods; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma acc_ok_clientZ : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PL,$9.PCS,P,$0.SpPE,$0.Pn,$:.PA,$0.Pk,$0.P,(;.R5.R2.R1.)P,(8.=R5.)P,(<.R6.(=.+2.+40.))P,(8.R5.R7.)P,(8.(5.R8.(>.R7.))(5.R6.R5.))(?.R;.R:.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R9.)R8.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof.
  intros L CS E n A k HC H0 H1 H2 H3. eapply acc_ok_client1; [exact HC| |]; rewrite unsigned_lit by lia; lia.
Qed.

Lemma acc_ok_aobjZ : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "Psegs,(16.$17.)PL,$9.PCS,P,$0.SpPm,P,(12.&40.)(18.(12.&8.))PE,$0.Pn,$:.PA,$0.Pk,$0.P,(19.R8.R7.R6.R5.R2.R1.)P,(8.=R5.)P,(<.R6.(=.+2.+40.))P,(8.R5.R7.)P,(8.(5.R8.(>.R7.))(5.R6.R5.))(?.R<.R;.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R9.)R8.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof. intros. eapply acc_ok_clientZ; eauto. eapply aobj_crange; eauto. Qed.

Lemma acc_ok_shadow1Z : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "Psegs,(16.$17.)PL,$9.PCS,P,$0.SpPm,P,(12.&40.)(18.(12.&8.))PE,$0.PA,$0.Pk,$0.Pc,$0.P,(1:.R7.R6.)P,(19.R9.R8.R7.R6.R4.R3.)P,(1;.(8.R5.R3.)(<.R3.(5.R5.R4.)))P,(1.$0.R7.(1<.R:.R4.))(?.R;.R:.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R8.)#1.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof.
  intros segs L CS m E A k c OK H Hc HS.
  destruct OK as (C1 & _). destruct (C1 c (aobj_crange _ _ _ _ _ _ H c Hc)) as (R0 & R1 & R2 & _).
  eapply acc_ok_shadow1; [eapply aobj_crange; exact H| exact Hc|].
  rewrite unsigned_lit by lia. exact HS.
Qed.

Lemma acc_ok_shadowZ : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "Psegs,(16.$17.)PL,$9.PCS,P,$0.SpPm,P,(12.&40.)(18.(12.&8.))PE,$0.Pn,$:.PA,$0.Pk,$0.Pc,$0.P,(1:.R8.R7.)P,(19.R:.R9.R8.R7.R4.R3.)P,(8.R5.R3.)P,(<.(5.R4.(1=.+8.(1>.(>.R7.)+1.)))(5.R6.R5.))P,(1.$0.(1?.R5.+8.)=)P,(20.#1.R9.)P,(1.$0.R;.(1<.R>.R7.))(?.R?.R>.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R<.)R;.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof.
  intros segs L CS m E n A k c OK H H1 H2 Hal Hn HS.
  destruct OK as (C1 & _). destruct (C1 c (aobj_crange _ _ _ _ _ _ H c ltac:(lia))) as (R0 & R1 & R2 & _).
  eapply acc_ok_shadow; [eapply aobj_crange; exact H| exact H1| exact H2| exact Hal|].
  rewrite unsigned_lit by lia. exact HS.
Qed.

(* [comment removed for export] *)
Lemma acc_ok_crZ : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PL,$9.PCS,P,$0.SpPE,$0.Pn,$:.P,(;.R3.R2.(>.R1.))P,(8.=R3.)P,(8.(5.R4.(>.R3.))(=.+2.+40.))P,(20.#1.R4.)(?.R8.R7.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R6.)R5.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof. intros L CS E n HC H0 H1 Hn. eapply (acc_ok_clientZ L CS E n E (Z.of_nat n)); eauto; lia. Qed.

(* [comment removed for export] *)
Lemma acc_ok_shcrZ : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PL,$9.PCS,P,$0.SpPE,$0.Pn,$:.Pc,$0.P,(1:.R5.R4.)P,(;.R5.R2.(1>.(1=.+8.(>.R3.))+7.))P,(7.(1.$:.R4.#1.)(1.$0.(1?.R3.+8.)=))P,(20.#1.R5.)P,(1.$0.R7.(1<.R9.R5.))(?.R:.R9.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R8.)R7.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof.
  intros L CS E n c OK HC Hal Hn HS.
  destruct OK as (C1 & _). destruct (C1 c (HC c ltac:(lia))) as (R0 & R1 & R2 & _).
  destruct Hal as [->|Hal].
  - eapply (acc_ok_shadow1 L CS _ c 1 c); [exact HC| lia|]. rewrite unsigned_lit by lia. exact HS.
  - eapply (acc_ok_shadow L CS _ n c (8 * Z.of_nat n - 7) c); [exact HC| lia| lia| exact Hal|]. rewrite unsigned_lit by lia. exact HS.
Qed.

Lemma acc_ok_imgZ : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PL,$9.PCS,P,$0.SpPE,$0.Pn,$:.P,(8.=R2.)P,(8.(21.R5.)R3.)P,(8.(5.R4.(>.R3.))(22.R6.))P,(<.(22.R7.)(=.+2.+40.))(?.R8.R7.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R6.)R5.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof. intros. apply acc_ok_img; rewrite unsigned_lit by lia; lia. Qed.

(* [comment removed for export] *)
Lemma shadow_of_shiftr : forall L c, 0 <= c -> Z.shiftr c 3 + al_sb L = shadow_of L c.
Proof. intros. unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma shadow_of_shiftr' : forall L c, 0 <= c -> al_sb L + Z.shiftr c 3 = shadow_of L c.
Proof. intros. rewrite <- shadow_of_shiftr by assumption. lia. Qed.
Lemma shadow_of_plus8k : forall L c k, shadow_of L (c + 8 * k) = shadow_of L c + k.
Proof. intros. unfold shadow_of. rewrite (Z.mul_comm 8 k), Z.div_add by lia. lia. Qed.

Ltac shadow_addr_eq :=
  rewrite ?shadow_of_plus8k; unfold shadow_of;
  rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
  first [ clear; lia | qlia ].

(* [comment removed for export] *)
Lemma dt_sh_eq0 : forall L c, Z.shiftr c 3 + al_sb L = shadow_of L c.
Proof. intros. unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma dt_sh_eq0' : forall L c, al_sb L + Z.shiftr c 3 = shadow_of L c.
Proof. intros. rewrite <- dt_sh_eq0. lia. Qed.
Lemma dt_sh_eqk : forall L c k, Z.shiftr c 3 + al_sb L + k = shadow_of L (c + 8 * k).
Proof. intros. rewrite shadow_of_plus8k, <- dt_sh_eq0. reflexivity. Qed.
Lemma dt_sh_eqk' : forall L c k, al_sb L + Z.shiftr c 3 + k = shadow_of L (c + 8 * k).
Proof. intros. rewrite shadow_of_plus8k, <- dt_sh_eq0'. reflexivity. Qed.
Lemma dt_sh_eqs : forall L c k, shadow_of L c + k = shadow_of L (c + 8 * k).
Proof. intros. rewrite shadow_of_plus8k. reflexivity. Qed.

Ltac shadow_addr_eq_ref :=
  rewrite ?shadow_of_plus8k; unfold shadow_of;
  rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8;
  first [ clear; lia | qlia ].
Ltac shadow_addr_eq ::=
  lazymatch goal with
  | |- Z.shiftr ?c 3 + al_sb ?L = shadow_of ?L ?c => exact (dt_sh_eq0 L c)
  | |- al_sb ?L + Z.shiftr ?c 3 = shadow_of ?L ?c => exact (dt_sh_eq0' L c)
  | |- Z.shiftr ?c 3 + al_sb ?L + ?k = shadow_of ?L (?c + 8 * ?k) => exact (dt_sh_eqk L c k)
  | |- al_sb ?L + Z.shiftr ?c 3 + ?k = shadow_of ?L (?c + 8 * ?k) => exact (dt_sh_eqk' L c k)
  | |- shadow_of ?L ?c + ?k = shadow_of ?L (?c + 8 * ?k) => exact (dt_sh_eqs L c k)
  | |- shadow_of ?L ?c = shadow_of ?L ?c => reflexivity
  | _ => shadow_addr_eq_ref
  end.

(* [comment removed for export] *)
Ltac shadow_client_of E :=
  lazymatch E with
  | Z.add (Z.add (Z.shiftr ?c 3) _) ?k => constr:(Z.add c (Z.mul 8 k))
  | Z.add (Z.add _ (Z.shiftr ?c 3)) ?k => constr:(Z.add c (Z.mul 8 k))
  | Z.add (Z.shiftr ?c 3) _ => c
  | Z.add _ (Z.shiftr ?c 3) => c
  | Z.add (shadow_of _ ?c) ?k => constr:(Z.add c (Z.mul 8 k))
  | shadow_of _ ?c => c
  end.

(* [comment removed for export] *)
Ltac base_of a := lazymatch a with | Z.add ?x _ => base_of x | Z.sub ?x _ => base_of x | _ => a end.
Ltac crange_by H A k a n := apply (crange_sub _ A k a n H); [ qlia | qlia ].
Ltac crange_byo H A k a n := apply (crange_sub _ A k a n (aobj_crange _ _ _ _ _ _ H)); [ qlia | qlia ].
Ltac solve_crange :=
  lazymatch goal with
  | |- crange ?CS ?a ?n =>
      first
        [ assumption
        | let b := base_of a in
          first
            [ lazymatch goal with
              | H : crange CS b ?k |- _ => crange_by H b k a n
              | H : aobj _ _ CS _ b ?k |- _ => crange_byo H b k a n
              | H : crange CS (b + ?j) ?k |- _ => crange_by H (b + j) k a n
              | H : aobj _ _ CS _ (b + ?j) ?k |- _ => crange_byo H (b + j) k a n
              end
            | match goal with
              | H : crange CS (b + ?j) ?k |- _ => crange_by H (b + j) k a n
              | H : aobj _ _ CS _ (b + ?j) ?k |- _ => crange_byo H (b + j) k a n
              | H : crange CS (b - ?j) ?k |- _ => crange_by H (b - j) k a n
              end ]
        | (* [comment removed for export] *)
          match goal with H : crange CS ?lo (?hi - ?lo) |- _ => crange_by H lo (hi - lo) a n end
        | match goal with
          | H : crange CS ?A ?k |- _ => crange_by H A k a n
          | H : aobj _ _ CS _ ?A ?k |- _ => crange_byo H A k a n
          end ]
  end.

Ltac solve_acc1 :=
  lazymatch goal with
  | |- acc_ok ?L ?CS [(Z_to_bv 64 ?E, ?n)] =>
    first
      [ (* [comment removed for export] *)
        let c := shadow_client_of E in
        lazymatch goal with
        | OK : cs_ok L CS |- _ =>
            eapply (acc_ok_shcrZ L CS E n c OK);
            [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.sub Z.pos_sub Pos.mul Pos.add]; solve_crange
            | first [ left; reflexivity | right; qlia ]
            | clear; cbn; lia
            | shadow_addr_eq ]
        end
      | (* [comment removed for export] *)
        eapply (acc_ok_crZ L CS E n); [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve_crange | qlia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; qlia | clear; cbn; lia ]
      | (* [comment removed for export] *)
        apply (acc_ok_imgZ L CS E n); [ qlia | cbn; qlia | cbn; qlia | qlia ]
      | fail 2 "solve_acc: cannot classify access at" E ]
  | |- acc_ok ?L ?CS [(?a, ?n)] =>
      (* [comment removed for export] *)
      rewrite <- (Z_to_bv_bv_unsigned a); solve_acc1
  end.

(* [comment removed for export] *)
Lemma dt_acc_ok_cr : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PL,$9.PCS,P,$0.SpPE,$0.Pn,$:.P,(1:.R4.R3.)P,(;.R4.R3.(>.R2.))P,(1.$2.(23.#1.R3.)$6.)(?.R7.R6.(10.(11.(12.&40.)$:.)(13.(12.&40.)$:.(14.&40.R5.)R4.)(15.(11.(12.&40.)$:.))))")
(* [comment removed for export] *).
Proof.
  intros L CS E n OK HC Hn. apply Nat.leb_le in Hn.
  destruct OK as (C1 & _).
  destruct (C1 E (HC E ltac:(lia))) as (R0 & _).
  destruct (C1 (E + Z.of_nat n - 1) (HC (E + Z.of_nat n - 1) ltac:(lia))) as (R1 & _).
  apply acc_ok_crZ; [exact HC| lia| lia| exact Hn].
Qed.
Ltac dt_nat_le1 :=
  lazymatch goal with
  | |- (1 <= ?n)%nat => first [ exact (proj1 (PeanoNat.Nat.leb_le 1 n) (@eq_refl bool true)) | clear; cbn; lia ]
  end.
Ltac solve_acc1 ::=
  lazymatch goal with
  | |- acc_ok ?L ?CS [(Z_to_bv 64 ?E, ?n)] =>
    first
      [ (* [comment removed for export] *)
        let c := shadow_client_of E in
        lazymatch goal with
        | OK : cs_ok L CS |- _ =>
            eapply (acc_ok_shcrZ L CS E n c OK);
            [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.sub Z.pos_sub Pos.mul Pos.add]; solve_crange
            | first [ left; reflexivity | right; qlia ]
            | dt_nat_le1
            | shadow_addr_eq ]
        end
      | (* [comment removed for export] *)
        lazymatch goal with
        | OK : cs_ok L CS |- _ =>
            apply (dt_acc_ok_cr L CS E n OK); [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve_crange | exact (@eq_refl bool true) ]
        end
      | (* [comment removed for export] *)
        eapply (acc_ok_crZ L CS E n); [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve_crange | qlia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; qlia | clear; cbn; lia ]
      | (* [comment removed for export] *)
        apply (acc_ok_imgZ L CS E n); [ qlia | cbn; qlia | cbn; qlia | qlia ]
      | fail 2 "solve_acc: cannot classify access at" E ]
  | |- acc_ok ?L ?CS [(?a, ?n)] =>
      rewrite <- (Z_to_bv_bv_unsigned a); solve_acc1
  end.

Ltac solve_acc :=
  lazymatch goal with
  | |- acc_ok _ _ [] => apply acc_ok_nil
  | |- acc_ok _ _ [_] => solve_acc1
  | |- acc_ok _ _ (?x :: _) => apply acc_ok_cons; [ solve_acc1 | solve_acc ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac exec_evalA t :=
  eval cbv beta iota zeta delta [liftA interp_eff_accesses access_value accessed_ranges
     exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     amo_val width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in t.
Ltac exec_cbvA :=
  idtac;
  let g := lazymatch goal with |- ?g => g end in
  let g' := exec_evalA g in set_concl g'.

(* [comment removed for export] *)
Lemma amo_aligned_of : forall wd (a : Z), 0 <= a < 2^64 -> a mod amo_bytes wd = 0 -> amo_aligned wd (Z_to_bv 64 a) = true.
Proof. intros wd a Ha Hm. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Lemma amo_aligned_var : forall wd (a : word), bv_unsigned a mod amo_bytes wd = 0 -> amo_aligned wd a = true.
Proof. intros wd a Hm. unfold amo_aligned. rewrite Hm. reflexivity. Qed.

Ltac amo_alignA :=
  repeat match goal with
  | |- context [amo_aligned ?w (Z_to_bv 64 ?e)] =>
      rewrite (amo_aligned_of w e) by (cbn [amo_bytes]; qlia)
  | |- context [amo_aligned ?w ?a] => is_var a;
      rewrite (amo_aligned_var w a) by (cbn [amo_bytes]; qlia)
  end;
  cbv beta iota delta [negb];
  try (rewrite Z.eqb_refl; cbv beta iota).

(* [comment removed for export] *)
Lemma Z_to_le_bytes_4_bv32 : forall x : bv 32, Z_to_le_bytes 4 (bv_unsigned x) = le4 (Z_to_bv 64 (bv_unsigned x)).
Proof.
  intros x. unfold le4. rewrite unsigned_lit; [reflexivity|].
  pose proof (bv_unsigned_in_range 32 x) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.
Lemma extract32_le4 : forall v : word, bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 v))) = bv_unsigned v mod 2^32.
Proof. intros v. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4. cbn [Z.of_N]. apply Z.mod_mod. lia. Qed.
Ltac amo_store_norm :=
  rewrite ?Z_to_le_bytes_4_bv32;
  rewrite ?bv_add_unsigned, ?extract32_le4;
  repeat match goal with
  | |- context [bv_unsigned (low32 ?v)] => rewrite (low32_unsigned v)   (* [comment removed for export] *)
  end.

Ltac is_amo i := lazymatch i with Amo _ _ _ _ _ _ _ => idtac | Lr _ _ _ _ _ => idtac | Sc _ _ _ _ _ _ => idtac end.

Ltac apply_step_lemmaA :=
  lazymatch goal with
  | |- evtA _ _ _ _ _ => eapply evtA_step
  | |- aevtA _ _ _ _ => eapply aevtA_step; [ eassumption | | | ]
  | |- ?g => fail "apply_step_lemmaA: goal is neither evtA nor aevtA"
  end.

(* [comment removed for export] *)
Section StepAF.
Variable segs : list Segment.
#[using="Type"] Lemma stepA_f : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "PR,(24.&5.(12.&40.))PF,(24.&5.(12.&40.))Ppc,(12.&40.)Pfc,(12.&20.)Prv,(18.(12.&40.))Pm,P,(12.&40.)(18.(12.&8.))Pro,P,(12.&40.)(18.(12.&8.))Pi,$25.Psz,$0.Prds,(16.(11.(12.&5.)(12.&40.)))Pg,P,(24.&5.(12.&40.))$26.Pacc,(16.$27.)P,(1.(18.(11.$25.$0.))(28.Vsegs,R:.)(29.(11.$25.$0.)(13.$25.$0.R5.R4.)))P,PR0,(24.&5.(12.&40.))(2:.R1.R5.(1.(2;.(2<.$26.))(2=.R8.(2>.Vsegs,(2?.(14.&40.R6.)R7.(30.R1.R=.R<.R;.R:.))R9.))(31.(2<.$26.)(32.$26.A1.R4.R1.R3.))))P,(33.R>.R5.)(1;.(1.(18.(12.&40.))(34.(35.R?.R>.R=.R<.R;.R:.R9.))(36.(12.&40.)))(1.(2;.(2<.$26.))(37.Vsegs,(35.R?.R>.R=.R<.R;.R:.R9.))(31.(2<.$26.)(32.$26.A1.R5.R?.R4.))))")
(* [comment removed for export] *).
Proof.
  intros R F pc fc rv m ro i sz rds g acc Hfd Hx Hr. split; [reflexivity|].
  unfold fetch_dec in Hfd.
  destruct (fetch_word segs pc) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  rewrite (step_accesses_gen segs R F pc fc rv m ro w i sz Hf He Hfd).
  exact (reads_imp_elim R rds _ (Hx R) Hr).
Qed.
End StepAF.

(* [comment removed for export] *)
Ltac step_coreA_ref segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        apply_step_lemmaA;
        [ split; [reflexivity|];
          rewrite (step_accesses_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbvA; simp_is_x0; simp_regs;
          tryif is_amo i then (vnorm; amo_alignA; exec_cbvA; amo_alignA; simp_is_x0; simp_regs; vnorm) else vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | solve_acc
        | simp_regs; (tryif is_amo i then (vnorm; try amo_store_norm) else vnorm_for i); mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.


Ltac step_coreA_r segs R F pc fc rv m ro i sz :=
  let t := constr:(fun R0 : bvmap 5 word =>
             liftA ro (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core R0 F (Z_to_bv 64 pc) fc rv)) m)) in
  let t' := exec_evalA t in
  let rds := collect_reads t' R constr:(@nil (bv 5 * word)) in
  let hasreads := lazymatch rds with nil => constr:(false) | _ => constr:(true) end in
  let Rf := match constr:(tt) with _ => fold_R31 R | _ => R end in
  (* [comment removed for export] *)
  (lazymatch Rf with
   | R => idtac
   | _ => lazymatch goal with |- ?HD (MS R F ?pcw fc rv m ?row) => change_no_check (HD (MS Rf F pcw fc rv m row)) end
   end);
  apply_step_lemmaA;
  [ eapply (stepA_f segs Rf F (Z_to_bv 64 pc) fc rv m ro i sz rds);
    [ vm_compute; reflexivity
    | let R0 := fresh "R0" in
      intro R0;
      lazymatch goal with |- reads_imp _ _ ?P => let G := reads_imp_unfold R0 rds P in change_no_check G end;
      intro_reads rds;
      (tryif is_plain_insn i
       then (lazymatch goal with
             | |- @eq ?MT _ ?rhs => let b := eval cbv beta in (t' R0) in change_no_check (@eq MT b rhs)
             end)
       else (exec_pre i; exec_cbvA));
      simp_is_x0;
      use_reads R0;
      simp_regs; vnorm_for i;
      try solve_load; try solve_store;
      lazymatch goal with
      | |- @eq ?MT (@MachineOk ?A (@mkAccessReport ?ST ?s ?ac)) (@MachineOk _ (@mkAccessReport _ (?gg _) ?acv)) =>
          let gt := eval pattern R0 in s in
          lazymatch gt with
          | ?f _ => unify gg f; unify acv ac; exact_no_check (@eq_refl MT (@MachineOk A (@mkAccessReport ST s ac)))
          end
      end
    | let pf := reads_all_proof rds in exact_no_check pf ]
  | solve_acc
  | lazymatch goal with
    | |- ?HD (?gg _) =>
        let s := eval cbv beta in (gg R) in
        let s' := lazymatch hasreads with
                  | true => slim_norm_state s map_cbv_get
                  | false => slim_norm_state s idtac
                  end in
        change_no_check (HD s')
    end;
    simp_regs; vnorm_for i; mem_after_store_opt; post_step i ].

Ltac step_coreA segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        tryif is_amo i then step_coreA_ref segs R F pc fc rv m ro
        else tryif is_concrete_map R then step_coreA_r segs R F pc fc rv m ro i sz
        else step_coreA_ref segs R F pc fc rv m ro
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

(* [comment removed for export] *)
Ltac lit_cond c :=
  lazymatch c with
  | negb ?c' => lit_cond c'
  | bv_eqb (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_lts (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_leu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  end.
Ltac has_var c := match c with context [?x] => is_var x end.
Ltac fold_lit_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif has_var c then idtac
      else (let v := eval vm_compute in c in
            lazymatch v with
            | true => change c with true; cbv_concl_iota
            | false => change c with false; cbv_concl_iota
            end)
  | _ => idtac
  end.

Ltac step ::=
  (lazymatch goal with
  | |- evtA ?segs _ _ _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m (seg_rom _)) => step_coreA segs R F pc fc rv m (seg_rom segs)
  | |- aevtA ?segs _ _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m (seg_rom _)) => step_coreA segs R F pc fc rv m (seg_rom segs)
  | |- ?EVHD (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m (seg_rom ?segs)) => step_core segs R F pc fc rv m (seg_rom segs)
  | |- _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end); fold_lit_if.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac solve_load_shadow0 :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 ?E) 1%nat] =>
      let c := shadow_client_of E in
      match goal with
      | H : aobj segs ?L ?CS m ?A ?k |- _ =>
          rewrite (aobj_shadow0_al segs L CS m A k c E H ltac:(qlia) ltac:(qlia) ltac:(qlia) ltac:(shadow_addr_eq));
          load_post
      end
  end.

Ltac solve_load ::= first [ solve_load_base | solve_load_shadow0 | solve_load_image ].

(* [comment removed for export] *)
Tactic Notation "shadow_byte" constr(H) constr(c) "as" ident(k) ident(RD) ident(HK) :=
  lazymatch type of H with
  | aobj ?segs ?L ?CS ?m ?A ?n =>
      destruct (aobj_shadow1_at segs L CS m A n c (Z.shiftr c 3 + al_sb L) H ltac:(qlia) ltac:(shadow_addr_eq))
        as (k & RD & HK)
  end.

(* [comment removed for export] *)

Lemma sxb_nonzero : forall k : byte, bv_unsigned (sxb k) <> 0 -> bv_unsigned k <> 0.
Proof.
  intros k H E. apply H. unfold sxb, bv_signed. rewrite E.
  change (bv_swrap 8 0) with 0. reflexivity.
Qed.

Lemma land7_mod : forall c, Z.land c 7 = c mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma shadow_slow_takenN : ltac2:(CDefT.buildp (gd_tbl_StepA ()) "Pc,$0.Pn,$0.Pk,(12.&8.)Pe,$0.P,(38.R4.R3.R2.)P,(39.(1.$0.(3:.&40.(3;.R3.))=))P,(8.=R6.)P,(1;.(8.+1.R6.)(8.R6.+8.))P,(1.$0.R5.(5.(3<.R8.+7.)(1>.R7.+1.)))(1.$2.(3=.&40.(14.&40.R6.)(3;.R7.))$6.)")
(* [comment removed for export] *).
Proof.
  intros c n k e HK NZ Hc Hn ->. destruct (shadow_val_signedN c n k HK (sxb_nonzero k NZ)) as [KS KR].
  rewrite land7_mod in *. pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as MB.
  unfold bv_lts, sxb. apply Z.ltb_lt. rewrite !Z_to_bv_signed, KS.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ (Z.of_N 64 - 1)) with 9223372036854775808. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Tactic Notation "shadow_byte" constr(H) constr(c) constr(n) "as" ident(k) ident(RD) ident(HK) :=
  lazymatch type of H with
  | aobj ?segs ?L ?CS ?m ?A ?sz =>
      destruct (aobj_shadowN_at segs L CS m A sz c n (Z.shiftr c 3 + al_sb L) H
                  ltac:(qlia) ltac:(qlia) ltac:(qlia) ltac:(shadow_addr_eq))
        as (k & RD & HK)
  end.

(* [comment removed for export] *)
Ltac decode_at segs pc :=
  eval vm_compute in (match fetch_word segs (Z_to_bv 64 pc) with Some w => decode_any w | None => None end).

(* [comment removed for export] *)
Ltac merge_cut_aevtA segs P := fail "shadow_merge_cut: aevtA goal, no cut rule for this K (see TacA)".
Ltac merge_cut_apply segs P :=
  lazymatch goal with
  | |- evtA ?segs' ?L ?CS ?Q _ => eapply (evtA_cut segs' L CS P Q)
  | |- aevtA _ _ _ _ => merge_cut_aevtA segs P
  end.
Ltac shadow_merge_cut_at segs R F cnd slow fast fc rv m ro :=
      let d1 := decode_at segs slow in
      lazymatch d1 with
      | Some (OpImm ALU_AND ?tmp _ _, _) =>
          let pt := eval vm_compute in (bv_key tmp) in
          let d2 := decode_at segs (slow + 4)%Z in
          let kr := lazymatch d2 with
                    | Some (Branch BC_LT _ ?kr _, _) => kr
                    | Some (OpImm ALU_ADD _ _ _, _) =>
                        lazymatch decode_at segs (slow + 8)%Z with
                        | Some (Branch BC_LT _ ?kr _, _) => kr
                        end
                    end in
          let pk := eval vm_compute in (bv_key kr) in
          merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro)
      | _ => fail "shadow_merge: no [andi t,c,7] at the slow-path target" slow
      end.
Ltac shadow_merge_cut :=
  lazymatch goal with
  | |- evtA ?segs _ _ _ (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      shadow_merge_cut_at segs R F cnd slow fast fc rv m ro
  | |- aevtA ?segs _ _ (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      shadow_merge_cut_at segs R F cnd slow fast fc rv m ro
  end.

(* [comment removed for export] *)
Ltac shadow_merge c k HK :=
  shadow_merge_cut;
  [ let Kz := fresh "Kz" in
    if_cases Kz; zify_cond Kz;
    [ (* [comment removed for export] *)
      zstep;
      (lazymatch goal with
       | |- _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac
       | _ => zstep;
              lazymatch goal with
              | |- _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac
              | _ => zstep
              end
       end);
      lazymatch goal with
      | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
          replace cnd with true by (symmetry; eapply (shadow_slow_takenN c _ k _ HK Kz); qlia); cbv iota
      end;
      apply evtA_done; eexists; eexists; reflexivity
    | apply evtA_done; eexists; eexists; reflexivity ]
  | let ms' := fresh "ms'" in let vk := fresh "vk" in let vt := fresh "vt" in
    intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ].

(* [comment removed for export] *)
Ltac step_to_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac
  | |- _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; step_to_if
  end.

Tactic Notation "shadow_chk" constr(H) constr(c) constr(n) :=
  let k := fresh "k" in let RD := fresh "RD" in let HK := fresh "HK" in
  shadow_byte H c n as k RD HK;
  zstep; clear RD; step_to_if;
  shadow_merge c k HK.

Tactic Notation "shadow_chk1" constr(H) constr(c) := shadow_chk H c 1.

(* [comment removed for export] *)
Ltac shadow_merge_slow c k HK Kz :=
  step_to_if;
  lazymatch goal with
  | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with true by (symmetry; eapply (shadow_slow_takenN c _ k _ HK Kz); qlia); cbv iota
  end.

Ltac shadow_merge_keys2 c k HK pk pt :=
  lazymatch goal with
  | |- evtA ?segs ?L ?CS ?Q (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      eapply (evtA_cut segs L CS
                (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro) Q);
      [ let Kz := fresh "Kz" in
        if_cases Kz; zify_cond Kz;
        [ shadow_merge_slow c k HK Kz; apply evtA_done; eexists; eexists; reflexivity
        | apply evtA_done; eexists; eexists; reflexivity ]
      | let ms' := fresh "ms'" in let vk := fresh "vk" in let vt := fresh "vt" in
        intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ]
  end.

Ltac shadow_merge_keys1 c k HK pk :=
  lazymatch goal with
  | |- evtA ?segs ?L ?CS ?Q (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      eapply (evtA_cut segs L CS
                (fun ms' => exists vk : word, ms' = MS (tset pk vk R) F (Z_to_bv 64 fast) fc rv m ro) Q);
      [ let Kz := fresh "Kz" in
        if_cases Kz; zify_cond Kz;
        [ shadow_merge_slow c k HK Kz; apply evtA_done; eexists; reflexivity
        | apply evtA_done; eexists; reflexivity ]
      | let ms' := fresh "ms'" in let vk := fresh "vk" in
        intros ms' (vk & ->); cbv beta iota delta [tset]; try clear HK; try clear k ]
  end.

Tactic Notation "shadow_merge_regs2" constr(c) constr(k) constr(HK) constr(nk) constr(nt) :=
  let pk := eval vm_compute in (bv_key (Z_to_bv 5 nk)) in
  let pt := eval vm_compute in (bv_key (Z_to_bv 5 nt)) in
  shadow_merge_keys2 c k HK pk pt.
Tactic Notation "shadow_merge_regs1" constr(c) constr(k) constr(HK) constr(nk) :=
  let pk := eval vm_compute in (bv_key (Z_to_bv 5 nk)) in
  shadow_merge_keys1 c k HK pk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  try (assert (Ha : (0 <= a)%Z) by lia);
  try (assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; slia));
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; first [ dt_apart_sb | slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | lia | simpl_sizes; lia ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia | simpl_sizes; lia | intros; simpl_sizes; lia ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | lia | simpl_sizes; lia | simpl_sizes; lia ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  (* [comment removed for export] *)
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (abase_frame segs L CS OK m a bs) in H; [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | sf_a0 | sf_al ]
            | idtac "note: could not carry abase across the store (dropping):" H; clear H ]
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (aobj_frame segs L CS OK m A n a bs) in H; [ | simpl_sizes; solve_crange | sf_a0 | sf_al ]
            | idtac "note: could not carry aobj across the store (dropping):" H; clear H ]
  end;
  try clear Ha; try clear Hl.

(* [comment removed for export] *)
Ltac solve_w_client :=
  lazymatch goal with
  | |- w_client ?CS ?W => unfold w_client; repeat (apply Forall_cons; [ cbn [fst snd]; solve_crange | ]); apply Forall_nil
  end.
Ltac solve_w_nonempty :=
  repeat (apply Forall_cons; [ cbn [fst snd]; qlia | ]); apply Forall_nil.

Ltac transport_after_callA segs m m' MU :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (aobj_munch segs L CS OK W m m' A n) in H; [ | solve_w_client | exact MU ]
            | idtac "note: dropping aobj (callee footprint not provably client):" H; clear H ]
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (abase_munch segs L CS OK W m m') in H; [ | solve_w_client | solve_w_nonempty | exact MU ]
            | idtac "note: dropping abase across call:" H; clear H ]
  end.

(* [comment removed for export] *)
Ltac post_callA segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_callA segs m m' MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ])
  end).

(* [comment removed for export] *)
Tactic Notation "callA" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtA ?segs _ _ _ (MS _ _ _ _ _ ?m _) => eapply evtA_cut; [ eapply SPEC | post_callA segs m ]
  end.
Tactic Notation "callxA" tactic3(apptac) :=
  lazymatch goal with
  | |- evtA ?segs _ _ _ (MS _ _ _ _ _ ?m _) => eapply evtA_cut; [ apptac | post_callA segs m ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac finish ::=
  first [ apply evt_done | apply aevtM_done | apply evtA_done ];
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  first [ dex_eexists_all | repeat (lazymatch goal with |- ex _ => eexists end) ];
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.
