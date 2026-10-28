(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict RestrictLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_exit_lib () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "mapped"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.B.ARestrict.AIMG_HI"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mrd"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"].


Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Z.sub].
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac solve_condU := unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec.
Ltac if_trueU :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condU]
  end.
Ltac if_falseU :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condU]
  end.
(* [comment removed for export] *)
Ltac addr_diff E A ::=
  let k := addr_diff_raw E A in
  lazymatch eval vm_compute in (Z.leb 0 k && Z.ltb k 4096)%bool with true => k end.

Ltac show_left := match goal with |- _ (MS _ _ ?pc _ _ ?mm _) => idtac "LEFT AT:" pc mm | |- ?g => idtac "SIDE:" g end.


Lemma low_byte_mul8_land7 : forall k, Z.land (bv_unsigned (Z_to_bv 8 (8 * k))) 7 = 0.
Proof.
  intros k. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite land_7_mod.
  pose proof (Z.div_mod (8 * k) 256 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (8 * k) 256 ltac:(lia)) as B.
  set (r := (8 * k) mod 256) in *. set (t := (8 * k) / 256) in *.
  replace r with ((k - 32 * t) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma shiftr3_mul8 : forall x, Z.shiftr (8 * x) 3 = x.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mul_comm. apply Z.div_mul. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seg_rom_high : forall x, AIMG_HI <= x < 2^64 -> seg_rom asegs (wa x) = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. unfold AIMG_HI in Hx.
  destruct (find_segment asegs (bv_unsigned (wa x)) (Z.of_N 1)) as [seg|] eqn:E; [|reflexivity].
  exfalso. rewrite wa_unsigned in E by lia.
  pose proof (find_segment_cov asegs asegs x (Z.of_N 1) seg E ltac:(auto) 0 ltac:(cbn; lia)) as C.
  rewrite Z.add_0_r in C. apply asegs_segcov in C. unfold AIMG_LO, AIMG_HI in C. lia.
Qed.

(* [comment removed for export] *)
Definition mapped (m : mem) (lo hi : Z) : Prop := forall x, lo <= x < hi -> exists b, m (wa x) = Some b.

Lemma mapped_sub : forall m lo hi lo' hi', mapped m lo hi -> lo <= lo' -> hi' <= hi -> mapped m lo' hi'.
Proof. intros m lo hi lo' hi' H H1 H2 x Hx. apply H. lia. Qed.

Lemma mapped_stk : forall m lo hi, mapped m lo hi -> 0 <= lo -> hi <= 2^64 -> stk asegs m lo hi.
Proof.
  intros m lo hi H Hlo Hhi. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [b Hb]. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mapped_rw_slice : ltac2:(CDefT.buildp (gd_tbl_A_exit_lib ()) "Pm,P,(0.&40.)(1.(0.&8.))Plo,$2.Phi,$2.PS,$2.Pk,$2.P,(3.R5.R4.R3.)P,(4.=R5.)P,(4.R5.(5.+2.+40.))P,(4.R7.R5.)P,(4.(6.R6.R5.)R7.)P,(4.=R6.)(7.(8.(0.&8.))Ljunk,(8.(0.&8.))(9.$:.R<.R9.(;.$<.(=.(>.R8.)R1.)(?.$<.))))")
(* [comment removed for export] *).
Proof.
  intros m lo hi S k H Hlo Hhi H1 H2 Hk.
  pose proof (mapped_stk m S (S + k) (mapped_sub m lo hi S (S + k) H H1 H2) ltac:(lia) ltac:(lia)) as ST.
  destruct (stk_carve asegs m S (S + k) (Z.to_nat k) ST ltac:(lia)) as [_ (junk & RW)].
  exists junk. replace S with (S + k - Z.of_nat (Z.to_nat k)) at 1 by lia. exact RW.
Qed.

(* [comment removed for export] *)
Lemma mapped_transport : ltac2:(CDefT.buildp (gd_tbl_A_exit_lib ()) "PW,(8.$10.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.Phi,$2.P,(3.R4.R2.R1.)P,(11.R6.R5.R4.)P,(4.$12.R4.)P,(4.R4.(5.+2.+40.))P,Px,$2.P,(13.(4.R7.R1.)(14.R1.R6.))(15.(16.R;.R2.)(7.(0.&8.)Lb,(0.&8.)(17.(1.(0.&8.))(18.$:.R:.(19.R3.))(1:.(0.&8.)R1.))))(3.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W m m' lo hi H MU Hlo Hhi CASE x Hx. unfold AIMG_HI in Hlo. destruct (CASE x Hx) as [O | (b & Hb)].
  - destruct (H x Hx) as [b Hb]. exists b. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. exact O.
  - unfold mrd in Hb. destruct (m' (wa x)) as [b'|] eqn:E; [exists b'; reflexivity|].
    rewrite seg_rom_high in Hb by (unfold AIMG_HI; lia). discriminate.
Qed.

Lemma rw_cells_mrd : ltac2:(CDefT.buildp (gd_tbl_A_exit_lib ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pn,$1;.Pbs,(8.(0.&8.))Pi,$2.P,(9.$:.R5.R4.(;.$<.(=.R3.R2.)(?.$<.)))P,(13.(4.=R2.)(14.R2.(1<.R4.)))(7.(0.&8.)Lb,(0.&8.)(17.(1.(0.&8.))(18.$:.R8.(19.(6.R7.R4.)))(1:.(0.&8.)R1.)))")
(* [comment removed for export] *).
Proof.
  (intros m A n bs i dd_H; ddestruct dd_H as [[WF (_ & _ & RD)] _]; intros Hi). cbn in WF. destruct WF as [WF _].
  cbn [cells_bytes cbytes] in RD. rewrite app_nil_r in RD.
  specialize (RD (Z.to_nat i) ltac:(rewrite WF; lia)). rewrite Z2Nat.id in RD by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; exact RD|].
  apply nth_error_None in E. rewrite WF in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wseg_638000 : wseg_ok asegs (Z_to_bv 64 0x63b700) 4096%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_6d4 : ltac2:(CDefT.buildp (gd_tbl_A_exit_lib ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$1;.P,(4.+63;700.R2.)P,(4.(6.R3.(1<.R2.))+63<700.)(17.$1=.(1>.$:.R5.(1?.&40.R4.)R3.)$20.)")
(* [comment removed for export] *).
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window asegs m (Z_to_bv 64 0x63b700) (Z_to_bv 64 a) 4096%nat n 0x63b700 0x63c700);
    [reflexivity | reflexivity | lia | exact wseg_638000 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia].
Qed.
