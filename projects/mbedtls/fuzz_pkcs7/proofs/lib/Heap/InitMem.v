(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import StrFun.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_InitMem () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "WithSegs.rw_bytes_b"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Lib.Mem.mrd"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.cells_wf"; "OSSVerify.KrLib.Lib.Cells.cells_bytes"; "OSSVerify.KrLib.Lib.Cells.cells_size"].



Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint rw_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A), wview segs (fun _ => None) (wa A) with
      | Some b', Some _ => bv_eqb b b' && rw_bytes_b (A + 1) bs'
      | _, _ => false
      end
  end.

#[using="Type"] Lemma rw_bytes_b_sound : ltac2:(CDefT.buildp (gd_tbl_InitMem ()) "Pbs,(0.(1.&8.))PA,$2.Pm,P,(1.&40.)(3.(1.&8.))P,(4.$5.(6.R2.R3.)$7.)P,Pa,(1.&40.)P,(8.(9.R4.(:.&40.R1.))(;.(:.&40.R1.)(<.R4.(=.(>.(1.&8.)R5.)))))(4.(3.(1.&8.))A1.R4.R2.(?.(1.&8.)))P,(9.=R4.)P,(9.(<.R5.(=.(>.(1.&8.)R6.)))(10.+2.+40.))Pi,$11.Pb,(1.&8.)P,(4.(3.(1.&8.))(12.(1.&8.)R9.R2.)(13.(1.&8.)R1.))(8.(4.(3.(1.&8.))(14.Vsegs,R8.(15.(<.R9.(=.R3.))))(13.(1.&8.)R2.))(16.(4.(3.(1.&8.))(17.Vsegs,R8.(15.(<.R9.(=.R3.))))(?.(1.&8.)))))")
(* [comment removed for export] *).
Proof.
  induction bs as [|b0 bs IH]; intros A m Hb Hm HA Hl i b Hn; [destruct i; discriminate|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom segs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
  cbn [length] in Hl, Hm.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. rewrite Z.add_0_r.
    assert (Hnone : m (wa A) = None). { apply Hm. rewrite wa_unsigned by lia. lia. }
    split. { unfold mrd. rewrite Hnone. exact Er. }
    unfold wview in *. rewrite Hnone. intros C. rewrite C in Ew. discriminate.
  - cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia.
    apply (IH (A + 1)%Z m Hb); try lia; [|exact Hn]. intros a Ha. apply Hm. lia.
Qed.

#[using="Type"] Lemma rw_cells_image0 : ltac2:(CDefT.buildp (gd_tbl_InitMem ()) "Pm,P,(1.&40.)(3.(1.&8.))PA,$2.Pbs,(0.(1.&8.))P,Pa,(1.&40.)P,(8.(9.R3.(:.&40.R1.))(;.(:.&40.R1.)(<.R3.(=.(>.(1.&8.)R2.)))))(4.(3.(1.&8.))A1.R5.R2.(?.(1.&8.)))P,(4.$5.(6.R3.R2.)$7.)P,(9.=R4.)P,(9.(<.R5.(=.(>.(1.&8.)R4.)))(10.+2.+40.))(18.Vsegs,R7.R6.(19.$1:.(1;.(>.(1.&8.)R5.)R5.)(1<.$1:.)))")
(* [comment removed for export] *).
Proof.
  intros m A bs Hm Hb HA Hl. pose proof (rw_bytes_b_sound bs A m Hb Hm HA Hl) as G.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:E. { apply (proj1 (G i b E)). } apply nth_error_None in E. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E. { apply (proj2 (G _ b E)). } apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_recast : ltac2:(CDefT.buildp (gd_tbl_InitMem ()) "Pm,P,(1.&40.)(3.(1.&8.))PA,$2.Pcs,(0.$1:.)Pcs',(0.$1:.)P,(18.Vsegs,R4.R3.R2.)P,(1=.R2.)P,(4.(0.(1.&8.))(1>.R3.)(1>.R4.))P,(4.$11.(1?.R4.)(1?.R5.))(18.Vsegs,R8.R7.R5.)")
(* [comment removed for export] *).
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)



End WithSegs.
