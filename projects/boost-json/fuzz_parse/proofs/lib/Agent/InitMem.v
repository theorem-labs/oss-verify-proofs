(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option37Corelib4Init5Logicm22eq46Stdlib6ZArith6BinInt1Znb3addnb6of_natnb2lek14Nonek14Somek16lengthm23and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~s42wahfbbv_unsignedk14boolk14listk13natk14truem23not01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshj55wview89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7InitMem8WithSegs~~~~~~hn5arw_bytes_bs43mrd36Stdlib5Lists4Listht29nth_errornb2ltnb3pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hvd4cellk14consk13nilhvd2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~il48rw_cellshvdbcells_byteshvdacells_sizehvd8cells_wf3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeis47Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithSegs.
Variable segs : ltac2:(zQ "20!hh8!iv9@1$0$1").

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

Lemma rw_bytes_b_sound : ltac2:(zQ "h90!h9!jc!l9!n6!p3!p9!q2!q7!qe!r5!re!ve!hg3!hh1!hh8!hhf!hi5!hic!hj2!hmc!hre!hsc!hu5!hv2!hv7>2bs@1$e@1$1@1$0#8>1A$h2>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0@3$3$d@2$h4^2^3$h0>0>1a@1$1@1$0#k0>0@2$a@2$6^4@2$c@1$0#k0^1@2$h7@2$c@1$0#k0^1@2$4^4@1$5@2$9@1$1@1$0#8^5@3$3@1$2@1$1@1$0#8@1^4^2@1$7@1$1@1$0#8>0@2$6Z^4>0@2$6@2$4^5@1$5@2$9@1$1@1$0#8^6@2$h8+2+k0>1i$f>1b@1$1@1$0#8>0@3$3@1$2@1$1@1$0#8@3$h6@1$1@1$0#8^9^2@2$8@1$1@1$0#8^1@2$a@3$3@1$2@1$1@1$0#8@3$h5?4segs^8@1$b@2$4^9@1$5^3@2$8@1$1@1$0#8^2@1$h1@3$3@1$2@1$1@1$0#8@3$h3?4segs^8@1$b@2$4^9@1$5^3@1$7@1$1@1$0#8").
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

Lemma rw_cells_image0 : ltac2:(zQ "h70!h9!jc!r5!q2!l9!n6!ij9!p3!p9!hg3!q7!hh1!ik1!hh8!ik8!hi5!re!hj2!hre!ike!iof!hv2!hv7>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1A$h1>2bs@1$d@1$1@1$0#8>0>1a@1$1@1$0#k0>0@2$h0@2$3^3@2$9@1$0#k0^1@2$h5@2$9@1$0#k0^1@2$7^3@1$8@2$2@1$1@1$0#8^2@3$5@1$4@1$1@1$0#8@1^5^2@1$a@1$1@1$0#8>0@3$5$b@2$h2^3^2$f>0@2$3Z^4>0@2$3@2$7^5@1$8@2$2@1$1@1$0#8^4@2$h6+2+k0@4$h4?4segs^7^6@3$c$6@2$h3@2$2@1$1@1$0#8^5^5@1$e$6").
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
Lemma rw_cells_recast : ltac2:(zQ "c0!hh8!h9!jc!n6!ij9!ipb!iqa!iof!hhf!l9!hj2!ir8>1m>0@1$2@1$1#k0@1$9@1$2@1$1#8>1A$a>2cs@1$0$4>3cs'@1$0$4>0@4$7?4segs^4^3^2>0@1$b^2>0@3$3@1$0@1$2@1$1#8@1$5^3@1$5^4>0@3$3$8@1$6^4@1$6^5@4$7?4segs^8^7^5").
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
End WithSegs.
(* [comment removed for export] *)
