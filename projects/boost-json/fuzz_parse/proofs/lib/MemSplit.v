(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec StepTac StoreOk StreamSim.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned37Corelib4Init9Datatypeskf6lengthkf6option46Stdlib6ZArith6BinInt1Zn93addn92len96of_natkf4Somekf4list37Corelib4Init5Logicr33andr32eq37Corelib5Lists7ListDeft23nth69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~uf6wbytesn92ltn93pown93subn96to_nathf7Z_to_bvr32orkf4boolkf4truekf5falsekf3natt26repeat3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeho07Segment69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hs03rdn01Z3h5LinuxProcessSemanticsfLinuxProcessSem5Stateig5estack_max_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MemSplit4FPX1~~~~~~ik56win_lon93lebkf4Noner33notik56in_winik53wfJ69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MemSplit~~~~~~ir34cmemir36win_loir36in_win3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjga8store_okir33wfJ69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~jl47wseg_okhs08wrap_memho08PhdrInfo3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjr39EntryDraw" s.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma wbytes_inside : ltac2:(zQ "h30!h9!jc!k1!m7!n0!p1!p7!pc!q5!qc!s7!sd!u9!hi9!hj2!hj7!hjd!hk3!hkc>2bs@1$9@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^2@1$7@2$3@1$1@1$0#8^4@2$f+2+k0>0@2$a@2$6@2$2@1$0#k0^3@2$2@1$0#k0^2@2$e@2$2@1$0#k0^2@2$5@2$2@1$0#k0^3@1$7@2$3@1$1@1$0#8^5@3$b@1$4@1$1@1$0#8@4$d^5^4^6^3@2$8@1$1@1$0#8@4$c@1$1@1$0#8@1$h1@2$h0@2$2@1$0#k0^3@2$2@1$0#k0^4^6@2$h2@1$0#8Z").
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
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : ltac2:(zQ "e0!h9!jc!k1!m7!n0!p1!p7!pc!qc!sd!hl6!hi9!hj2!hj7>2bs@1$8@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$6@2$5@2$2@1$0#k0^2@1$7@2$3@1$1@1$0#8^4@2$d+2+k0>0@2$a@2$c@2$2@1$0#k0^2@2$2@1$0#k0^3@2$6@2$5@2$2@1$0#k0^3@1$7@2$3@1$1@1$0#8^5@2$2@1$0#k0^2@3$9@1$4@1$1@1$0#8@4$b^5^4^6^3@1^5^3").
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma wbytes_select : ltac2:(zQ "h01!h9!jc!hlb!n0!k1!m7!sd!hi9!p1!p7!pc!qc!hm2!s7!hj2!hj7&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1P>0@1$1@1$0#k0$2>1f~0>1g~0>1a@1$1@1$0#k0>2bs@1$b@1$1@1$0#8>0@2$9@2$8@2$4@1$0#k0^2@1$a@2$5@1$1@1$0#8^1@2$f+2+k0>0>1x@1$1@1$0#k0>0@2$d@2$9@2$4@1$0#k0^4@2$4@1$0#k0^1@2$e@2$4@1$0#k0^1@2$8@2$4@1$0#k0^4@1$a@2$5@1$1@1$0#8^3@3$6$2@1^8^2$c@3$6~0@3$7\1x@1$1@1$0#k0M2\0$2@1$3@1$1@1$0#8@1^8^1@1^7^1@1^6^1^4^3\1x@1$1@1$0#k0M2\0$2@1$3@1$1@1$0#8@1^8^1@4$7^7^5^4^1@1^6^1").
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : ltac2:(zQ "h01!h9!jc!hlb!n0!k1!m7!sd!hi9!p1!p7!pc!hm9!qc!s7!hj2!hj7&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1P>0@1$1@1$0#k0$2>1f~0>1g~0>1a@1$1@1$0#k0>2bs@1$c@1$1@1$0#8>0@2$9@2$8@2$4@1$0#k0^2@1$a@2$5@1$1@1$0#8^1@2$f+2+k0>0>1x@1$1@1$0#k0>0@2$d@2$9@2$4@1$0#k0^4@2$4@1$0#k0^1@2$e@2$4@1$0#k0^1@2$8@2$4@1$0#k0^4@1$a@2$5@1$1@1$0#8^3@3$6$2@1^8^2$b@3$6~0@3$7\1x@1$1@1$0#k0M2\0$2@1$3@1$1@1$0#8@1^8^1@1^7^1@1^6^1^4^3\1x@1$1@1$0#k0M2\0$2@1$3@1$1@1$0#8@1^8^1@1^7^1@4$7^6^5^4^1").
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_shadow : ltac2:(zQ "d1!h9!jc!m7!hi9!qc!n0!sd!hn1!p1!p7!pc!hj7!k1&>0@1$1@1$0#k0@1$5@1$1@1$0#8>1m~0>1a@1$1@1$0#k0>3bs1@1$4@1$1@1$0#8>3bs2@1$4@1$1@1$0#8>0@3$6$7@2$2@1$1@1$0#8^2@2$2@1$1@1$0#8^1>0@2$9@2$8@2$c@1$0#k0^4@1$a@2$2@1$1@1$0#8^2@2$b+2+k0@3$6~0@3$3@3$3^6^5^4^5^3@3$3^6^5^3").
Proof.
  intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_const : ltac2:(zQ "h10!h9!jc!k1!qc!n0!q5!sd!p1!p7!pc!hn1!s7!hn7!hr5!hvb!hj2!hj7>4segs@1$3$d>1m>1x@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>1n$a>1b@1$1@1$0#8>0@2$8@2$7@2$2@1$0#k0^3@1$9^2@2$h0+2+k0>0>1x@1$1@1$0#k0>0@2$b@2$8@2$2@1$0#k0^5@2$2@1$0#k0^1@2$f@2$2@1$0#k0^1@2$7@2$2@1$0#k0^5@1$9^4@3$6@1$4@1$1@1$0#8@1^7^2@2$5@1$1@1$0#8^4@3$6@1$4@1$3@1$1@1$0#8@4$e^7^6^5^4@2$5@1$3@1$1@1$0#8@3$c@1$1@1$0#8^3^4").
Proof.
  intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat]. rewrite (Hall a) by lia.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition win_lo : ltac2:(zQ "30!h9!ig2!jc>3sp0@1$2@1$0#k0$1") := ltac2:(zQ "50!h9!ij3!hjd!jc!k1\3sp0@1$3@1$0#k0@2$2@2$4@1$0#k0^1$1").

Definition in_win : ltac2:(zQ "20!h9!jc>3sp0@1$1@1$0#k0>1x@1$1@1$0#k0P") := ltac2:(zQ "70!h9!k1!jc!s7!io5!p7!hj2\3sp0@1$2@1$0#k0\1x@1$2@1$0#k0@2$3@2$5@1$4^2@2$1@1$0#k0^1@2$6@2$1@1$0#k0^1@2$1@1$0#k0^2").

Definition cmem : ltac2:(zQ "31!h9!jc!n0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3sp0@1$1@1$0#k0>4mem0~0>1J~0>1D~0~0") := ltac2:(zQ "71!h9!jc!n0!hlb!k1!iof!io5&>0@1$1@1$0#k0@1$2@1$1@1$0#8\3sp0@1$1@1$0#k0\4mem0~0\1J~0\1D~0\1a@1$1@1$0#k0M3\0$3@1$2@1$1@1$0#8@2$5@2$4@1$0#k0^5@2$4@1$0#k0^1@1^4^1M3\0$3@1$2@1$1@1$0#8@2$5@1$6^5@2$4@1$0#k0^1@1^3^1@1^2^1").

(* [comment removed for export] *)
Definition wfJ : ltac2:(zQ "30!h9!jc!n0>3sp0@1$1@1$0#k0>1J>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "70!h9!jc!n0!ip5!sd!ipc!iq2\3sp0@1$1@1$0#k0\1J>0@1$1@1$0#k0@1$2@1$1@1$0#8>1x@1$1@1$0#k0>0@2$6^3^1@1$5@3$4@1$2@1$1@1$0#8@1^3^2@1$3@1$1@1$0#8").

Lemma wfJ_const : ltac2:(zQ "40!h9!jc!q5!iqc>3sp0@1$1@1$0#k0>1b@1$1@1$0#8@2$3^2\0@1$1@1$0#k0@2$2@1$1@1$0#8^2").
Proof. intros sp0 b x _. discriminate. Qed.

Lemma wfJ_wbytes : ltac2:(zQ "60!h9!jc!iqc!qc!n0!hi9>3sp0@1$1@1$0#k0>1J>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>2bs@1$3@1$1@1$0#8>0@2$2^4^3@2$2^5@3$5^4^3^2").
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

(* [comment removed for export] *)

End FPX1.

Section CMem.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable mem0 : ltac2:(zQ "30!h9!jc!n0>0@1$1@1$0#k0@1$2@1$1@1$0#8").

  Let csel := cmem sp0 mem0.

  Lemma stack_max_size_pos : ltac2:(zQ "20!ij3!hj2@2$1Z$0").
  Proof. rewrite stack_max_size_val. lia. Qed.

  (* [comment removed for export] *)

  Lemma wbytes_cmem_win : ltac2:(zQ "d1!h9!jc!n0!k1!hi9!iue!p7!m7!qc!sd!iv6!p1!pc&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0>1D~0>1a@1$1@1$0#k0>2bs@1$8@1$1@1$0#8>0@2$6@1$a?3sp0@2$3@1$0#k0^2>0@2$6@2$b@2$3@1$0#k0^3@1$c@2$7@1$1@1$0#8^2@2$3@1$0#k0?3sp0@3$9~0@3$4@4$5?3sp0?4mem0^6^5^4^3@4$5?3sp0?4mem0@3$4^6^4^3^5").
  Proof.
    intros J D a bs Hlo Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_le; lia]).
    reflexivity.
  Qed.

  Lemma wbytes_cmem_data : ltac2:(zQ "d1!h9!jc!n0!hi9!iue!m7!qc!sd!iv6!p1!p7!pc!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0>1D~0>1a@1$1@1$0#k0>2bs@1$6@1$1@1$0#8>0@2$a@2$9@2$c@1$0#k0^2@1$b@2$5@1$1@1$0#8^1@1$8?3sp0@3$7~0@3$3@4$4?3sp0?4mem0^5^4^3^2@4$4?3sp0?4mem0^5@3$3^4^3^2").
  Proof.
    intros J D a bs Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
    unfold win_lo in *.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma rdn_cmem_above : ltac2:(zQ "e1!h9!jc!n0!k1!qc!hvb!p7!hn1!sd!hr5!iue!p1!pc!hj7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$4$9>1J~0>1D~0>1a@1$1@1$0#k0>1n$7>0@2$6@2$3@1$0#k0?3sp0@2$3@1$0#k0^2>0@2$6@2$b@2$3@1$0#k0^3@1$c^2@2$d+2+k0@3$8@1$2@1$4@1$1@1$0#8@4$5^7@4$a?3sp0?4mem0^6^5^4^3@4$5^7?4mem0^4^3").
  Proof.
    intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
    intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_win : ltac2:(zQ "e1!h9!jc!n0!k1!qc!hvb!p7!hn1!sd!hr5!iue!iv6!p1!pc&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$4$9>1J~0>1D~0>1a@1$1@1$0#k0>1n$7>0@2$6@1$b?3sp0@2$3@1$0#k0^2>0@2$6@2$c@2$3@1$0#k0^3@1$d^2@2$3@1$0#k0?3sp0@3$8@1$2@1$4@1$1@1$0#8@4$5^7@4$a?3sp0?4mem0^6^5^4^3@4$5^7^6^4^3").
  Proof.
    intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_data : ltac2:(zQ "e1!h9!jc!n0!qc!hvb!hn1!sd!hr5!iue!iv6!p1!p7!pc!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$3$7>1J~0>1D~0>1a@1$1@1$0#k0>1n$5>0@2$b@2$a@2$d@1$0#k0^2@1$c^1@1$9?3sp0@3$6@1$2@1$3@1$1@1$0#8@4$4^6@4$8?3sp0?4mem0^5^4^3^2@4$4^6^4^3^2").
  Proof.
    intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
    unfold win_lo in *.
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem, win_lo.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma cmem_at_win : ltac2:(zQ "61!h9!jc!n0!sd!iue!jg0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0>1D~0>1x@1$1@1$0#k0>0@2$5?3sp0^1@3$3@1$2@1$1@1$0#8@5$4?3sp0?4mem0^4^3^2@1^4^2").
  Proof.
    intros J D x [Hlo Hhi]. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma cmem_at_data : ltac2:(zQ "81!h9!jc!n0!sd!iue!iv6!hj2!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1J~0>1D~0>1x@1$1@1$0#k0>0@2$6@2$7@1$0#k0^1@1$5?3sp0@3$3@1$2@1$1@1$0#8@5$4?3sp0?4mem0^4^3^2@1^3^2").
  Proof.
    intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma store_ok_cmem_win : ltac2:(zQ "h11!h9!jc!k1!n0!p7!hlb!qc!hn1!hm2!sd!hr5!jk1!iue!jkd!iv6!p1!pc&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$6$a>1J~0>1D~0>1a@1$1@1$0#k0>1n$7>0@2$d?3sp0^4>0@2$4@1$e?3sp0@2$2@1$0#k0^3>0@2$4@2$f@2$2@1$0#k0^4@1$h0^3@2$2@1$0#k0?3sp0@3$9$5@4$b^8@4$c?3sp0?4mem0^7^6^5^4$8").
  Proof.
    intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
    apply store_ok_of_all; [lia|].
    intros x Hx. unfold wview.
    rewrite cmem_at_win by (unfold in_win; lia).
    destruct (J x) as [b|] eqn:E; [discriminate|].
    exfalso. apply (HJ x); [unfold in_win; lia | exact E].
  Qed.

  Lemma store_ok_cmem_data : ltac2:(zQ "c1!h9!jc!hlb!n0!hm2!sd!qc!hn1!hr5!jk1!iue!jp0&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$6$8>1J~0>1D~0>1a@1$1@1$0#k0>1n$7>0@3$5$2@3$b^5^2^1$4@3$5$2@4$9^6@4$a?3sp0?4mem0^5^4^3^2$4").
  Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma cmem_init : ltac2:(zQ "c0!h9!jc!qc!jpb!ip5!q5!n0!sd!jq7!ju7!iue!hkc>2ph$8>3sp0@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>5rdraw$9@3$7>0@1$1@1$0#k0@1$6@1$1@1$0#8@7$3^7^6^5^4^3^2^1@4$a^6@7$3^7^6^5^4^3^2^1\0@1$1@1$0#k0@2$5@1$1@1$0#8@2$b@1$0#8Z\0@1$1@1$0#k0@1$4@1$1@1$0#8").
Proof.
  intros ph sp0 av ev uid hw rdraw. apply functional_extensionality. intro x.
  unfold cmem.
  destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
  apply Z.leb_gt in E1.
  unfold wrap_mem, win_lo.
  assert (Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = None).
  { unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r. reflexivity.
Qed.
End FPX2.
(* [comment removed for export] *)
