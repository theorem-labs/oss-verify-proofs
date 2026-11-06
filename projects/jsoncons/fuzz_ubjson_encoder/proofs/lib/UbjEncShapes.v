(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import ShapeAlg Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_UbjEncShapes () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec=list_byte_eqbC13~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C47Corelib4Init5Logic3notc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapesBlist_byte_eqb_trueC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ue_cfg (fdata : list byte) : Z :=
  (bv_unsigned (nth 0 fdata (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 fdata (Z_to_bv 8 0))) mod 32768.
(* [comment removed for export] *)
Definition ue_payload (fdata : list byte) : list byte := skipn (Z.to_nat (6 + ue_cfg fdata)) fdata.
Definition ue_header_ok (fdata : list byte) : Prop :=
  Z.of_nat (length fdata) < MAX_INPUT /\ 6 + ue_cfg fdata <= Z.of_nat (length fdata).
(* [comment removed for export] *)
Definition ue_reach_ok (P : list byte -> Prop) (inp : ProcInput) : Prop :=
  forall a0s path fdata,
    in_argv inp = [a0s; path] -> (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
    fs_lookup (in_fs inp) path = Some fdata -> ue_header_ok fdata -> P (ue_payload fdata).

(* [comment removed for export] *)
Definition t_body_k (K : TSet) (data : list byte) (fs : Fs.Fs) : TSet :=
  let len := length data in
  if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
  else if (len <? 6)%nat then t_die msg_short fs
  else
    let b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0)) in
    let b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0)) in
    let cfg := (b0 + 256 * b1)%Z in
    let config_len := Z.to_nat (cfg mod 32768) in
    if (len <? 6 + config_len)%nat then t_die msg_overrun fs
    else K.
Definition spec_k (K : TSet) (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
  match argv with
  | [_; path] =>
      if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
      else if list_byte_eqb path dot_path then
        t_alt2 (t_die (msg_cannot_open path) fs0) (t_die (msg_read_error path) fs0)
      else match fs_lookup fs0 path with
           | None => t_die (msg_cannot_open path) fs0
           | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_body_k K data fs0)
           end
  | _ => t_die (msg_usage (hd [] argv)) fs0
  end.

Lemma list_byte_eqb_true : forall p q, list_byte_eqb p q = true -> p = q.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncShapes ()) [] "p'0h01Hh12b1h22b2h31nh42H0h51ph61qh72H1h81bi001bh91mh:2q0h;2H2h<2IHh=1ah>1ei011lp;1p;3p;2p;6p;8p;5g0000j1:Tg000Uj1ITg0013j15Tg001VR0j1ATg0026j30Tg002Pj1GTg0030j2?Tg003Jj6BTg003fj33j2=j1DTg004Fj2<Tg004ej37Tg005Rj29Tg006_j2;Tg007=R1j28Tg007Xj2HTg0089j2@Tg008Vj2FTg0096j26Tg009`j3CTg00:Dj8>Tg00:aj5ETg00;CR2f1R3f0R4'9g00;cR530p=2A0245p=1g00<CR6?034p=4g00<a#:#:#:#IR7#5R8#AR9P81234f2R:=093[^69R;X59P0P8%G8R</24A09<3[P4A02551?9<U12<<A09<<[eg00=FR==025R>P2P=P2p-0P4g00=fR=g00>Cn0110000020000X>2g00>_P5P4EBR5P=f3R?=38:R@909</<4b4W0A3834RA,2<A38:3RB909<[eX69X88P3P4O2n10110100020020100101X:9P0P8f4R0=38?RC/24f5=380RD=093[P4P5P=A09D</<4b4X0>12@<A09C<[ef7RC=773f6R</94';#1P11;34#1%1:R@%13R>'8[R=%14,8>1;:3#1R>[%1?/8@\>1H34P3n2001000000120000000X22X12P=^22^12P4f9R2=77?R=f8R>/9:R@P3O3%1=%1@'8P1f:R@=770#1122?f;R==38@=09DP4f<RD=77<#112D<P11@34#114:3[RD14341@:3#1R5[14?:\51F34P3n2001000000120000000X96X36PD^96^36P4f?R6,67RD1672R5P:O314D5P9P9f@R5,=81=8@P6P2P8P9\9R6%D8RDPDP5P@P6\8/?Dg00?;RD%54R6%53R@P1%5:?03416?:16?3'4R1[16:316:4'4%5??0:3[R5%50?0?:\1AC:34P4n2001000000120000000W2W1W3P5^2@^16^3DP4P7fAP=P3O4b0G>f>P2P:O2G>b7b0W;W7P3P4O2n2001000000121000000b0b4W0A38C</2AA38>C=09B[eX69X88P3P4O2n10110100020021100101X:9X<;X59X=8P4DEW5o"). Qed.
Lemma list_byte_eqb_neq : forall p q, p <> q -> list_byte_eqb p q = false.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncShapes ()) [] "p'0h01Eh11Hh21bi001bh31ph41qp;1p;3p;2g0000j12Tg000Uj19Tg0013j15Tg001Vj14Tg0026j30Tg00?Yj18Tg005Rj21Tg0030j23Tg00@2j36Tg004Fj27Tg00<a#2#2#2#9#5#4R0f1R1f0R2500#8f2R3/11g00;CR41342f3R5/13=042P4f5R3f4R6'1=042g00=FR79041]0P11165R1g00;cR8504A0487P5A6362O1'7W0A04171347W0n0110000020000P2O1b0b2W1X40W3o"). Qed.

