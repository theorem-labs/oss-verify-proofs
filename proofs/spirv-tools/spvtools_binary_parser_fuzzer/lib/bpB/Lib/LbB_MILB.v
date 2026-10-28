(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_MILB () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2InI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC47Corelib4Init9Datatypes3fstK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblI47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_r".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition LY_A : Layout.
Proof.
  refine {| ly_malloc := 0; ly_free := 0; ly_new := 0; ly_new_arr := 0; ly_delete := 0; ly_delete_arr := 0;
            ly_new_handler := 0; ly_oom_spin := 0; ly_gp := 0; ly_tp := 0; ly_errno_off := 0;
            ly_img := [(0, 4)]; ly_rw := [(0, 4)]; ly_relro := [] |}.
  - intros a H. exact H.
  - intros a H. exists 0, 4. split; [left; reflexivity | lia].
Defined.

Section MILB.
  Context {AC : AllocCeiling}.

  Definition MI_LB : MallocIface ASEGS LY_A.
  Proof.
    refine {| AS := list (Z * Z); ainv := fun _ _ _ => False; live := fun A => A; owned := fun _ _ => False;
              size_class := fun _ => 0; BIG := 1; NMAX := 1; round_big := fun n => n;
              caps := fun _ _ => 0; bigcap := fun _ => 0; room_for := fun _ _ => True; MALLOC_STACK := 0;
              static_cells := []; may_fail := fun _ _ => True |}.
    all: intros; try contradiction; try lia; try exact I.
    all: try match goal with H : In _ [] |- _ => destruct H end.
  Defined.
End MILB.

Definition AC_A : AllocCeiling.
Proof.
  refine {| alloc_ceiling := sp_window_lo - stack_max_size |}.
  - unfold sp_window_lo, sp_window_hi, stack_max_size. lia.
  - unfold sp_window_lo, stack_max_size. reflexivity.
Defined.

Definition MI_A : MallocIface ASEGS LY_A := @MI_LB AC_A.

Definition lbl (LB : list (Z * Z * Z)) : list (Z * Z) := map (fun b => (snd (fst b), snd b)) LB.

Lemma lbl_in : forall LB p A n, In (p, A, n) LB -> In (A, n) (lbl LB).
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_MILB ()) [] "h01Ah11xh21Bh31fh41lh51yh61Hh72H0h82LBh91bh:1nh;1pp;2p;1p;4p;3p;5p-1R0g0000R1p4p710p8P0P1p4p7210p8P0g000LR2p4p710p8P0P2p4p7210p8g000ij29Tg001Ij1:Tg001ij45Tg002Ij30TP1j46Tg002`j32Tg003:R1j24Tg003Uj28Tg003oj5<Tg004Nj37TP2j33Tg004kj2;Tg005Ej4?Tg005`j4>Tg006:j1=Tg0073R2P2f1R0f0R3C5p=11922R4/92R5#:P4P2f2R6/10R7P3C5f3R8505g007QR9p4p710R:P9p4p7210R9P0\0R;%:6R<P1f4R1P8P6P0C69083f5R=P1P3O1=2=6f6R>?038'4X1='8R?[P8P3O1=210A0=36'4X11,81P=P1P8P6C69010[R@P>P=P1P8C690=6\?P1P8P6P0P3D<P3n2001000000120000000X56W4W3W2W0P@^56^4<^3;^29^0:P3P5P4A74239322A3423'1R:X95P=1186R9P51118R8924:A053>'4X15P4P2P8P6C5R6A74269322A3426'1=249A056=1;49P0C?C>O6b7%=19047eW6X:2X02X;2W8o"). Qed.

Lemma lbl_in_inv : forall LB A n, In (A, n) (lbl LB) -> exists p, In (p, A, n) LB.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_MILB ()) [] "p'0h01pi001ph11Hh21xi011xh31Eh41Ih52H0h61Ah71zi021zh82A'h91Bh:2H1h;1eh<1fh=1lh>2n'h?1yh@2H2hA2LBhB1bhC1nhD2p0p;2p;1p;3p;4p;5p;6p;8g000iR0j2?Tg001Ij1BTg006:j1DTg002Ij36Tg0000j4ATg003UR1j2:Tg003oj5ETg004Nj39Tg000Lj37Tg002`R2j32Tg007nj6@Tg005`j4HTg008Kj8=j6>Tg004kj2FTg001ij44Tg003:R3j2GTg0073R4P4f1R5f0R6C4p=0f5R7f4R8f3R932f2R:?656'Gp=5A7446p=8P8P4P4P4P9P:C4P5C4=676p=11:46p=3P:P4P5P6C4p=<P9P4P:P5C4=686p=CP9P4P4P4P:P5C4P6C4p=IP4P4P5P6C4929:p=;1?44R;/?4R<#B1056%D:56;g007QR=p4p710R>P=p4p7210R=P5\5R?%B:R@P3P8P9P:P5CA9696P7P8P6O1P:f6RAP6P9E5X27,:7[RBP8P9P6O1P5P7P6P:E5X28,:8P7P8P9P:CA9685RC[PAP7P6O1P9f7RDP6P8E5X2A,:A\CP8P9P:P5P6DEP5n2001000000120000000X?:W=W<W9W6PB^?:^=@^<?^9=^6>P6P<P;A9;46#8A7;46'0R>XB<P8109:R=P5O6P;P>1089P<P6P7E5X2<,:<P1P<P;P>1078R1P<P6PAE5X2<P<P;P6PAP7PDE1X04#3P6P0P;P4P;P>f8R>/0DR?P<P6f9R@E5P<P;P6f:RBP@f;RCE1X04#3[P6P0P4P4P;A<;56RE99;4#8A7;4E'0f<RF/0CP<PEf=REE5P<P;f>RG,06RHPEf?RIDCX04#3[^74P6P;P;P:P5P6CIR:99;4#8A7;4:'010IGP<P:f@R:E5P3P;A<;=5R=99;4#8A7;4='0P:PIC;fAR396<=P<P;P6fBR=P3fCRJE1X04#3P6P;A<;19R199;4#8A7;41'0P=P3C;P<P;10A7R7P8fDR8DCP2P;P7fFR2fER1'0RK92;5P<P;P6fHRLfGRMfIRNE1X04#3[P5108JRO92;710DA1018R852;P;P4P0P4P4P4P6P6n2001100000120102102X;;P?PKP6E@A24D1P;P4P0P4P4P4P6P5n2001100000120102102X;;10@>10M2P5E@A24@MA24BLP6A24CNRNP4fJRCA24FCRCP<P;P6fMRBfLR0fNR1E1X04#3[X74P6PCP4fKRCP<P;P6P1PBfORDE1X04#3X74P4P0P;PHPBP0C;P<P;P3P5PIPDE1P<P;P6fPRHPDfQRKE1X04#3]4]3X84P;100EP0PCC;P<P;P:PBPGP1E1P4PBP<P;P=PDP6PHE1P;10H5PHPDC;P<P;P6fRR=PKfSE1X04#3]3]4X>4P<P;P3P1PBPDE110D1RD=2;DP4P<P;P6PKPHP=E1X04PJP5CHW3W4PIP9P6P5G=W4W3PGP9P@P>G=PEP6E>b@X:NPFP6E>b:W5P6O1b5P6O1b5W1P6O1W1n2002100000000101A2;68P<P;P6PMP2PLE1X04#3[X0;POO1P61F;8O1b1W4W3P5P6O2n2001000000121000000W1X>4X84X04P5P6O2n2001100000121102102XD;P5P6O2n2001100000121100102X2<P5P6O2n2001000000121101000b1b5W1XC4X64WAo"). Qed.

