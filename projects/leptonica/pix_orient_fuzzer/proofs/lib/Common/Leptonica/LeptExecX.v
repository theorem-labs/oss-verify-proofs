(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptExecX () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK47Corelib4Init9Datatypes6option01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C69OSSVerify5KrLib6Common9Leptonica8LeptExec:ex_ptr_valC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib6Common9Leptonica8LeptExec:ex_kword_ZC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib6Common9Leptonica8LeptExec6ex_kwrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic2or00C69OSSVerify5KrLib6Common9Leptonica8LeptExec8ex_kdisjC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac ex_ext := repeat first [ rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ])
                            | rewrite ext_val_zx_id by (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]; try reflexivity;
                rewrite ?m_mul, ?zbv_mul, ?zbv_add, ?ex_ptr_val; try reflexivity; try (f_equal; lia);
                rewrite ?zbv_addw_small by lia; try reflexivity; try (f_equal; lia).
(* [comment removed for export] *)
Ltac ex_mem2 regs Hms :=
  eapply ex_msteps_mem; [exact Hms|]; cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs
                               | first [ solve [ex_bytes_eq regs]
                                       | (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; f_equal; ex_ext) ] ]);
  reflexivity.

(* [comment removed for export] *)
Ltac ex_runN nx fuel stops scr HR HK R' HR' Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in let Hlf := fresh "Hlf" in let Hex := fresh "Hex" in
              assert (Hex : sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr')) by (vm_cast_no_check (eq_refl (ss', scs, scr')));
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; ex_sc regs
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          Hex HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc Hlf Hex ]
          end
      end
    end
  end.

(* [comment removed for export] *)
Ltac exx_named z Hrdn tac :=
  eapply (dl_read _ _ _ z); [ tac | exact Hrdn | first [ reflexivity | (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; reflexivity) ] ].

Section KnowSum.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma exx_kword_sum : forall E m (eb eo v : expr) (b o off z : Z) (w : nat),
  edenot E eb = Z_to_bv 64 b -> edenot E eo = Z_to_bv 64 o -> edenot E v = Z_to_bv 64 z -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= b + o < 2 ^ 64)%Z -> (0 <= b + o + off)%Z -> (b + o + off + Z.of_nat w <= 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (b + o + off)) w = Some (Z_to_le_bytes w z) ->
  kentry_ok segs E m (KWord (SA (EAlu ALU_ADD eb eo) off) w v).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptExecX ()) ["KnowSum"] "h01bh11Eh22H1h32H2h42Hbh53Hboh62Hoh72Hrh82Hvh92Hwh:3Hw1h;2Hzh<2ebh=2eoh>1mh?1oh@3offhA1vhB1whC1zp;1p;2p;3p;4p;6p;Bg0000j15Tg000Uj1?Tg0013j1<Tg001Vj1:Tg0028j24Tg003Aj21Tg003gj33Tg004Aj12Tg004`j29Tg005:j20Tg005Wj26Tg0063j17Tg006Qj2@Tg006nj2>Tg007Jj2=Tg007ej1HTg008Ej1GTg008ej4FTg009]j2ETg00:Zj2DTg00;<j3CTg00<Ej3;Tg00<mj2BTg00>6j68Tg00>TlBATg00?]g00@e#5R0#5#5R1#5#5#5R2#?R3#<R4%?1#<R1#:[g00AJR5g00BSR6g00C1f9R7f7R8'4f4R9,13R:534f:R;/48=34:f;R:/48f3R<,13534g00CP#2R=/9<%2=#2#2#2#2#2#2,99g00CoR=f8R>,07R?'6%70%72'@R2,>?'=10;7/0>,6=10:;/07%H8'0/6216=71>72'=%G1R1#:p,4segsR2fAR=f=R?f<R0'0/0:,13P7CF1E7;,D133P2fCR2fBg00DMR1f@R@7C=RAf?RBf>RC/0?RDP0P:P;P4113Cf0R;fD/4=5;110BC,13R:534X04P4113?113B=;1;=34:X041BC?142@P>E8142=P7E8142A113D534eP8f6f5P9P<f2f1P;MBAW7W;W3W2W5W9W:W8W6W4WBXC6X@6X?6W0XA5X=5W<W>W1o"). Qed.

Lemma exx_kwr_sum : forall E m (eb eo : expr) (b o off n lo : Z) (N : nat),
  edenot E eb = Z_to_bv 64 b -> edenot E eo = Z_to_bv 64 o -> store_ok segs m (Z_to_bv 64 lo) N = true ->
  (0 <= lo)%Z -> (lo + Z.of_nat N <= 2 ^ 64)%Z -> (0 <= b + o < 2 ^ 64)%Z -> (lo <= b + o + off)%Z -> (0 < n)%Z -> (b + o + off + n <= lo + Z.of_nat N)%Z ->
  kentry_ok segs E m (KWr (SA (EAlu ALU_ADD eb eo) off) n).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptExecX ()) ["KnowSum"] "h01bh11Eh22H1h32H2h42HNh52HSh62Hbh73Hboh83Hloh92Hnh:2Hoh;1Nh<2ebh=2eoh>2loh?1mh@1nhA1ohB3offp;1p;2p;3p;4p;6p;Ag0000j14Tg000Uj1;Tg0013j18Tg001Vj1>Tg0028j23Tg003Aj21Tg003gj32Tg00E9j4?Tg005Wj25Tg007ej17Tg005:j20Tg0063j16Tg006Qj2=Tg006nj2<Tg007Jj2CTg00;<j3BTg00<Ej3:Tg00<mj2ATg00>6j69Tg00F9lA@Tg00?]g00@e#4R0#4#4R1#4#4#4R2#;R3#8R4%;1#8#>[g00AJR1g00BSR5g00C1f9R6f7R7'3f5R8,13R9524f:R:/37=249g00G>p,4segsR9P:f3R;,13f2R<C?g00G^32g00CoR=f4R>'5%7>,08%60%62'=R2'510:6R0,5=1<02'Cf;R0/0:/06,571<=6f=R=f<R2'0/00/0:f8R?#7,06'5P9fBR9fAg00DMR@f@RAf?RB3BRCf>RD/0=REP2P0P:P6P4113Df0R6fC/3A5:@10BD,13R:524X04P4113=113B=:@6=24:X041AD=139BP7E9139AP?E9139C113E524ef6P8P>P;P<f1P6MA@W3W9W2W7W4W8W5W:W6W;X>5X@5XB5XA5W0X=1W<W?W1o"). Qed.

Lemma exx_kdisj_sum : forall E m (eb1 eo1 eb2 eo2 : expr) (b1 o1 b2 o2 k1 n1 k2 n2 : Z),
  edenot E eb1 = Z_to_bv 64 b1 -> edenot E eo1 = Z_to_bv 64 o1 -> edenot E eb2 = Z_to_bv 64 b2 -> edenot E eo2 = Z_to_bv 64 o2 ->
  (0 <= b1 + o1 < 2 ^ 64)%Z -> (0 <= b2 + o2 < 2 ^ 64)%Z ->
  (b1 + o1 + k1 + n1 <= b2 + o2 + k2 \/ b2 + o2 + k2 + n2 <= b1 + o1 + k1)%Z ->
  kentry_ok segs E m (KDisj (SA (EAlu ALU_ADD eb1 eo1) k1) n1 (SA (EAlu ALU_ADD eb2 eo2) k2) n2).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptExecX ()) ["KnowSum"] "h01bh11Dh21Eh32H1h42H2h52H3h62H4h72R1h82R2h92b1h:2b2h;3eb1h<3eb2h=3eo1h>3eo2h?2k1h@2k2hA1mhB2n1hC2n2hD2o1hE2o2p;1p;2p;3p;6p;@g0000j14Tg000Uj1>Tg0013j1;Tg001Vj1@Tg0028j20Tg003Aj23Tg003gj32Tg005:j21Tg005Wj25Tg0063j1:Tg006Qj2?Tg006nj28Tg007Jj29Tg00H>j2BTg00;<j3=Tg00<Ej37Tg00<mj2<Tg00>6j66Tg00HXl@ATg00?]g00@e#4R0#4#4R1#4#4#4R2#>R3#;R4%>1#;#@[g00AJR1g00BSR5f=R6f;R7'0f7R8,33R9524f>R:/07=249f?R;/07=249f@R</07=249g00CoR9f:R=,17R>'5%:0%:2'?R2,8>'9f9R0,1=R?,5918?2'9f<R?,16R2/10R9f8R@'111>8R>'5f6RA,1>/59'Bp,4segsfDR9fCg00DMR>fBRBfARC3=RDA=><;RE11:6RF11?7RGP=P0P@P8P4133:f0R8fER@/0B57>11;:,33R0524X04P41336R=133;=7>8=240X041<:6109Cf5E6109BPAE6109D133F524eP4133?10@<97>81332R2524X04P41337A7>=8=242X041<?7109;f3E6109<f4E6109E133G524ef2f1P8M@AW1W8W7W6W5W4W3XC5X@5XB5X?5XE5X:5XD5W9X>1X<1X=1W;WAW2o"). Qed.
End KnowSum.
