(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Canon () := "C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4list00c69OSSVerify5KrLib2K54Spec5Canon6canonTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Canon<canon_tracesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c69OSSVerify5KrLib2K54Spec5Canon9ctrace_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01c69OSSVerify5KrLib2K54Spec5Canon9ct_eventsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init9Datatypes4bool00i69OSSVerify5KrLib2K54Spec5Canon6ctrace00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02c69OSSVerify5KrLib2K54Spec5Canon:canonT_iffC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib2K54Spec5Canon:open_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib2K54Spec5Canon9msg_usageC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec5Canon6ctrace01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Canon?msg_cannot_openC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Canon>msg_read_errorC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedc69OSSVerify5KrLib2K54Spec5Canon:file_traceC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3eqbC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive03i69OSSVerify5KrLib2K54Spec5Canon6oclass00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01k69OSSVerify5KrLib2K54Spec5Canon6oclass01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C46Stdlib5Lists4List7map_appc69OSSVerify5KrLib2K54Spec5Canon3evwC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c69OSSVerify5KrLib2K54Spec5Canon9zeros_outC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K46Stdlib7Strings5Ascii5ascii01C69OSSVerify5KrLib2K54Spec6Prelim3strC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string02K46Stdlib7Strings6String6string01C69OSSVerify5KrLib2K54Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Canon;msg_too_bigC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib2K54Spec5Canon=msg_short_hdrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Canon?msg_cfg_overrunC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition evw (fd : Z) (bs : list Z) : list event :=
  map (fun b => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)) bs.

(* [comment removed for export] *)
Record ctrace : Type := mkCT { ct_fd : Z; ct_bytes : list Z; ct_code : Z }.

Definition ct_events (fs : Fs) (ct : ctrace) : list event :=
  evw (ct_fd ct) (ct_bytes ct) ++ [ExitEv (Z_to_bv 64 (ct_code ct)) fs].

(* [comment removed for export] *)

Definition msg_usage (argv0 : list Z) : list Z := str "usage: " ++ argv0 ++ str " INPUT" ++ [10].
Definition msg_cannot_open (path : list Z) : list Z := str "cli: cannot open " ++ path ++ [10].
Definition msg_read_error (path : list Z) : list Z := str "cli: read error on " ++ path ++ [10].
Definition msg_too_big : list Z := str "cli: input >= 67108864 bytes, refused" ++ [10].
Definition msg_short_hdr : list Z := str "cli: input shorter than header" ++ [10].
Definition msg_cfg_overrun : list Z := str "cli: config_len overruns input" ++ [10].

(* [comment removed for export] *)
Definition zeros_out (calls : nat) : list Z := concat (repeat [48; 10] calls).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cfg_len (data : list Z) : Z := Z.land (znth data 0 + znth data 1 * 256) 0x7fff.

(* [comment removed for export] *)
Definition cfg_calls (data : list Z) : nat :=
  let cfg := if 0 <? cfg_len data then znth data 2 else 0 in
  Z.to_nat (Z.land cfg 3 + 1).

Definition file_trace (data : list Z) : ctrace :=
  let len := zlength data in
  if 67108864 <=? len then mkCT 2 msg_too_big 2
  else if len <? 6 then mkCT 2 msg_short_hdr 2
  else if len <? 6 + cfg_len data then mkCT 2 msg_cfg_overrun 2
  else mkCT 1 (zeros_out (cfg_calls data)) 0.

(* [comment removed for export] *)
Inductive oclass : Type := OCFail | OCDir | OCFile (data : list byte).

Definition open_class (path : list Z) (fs : Fs) : oclass :=
  let p := map (Z_to_bv 8) path in
  if (path_max <=? length p)%nat then OCFail
  else match p with
       | [] => OCFail
       | _ :: _ => if path_eqb p dot_path then OCDir
                   else match fs_lookup fs p with
                        | None => OCFail
                        | Some data => OCFile data
                        end
       end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctrace_of (argv : list (list Z)) (fs : Fs) (ok : bool) : ctrace :=
  if negb (Z.of_nat (length argv) =? 2) then mkCT 2 (msg_usage (nth 0 argv [])) 2
  else
    let path := nth 1 argv [] in
    match (if ok then open_class path fs else OCFail) with
    | OCFail => mkCT 2 (msg_cannot_open path) 2
    | OCDir => mkCT 2 (msg_read_error path) 2
    | OCFile data => file_trace (map bv_unsigned data)
    end.

Definition canon_traces (argv : list (list Z)) (fs : Fs) : list ctrace :=
  [ctrace_of argv fs false; ctrace_of argv fs true].

(* [comment removed for export] *)
Definition canonT (argv : list (list Z)) (fs : Fs) : list event -> Prop :=
  fun tr => exists ct, In ct (canon_traces argv fs) /\ is_prefix tr (ct_events fs ct).

(* [comment removed for export] *)

Lemma canonT_iff : forall argv fs tr,
  canonT argv fs tr <-> exists ok, is_prefix tr (ct_events fs (ctrace_of argv fs ok)).
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p'0h02okh11Hh22Hph32cth43Hinh54argvh62fsh72trh81xi001xi011bp;1p;3p;2p;4p;7p-1g0000R0p4p710p8g000GR1p4p70R2p10015p4p7210p8P2g001QR3p4p710p8P2p1002Gp4p710p8P2p1003Bp4p710p8P2p1004<p4p710p8P2p10058p4p710p8P2p1005Up4p7210p8g0062j1=Tg006Rj3:Tg007Kj27Tg008JR2j2;Tg008ej36Tg009aR4j28Tg00:;j49Tg00:Uj7BTg00;1j2ATg00;Kj3@Tg00;ej3FTg00<?j4<Tg00<Zj2?TP3j3>Tg00=VR3j2ETP0j3DTg00>0j3CTg00>JR0f4R5f3R6f2R7f1R8f0R936'?3>p=1g00?@R:/E9p=3g00?`R;?D89p=51?899>07p=0AC;89p=2g00@[R<9689p=4g00A;#=#=%=0A:789R0P7P6P5P6P9D1X0:R=#3[P8P7P6P7P9D1X0:#3R>A:678[P3P;1756,59A0769';X3;P6P5f5R?P5P9D1X0:#3P9f6R@/7?,59A05?9';P2f7R2/7@RA,58A0?@8P2f8RBf9RCPBP9D1X0:#3P917CB,56A0BC5P4f;RDf:REg00AYRF36/2?14DE/2?g00B9RE'8PDf<RGf=RHPGP9D1X0:#3P8A6GDF/2@P;A6HGFRIA0GH9f>RJf?RKf@RLPKP9D1X0:#3]2X3;A0DGIP:PHPJPKPJP9D1X0:RIPFP9C9W2P2P9P7FBW1P9O114GD/2@/8EP414HG/22PE%3IP914JH/2BP;14KJRIA0JK9PLfARGfBPGP9D1X0:#3]2X3;A0HJIP:PKPLPGPLP9D1X0:RLP<P9C9W2PCP9P5FBW1P9O1PE%3LP9n010000000X1EP9O1n200100000021000010000W1P9O1n200100000021000010000W2W4P8P9O2n2001000000120000000W1X3;P8P9O2n2001000000121100000X10P3P:P=A:567P9P:P?P@P2P@P9D1A:B2@[P914@?905?P;17B2,59A0@29';X3;RB142@R7157AR6A0?@7A62@FR2/271277R=/8E1A;79@=E3FP6eP9C<C9W2P5P?P@P?PFD1P;PBP2152ARAA0?@212221272/8E1A;23@PAeP9C<C9W2n0110100020000X8:P8P9O2n2001000000120100000X1>C<W7X61W5o"). Qed.

Lemma canonT_nil : forall argv fs, canonT argv fs [].
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "h04argvh12cth22fsp;1p;2p;3p;4g0062j16Tg007Kj23Tg0000j30Tg00BVj14Tg00<Zj25Tg001Qj32Tg008Jj2<Tg008ej31Tg00>0j3;Tg00C6j3:Tg00;1j27Tg00;Kj38Tg003Bj29Tg00<?j4>Tg00:;j4=Tg00A;#6#6g000Gg00?`R0f0R1f2f1R2'3500g00>JR3%43R4152132'<X10g00AY9121R5132190051515R69234A;055g00@[9121%405:090051705381936C>C=W2W0o"). Qed.

Lemma canonT_pclosed : forall argv fs tr tr',
  canonT argv fs tr -> is_prefix tr' tr -> canonT argv fs tr'.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p'0h02cth11Hh23Hinh32Hph43Hp'h54argvh62fsh72trh83tr'i001xp;1p;3p;2p;6p;4g0062j14Tg006Rj36Tg007Kj22Tg00<Zj23Tg008JR0j25Tg004<j6;Tg00<?j4:Tg00:;j49Tg0000j37Tg001Qj38Tg00?`R1f1R2f0R337p=1g00>JR4?823p=0g00A;#4#4g000G%44R5f3R6f2R7;62g00=VP1f5R8f4R9'2,131393,06'5X011076f6R:?686[P3f7R;/2:,1313:3,08'5P0f8/2;,1213;2,0:10:;f:R0f9R8;6;[P31208,161309,081080P1f>f=R8'2,13f;R91383'0'5X01P:f<R6,28,1:136:R6,00P7P4P0P9P6P3P2E;C:C9W4W3W2P2P3O2n2001000000120000000W1X01P2P3O2n2001000000120100000W1X85W7W6W5o"). Qed.

Lemma canonT_max : forall argv fs ok, canonT argv fs (ct_events fs (ctrace_of argv fs ok)).
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "h02okh14argvh22fsh32trh41Hp;1p;3p;2p;4g0062j12Tg006Rj33Tg008ej30Tg00<Zj21Tg001Qj34Tg00=Vj25Tg00CVj38Tg002Gj27Tg00:;j46Tg00A;#2#2R0g000GR1g00?@R2g00>JR3#2R4g008Jf2R5f1R6f0R733f3R8f4R9?087'1R:9435X02,52R;[A0857,159436X02,52A3856[R<A3985\;A8567P7n2001000000120000000W3X21X10P<^34^21^10P7P8P5A0856,15R7P2A0985,18=43:X02P61737C6O4b4W0W2W1o"). Qed.

(* [comment removed for export] *)
Lemma ctrace_of_fail : forall argv fs ok,
  Z.of_nat (length argv) = 2 -> open_class (nth 1 argv []) fs = OCFail ->
  ctrace_of argv fs ok = mkCT 2 (msg_cannot_open (nth 1 argv [])) 2.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p'0h02Hch12Hlh24argvh32fsh41oh52oki002okh61zi011bi024datai031xp;1p;2p;3p;4p;6g0062j1:Tg00DSj2=Tg00E3j1;Tg00ESj13Tg00F8j1HTg00>0j30Tg00FVj1CTg00BVj1?Tg00G5j42Tg00GQj24Tg00HNj26Tg00Hkj15Tg00IIj19Tg00JEj31Tg00K@j1<Tg00LBj17Tg00MCj1GTg00Maj1FTg00NDj1ETg0015j4BTg00Nnj1@Tg00Okj2ATg00;1j2>Tg00PLj68Tg008ej3DTg00A;R0#:R1#:g000Gg00?@R2f2R3,=1#;g00Pj#3R4#HR5500g00QOR6P1g00RJR7#CR8f3R9%?0R:C2/43g00RiR;30P0P5g00?`R<P2P<f0R=/65#5P1P7f5R>P:C2#9=155R?P6P<P2P6P9P1P8P>P:C2R>f4R@'4RAP;n0110000020000%<>=155RB%7>=155R>%34#3#GRC#FP0%ECP=CB#@RCn011030003000010102n0100000020000;0BX60P2P2P<1A44#5R4P?P6P<P2P6P=PAP;n0110000020000PBP>PCn011030003000010102n0100000020000=0<BP3P6P;P2P<P4P?P6P<P=PBP>PCn011030003000010102n0100000020000=0<BX46P1P8P@P:C2R8#<=155RB,><R>1489R?P=E8P>n0110100020000P2P<1655#5P1P7P@P:C2#9=155P6P<P2P6P3P?P;n0110000020000PB%78=155PCn011030003000010102n0100000020000=0<Be1=1@#;f1E8AD@93=0<BeW0W1W5W3W2o"). Qed.

Lemma evw_app : forall fd l1 l2, evw fd (l1 ++ l2) = evw fd l1 ++ evw fd l2.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "h01bh12fdh22l1h32l2p;1p;2p;5p;3g0062j15Tg00ESj10Tg00MCj14Tg00Sdj22Tg00TJj28Tg00U@j57Tg0058j33Tg00U\j21Tg00>0j36Tg00A;R0%50R1P0g00>JR2g00Pj#0#0#0R3#0#0#0#4f3'2%43f0R3'2'8X00f1R4P3D7%52f2R5A3043'11154115353236eX31W2W1o"). Qed.

Lemma zeros_out_S : forall n, zeros_out (S n) = [48; 10] ++ zeros_out n.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "h01np;1p;3p;2g0062j18Tg00VRj13Tg00ESj10Tg00F8j11Tg00BVj17Tg00C6j32Tg00W7j16Tg0058j34Tg00;1j25Tg00X3g00A;R0#8g00PjR1#3#0#0#0#0#1%01#3#0#1%70520520f0#6540'5W0o"). Qed.

(* [comment removed for export] *)
Example msg_usage_ex : msg_usage (str "prog") = str "usage: prog INPUT" ++ [10].
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p;1p;2p;8p;3g0062j1@Tg00VRj11Tg00ESj10Tg00F8j16Tg00BVj1=Tg00;1j2<Tg00XRj82Tg00Y1j1:Tg00IIj1;Tg00Yhj25Tg0058j3?Tg00>0j3>Tg00C6j38Tf0R0#1#6p=9g00A;R1f1R2#6;80p=3f2R3A8120581p=7f4f31520,53'5'5p=4%@1R3g00PjR2#1R0#1#0R4#1#0R5#1%04R4#1R6#1%00R0#0R7#0#0#1%17R7#1#9R8%07#9%02R2#0R7#0#0#0#6R9%04#0#6%06%10#1#1#1%17R7#0#0#1%17#1#0%12#0R2#0#0#0%12#0R7#1%07%=1,32R2'3'3'3'3'39789'3'337,3537'3'3'3'<g00AYR5P5P5P5g00@[R9P9P9P5G2R8P5P9P5P5P9P9P9P5G2R7P9P9P9P9P5P9P9P5G2R0P9P9P9P5P5P9P9P5G2R6g00ZIR4D4#:#;P9P5P9P5P9P9P9P5G2P9P9P5P5P9P9P9P5G2P9P5P5P5P5P9P9P5G2P6P9P5P9P5P5P9P9P5G2P5P9P5P9P9P9P5P5G2P5P5P5P5P5P9P5P5G2R:P8P7P0P6P:P9P5P5P9P5P5P9P5G2P5P9P9P9P5P5P9P5G2P5P5P5P5P9P5P9P5G2P9P5P9P5P9P5P9P5G2P5P5P9P5P9P5P9P5G2/54D4D4D4D4#:=?125>3do"). Qed.
Example msg_too_big_len : zlength msg_too_big = 38.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p;1p;2p;3g00ESj10Tg00VRj11Tg00F8j13Tg00;1j22Tg00Zjj25Tg00>0j34Tg00A;R0g00Pj#0#0#1#1#0#3R1'2g00[e,50=401do"). Qed.
Example file_trace_ex :
  file_trace [1; 0; 3; 0; 0; 0; 0] = mkCT 1 [48; 10; 48; 10; 48; 10; 48; 10] 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p;1p;3p;2g00F8j13Tg00VRj15Tg00ESj11Tg00BVj16Tg00JEj3:Tg00;1j29Tg00Nnj18Tg00>0j37Tg00C6j34Tg00A;R0f1f0R134p=0g00\cR2=401p=2g00?`R1g00PjR3#3R4%53R5#1#1#1#1#3R6%13#5#1#3R3%60R0,03,06,03,06,03,06'0'0;:2R2'9%35%20#2#2#2'0#2,04#8=712do"). Qed.
Example file_trace_ex2 : file_trace [1; 0; 3; 0; 0] = mkCT 2 msg_short_hdr 2.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p;1p;3p;2g00ESj10Tg00F8j13Tg00VRj11Tg00BVj1=Tg00JEj39Tg00;1j2<Tg00Nnj1;Tg00>0j3:Tg00C6j32Tf0R0#0#3p=4g00A;R1f1R2#3;20p=5f2R3A2120521p=8f4f3A21209213521521p=6g00\c=210p=7g00?`R0g00PjR3#0R2#3R4%13R5#0R6#0R7#0R8#1#1%16R6#1R9#0#0%06#0R6#1#3R:%15#0R;#1#0R<#3%02#0#0#4R=P:%19R9#4R:%0;R;#0#4%1<%4<R<%1;R;#1%46R6%19#3%4;R;P<%17#0R7#1#3R9P;P=P<P6%08#1#3R8P:P=P6P9P8%47%12#0%=1R1'5989;D6D6D6D6'578='538D6'5'5;94'<%71#7,55#7,53#;g00]A=9445:0do"). Qed.
Example file_trace_ex3 : file_trace [9; 0; 3; 0; 0; 0; 0] = mkCT 2 msg_cfg_overrun 2.
Proof.
ltac2:(KReplay.run1 (kr_t_Canon ()) [] "p;1p;3p;2g00ESj11Tg00F8j18Tg00VRj10Tg00BVj1=Tg00JEj39Tg00;1j2<Tg00Nnj1;Tg00>0j3>Tg00C6j32Tf0R0#0#8p=3%10#8p=4g00A;R1f1R2#8;20p=7f2R3A2120521p=:f4f3A21209213521521p=5g00\c=210p=6g00?`R0g00PjR3#1R2#8R4%03R3#1R5#1R6#1#0#3R7%05R5#0R8#1#4R9%15#1#3R5%03#1R:#0R;#1R<#8%12R=#1#1#4R>P7%08R8#3R7%48R8%06R6#0R?#1%3?%02R2#0#0#0#0P9%16#3R6P8P>P7%0;#4P6%1:R:#0R6#4R;P;%3<R;P8%36P>P5P8%1:#4%4<%12%=1R1'75:;D5D5D5D5'75:5'7D5D5;94'<%0=%61#6#6#6,73#6'7#;g00^A=9445>0do"). Qed.
