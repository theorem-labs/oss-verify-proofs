(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.G3 Require Import LeptFormats.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptShapes () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7forallbc69OSSVerify5KrLib2K52G3:LeptShapes6pshapeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K52G3;LeptFormats5lkind00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52G3:LeptShapes<shape_row_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52G3:LeptShapes;LEPT_SHAPESC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib2K52G3;LeptFormats5lkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52G3;LeptFormats5lkind02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K69OSSVerify5KrLib2K52G3;LeptFormats5lkind03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52G3;LeptFormats=LEPT_FMT_LISTC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pshape : Type := list (lkind * Z * list Z).

Definition lkind_bytes (k : lkind) : list Z :=
  match k with LK_s => [37; 115] | LK_d => [37; 100] | LK_zu => [37; 122; 117] end.

Fixpoint pshape_bytes (sh : pshape) : list Z :=
  match sh with
  | [] => []
  | (k, nx, t) :: r => lkind_bytes k ++ nx :: t ++ pshape_bytes r
  end.

(* [comment removed for export] *)
Definition ptxt_ok (l : list Z) : bool := forallb (fun c => (0 <? c) && (c <? 256) && negb (c =? 37)) l.
Definition pshape_ok (sh : pshape) : bool := forallb (fun it => ptxt_ok (snd (fst it) :: snd it)) sh.

Definition LS_00 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32]); (LK_s, 10, [])]).
Definition LS_01 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 119; 32; 61; 32]); (LK_d, 44, [32; 104; 32; 61; 32]); (LK_d, 44, [32; 100; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_02 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 102; 117; 122; 122; 101; 114; 32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 62; 32; 54; 52; 32; 77; 66; 59; 32; 114; 101; 102; 117; 115; 101; 100; 10])]).
Definition LS_03 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 102; 117; 122; 122; 101; 114; 32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 119; 105; 100; 116; 104; 32; 62; 32; 50; 48; 75; 59; 32; 114; 101; 102; 117; 115; 101; 100; 10])]).
Definition LS_04 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 102; 117; 122; 122; 101; 114; 32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 104; 101; 105; 103; 104; 116; 32; 62; 32; 50; 48; 75; 59; 32; 114; 101; 102; 117; 115; 101; 100; 10])]).
Definition LS_05 : list Z * pshape := ([87; 97; 114; 110; 105; 110; 103; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 116; 114; 32; 97; 100; 100; 114; 101; 115; 115; 32; 105; 115; 32; 110; 117; 108; 108; 33; 10])]).
Definition LS_06 : list Z * pshape := ([87; 97; 114; 110; 105; 110; 103; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 116; 114; 32; 97; 100; 100; 114; 101; 115; 115; 32; 105; 115; 32; 110; 117; 108; 108; 33; 10])]).
Definition LS_07 : list Z * pshape := ([73; 110; 102; 111; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 105; 120; 32; 105; 115; 32; 50; 52; 32; 98; 112; 112; 10])]).
Definition LS_08 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 99; 109; 97; 112; 32; 100; 101; 112; 116; 104; 58; 32]); (LK_d, 10, [])]).
Definition LS_09 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 99; 109; 97; 112; 32; 110; 97; 108; 108; 111; 99; 32; 61; 32]); (LK_d, 59, [32; 100; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_10 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 99; 109; 97; 112; 32; 110; 58; 32]); (LK_d, 59, [32; 110; 97; 108; 108; 111; 99; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_11 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 105; 120; 32; 100; 101; 112; 116; 104; 32]); (LK_d, 32, [62; 32; 56; 10])]).
Definition LS_12 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 40; 112; 105; 120; 32; 100; 101; 112; 116; 104; 32; 61; 32]); (LK_d, 41, [32; 62; 32; 40; 99; 109; 97; 112; 32; 100; 101; 112; 116; 104; 32; 61; 32]); (LK_d, 41, [10])]).
Definition LS_13 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 99; 109; 97; 112; 32; 97; 114; 114; 97; 121; 32; 105; 115; 32; 101; 109; 112; 116; 121; 59; 32; 105; 110; 118; 97; 108; 105; 100; 32; 119; 105; 116; 104; 32; 97; 110; 121; 32; 112; 105; 120; 10])]).
Definition LS_14 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 99; 109; 97; 112; 32; 101; 110; 116; 114; 105; 101; 115; 32; 61; 32]); (LK_d, 32, [62; 32; 109; 97; 120; 32; 99; 111; 108; 111; 114; 115; 32; 102; 111; 114; 32; 112; 105; 120; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_15 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 40; 109; 97; 120; 32; 105; 110; 100; 101; 120; 32; 105; 110; 32; 105; 109; 97; 103; 101; 32; 61; 32]); (LK_d, 41, [32; 62; 61; 32; 40; 110; 117; 109; 98; 101; 114; 32; 101; 110; 116; 114; 105; 101; 115; 32; 105; 110; 32; 99; 111; 108; 111; 114; 109; 97; 112; 32; 61; 32]); (LK_d, 41, [10])]).
Definition LS_16 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 110; 98; 121; 116; 101; 115; 32; 61; 32]); (LK_zu, 10, [])]).
Definition LS_17 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 105; 120; 100; 97; 116; 97; 95; 115; 105; 122; 101; 32; 61; 32]); (LK_d, 44, [32; 109; 101; 109; 100; 97; 116; 97; 95; 115; 105; 122; 101; 32; 61; 32]); (LK_d, 44, [32; 105; 109; 100; 97; 116; 97; 95; 115; 105; 122; 101; 32; 61; 32]); (LK_d, 32, [110; 111; 116; 32; 97; 108; 108; 32; 101; 113; 117; 97; 108; 33; 10])]).

Definition LEPT_SHAPES : list (list Z * list lkind * (list Z * pshape)) :=
  [ (LF_00, map (fun it => fst (fst it)) (snd LS_00), LS_00)
  ; (LF_01, map (fun it => fst (fst it)) (snd LS_01), LS_01)
  ; (LF_02, map (fun it => fst (fst it)) (snd LS_02), LS_02)
  ; (LF_03, map (fun it => fst (fst it)) (snd LS_03), LS_03)
  ; (LF_04, map (fun it => fst (fst it)) (snd LS_04), LS_04)
  ; (LF_05, map (fun it => fst (fst it)) (snd LS_05), LS_05)
  ; (LF_06, map (fun it => fst (fst it)) (snd LS_06), LS_06)
  ; (LF_07, map (fun it => fst (fst it)) (snd LS_07), LS_07)
  ; (LF_08, map (fun it => fst (fst it)) (snd LS_08), LS_08)
  ; (LF_09, map (fun it => fst (fst it)) (snd LS_09), LS_09)
  ; (LF_10, map (fun it => fst (fst it)) (snd LS_10), LS_10)
  ; (LF_11, map (fun it => fst (fst it)) (snd LS_11), LS_11)
  ; (LF_12, map (fun it => fst (fst it)) (snd LS_12), LS_12)
  ; (LF_13, map (fun it => fst (fst it)) (snd LS_13), LS_13)
  ; (LF_14, map (fun it => fst (fst it)) (snd LS_14), LS_14)
  ; (LF_15, map (fun it => fst (fst it)) (snd LS_15), LS_15)
  ; (LF_16, map (fun it => fst (fst it)) (snd LS_16), LS_16)
  ; (LF_17, map (fun it => fst (fst it)) (snd LS_17), LS_17) ].

(* [comment removed for export] *)
Definition shape_row_ok (e : list Z * list lkind * (list Z * pshape)) : bool :=
  let '(f, ks, (t0, sh)) := e in
  (if list_eq_dec Z.eq_dec f (t0 ++ pshape_bytes sh ++ [0]) then true else false)
  && ptxt_ok t0 && pshape_ok sh && (1 <=? Z.of_nat (length (t0 ++ pshape_bytes sh))).

Lemma LEPT_SHAPES_ok : forallb shape_row_ok LEPT_SHAPES = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptShapes ()) [] "p;2p;1p;3p-1R0p10000R1p4p710R2p8P0P1p4p7210p8P0p1000LR1p4p710p8P0P1p4p7210R1p8P0g000iR0p4p710R3p8g001ER4p4p70R5P2p8P5P1p8P5P3p8g002Aj24Tg002[j11Tg003;j20TP0j32Tg003[j33Tg0045R0g004UR3'4g0055#1R5g005S#1'01054'0g006Qg007S32=303do"). Qed.

Lemma LEPT_SHAPES_cover : map (fun e => fst e) LEPT_SHAPES = LEPT_FMT_LIST.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptShapes ()) [] "h01ep;1p;2p;3p;4g002[j1@Tg003;j2?Tg008Tj12Tg0099j11Tg009^j17Tg00:<j1=Tg00:\j33Tg002Aj2ETg000Lj3DTg0000j4CTg003[j3BTg00;<j4>Tf0R0#1#7p=4%20#7p=5g0055R1f1R2#7;30p=9A3120p=8f4R3f3R4f2R5A3120531531531p=0g005SR6g00;\;30p=;A31209315p=<g00<Z=360p=Af6R7f5R8A3120931593149313531531p=:P3P4A3152P0C>p=Hf7P7P8A31459313P2C>;30p=6P3P4P5P2C>=380p=GA35209334p=F%@1R4%@6R3'?R5#@R2P5P4P3g00=XR8#2R7#2R9#2R:#1#2#4R;%18R8#1R<#2R=#2R>#1R?#5R@P@%28R8#1RA#1RB#1RC#4RDP@%2:R:#5RE%2A#2RA#4RF%5CRCPE%19R9#2RG#1RH#7RI%4?R?%1=R=#2RJ#7RKPEPI%17R7#2RLg00>=%=1531'9R1,8?D0D0D0%=6RM#;RN#;P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEP@%28R8#1RO#2RP#4RQ%2>R>#4RR%4JRSPQP?%5JRJPQ%5PRTPE%1=R=#4RUPE%1<R<#2RV#1RW#7RXPEPIPT%17R7#2#5RYPE%5ARZPEPXPEPIPTPY18T1R[9<EIR\9<EXR]9<ETR^D0D0D0D0D0D0D0D0D0%AMR_#AR`#A#;RaP5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPE%1ORO#5RbPS%5WRWPWPQP@PEP@PQPRPSPQP?PJPQPTPE%1<#5R<PE%2BRB%7ARA%19#2#1%1:R:#2%7=R9PEP@PQPbPSP?PQP[D0D0R['9'97<E'9F:D0D0D0D0D0D0PNP5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEPbPSPWPWPQP@PEP@PQPRPSPQP?PJPQPTPEPUPFPTPJPEP<PE%7PRP%28R8#2Rc%1H/9['9D0R[,8ZD0D0D0D0D0D0D0D0PNP5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEPbPSPWPWPQP@PEP@PQPRPSPQP?PJPQPTPEPZPQPF%4OROPZPJP[F:D0D0D0D0D0D0D0PNP5P4P3%1L#1#4%4cRcP@PCPFPCPOPEPFPCPEPIP?PKPE%5>R[PJP@PEPcPTPTP@PQP?P?PEPFP?PEPCPS%5BRH%7:=<H1R:D0D0D0D0D0D0D0D0PNDHRdP5PdP5P4P3%2G#1PCPbPDPEPFPCPEPIP?PKPEP[PF%2VRV#5RGPEPFP?PEPPPAPE%18R8#5RAP[P[P1D0D0D0D0D0D0'9PNP5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEPFPC%5=R=PcPHPFPTPE%48R8%4BRBPcP[PEPTPQP[PJPZPKP\F:D0D0D0D0D0D0%;_R_P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEPFPCP=PcPHPFPTPEP8PBPcP[PEPCPcPHPHPDP8PEPXPEPIPTP9P^D0D0D0D0D0D0D0D0D0%;`R`P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEPFPCP=PcPHPFPTPEP8PBPcP[PEPCPKPEPIPTP9PEPCPcPHPHPD188]D0D0D0D0D0D0D0D0D0P`P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEP[PFPGPEPTPQP[PJPZPEPIPTPEP<PE19>1F:D0D0D0D0D0P_P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPE%2LRL#5R_P[PFPGPEPTPQP[PJPZPEPXPEPIPT%4LRLPEP<PEP_P8PBPcP[PEPTPQP[PJPEPXPEPIPTPLP1F:R>,8ZD0D0D0D0D0D0D0D0D0D0P`P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEP8PBPcP[PEPcP@P@Pc%4VRVPEPFP?PEPQPBP[PJPVP9PEPFPCP=PcPHPFPTPEPUPFPJPZPEPcPCPVPEP[PFPGP1D0D0D0D0D0D0D0D0D0D0D0D0D0PNP5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEP8PBPcP[PEPQPCPJP@PFPQP?PEPXPEPIPTPEP<PEPBPcPGPEP8PDPHPDP@P?PEPbPDP@PEP[PF18G]D0D0D0D0D0D0D0D0D0D0D0D0P`P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEP_PBPcPGPEPFPCPTPQPGPEPFPCPEPFPBPcPOPQPEPXPEPIPTPLPEP<PXPEP_PCPSPBPAPQP@PEPQPCPJP@PFPQP?PEPFPCPEP8PDPHPDP@PBPc18[>F:D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P`P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEPFPCP=PcPHPFPTPEPCPAPVPJPQP?PEPXPEPIPW18S1F:D0D0D0D0D0D0g00>[=36M#;P5P4P3P;P@P@PDP@PEPFPCPEPIP?PKPEP[PFPGPTPcPJPc%17#1#4R7P?PFPWPQPEPXPEPIPTPYPEPBPQPBPTPcPJPcP7P?PFPWPQPEPXPEPIPTPYPEPFPBPTPcPJPcP7P?PFPWPQPEPXPEPIPTPEPCPDPJPEPcPHPHPEPQPRPSPcP:F:D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0Pa%=5G6G6G6G6G6G6G6G6G6G6EGDFG6G6G6G6G6'Eg001E,?4R4,?5RaP5AD540X0ag007SCCg00?Y5B2do"). Qed.
