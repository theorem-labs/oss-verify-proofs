(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlan. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesIO AsanNodesArg AsanMainLib ImgParams MainDefs Img_utf8_ubsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Cert_common ITab_utf8_ubsan.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SegPrint_utf8_ubsan_p2.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SegPrint_utf8_ubsan_p3.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SegPrint_utf8_ubsan_p4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SD1_utf8_ubsan : segdef := (SEG 64%nat 103%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 103%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 104);
   (EVar 105);
   (EVar 103);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 115)]
  [] 116%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 103%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 104);
   (EVar 105);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 103));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 115)]
  [KRange (EVar 103) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 103)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 103))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 116%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 103) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 104);
   (EVar 105);
   (EVar 103);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 115)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 116%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 103) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 116)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 117)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 118))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 119))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 117)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 117)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 118))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 117))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 117))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 117))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 124)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 125))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 126))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 127)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 116)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 117))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 118))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 119))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 128)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 129))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 130))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 131)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 120)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 121))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 122))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 123))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 132)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 133)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 134))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 135))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 133)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 133)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 134))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 133))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 133))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 133))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD2_utf8_ubsan : segdef := (SEG 64%nat 121%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 121%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118); (EVar 119, EVar 120)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 122);
   (EVar 123);
   (EVar 121);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (EVar 129);
   (EVar 130);
   (EVar 131);
   (EVar 132);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 133)]
  [] 134%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118); (EVar 119, EVar 120)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 121%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 122);
   (EVar 123);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 121));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (EVar 129);
   (EVar 130);
   (EVar 131);
   (EVar 132);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 133)]
  [KRange (EVar 121) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 121)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 121))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 134%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118); (EVar 119, EVar 120)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 121) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 122);
   (EVar 123);
   (EVar 121);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (EVar 129);
   (EVar 130);
   (EVar 131);
   (EVar 132);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 133)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 134%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118); (EVar 119, EVar 120)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 121) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 134)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 135)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 136))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 137))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 135)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 135)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 136))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 135))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 135))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 135))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 142)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 143))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 144))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 145)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 134)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 135))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 136))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 137))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 146)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 147))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 148))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 149)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 138)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 139))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 140))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 141))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 150)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 151)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 152))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 153))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 151)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 151)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 152))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 151))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 151))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 150)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 151))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 121) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD3_utf8_ubsan : segdef := (SEG 64%nat 105%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 105%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 106);
   (EVar 107);
   (EVar 105);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 117)]
  [] 118%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 105%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 106);
   (EVar 107);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 105));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 117)]
  [KRange (EVar 105) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 105)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 105))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 118%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 105) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 106);
   (EVar 107);
   (EVar 105);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 117)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 118%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 105) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 118)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 119)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 120))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 121))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 119)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 119)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 120))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 119))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 119))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 118)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 119))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 126)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 127))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 128))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 129)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 118)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 119))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 120))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 121))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 130)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 131))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 132))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 133)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 122)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 123))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 124))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 125))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 134)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 135)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 136))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 137))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 135)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 135)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 136))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 135))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 135))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 134)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 135))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 105) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD4_utf8_ubsan : segdef := (SEG 64%nat 107%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 107%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 108);
   (EVar 109);
   (EVar 107);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 119)]
  [] 120%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 107%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 108);
   (EVar 109);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 107));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 119)]
  [KRange (EVar 107) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 107)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 107))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 120%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 107) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 108);
   (EVar 109);
   (EVar 107);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 119)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 120%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 107) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 120)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 121)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 122))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 123))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 121)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 121)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 122))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 121))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 121))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 120)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 121))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 128)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 129))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 130))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 131)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 120)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 121))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 122))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 123))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 132)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 133))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 134))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 135)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 124)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 125))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 126))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 127))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 136)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 137)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 138))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 139))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 137)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 137)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 138))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 137))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 137))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 136)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 137))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 107) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD5_utf8_ubsan : segdef := (SEG 64%nat 109%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 109%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 110);
   (EVar 111);
   (EVar 109);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 121)]
  [] 122%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 109%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 110);
   (EVar 111);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 109));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 121)]
  [KRange (EVar 109) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 109)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 109))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 122%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 109) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 110);
   (EVar 111);
   (EVar 109);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 121)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 122%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 109) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 122)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 123)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 124))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 125))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 123)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 123)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 124))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 123))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 123))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 122)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 123))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 130)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 131))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 132))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 133)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 122)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 123))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 124))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 125))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 134)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 135))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 136))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 137)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 126)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 127))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 128))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 129))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 138)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 139)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 140))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 141))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 139)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 139)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 140))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 139))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 139))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 138)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 139))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 109) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD6_utf8_ubsan : segdef := (SEG 64%nat 111%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 111%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 112);
   (EVar 113);
   (EVar 111);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 123)]
  [] 124%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 111%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 112);
   (EVar 113);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 111));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 123)]
  [KRange (EVar 111) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 111)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 111))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 124%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 111) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 112);
   (EVar 113);
   (EVar 111);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 114);
   (EVar 115);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 123)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 124%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 111) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 124)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 125)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 126))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 127))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 125)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 125)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 126))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 125))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 125))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 124)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 125))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 132)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 133))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 134))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 135)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 124)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 125))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 126))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 127))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 136)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 137))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 138))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 139)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 128)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 129))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 130))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 131))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 140)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 141)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 142))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 143))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 141)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 141)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 142))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 141))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 141))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 140)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 141))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 111) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD7_utf8_ubsan : segdef := (SEG 64%nat 113%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 113%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 114);
   (EVar 115);
   (EVar 113);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 125)]
  [] 126%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 113%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 114);
   (EVar 115);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 113));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 125)]
  [KRange (EVar 113) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 113)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 113))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 126%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 113) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 114);
   (EVar 115);
   (EVar 113);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 116);
   (EVar 117);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 125)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 126%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 113) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 126)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 127)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 128))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 129))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 127)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 127)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 128))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 127))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 127))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 127))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 134)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 135))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 136))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 137)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 126)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 127))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 128))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 129))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 138)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 139))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 140))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 141)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 130)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 131))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 132))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 133))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 142)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 143)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 144))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 145))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 143)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 143)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 144))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 143))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 143))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 142)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 143))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 113) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD8_utf8_ubsan : segdef := (SEG 64%nat 115%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 115%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 116);
   (EVar 117);
   (EVar 115);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 127)]
  [] 128%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 115%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 116);
   (EVar 117);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 115));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 127)]
  [KRange (EVar 115) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 115)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 115))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 128%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 115) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 116);
   (EVar 117);
   (EVar 115);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 118);
   (EVar 119);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 127)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 128%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 115) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 128)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 129)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 130))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 131))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 129)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 129)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 130))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 129))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 129))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 128)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 129))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 136)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 137))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 138))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 139)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 128)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 129))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 130))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 131))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 140)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 141))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 142))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 143)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 132)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 133))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 134))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 135))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 144)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 145)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 146))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 147))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 145)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 145)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 146))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 145))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 145))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 144)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 145))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 115) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD9_utf8_ubsan : segdef := (SEG 64%nat 117%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 117%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 118);
   (EVar 119);
   (EVar 117);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 129)]
  [] 130%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 117%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 118);
   (EVar 119);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 117));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 129)]
  [KRange (EVar 117) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 117)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 117))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 130%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 117) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 118);
   (EVar 119);
   (EVar 117);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 120);
   (EVar 121);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 129)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 130%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 117) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 130)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 131)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 132))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 133))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 131)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 131)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 132))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 131))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 131))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 131))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 138)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 139))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 140))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 141)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 130)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 131))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 132))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 133))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 142)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 143))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 144))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 145)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 134)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 135))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 136))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 137))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 146)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 147)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 148))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 149))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 147)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 147)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 148))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 147))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 147))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 146)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 147))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 117) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD10_utf8_ubsan : segdef := (SEG 64%nat 119%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 67108864;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 119%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 120);
   (EVar 121);
   (EVar 119);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (EVar 129);
   (EVar 130);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 131)]
  [] 132%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 119%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 120);
   (EVar 121);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 119));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (EVar 129);
   (EVar 130);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 131)]
  [KRange (EVar 119) 1 67108864;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 119)) 0 67108864;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 119))) 1 281474976710656;
   KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 132%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 119) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 120);
   (EVar 121);
   (EVar 119);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 122);
   (EVar 123);
   (EVar 124);
   (EVar 125);
   (EVar 126);
   (EVar 127);
   (EVar 128);
   (EVar 129);
   (EVar 130);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 131)]
  [KRange (EVar 65) 1 67108864;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 132%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102); (EVar 103, EVar 104); (EVar 105, EVar 106); (EVar 107, EVar 108); (EVar 109, EVar 110); (EVar 111, EVar 112); (EVar 113, EVar 114); (EVar 115, EVar 116); (EVar 117, EVar 118)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 119) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 132)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 133)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 134))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 135))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 133)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 133)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 134))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 133))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 133))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 133))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 140)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 141))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 142))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 143)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 132)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 133))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 134))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 135))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 144)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 145))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 146))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 147)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 136)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 137))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 138))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 139))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 148)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 149)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 150))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 151))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 149)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 149)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 150))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 149))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 149))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 148)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 149))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 119) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD11_utf8_ubsan : segdef := (SEG 64%nat 101%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 65535;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 65535;
   KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 101%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 102);
   (EVar 103);
   (EVar 101);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 104);
   (EVar 105);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 113)]
  [] 114%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 101%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 102);
   (EVar 103);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 101));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 104);
   (EVar 105);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 113)]
  [KRange (EVar 101) 1 65535;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 101)) 0 65535;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 101))) 1 281474976710656;
   KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 114%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 101) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 102);
   (EVar 103);
   (EVar 101);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 104);
   (EVar 105);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 113)]
  [KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 114%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 101) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 114)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 115)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 116))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 117))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 115)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 115)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 116))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 115))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 115))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 114)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 115))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 122)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 123))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 124))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 125)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 114)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 115))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 116))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 117))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 126)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 127))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 128))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 129)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 118)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 119))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 120))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 121))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 130)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 131)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 132))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 133))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 131)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 131)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 132))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 131))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 131))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 130)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 131))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 101) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD12_utf8_ubsan : segdef := (SEG 64%nat 103%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 65535;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 65535;
   KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 103%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 104);
   (EVar 105);
   (EVar 103);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 115)]
  [] 116%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 103%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 104);
   (EVar 105);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 103));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 115)]
  [KRange (EVar 103) 1 65535;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 103)) 0 65535;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 103))) 1 281474976710656;
   KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 116%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true)
 (EVar 103) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 104);
   (EVar 105);
   (EVar 103);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (EVar 109);
   (EVar 110);
   (EVar 111);
   (EVar 112);
   (EVar 113);
   (EVar 114);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 115)]
  [KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 116%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}; {| am_base := EVar 86; am_len := EVar 87; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96); (EVar 97, EVar 98); (EVar 99, EVar 100); (EVar 101, EVar 102)] [] 4398046511104 (EVar 88) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 103) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 116)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 117)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 118))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 119))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 117)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 117)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 118))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 117))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 117))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 116)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 117))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 124)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 125))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 126))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 127)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 116)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 117))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 118))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 119))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 128)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 129))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 130))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 131)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 120)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 121))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 122))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 123))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 132)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 133)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 134))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 135))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 133)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 133)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 134))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 133))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 133))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 132)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 133))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 103) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD13_utf8_ubsan : segdef := (SEG 64%nat 97%nat
  (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 67);
   (EVar 68);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 69);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 78)]
  [KRange (EVar 64) 1 65535;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 64)) 0 65535;
   KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 97%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 87, EVar 88); (EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96)] [] 4398046511104 (EVar 86) (FdStd) true)
  (* [comment removed for export] *) []
  (* [comment removed for export] *) [(ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 98);
   (EVar 99);
   (EVar 97);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 100);
   (EVar 101);
   (EVar 102);
   (EVar 103);
   (EVar 104);
   (EVar 105);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 109)]
  [] 110%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 87, EVar 88); (EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96)] [] 4398046511104 (EVar 86) (FdStd) true)]
  (* [comment removed for export] *) (SHole 0)
  (* [comment removed for export] *) ((PWhile 97%nat
 (* [comment removed for export] *) (ACS (mk_ss 258472 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 98);
   (EVar 99);
   (mkAlu Instr.ALU_SUB (EVar 65) (EVar 97));
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 100);
   (EVar 101);
   (EVar 102);
   (EVar 103);
   (EVar 104);
   (EVar 105);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 109)]
  [KRange (EVar 97) 1 65535;
   KRange (mkAlu Instr.ALU_SUB (EVar 65) (EVar 97)) 0 65535;
   KRange (mkAlu Instr.ALU_ADD (EVar 66) (mkAlu Instr.ALU_SUB (EVar 65) (EVar 97))) 1 281474976710656;
   KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 110%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 87, EVar 88); (EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96)] [] 4398046511104 (EVar 86) (FdStd) true)
 (EVar 97) (SHole 0)
 [((* [comment removed for export] *) (ACS (mk_ss 258976 [(ELit 0);
   (ELit 245040);
   (EVar 79);
   (ELit 67584);
   (ELit 973432);
   (ELit 27);
   (ELit 7);
   (ELit 240);
   (EVar 98);
   (EVar 99);
   (EVar 97);
   (EVar 66);
   (EVar 65);
   (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 66)) (ELit (-1)));
   (ELit 192);
   (ELit 18446744073709551551);
   (ELit 224);
   (ELit 128);
   (EVar 100);
   (EVar 101);
   (EVar 102);
   (EVar 103);
   (EVar 104);
   (EVar 105);
   (EVar 106);
   (EVar 107);
   (EVar 108);
   (ELit 0);
   (ELit 18446744073708437504);
   (ELit 18446744073708503040);
   (ELit 18446744073709551608);
   (EVar 109)]
  [KRange (EVar 65) 1 65535;
   KUnk {| a_base := EVar 66; a_off := 0 |} (EVar 65);
   KRange (EVar 66) 4096 140737488355328;
   KImg 65536 868352] 110%nat)
  [{| am_base := EVar 80; am_len := EVar 81; am_kind := KRW |}; {| am_base := EVar 82; am_len := EVar 83; am_kind := KRW |}; {| am_base := EVar 84; am_len := EVar 85; am_kind := KRW |}] 1099511627776 0 1099511627776 [(EVar 87, EVar 88); (EVar 89, EVar 90); (EVar 91, EVar 92); (EVar 93, EVar 94); (EVar 95, EVar 96)] [] 4398046511104 (EVar 86) (FdStd) true),
   (PBreak 0 []))]
 (* [comment removed for export] *) ((PRun [258472; 258976; 259028] (PCase2 (EVar 97) 15
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 110)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 111)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 112))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 113))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 111)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 4
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 111)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 112))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 111))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 111))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 3
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 1
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 110)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 111))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 2
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 118)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 119))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 120))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 121)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 110)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 111))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 112))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 113))))))) (EMd Instr.M_MUL (ELit 4294967296) (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 122)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 123))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 124))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 125)))))) (EAlu Instr.ALU_ADD (EExt false 0 1 (EVar 114)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 256) (EExt false 0 1 (EVar 115))) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 65536) (EExt false 0 1 (EVar 116))) (EMd Instr.M_MUL (ELit 16777216) (EExt false 0 1 (EVar 117))))))))) (ELit 9259542123273814144)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 126)) (ELit 0)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 224)) (ELit 192)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 240)) (ELit 224)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 248)) (ELit 240)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 127)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 128))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 129))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 2305843009213693952) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 43)) (EMd Instr.M_MUL (ELit 4096) (EAlu Instr.ALU_AND (EExt false 0 1 (EVar 127)) (ELit 48)))) (ELit (-1114112))) (ELit 18446744073708503040)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EMd Instr.M_MUL (ELit 64) (EAlu Instr.ALU_SRL (EExt false 0 1 (EVar 127)) (ELit 6))) (ELit 128)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 128))) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 127))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 288230376151711744) (EExt false 0 1 (EVar 127))) (ELit 52)) (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 48))) (ELit 11)) (ELit 27)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 1152921504606846976) (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 255))) (ELit 48)) (ELit 13)) (ELit 7)) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PNextW []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 126)) (ELit 30)) (ELit 0)) (ELit 1)) 0
 (PRun [258472; 258976; 259028] (PCase2 (EAlu Instr.ALU_SLT (ELit 18446744073709551551) (EExt true 0 1 (EVar 127))) 0
 (PRun [258472; 258976; 259028] (PNextW []))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))
 (PRun [258472; 258976; 259028] (PBreak 0 []))))))))
 (PRun [258472; 258976; 259028] (PCase2 (EVar 97) 16
 (PRun [258472; 258976; 259028] (PBreak 0 []))
 (PRun [258472; 258976; 259028] (PNextW [])))))))))))
  3000%nat 400000%nat).

(* [comment removed for export] *)
Definition SD32_utf8_ubsan : segdef := SegPrint_utf8_ubsan_p2.SD_print.

(* [comment removed for export] *)
Definition SD33_utf8_ubsan : segdef := SegPrint_utf8_ubsan_p3.SD_print.

(* [comment removed for export] *)
Definition SD34_utf8_ubsan : segdef := SegPrint_utf8_ubsan_p4.SD_print.

Definition SG_utf8_ubsan (sid : nat) : option segdef :=
  match sid with | 1%nat => Some SD1_utf8_ubsan | 2%nat => Some SD2_utf8_ubsan | 3%nat => Some SD3_utf8_ubsan | 4%nat => Some SD4_utf8_ubsan | 5%nat => Some SD5_utf8_ubsan | 6%nat => Some SD6_utf8_ubsan | 7%nat => Some SD7_utf8_ubsan | 8%nat => Some SD8_utf8_ubsan | 9%nat => Some SD9_utf8_ubsan | 10%nat => Some SD10_utf8_ubsan | 11%nat => Some SD11_utf8_ubsan | 12%nat => Some SD12_utf8_ubsan | 13%nat => Some SD13_utf8_ubsan | 32%nat => Some SD32_utf8_ubsan | 33%nat => Some SD33_utf8_ubsan | 34%nat => Some SD34_utf8_ubsan | _ => None end.

Lemma seg1_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 1%nat SD1_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg2_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 2%nat SD2_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg3_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 3%nat SD3_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg4_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 4%nat SD4_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg5_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 5%nat SD5_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg6_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 6%nat SD6_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg7_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 7%nat SD7_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg8_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 8%nat SD8_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg9_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 9%nat SD9_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg10_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 10%nat SD10_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg11_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 11%nat SD11_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg12_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 12%nat SD12_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg13_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 13%nat SD13_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg32_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 32%nat SD32_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg33_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 33%nat SD33_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma seg34_ok_utf8_ubsan : seg_ok SEGS_utf8_ubsan ITm_utf8_ubsan AT_utf8_ubsan NX0 LIMIT_utf8_ubsan (XNp IP_utf8_ubsan ITm_utf8_ubsan T0) (XEp IP_utf8_ubsan) (XBp IP_utf8_ubsan T0) KCm (XPm SG_utf8_ubsan) 34%nat SD34_utf8_ubsan = true.
Proof. cert_vm true. Qed.

Lemma SG_ok_utf8_ubsan : segs_ok IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan.
Proof.
  intros sid SD H.
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [injection H as <-; exact seg1_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg2_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg3_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg4_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg5_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg6_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg7_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg8_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg9_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg10_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg11_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg12_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg13_ok_utf8_ubsan |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [discriminate H |].
  destruct sid as [|sid]; [injection H as <-; exact seg32_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg33_ok_utf8_ubsan |].
  destruct sid as [|sid]; [injection H as <-; exact seg34_ok_utf8_ubsan |].
  discriminate H.
Qed.
