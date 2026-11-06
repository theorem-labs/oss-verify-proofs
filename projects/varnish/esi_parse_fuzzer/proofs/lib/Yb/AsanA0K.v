(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe Asanz3l AsanPlan Starob1 Star2r0 Asanii6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyclu.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyclu.Boot34w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Boots35.   (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A0K_L : list kentry :=
  [ (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 228)));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 8) 8%nat (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 356))));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 16) 8%nat (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 356))) (ELit (-8388608))));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 24) 8%nat (ELit 0));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 32) 8%nat (ELit 0));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 40) 1%nat (ELit 0));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 48) 8%nat (ELit 6195984));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 56) 8%nat (ELit 6196204));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 64) 8%nat (ELit 6194144));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 72) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 405)));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 3168) 1%nat (ELit 0));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 80) (ELit 3088));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 3169) (ELit 927));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) 8%nat (ELit 690856));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 8) 4%nat (ELit 0));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 152) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 227)));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 160) (ELit 65376));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 24));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 24) 8%nat (ELit 6194136));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 32) 8%nat (ELit 0));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 40) (ELit 4056));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 88));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 88) 8%nat (ELit 20));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 96) (ELit 11571104));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 405)) 2147450880) (ELit 1446400));
    (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 405)) 2147450880) (ELit 1446400));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 16));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 24) 4%nat (ELit 0));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 28) 4%nat (ELit 1));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 32) (ELit 1048544));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 480)) 2147450880) (ELit 131072));
    (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 480)) 2147450880) (ELit 131072));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 481)) 2147450880) (ELit 1048576));
    (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 481)) 2147450880) (ELit 1048576));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 4211)) 2147450880) (ELit 512));
    (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 4211)) 2147450880) (ELit 512));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 498)) 2147450880) (ELit 512));
    (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 498)) 2147450880) (ELit 512));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360));
    (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360));
    (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536));
    (KWr (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) 137439019008) (ELit 4096));
    (KZero (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) 137439019008) (ELit 4096));
    (KWr (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (-8388608)) (ELit 8388608));
    (KWr (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10))) 2146402304) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992)));
    (KZero (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10))) 2146402304) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992)));
    (KWr (SA (ELit 0) 2147459072) (ELit 783360));
    (KWord (SA (ELit 0) 6194136) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 405)));
    (KWord (SA (ELit 0) 6194144) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 322)));
    (KWord (SA (ELit 0) 6330240) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 228)));
    (KWord (SA (ELit 0) 728408) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 208)));
    (KWord (SA (ELit 0) 728440) 8%nat (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 65536)));
    (KWord (SA (ELit 0) 728456) 8%nat (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 137439019008)));
    (KWord (SA (ELit 0) 728480) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 226)));
    (KWord (SA (ELit 0) 728488) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 226)));
    (KWord (SA (ELit 0) 5862056) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 480)));
    (KWord (SA (ELit 0) 1602200) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 481)));
    (KRange (EVar 0) 4294901760 4294967295);
    (KRange (EVar 6) 0 2047);
    (KRange (EVar 1) 1 1024);
    (KRange (EVar 2) 0 256);
    (KRange (EVar 3) 0 131071);
    (KRange (EVar 4) 0 280000);
    (KRange (EVar 7) 0 131071);
    (KRange (EVar 10) 0 7);
    (KRange (EVar 78) 1546 34359736304);
    (KRange (EVar 207) 1546 34359735410);
    (KRange (EVar 208) 4295491576 34326181871);
    (KRange (EVar 209) 0 15);
    (KRange (EVar 226) 1546 34359734272);
    (KRange (EVar 227) 1 34359736319);
    (KRange (EVar 228) 1546 34359736304);
    (KRange (EVar 257) 1 34359736319);
    (KRange (EVar 322) 1 34359736319);
    (KRange (EVar 323) 1 34359736319);
    (KRange (EVar 356) 0 8);
    (KRange (EVar 405) 1546 34359733495);
    (KRange (EVar 422) 1 34359736319);
    (KRange (EVar 423) 1 34359736319);
    (KRange (EVar 480) 1546 34359736064);
    (KRange (EVar 481) 1546 34359734272);
    (KRange (EVar 498) 1 34359736319);
    (KRange (EVar 4211) 1 34359736319);
    (KRange (EVar 5) 1546 525834);
    (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 209)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (ELit 65535))) 0 0);
    (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) 140735340871680 140737488355136);
    (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10))) 140735340871680 140737488351232);
    (KImg 5862064 6125440);
    (KImg 746940 1275400);
    (KImg 1339007 1339104);
    (KImg 728512 729088);
    (KImg 729290 732024);
    (KImg 729290 732024);
    (KImg 1275426 1330768);
    (KImg 1339007 1339104);
    (KImg 1275426 1330768);
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 323)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 323)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 323)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360));
    (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536));
    (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536));
    (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 8) 8%nat (ELit 280096));
    (KImg 1602216 2480068);
    (KImg 2480072 5392900);
    (KImg 5392904 5862040) ].
Definition A0K_T : ptree kentry := Eval vm_compute in BFXT.pt_of_list A0K_L xH PTLeaf.
Definition a0k (cs : acs) : Prop := BFXT.pt_all (khas cs) A0K_T = true.
Lemma k_thr_0 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 228))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) xH A0K_T _ H eq_refl). Qed.
Lemma k_thr_8 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 8) 8%nat (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 356)))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO xH) A0K_T _ H eq_refl). Qed.
Lemma k_thr_16 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 16) 8%nat (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 356))) (ELit (-8388608)))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI xH) A0K_T _ H eq_refl). Qed.
Lemma k_thr_24 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 24) 8%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO xH)) A0K_T _ H eq_refl). Qed.
Lemma k_thr_32 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 32) 8%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO xH)) A0K_T _ H eq_refl). Qed.
Lemma k_thr_40 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 40) 1%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI xH)) A0K_T _ H eq_refl). Qed.
Lemma k_thr_48 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 48) 8%nat (ELit 6195984)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI xH)) A0K_T _ H eq_refl). Qed.
Lemma k_thr_56 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 56) 8%nat (ELit 6196204)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO xH))) A0K_T _ H eq_refl). Qed.
Lemma k_thr_64 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 64) 8%nat (ELit 6194144)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO xH))) A0K_T _ H eq_refl). Qed.
Lemma k_thr_72 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 72) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 405))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO xH))) A0K_T _ H eq_refl). Qed.
Lemma k_thr_3168 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 3168) 1%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO xH))) A0K_T _ H eq_refl). Qed.
Lemma k_thr_z80 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 80) (ELit 3088)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI xH))) A0K_T _ H eq_refl). Qed.
Lemma k_thr_z3169 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 3169) (ELit 927)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI xH))) A0K_T _ H eq_refl). Qed.
Lemma k_thr_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI xH))) A0K_T _ H eq_refl). Qed.
Lemma k_ctx_0 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) 8%nat (ELit 690856)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI xH))) A0K_T _ H eq_refl). Qed.
Lemma k_ctx_8 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 8) 4%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_ctx_152 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 152) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 227))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_ctx_z160 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 160) (ELit 65376)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_ctx_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_m11_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_dtls_z0 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 24)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_dtls_24 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 24) 8%nat (ELit 6194136)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_dtls_32 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 32) 8%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_dtls_z40 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 40) (ELit 4056)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_dtls_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_fs_z0 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 88)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_fs_88 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 88) 8%nat (ELit 20)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_fs_z96 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 96) (ELit 11571104)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_fs_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_fs_shwr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 405)) 2147450880) (ELit 1446400)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_fs_shz : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 405)) 2147450880) (ELit 1446400)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI xH)))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_z0 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 16)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_24 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 24) 4%nat (ELit 0)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_28 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 28) 4%nat (ELit 1)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_z32 : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 32) (ELit 1048544)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_shwr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 480)) 2147450880) (ELit 131072)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_nd_shz : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 480)) 2147450880) (ELit 131072)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_fr_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_fr_shwr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 481)) 2147450880) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_fr_shz : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 481)) 2147450880) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_gvec_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_gvec_shwr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 4211)) 2147450880) (ELit 512)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_gvec_shz : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 4211)) 2147450880) (ELit 512)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_dvec_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_dvec_shwr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 512) (EVar 498)) 2147450880) (ELit 512)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_dvec_shz : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar 498)) 2147450880) (ELit 512)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xO xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_itab_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_itab_z : forall cs : acs, a0k cs -> khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_m64k_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_ri_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) 137439019008) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_ri_z : forall cs : acs, a0k cs -> khas cs (KZero (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) 137439019008) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_stk_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (-8388608)) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_stksh_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10))) 2146402304) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_stksh_z : forall cs : acs, a0k cs -> khas cs (KZero (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10))) 2146402304) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_imgsh_wr : forall cs : acs, a0k cs -> khas cs (KWr (SA (ELit 0) 2147459072) (ELit 783360)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_tp_fs : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 6194136) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 405))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_tp_dtls : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 6194144) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 322))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_tsd_ctx : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 6330240) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 228))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_inst_b6 : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 728408) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 208))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_inst_sb : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 728440) 8%nat (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 65536))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_inst_ri : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 728456) 8%nat (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 137439019008))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_inst_pa1 : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 728480) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 226))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xI xH))))) A0K_T _ H eq_refl). Qed.
Lemma k_inst_pa2 : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 728488) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 226))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_map1_0 : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 5862056) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 480))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_ss_blk0 : forall cs : acs, a0k cs -> khas cs (KWord (SA (ELit 0) 1602200) 8%nat (EMd Instr.M_MUL (ELit 4096) (EVar 481))) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_0 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 0) 4294901760 4294967295) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_6 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 6) 0 2047) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_1 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 1) 1 1024) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_2 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 2) 0 256) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_3 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 3) 0 131071) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_4 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 4) 0 280000) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_7 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 7) 0 131071) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_10 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 10) 0 7) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_78 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 78) 1546 34359736304) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_207 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 207) 1546 34359735410) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_208 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 208) 4295491576 34326181871) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_209 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 209) 0 15) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_226 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 226) 1546 34359734272) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xO (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_227 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 227) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_228 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 228) 1546 34359736304) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_257 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 257) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_322 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 322) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_323 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 323) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_356 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 356) 0 8) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_405 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 405) 1546 34359733495) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_422 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 422) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_423 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 423) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_480 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 480) 1546 34359736064) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_481 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 481) 1546 34359734272) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_498 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 498) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_4211 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 4211) 1 34359736319) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_5 : forall cs : acs, a0k cs -> khas cs (KRange (EVar 5) 1546 525834) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_v209rel : forall cs : acs, a0k cs -> khas cs (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 209)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (ELit 65535))) 0 0) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_sp0 : forall cs : acs, a0k cs -> khas cs (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) 140735340871680 140737488355136) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xI (xO xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_rng_pgsp0 : forall cs : acs, a0k cs -> khas cs (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10))) 140735340871680 140737488351232) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_map1 : forall cs : acs, a0k cs -> khas cs (KImg 5862064 6125440) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_ia : forall cs : acs, a0k cs -> khas cs (KImg 746940 1275400) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_hooks : forall cs : acs, a0k cs -> khas cs (KImg 1339007 1339104) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_inst112 : forall cs : acs, a0k cs -> khas cs (KImg 728512 729088) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_inst888 : forall cs : acs, a0k cs -> khas cs (KImg 729290 732024) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_inst984 : forall cs : acs, a0k cs -> khas cs (KImg 729290 732024) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_rss : forall cs : acs, a0k cs -> khas cs (KImg 1275426 1330768) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_dying : forall cs : acs, a0k cs -> khas cs (KImg 1339007 1339104) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_img_ia1 : forall cs : acs, a0k cs -> khas cs (KImg 1275426 1330768) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_498_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_481_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_480_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_405_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_322_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_257_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xO (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_4211 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_481_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_480_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_405_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_322_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_257_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xI (xI xH)))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_498 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_480_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_405_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_322_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_257_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_481 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_405_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_322_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_257_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xO (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_480 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_322_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_257_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_405 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_257_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xI (xO (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_322 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_228_257 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_257 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_257 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_257 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_257 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_257 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_227_228 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_228 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_228 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_228 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_228 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_226_227 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_227 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xO (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_227 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_227 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_226 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_226 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_226 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_207_208 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_208 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_78_207 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_323 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 323)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_422p : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_disj_208_423 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_0 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_1 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_2 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_3 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_4 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xI (xI (xO xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_5 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_6 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_7 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_8 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_9 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_10 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_11 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_12 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_13 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_14 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 323)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_15 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 323)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_16 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_17 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_18 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_19 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_20 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xI (xO (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_21 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_22 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_23 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_24 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_25 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_26 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_27 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_28 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xI (xO (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_29 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xO (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_30 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xO (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma k_band_31 : forall cs : acs, a0k cs -> khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 268435456) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xO (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma kd_key0 : forall cs : acs, a0k cs -> khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 8) 8%nat (ELit 280096)) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xI (xO (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma kd_img_lo : forall cs : acs, a0k cs -> khas cs (KImg 1602216 2480068) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xO (xI (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma kd_img_md : forall cs : acs, a0k cs -> khas cs (KImg 2480072 5392900) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xI (xO (xI (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.
Lemma kd_img_hi : forall cs : acs, a0k cs -> khas cs (KImg 5392904 5862040) = true.
Proof. intros cs H. exact (BFXT.pt_all_get kentry (khas cs) (xO (xI (xI (xI (xI (xO (xI xH))))))) A0K_T _ H eq_refl). Qed.

(* [comment removed for export] *)
Definition A0_DISJ : list kentry :=
  [ (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 4211)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 498)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 0) (ELit 1048576));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 405)) 0) (ELit 11571200));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 322)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 257)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 228)) 0) (ELit 65536));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 227)) 0) (ELit 4096));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 226)) 0) (ELit 8388608));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 208)) 0) (ELit 137439023104));
    (KDisj (SA (EMd Instr.M_MUL (ELit 4096) (EVar 78)) 0) (ELit 65536) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 207)) 0) (ELit 3727360)) ].

(* [comment removed for export] *)
Record a0kd1 (cs : acs) : Prop := A0KD1 {
  a0kd1_kd_hash : khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 16) 8%nat (ELit 5699640298485724635)) = true;
  a0kd1_kd_len : khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) 8%nat (ELit 2)) = true;
  a0kd1_kd_key1 : khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 16) 8%nat (ELit 285040)) = true;
  a0kd1_kd_frz : khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 24) (ELit 8388584)) = true;
  a0kd1_kd_total : khas cs (KWord (SA (ELit 0) 1602184) 8%nat (ELit 3)) = true;
  a0kd1_kd_stored : khas cs (KWord (SA (ELit 0) 1602208) 4%nat (ELit 3)) = true;
  a0kd1_kd_tab : khas cs (KWord (SA (ELit 0) 5392900) 4%nat (ELit 1)) = true;
  a0kd1_kd_tabo : khas cs (KWord (SA (ELit 0) 2480068) 4%nat (ELit 0)) = true
}.

Record a0kd2 (cs : acs) : Prop := A0KD2 {
  a0kd2_kd_hash : khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 480)) 16) 8%nat (ELit 15557900658911942987)) = true;
  a0kd2_kd_len : khas cs (KWord (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 0) 8%nat (ELit 1)) = true;
  a0kd2_kd_frz : khas cs (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 481)) 16) (ELit 8388592)) = true;
  a0kd2_kd_total : khas cs (KWord (SA (ELit 0) 1602184) 8%nat (ELit 2)) = true;
  a0kd2_kd_stored : khas cs (KWord (SA (ELit 0) 1602208) 4%nat (ELit 2)) = true;
  a0kd2_kd_tab : khas cs (KWord (SA (ELit 0) 2480068) 4%nat (ELit 1)) = true;
  a0kd2_kd_tabo : khas cs (KWord (SA (ELit 0) 5392900) 4%nat (ELit 0)) = true
}.

Definition A0_MAPS : list amap := [{| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 4211); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 498); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 481); am_len := ELit 8388608; am_kind := KRWLAZY |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 480); am_len := ELit 1048576; am_kind := KRW |}; {| am_base := ELit 0; am_len := ELit 8192; am_kind := KFOG |}; {| am_base := ELit 0; am_len := ELit 8192; am_kind := KFOG |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 405); am_len := ELit 11571200; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 322); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 257); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 228); am_len := ELit 65536; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 226); am_len := ELit 8388608; am_kind := KNONELAZY |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 208); am_len := ELit 137439023104; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 207); am_len := ELit 3727360; am_kind := KRW |}; {| am_base := EMd Instr.M_MUL (ELit 4096) (EVar 78); am_len := ELit 65536; am_kind := KRW |}; {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |}; {| am_base := ELit 2415882240; am_len := ELit 2199023255552; am_kind := KNONELAZY |}; {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |}].

Definition A0_VIS : list (expr * expr) := [(EMd Instr.M_MUL (ELit 4096) (EVar 4211), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 498), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 481), ELit 8388608); (EMd Instr.M_MUL (ELit 4096) (EVar 480), ELit 1048576); (EMd Instr.M_MUL (ELit 4096) (EVar 405), ELit 11571200); (EMd Instr.M_MUL (ELit 4096) (EVar 322), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 257), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 228), ELit 65536); (EMd Instr.M_MUL (ELit 4096) (EVar 227), ELit 4096); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 137439019008), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 207), ELit 3727360); (EMd Instr.M_MUL (ELit 4096) (EVar 78), ELit 65536); (ELit 65536, ELit 6266880); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10))) (ELit (-8388608)), EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-32768)) (EVar 0)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 10))) (ELit 140737496743936))].

Definition A0_GHOST_A : list (expr * expr) := [(EMd Instr.M_MUL (ELit 4096) (EVar 323), ELit 4096); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 423), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 5), ELit 8192); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 423), ELit 4096)].

Definition A0_GHOST_B : list (expr * expr) := [(EMd Instr.M_MUL (ELit 4096) (EVar 323), ELit 4096); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 423), ELit 4096); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 422)) (ELit 4096), ELit 4096); (EMd Instr.M_MUL (ELit 4096) (EVar 423), ELit 4096)].

Record a0s (cs : acs) (gh : list (expr * expr)) : Prop := A0S { s_maps : a_maps cs = A0_MAPS; s_vis : a_vis cs = A0_VIS; s_ghost : a_ghost cs = gh; s_eager : Z.leb (a_eager cs) (2^30) = true; s_abytes : Z.leb (a_abytes cs) (2^34) = true }.
Lemma a0s_1 : a0s HS_asan2_1 A0_GHOST_A. Proof. constructor; reflexivity. Qed.
Lemma a0s_2 : a0s HS_asan2_2 A0_GHOST_A. Proof. constructor; reflexivity. Qed.
Lemma a0s_3 : a0s HS_asan2b_1 A0_GHOST_B. Proof. constructor; reflexivity. Qed.
Lemma a0s_4 : a0s HS_asan2b_2 A0_GHOST_B. Proof. constructor; reflexivity. Qed.
(* [comment removed for export] *)
Lemma pt_all_ext_a0k : forall (A : Type) (f g : A -> bool) (t : ptree A), (forall a, f a = g a) -> BFXT.pt_all f t = BFXT.pt_all g t.
Proof.
  intros A f g t H. induction t as [|l IHl o r IHr]; [reflexivity|]. cbn [BFXT.pt_all]. rewrite IHl, IHr.
  destruct o as [a|]; cbn [BFXT.oall]; [rewrite (H a)|]; reflexivity.
Qed.
Lemma a0k_fast : forall cs : acs, BFXT.pt_all (Boots35.BFXE.mem' (Boots35.BFXE.build (kn cs))) A0K_T = true -> a0k cs.
Proof.
  intros cs H. unfold a0k. rewrite <- H. apply pt_all_ext_a0k. intros K. unfold khas. symmetry. apply Boots35.BFXE.mem'_eq.
Qed.
Lemma a0k_1 : a0k HS_asan2_1. Proof. apply a0k_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma a0k_2 : a0k HS_asan2_2. Proof. apply a0k_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma a0k_3 : a0k HS_asan2b_1. Proof. apply a0k_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma a0k_4 : a0k HS_asan2b_2. Proof. apply a0k_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma a0kd_1 : a0kd1 HS_asan2_1. Proof. constructor; vm_compute; reflexivity. Qed.
Lemma a0kd_2 : a0kd2 HS_asan2_2. Proof. constructor; vm_compute; reflexivity. Qed.
Lemma a0kd_3 : a0kd1 HS_asan2b_1. Proof. constructor; vm_compute; reflexivity. Qed.
Lemma a0kd_4 : a0kd2 HS_asan2b_2. Proof. constructor; vm_compute; reflexivity. Qed.
Lemma a0_disj_1 : forallb (khas HS_asan2_1) A0_DISJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma a0_disj_2 : forallb (khas HS_asan2_2) A0_DISJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma a0_disj_3 : forallb (khas HS_asan2b_1) A0_DISJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma a0_disj_4 : forallb (khas HS_asan2b_2) A0_DISJ = true. Proof. vm_compute. reflexivity. Qed.
