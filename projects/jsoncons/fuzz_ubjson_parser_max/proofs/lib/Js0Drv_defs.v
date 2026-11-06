(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Js0MainEntry Js0LibStdioCall DrvKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Drv_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Drv_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0MainEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."], [["1O"; "1bool"; "1fst"; "1list"; "1nil"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "3nth"; "4Z"; "5ALU_ADD"; "6ksubl_b"; "7MSO"]; ["7kn_d0"; "7rA"; "7rB"; "7srB"; "8kn_main"; "9EAlu"; "9ELit"; "9EVar"; "9expr"; "9s_log"; "9s_pc"; "9scripts"; "9sentry"; "9sidecond"; "9sym_state"]]).
Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS : list Z :=
[0xa9160; 0xa96e0; 0xa9c54; 0xa9064; 0x98ad0; 0x9dc38; 0x9aab4; 0x9a974; 0x3404c; 0x34004]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition kn_image_d : list kentry :=
[KWr (SA (ELit 0) 0xb5000) 0x34000;
KImg 0x10000 0xb61e0;
KImg 0xb61e1 0xb6229; KImg 0xc6229 0xc7b90; KImg 0xe7c68 0xe7c88;
KWord (SA (ELit 0) 0xc7b98) 8 (ELit 0xc7b98);
KWord (SA (ELit 0) 0xc7bb8) 4 (EVar 5);
KImg 0xc7bc4 0xc7c10; KImg 0xc7c18 0xc7c30; KWord (SA (ELit 0) 0xc7c30) 8 (ELit 0xe7f28); KImg 0xc7c38 0xc7c50;
KBlob (SA (ELit 0) 0xc7c50) (ELit 8) 2;
KImg 0xc7c60 0xc7c70; KImg 0xc7c78 0xe7c68; KImg 0xe7ca0 0xe7ca8; KImg 0xe7ca8 0xe7ec8; KImg 0xe7ec8 0xe7ed0;
KBlob (SA (ELit 0) 0xe7ed0) (ELit 8) 2;
KImg 0xe7ed8 0xe7ee0;
KImg 0xe7ef1 0xe7ef8; KWord (SA (ELit 0) 0xe7ef8) 8 (EVar 3);
KImg 0xe7f00 0xe7f08; KImg 0xe7f18 0xe7f20; KWord (SA (ELit 0) 0xe7f20) 8 (ELit 4096);
KImg 0xe7f28 0xe7f58; KBlob (SA (ELit 0) 0xe7f58) (ELit 8) 3; KImg 0xe7f60 0xe8068; KImg 0xe8410 0xe9000;
KRange (EVar 5) 1 4194303;
KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.
Lemma kn_d0_sub : ltac2:(TCodec.tc2 tcn__Js0Drv_defs "8':'1&>&D&@%3221(8%73621").
Proof. vm_compute. reflexivity. Qed.
Definition ssA0 : sym_state := SS 0x33bac sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xaa10c srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xc7bbc); (0xc7bc0, 0xe8068); (0xe8410, 0xe9000)]%Z.
Definition IMG_RW : list (Z * Z) := [(0xaf000, 0xb5000); (0xb5000, 0xe9000)]%Z.
Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.
Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.
Definition kn_blk (v : nat) (n : Z) : list kentry :=
[KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
KDisj (SA (ELit 0) 0x10000) 0xd9000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.
Lemma drv_itinerary_ok : ltac2:(TCodec.tc2 tcn__Js0Drv_defs "RG'9':'6'<'3'M%211%5241(5&J&2'N%:216'K&A%53321%635:1%811&7%138=4%<4A>31+eXX8(4%11B%@4EB31%H3B51'L%G11%J2E1&B%D3BA1%E3DI1%G11%?3FK3%J4OL21&I%115%M4N:31+cZeD%O4Q4Q11@%B1>%Q14Q2>21%Q93>51'H%Q:211%Q;212%Q<213%Q=214&;u:&C(Fz%211%64;541uE%84=163%QA4>>31uD%;4@196%QD4@A31uB%>4C1<9%QG4BD31u2%A4F1?<%QJ4DG31+RPP0%A11%QM4JJ11+3%D11%R04LM31(G%11:%R34NQ031(E(=(0%611&?%N11%63531%R;4Q5Q881%RC3Q5B1%RE2Q;1%RF2QM1").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
