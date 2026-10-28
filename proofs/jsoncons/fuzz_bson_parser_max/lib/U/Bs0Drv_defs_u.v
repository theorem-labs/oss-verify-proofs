(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0MainEntry_u Bs0LibStdioCall_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKit.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS : list Z :=
  [0xab480; 0xaba00; 0xabf74; 0xab384; 0x9adf0; 0x9ff58; 0x9cdd4; 0x9cc94; 0x3471c; 0x346d4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xb8000) 0x33000;
   KImg 0x10000 0xb8500;
   KImg 0xb8501 0xb8549; KImg 0xc8549 0xc9ef0; KImg 0xe9fc8 0xe9fe8;
   KWord (SA (ELit 0) 0xc9ef8) 8 (ELit 0xc9ef8);
   KWord (SA (ELit 0) 0xc9f18) 4 (EVar 5);
   KImg 0xc9f24 0xc9f70; KImg 0xc9f78 0xc9f90; KWord (SA (ELit 0) 0xc9f90) 8 (ELit 0xea288); KImg 0xc9f98 0xc9fb0;
   KBlob (SA (ELit 0) 0xc9fb0) (ELit 8) 2;
   KImg 0xc9fc0 0xc9fd0; KImg 0xc9fd8 0xe9fc8; KImg 0xea000 0xea008; KImg 0xea008 0xea228; KImg 0xea228 0xea230;
   KBlob (SA (ELit 0) 0xea230) (ELit 8) 2;
   KImg 0xea238 0xea240;
   KImg 0xea251 0xea258; KWord (SA (ELit 0) 0xea258) 8 (EVar 3);
   KImg 0xea260 0xea268; KImg 0xea278 0xea280; KWord (SA (ELit 0) 0xea280) 8 (ELit 4096);
   KImg 0xea288 0xea2b8; KBlob (SA (ELit 0) 0xea2b8) (ELit 8) 3; KImg 0xea2c0 0xea3c8; KImg 0xea770 0xeb000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x3427c sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xac42c srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xc9f1c); (0xc9f20, 0xea3c8); (0xea770, 0xeb000)]%Z.
(* [comment removed for export] *)
Definition IMG_RW : list (Z * Z) := [(0xb1000, 0xb8000); (0xb8000, 0xeb000)]%Z.
(* [comment removed for export] *)
Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.
(* [comment removed for export] *)
Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xdb000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

(* [comment removed for export] *)
Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xac428%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0x9cdd4%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
