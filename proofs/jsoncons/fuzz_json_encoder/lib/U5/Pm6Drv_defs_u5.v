(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6MainEntry_u5 Pm6LibStdioCall_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import DrvKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS : list Z :=
  [0xbe048; 0xbe5c8; 0xbeb3c; 0xbdf4c; 0xad914; 0xb2bb8; 0xaf8f8; 0xaf7b8; 0x3a610; 0x3a5c8]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xcb000) 0x33000;
   KImg 0x10000 0xcb538;
   KImg 0xcb541 0xcb589; KImg 0xdb589 0xdcf40; KImg 0xfd018 0xfd038;
   KWord (SA (ELit 0) 0xdcf48) 8 (ELit 0xdcf48);
   KWord (SA (ELit 0) 0xdcf68) 4 (EVar 5);
   KImg 0xdcf74 0xdcfc0; KImg 0xdcfc8 0xdcfe0; KWord (SA (ELit 0) 0xdcfe0) 8 (ELit 0xfd2d8); KImg 0xdcfe8 0xdd000;
   KBlob (SA (ELit 0) 0xdd000) (ELit 8) 2;
   KImg 0xdd010 0xdd020; KImg 0xdd028 0xfd018; KImg 0xfd050 0xfd280;
   KBlob (SA (ELit 0) 0xfd280) (ELit 8) 2;
   KImg 0xfd288 0xfd290;
   KImg 0xfd2a1 0xfd2a8; KWord (SA (ELit 0) 0xfd2a8) 8 (EVar 3);
   KImg 0xfd2b0 0xfd2b8; KImg 0xfd2c8 0xfd2d0; KWord (SA (ELit 0) 0xfd2d0) 8 (ELit 4096);
   KImg 0xfd2d8 0xfd308; KBlob (SA (ELit 0) 0xfd308) (ELit 8) 3; KImg 0xfd310 0xfd418 (* [comment removed for export] *); KImg 0xfd7c0 0xfe000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x3a170 sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xbeff4 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xdcf6c); (0xdcf70, 0xfd418); (0xfd7c0, 0xfe000)]%Z.
(* [comment removed for export] *)
Definition IMG_RW : list (Z * Z) := [(0xc4000, 0xcb000); (0xcb000, 0xfe000)]%Z.
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
   KDisj (SA (ELit 0) 0x10000) 0xee000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

(* [comment removed for export] *)
Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xbeff0%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0xaf8f8%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
