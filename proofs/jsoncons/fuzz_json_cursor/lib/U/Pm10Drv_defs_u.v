(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10MainEntry_u Pm10LibStdioCall_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import DrvKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Section FPX_1. Context {fx : PropExec.FPState}.

Definition STOPS : list Z :=
  [0xb7894; 0xb7e14; 0xb8388; 0xb7798; 0xa7160; 0xac404; 0xa9144; 0xa9004; 0x396ec; 0x396a4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xc4000) 0x34000;
   KImg 0x10000 0xc4d70;
   KImg 0xc4d71 0xc4db9; KImg 0xd4db9 0xd6730; KImg 0xf6808 0xf6828;
   KWord (SA (ELit 0) 0xd6738) 8 (ELit 0xd6738);
   KWord (SA (ELit 0) 0xd6758) 4 (EVar 5);
   KImg 0xd6764 0xd67b0; KImg 0xd67b8 0xd67d0; KWord (SA (ELit 0) 0xd67d0) 8 (ELit 0xf6ac8); KImg 0xd67d8 0xd67f0;
   KBlob (SA (ELit 0) 0xd67f0) (ELit 8) 2;
   KImg 0xd6800 0xd6810; KImg 0xd6818 0xf6808; KImg 0xf6840 0xf6a70;
   KBlob (SA (ELit 0) 0xf6a70) (ELit 8) 2;
   KImg 0xf6a78 0xf6a80;
   KImg 0xf6a91 0xf6a98; KWord (SA (ELit 0) 0xf6a98) 8 (EVar 3);
   KImg 0xf6aa0 0xf6aa8; KImg 0xf6ab8 0xf6ac0; KWord (SA (ELit 0) 0xf6ac0) 8 (ELit 4096);
   KImg 0xf6ac8 0xf6af8; KBlob (SA (ELit 0) 0xf6af8) (ELit 8) 3; KImg 0xf6b00 0xf6c08  ; KImg 0xf6fb0 0xf8000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vmc_refl. Qed.

Definition ssA0 : sym_state := SS 0x3924c sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xb8840 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xd675c); (0xd6760, 0xf6c08); (0xf6fb0, 0xf8000)]%Z.

Definition IMG_RW : list (Z * Z) := [(0xbd000, 0xc4000); (0xc4000, 0xf8000)]%Z.

Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.

Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.

Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xe8000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xb883c%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0xa9144%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
