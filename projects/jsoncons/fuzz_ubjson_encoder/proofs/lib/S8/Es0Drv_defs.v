(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Es0MainEntry Es0LibStdioCall DrvKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

Definition STOPS : list Z :=
  [0xac48c; 0xaca0c; 0xacf80; 0xac390; 0x9bdf8; 0xa0ffc; 0x9dddc; 0x9dc9c; 0x349e4; 0x3499c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xb9000) 0x33000;
   KImg 0x10000 0xb95c0;
   KImg 0xb95c1 0xb9609; KImg 0xc9609 0xcaf70; KImg 0xeb048 0xeb068;
   KWord (SA (ELit 0) 0xcaf78) 8 (ELit 0xcaf78);
   KWord (SA (ELit 0) 0xcaf98) 4 (EVar 5);
   KImg 0xcafa4 0xcaff0; KImg 0xcaff8 0xcb010; KWord (SA (ELit 0) 0xcb010) 8 (ELit 0xeb308); KImg 0xcb018 0xcb030;
   KBlob (SA (ELit 0) 0xcb030) (ELit 8) 2;
   KImg 0xcb040 0xcb050; KImg 0xcb058 0xcb0c8; KImg 0xeb080 0xeb2a8; KImg 0xeb2a8 0xeb2b0;
   KBlob (SA (ELit 0) 0xeb2b0) (ELit 8) 2;
   KImg 0xeb2b8 0xeb2c0;
   KImg 0xeb2d1 0xeb2d8; KWord (SA (ELit 0) 0xeb2d8) 8 (EVar 3);
   KImg 0xeb2e0 0xeb2e8; KImg 0xeb2f8 0xeb300; KWord (SA (ELit 0) 0xeb300) 8 (ELit 4096);
   KImg 0xeb308 0xeb338; KBlob (SA (ELit 0) 0xeb338) (ELit 8) 3; KImg 0xeb340 0xeb448; KImg 0xeb7f0 0xec000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof. vm_compute. reflexivity. Qed.

Definition ssA0 : sym_state := SS 0x34544 sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xad438 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xcaf9c); (0xcafa0, 0xeb448); (0xeb7f0, 0xec000)]%Z.

Definition IMG_RW : list (Z * Z) := [(0xb2000, 0xb9000); (0xb9000, 0xec000)]%Z.

Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.

Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.

Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xdc000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xad434%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0x9dddc%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
