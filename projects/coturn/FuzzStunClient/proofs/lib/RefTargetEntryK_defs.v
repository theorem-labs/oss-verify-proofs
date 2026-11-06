(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymPlan TargetKDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
Import ListNotations. Import SX2. Import SP.
Open Scope Z_scope.

Definition NX0k : N := 46%N.   (* [comment removed for export] *)
Definition sr_Tk (k : Z) : list expr :=
  [ELit 0;
   ELit 0x13b54;
   EAlu ALU_ADD (EVar 0) (ELit (-128));
   ELit 0x10800;
   ELit 0x367b0;
   EVar 17;
   EVar 18;
   EVar 19;
   EAlu ALU_ADD (EVar 1) (ELit (offk k + 2));
   EAlu ALU_ADD (EVar 1) (ELit (offk k));
   EAlu ALU_ADD (EVar 1) (ELit (offk k + 2));
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit (offk k + 6));
   EVar 4;
   EVar 26;
   EVar 27;
   EVar 28;
   EVar 29;
   EVar 5;
   EAlu ALU_ADD (EAlu ALU_ADD (EVar 1) (EVar 5)) (ELit (offk k + 6));
   EVar 4;
   EExt true 0 1 (EVar 7);
   ELit 0x26689;
   EVar 35;
   EVar 36;
   EVar 37;
   EVar 38;
   EVar 39;
   EVar 40;
   EVar 41;
   EVar 42;
   EVar 43].

Definition kn_Tk0 (k : Z) : list kentry :=
  [KAlign (EVar 0) 16;
   KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) (ELit 8388608);
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x1b594);
   KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8));
   KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x139e0);
   KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32));
   KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0);
   KWord (SA (EVar 0) (-120)) 8 (ELit 0);
   KAlign (EVar 2) 4096;
   KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KAlign (EVar 1) 4096;
   KRange (EVar 1) 0x58000 (0x7fffff800000 - nbk k);
   KWr (SA (EVar 1) (0)) (ELit (nbk k));
   KWr (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x80800000) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x80800000) (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 2) (0)) (ELit 4096) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0x48000) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0x48000) (SA (EVar 2) (0)) (ELit 4096);
   KWord (SA (EVar 2) (0)) 8 (EVar 45);
   KWord (SA (EVar 2) (8)) 8 (ELit 0);
   KWord (SA (EVar 2) (16)) 4 (ELit 101);
   KWord (SA (EVar 2) (slotC k 0)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 8)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 16)) 8 (EVar 1);
   KWord (SA (EVar 2) (slotC k 0 + 24)) 4 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 28)) 4 (ELit 0);
   KWord (SA (EVar 2) (slotC k 0 + 32)) 8 (ELit (Wk k));
   KWord (SA (EVar 2) (slotF k 0)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (EVar 2) (slotF k 0 + 8)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (EVar 2) (slotF k 0 + 16)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotF k 0 + 24)) 8 (ELit 0);
   KWord (SA (EVar 2) (slotF k 0 + 32)) 8 (ELit 0);
   KZero (SA (EVar 2) (104)) (ELit (4096 - 104));
   KWord (SA (EVar 1) (0)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotC k 0)));
   KWord (SA (EVar 1) (8)) 1 (ELit 0);
   KZero (SA (EVar 1) (9)) (ELit 4);
   KWord (SA (EVar 1) (13)) 1 (ELit 224);
   KWord (SA (EVar 1) (14)) 2 (ELit (k + 1));
   KWord (SA (EVar 1) (offk k - 4)) 1 (ELit 0);
   KWord (SA (EVar 1) (offk k - 3)) 1 (ELit 160);
   KWord (SA (EVar 1) (offk k - 2)) 2 (ELit (k + 1));
   KWord (SA (EVar 1) (offk k + capk k)) 1 (ELit 0);
   KWord (SA (EVar 1) (nbk k - 9)) 1 (ELit 0);
   KWord (SA (EVar 1) (nbk k - 8)) 4 (ELit (resk k));
   KZero (SA (EVar 1) (nbk k - 4)) (ELit 4);
   KBlob (SA (EVar 1) (offk k)) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) 0;
   KWr (SA (ELit 0) 0x26000) (ELit 0x32000);
   KImg 0x0 0x1000;
   KImg 0x10000 0x26640;
   KImg 0x26641 0x26689; KImg 0x36689 0x366e0;
   KImg 0x567b8 0x567d8;
   KWord (SA (ELit 0) (222952)) 8 (ELit 0x366e8);
   KWord (SA (ELit 0) (222984)) 4 (EVar 3);
   KWord (SA (ELit 0) (222988)) 4 (EVar 11);
   KImg 0x36714 0x36760;
   KImg 0x36768 0x36780;
   KImg 0x36788 0x367a0;
   KImg 0x367b0 0x367c0;
   KImg 0x367c8 0x36838; KImg 0x567f8 0x56a20;
   KWord (SA (ELit 0) (354288)) 8 (EVar 44);
   KImg 0x56a20 0x56a28;
   KImg 0x56a39 0x56a40;
   KImg 0x56a48 0x56a50;
   KImg 0x56a60 0x56a68;
   KWord (SA (ELit 0) (354920)) 8 (ELit 4096);
   KImg 0x56a70 0x56aa0;
   KImg 0x56aa8 0x56ab0;
   KWord (SA (ELit 0) (354992)) 8 (EVar 45);
   KWord (SA (ELit 0) (355000)) 4 (ELit 1);
   KWord (SA (ELit 0) (355004)) 4 (ELit (1 + k));
   KWord (SA (ELit 0) (355008)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (ELit 0) (355016)) 8 (EAlu ALU_ADD (EVar 2) (ELit 104));
   KWord (SA (ELit 0) (355024)) 8 (ELit 99);
   KWord (SA (ELit 0) (355032)) 8 (ELit 0);
   KWord (SA (ELit 0) (355040)) 8 (EVar 10);
   KWord (SA (ELit 0) (355048)) 8 (EVar 2);
   KWord (SA (ELit 0) (355056)) 8 (EVar 2);
   KWord (SA (ELit 0) (355064)) 8 (EAlu ALU_ADD (EVar 2) (ELit 4096));
   KImg 0x56b00 0x56c60;
   KWord (SA (ELit 0) (355424)) 8 (ELit 0);
   KImg 0x56c68 0x56c80;
   KImg 0x56c80 0x56de0;
   KWord (SA (ELit 0) (355808)) 8 (ELit 0);
   KImg 0x56de8 0x56e00;
   KImg 0x56e00 0x56e40;
   KWord (SA (ELit 0) (355904)) 1 (ELit (1 + 2 * k));
   KImg 0x56e41 0x56e48;
   KWord (SA (ELit 0) (355912)) 8 (EVar 9);
   KImg 0x56e58 0x58000;
   KRange (EVar 3) 1 4194303;
   KRange (EVar 10) 0 1;
   KRange (EVar 11) 0 4294967295;
   KRange (EVar 5) 0 32767;
   KRange (EVar 6) 0 255;
   KRange (EVar 7) 0 255;
   KRange (EVar 8) 0 255;
   KRange (EAlu ALU_ADD (EAlu ALU_ADD (EVar 4) (EVar 5)) (ELit 6)) (capk (k - 1)) (capk k - 1)].

(* [comment removed for export] *)
Definition kn_Tk (k nlo nhi : Z) : list kentry :=
  KRange (EVar 4) nlo nhi :: KRange (EVar 5) 0 (Z.min 32767 (capk k - 7 - nlo)) :: kn_Tk0 k.

(* [comment removed for export] *)
Definition maps_Tk (k : Z) : list smap := [SM (EVar 1) (ELit (nbk k)) true; SM (EVar 2) (ELit 4096) false].

(* [comment removed for export] *)
Definition slots_Tk (k : Z) : list sslot :=
  [SL (EAlu ALU_ADD (EVar 1) (ELit 16)) (ELit (nbk k - 16)) (ELit (capk k)) (ELit (k + 1)) (ELit (Wk k)) 0 (EAlu ALU_ADD (EVar 1) (ELit (offk k)))].

(* [comment removed for export] *)
Definition cs_Tk (k nlo nhi : Z) : cstate := CS (SS 0x13cb0 (sr_Tk k) [] (kn_Tk k nlo nhi) NX0k) (maps_Tk k) 9 (nbk k + 2^20 + 8192) (slots_Tk k).
