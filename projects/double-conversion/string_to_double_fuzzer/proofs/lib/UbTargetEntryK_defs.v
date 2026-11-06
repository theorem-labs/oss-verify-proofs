(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymPlan UbWorldK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SP.
Open Scope Z_scope.

Definition NX0k : nat := 44%nat.
Definition sr_Tk (k : Z) : list expr :=
  [ELit 0;
   ELit 0x327a8;
   EAlu ALU_ADD (EVar 0) (ELit (-128));
   ELit 0x10800;
   ELit 0xc5018;
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
   ELit 0xb35e9;
   ELit 0;
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
   KWord (SA (EVar 0) (-56)) 8 (ELit 0x96140);
   KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8));
   KWord (SA (EVar 0) (-72)) 8 (ELit 2);
   KWord (SA (EVar 0) (-80)) 8 (ELit 0x32634);
   KWord (SA (EVar 0) (-88)) 8 (EAlu ALU_ADD (EVar 0) (ELit 32));
   KWord (SA (EVar 0) (-96)) 8 (ELit 0);
   KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-112)) 8 (ELit 0);
   KWord (SA (EVar 0) (-120)) 8 (ELit 0);
   KAlign (EVar 2) 4096;
   KRange (EVar 2) 0x2000 0x7fffff7ff000;
   KDisj (SA (EVar 0) (-8388608)) (ELit 281474976710656) (SA (EVar 2) (0)) (ELit 4096);
   KRange (EAlu ALU_SUB (EVar 0) (EVar 2)) 8392704 0x800000000000;
   KAlign (EVar 1) 4096;
   KRange (EVar 1) 0xe6000 (0x7fffff800000 - nbk k);
   KDisj (SA (EVar 0) (-8388608)) (ELit 281474976710656) (SA (EVar 1) (0)) (ELit (nbk k));
   KRange (EAlu ALU_SUB (EVar 0) (EVar 1)) (8388608 + nbk k) 0x800000000000;
   KWr (SA (EVar 1) (0)) (ELit (nbk k));
   KWr (SA (EVar 2) (0)) (ELit 4096);
   KDisj (SA (EVar 2) (0)) (ELit 4096) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xd6000) (SA (EVar 1) (0)) (ELit (nbk k));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xd6000) (SA (EVar 2) (0)) (ELit 4096);
   KWord (SA (EVar 2) (0)) 8 (EVar 13);
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
   KWr (SA (ELit 0) 0xb3000) (ELit 0x10620);
   KWr (SA (ELit 0) 0xc4708) (ELit 0x218f8);
   KImg 0x0 0x1000;
   KImg 0x10000 0xb35a0;
   KImg 0xb35a1 0xb35e9;
   KImg 0xc35e9 0xc3620;
   KImg 0xc4708 0xc4f48;
   KImg 0xe5020 0xe5040;
   KWord (SA (ELit 0) (806736)) 8 (ELit 0xc4f50);
   KWord (SA (ELit 0) (806768)) 4 (EVar 3);
   KWord (SA (ELit 0) (806772)) 4 (EVar 11);
   KImg 0xc4f7c 0xc4fc8;
   KImg 0xc4fd0 0xc4fe8;
   KImg 0xc4ff0 0xc5008;
   KImg 0xc5018 0xc5028;
   KImg 0xc5030 0xc50a0; KImg 0xe5058 0xe5288;
   KWord (SA (ELit 0) (938632)) 8 (EVar 12);
   KImg 0xe5290 0xe5298;
   KImg 0xe52a9 0xe52b0;
   KImg 0xe52b8 0xe52c0;
   KImg 0xe52d0 0xe52d8;
   KWord (SA (ELit 0) (938712)) 8 (ELit 4096);
   KImg 0xe52e0 0xe5310;
   KImg 0xe5318 0xe5428;
   KWord (SA (ELit 0) (939048)) 8 (EVar 13);
   KWord (SA (ELit 0) (939056)) 4 (ELit 1);
   KWord (SA (ELit 0) (939060)) 4 (ELit (1 + k));
   KWord (SA (ELit 0) (939064)) 8 (EAlu ALU_ADD (EVar 2) (ELit (slotF k 0)));
   KWord (SA (ELit 0) (939072)) 8 (EAlu ALU_ADD (EVar 2) (ELit 104));
   KWord (SA (ELit 0) (939080)) 8 (ELit 99);
   KWord (SA (ELit 0) (939088)) 8 (ELit 0);
   KWord (SA (ELit 0) (939096)) 8 (EVar 10);
   KWord (SA (ELit 0) (939104)) 8 (EVar 2);
   KWord (SA (ELit 0) (939112)) 8 (EVar 2);
   KWord (SA (ELit 0) (939120)) 8 (EAlu ALU_ADD (EVar 2) (ELit 4096));
   KImg 0xe5478 0xe55d8;
   KWord (SA (ELit 0) (939480)) 8 (ELit 0);
   KImg 0xe55e0 0xe55f8;
   KImg 0xe55f8 0xe5758;
   KWord (SA (ELit 0) (939864)) 8 (ELit 0);
   KImg 0xe5760 0xe5778;
   KImg 0xe5778 0xe57b8;
   KWord (SA (ELit 0) (939960)) 1 (ELit (1 + 2 * k));
   KImg 0xe57b9 0xe57c0;
   KWord (SA (ELit 0) (939968)) 8 (EVar 9);
   KImg 0xe57c8 0xe6000;
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
Definition cs_Tk (k nlo nhi : Z) : cstate := CS (SS 0x32904 (sr_Tk k) [] (kn_Tk k nlo nhi) NX0k) (maps_Tk k) 9 (nbk k + 2^20 + 8192) (slots_Tk k).
