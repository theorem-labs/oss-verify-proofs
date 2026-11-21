(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's ubsan binary from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/PM_fz2Cert.v: this harness's second segment (operator new's return to the join point), its code ranges, kept windows from this unit's rclient_addr, start facts, footprint, final registers and the facts fuzz_join_stmt reads, each run-dependent value read from a probe run of the same symbolic run at LPS c0dd863a. *)
(* The second segment of fuzz_utf8's first call, as a checked symbolic run: from operator new's return into the
   split buffer (0x3c918) through push_back storing the fallback singleton's address into the new 8-byte block,
   back to the harness, __cxa_atexit registering the vector's destructor (patexit table entry 3), the guard's
   release, to the join point (0x3bcf0).  Its start state is the first segment's end after operator new
   (opnew_post): the callee-saved registers kept, a0 = the block (EVar 33), the caller-saved ones fresh, and the
   first segment's facts in the windows operator new leaves alone (fz2_KEEP: the stack from operator new's sp
   and rclient_addr's static windows, i.e. 0xd4000..0x10f000 without ralloc_static), with the new block's facts. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import PM_fz1Cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition fz2_ranges : list (Z * nat) := [(242716, 14%nat); (242964, 29%nat); (245232, 9%nat); (247608, 1%nat); (247616, 28%nat); (247732, 55%nat); (247956, 4%nat); (247996, 2%nat); (248024, 1%nat); (248088, 5%nat); (371820, 5%nat); (775084, 19%nat); (775168, 3%nat); (775212, 18%nat); (844500, 2%nat); (844776, 5%nat); (844848, 2%nat); (844880, 2%nat); (845460, 5%nat); (847716, 3%nat); (848220, 1%nat); (848364, 3%nat)].
Definition fz2_IT : itab := APC.mk_itab_ranges usegs fz2_ranges.
Lemma fz2_IT_ok : itab_sound usegs fz2_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz2_ENTRY : Z := 248088.   (* operator new's return address in the split buffer *)
Definition fz2_RET : Z := 244976.     (* PJOIN *)
Definition fz2_KEEP : list fpwin := [(EVar 2, -304, 4096); (ELit 0, 868352, 893032); (ELit 0, 893040, 973268); (ELit 0, 973272, 1105128); (ELit 0, 1105136, 1105160); (ELit 0, 1106472, 1108588); (ELit 0, 1108592, 1110016)].
Definition fz2_kn0 : list kentry :=
  kn_keep fz2_KEEP (s_know fz1_ssF) ++
  [KRange (EVar 33) 16 140737479966712;
   KAlign (EVar 33) 16;
   KWr (SA (EVar 33) 0) (ELit 8);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (ELit 0) 65536) (ELit 1044480);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (EVar 2) (-8192)) (ELit 16384);
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWr (SA (ELit 0) 868352) (ELit 241664);
   KWord (SA (ELit 0) 1105163) 1 (ELit 0);
   KImg 65536 868352].
Definition fz2_sr0 : list expr := [ELit 0; ELit 248088; EAlu ALU_ADD (EVar 2) (ELit (-304)); EVar 3; ELit 973432; EVar 34; EVar 35; EVar 36; ELit 1; ELit 0; EVar 33; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; ELit 964712; ELit 0; ELit 18446744073709551608; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_ss0 : sym_state := SS fz2_ENTRY fz2_sr0 [] fz2_kn0 48%nat.
(* the writes: the stack below sp, the new block, and client_wr's four windows (statics, patexit count, slot 3) *)
Definition fz2_W : list fpwin := [(EVar 2, -4096, 0); (EVar 33, 0, 8); (ELit 0, 964576, 964832); (ELit 0, 1104584, 1104588); (ELit 0, 1104624, 1104632); (ELit 0, 1104880, 1104888)].
Definition fz2_ssF : sym_state := match srun usegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 with Some (ss', _) => ss' | None => fz2_ss0 end.
Definition fz2_srF : list expr := [ELit 0; ELit 245264; EAlu ALU_ADD (EVar 2) (ELit (-112)); EVar 3; ELit 973432; EVar 34; EVar 35; EVar 36; EVar 11; EVar 10; ELit 964584; ELit 1; ELit 16; ELit 0; ELit 0; ELit 0; ELit 0; EVar 43; ELit 964584; ELit 964616; ELit 964576; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_exports : list (Z * list byte) := [].
(* the facts fuzz_join_stmt's premises read at the join: the saved ra and s0..s9 (sp-88..sp), the block's
   element (the fallback singleton), the guard, the vector, the singleton's vtable, the patexit table *)
Definition fz2_wexports : list wexp := [(EVar 2, -88, 8%nat, EVar 25); (EVar 2, -80, 8%nat, EVar 24); (EVar 2, -72, 8%nat, EVar 23); (EVar 2, -64, 8%nat, EVar 22); (EVar 2, -56, 8%nat, EVar 21); (EVar 2, -48, 8%nat, EVar 20); (EVar 2, -40, 8%nat, EVar 19); (EVar 2, -32, 8%nat, EVar 18); (EVar 2, -24, 8%nat, EVar 9); (EVar 2, -16, 8%nat, EVar 8); (EVar 2, -8, 8%nat, ELit 242324); (EVar 33, 0, 8%nat, ELit 964784); (ELit 0, 964584, 1%nat, ELit 1); (ELit 0, 964585, 1%nat, ELit 1); (ELit 0, 964616, 8%nat, EVar 33); (ELit 0, 964624, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 964632, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 964784, 8%nat, ELit 869216); (ELit 0, 1104576, 1%nat, ELit 0); (ELit 0, 1104577, 3%nat, ELit 0); (ELit 0, 1104580, 4%nat, ELit 0); (ELit 0, 1104584, 4%nat, ELit 3); (ELit 0, 1104592, 8%nat, ELit 1104600); (ELit 0, 1104600, 8%nat, ELit 0); (ELit 0, 1104608, 8%nat, ELit 522092); (ELit 0, 1104616, 8%nat, ELit 775480); (ELit 0, 1104624, 8%nat, ELit 243108); (ELit 0, 1104864, 8%nat, ELit 965400); (ELit 0, 1104872, 8%nat, ELit 242464); (ELit 0, 1104880, 8%nat, ELit 964616)].
(* The run reaches the join with the registers fz2_srF, writes only inside fz2_W, and every fz2_wexports fact
   holds in its final memory. *)
Lemma fz2_cert : scheck usegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 fz2_W fz2_RET fz2_srF fz2_exports fz2_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
