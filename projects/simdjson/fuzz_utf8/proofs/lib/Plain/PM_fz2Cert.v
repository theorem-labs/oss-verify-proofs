(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's plain binary in the form of simdjson/fuzz_minifyimpl's proofs/lib/Plain/PM_fz2Cert.v: module paths; this harness's join point, kept windows, written windows (its guard, vector and atexit cells) and the join's words (its 128-byte frame, the fallback object); the code ranges, entry, start and final registers read from a probe of this run at LPS c0dd863a. *)
(* The certified run of fuzz_utf8's plain LLVMFuzzerTestOneInput, first call, from operator new's return to the
   join point (the vector filled, its destructor registered with atexit, the guard released). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PM_fz1Cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
(* The instructions the run executes (probe). *)
Definition fz2_ranges : list (Z * nat) := [(243204, 41%nat); (245276, 9%nat); (247256, 3%nat); (247288, 2%nat); (247312, 1%nat); (247368, 5%nat); (330424, 5%nat); (733688, 19%nat); (733772, 3%nat); (733816, 18%nat); (803104, 2%nat); (803380, 5%nat); (803452, 2%nat); (803484, 2%nat); (804064, 5%nat); (806320, 3%nat); (806824, 1%nat); (806968, 3%nat)].
Definition fz2_IT : itab := APC.mk_itab_ranges psegs fz2_ranges.
Lemma fz2_IT_ok : itab_sound psegs fz2_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz2_ENTRY : Z := 247368.   (* operator new's return address, fz1_srF's ra (probe) *)
Definition fz2_RET : Z := 245092.     (* PM_iface.PJOIN = 0x3bd64 *)
(* The facts operator new keeps (rheap_pres): the stack from its sp up, the writable window without
   RMalloc_iface.ralloc_static and without [RATP + 0x88, PATX - 8). *)
Definition fz2_KEEP : list fpwin := [(EVar 2, -256, 4096); (ELit 0, 827392, 851640); (ELit 0, 851648, 931108); (ELit 0, 931112, 931408); (ELit 0, 1062408, 1062968); (ELit 0, 1062976, 1063000); (ELit 0, 1064312, 1066428); (ELit 0, 1066432, 1069056)].
(* The new block A = EVar 33 (rblock_range A 8), apart from the image and the stack; the stack page, the writable
   window, RNEED_LOCKS = 0 and the read-only image again. *)
Definition fz2_kn0 : list kentry :=
  kn_keep fz2_KEEP (s_know fz1_ssF) ++
  [KRange (EVar 33) 16 140737479966712;
   KAlign (EVar 33) 16;
   KWr (SA (EVar 33) 0) (ELit 8);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (ELit 0) 65536) (ELit 1003520);
   KDisj (SA (EVar 33) 0) (ELit 8) (SA (EVar 2) (-8192)) (ELit 16384);
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWr (SA (ELit 0) 827392) (ELit 241664);
   KWord (SA (ELit 0) 1063003) 1 (ELit 0);
   KImg 65536 827392].
(* fz1_srF with operator new's post: ra, sp, gp, tp, s0..s11 kept, a0 = A, the rest new (probe). *)
Definition fz2_sr0 : list expr := [ELit 0; ELit 247368; EAlu ALU_ADD (EVar 2) (ELit (-256)); EVar 3; ELit 931272; EVar 34; EVar 35; EVar 36; ELit 1; ELit 922544; EVar 33; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; ELit 922552; ELit 0; ELit 2305843009213693951; ELit 9223372036854775800; ELit 0; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_ss0 : sym_state := SS fz2_ENTRY fz2_sr0 [] fz2_kn0 48%nat.
(* The windows the run writes: the stack page, the block, the guard (PVEC_GUARD), the vector (PVEC), atexit's
   count, function and argument cells. *)
Definition fz2_W : list fpwin := [(EVar 2, -4096, 0); (EVar 33, 0, 8); (ELit 0, 922424, 922426); (ELit 0, 922456, 922480); (ELit 0, 1062424, 1062428); (ELit 0, 1062464, 1062472); (ELit 0, 1062720, 1062728)].
Definition fz2_ssF : sym_state := match srun psegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 with Some (ss', _) => ss' | None => fz2_ss0 end.
(* The registers at the join point (probe). *)
Definition fz2_srF : list expr := [ELit 0; ELit 245308; EAlu ALU_ADD (EVar 2) (ELit (-128)); EVar 3; ELit 931272; EVar 34; EVar 35; EVar 36; EVar 11; EVar 10; ELit 922424; ELit 1; ELit 16; ELit 0; ELit 0; ELit 0; EVar 42; EVar 43; ELit 922424; ELit 922456; ELit 922416; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 44; EVar 45; EVar 46; EVar 47].
Definition fz2_exports : list (Z * list byte) := [].
(* What the join reads: the caller's s9..s0 and ra at sp - 88, the block's word PFALLBACK, guard1, the vector
   [A; A + 8; A + 8], the fallback object's vtable, patexit 3 PDTOR_THUNK PVEC. *)
Definition fz2_wexports : list wexp := [(EVar 2, -88, 8%nat, EVar 25); (EVar 2, -80, 8%nat, EVar 24); (EVar 2, -72, 8%nat, EVar 23); (EVar 2, -64, 8%nat, EVar 22); (EVar 2, -56, 8%nat, EVar 21); (EVar 2, -48, 8%nat, EVar 20); (EVar 2, -40, 8%nat, EVar 19); (EVar 2, -32, 8%nat, EVar 18); (EVar 2, -24, 8%nat, EVar 9); (EVar 2, -16, 8%nat, EVar 8); (EVar 2, -8, 8%nat, ELit 242740); (EVar 33, 0, 8%nat, ELit 922624); (ELit 0, 922424, 1%nat, ELit 1); (ELit 0, 922425, 1%nat, ELit 1); (ELit 0, 922456, 8%nat, EVar 33); (ELit 0, 922464, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 922472, 8%nat, EAlu ALU_ADD (EVar 33) (ELit 8)); (ELit 0, 922624, 8%nat, ELit 827824); (ELit 0, 1062416, 1%nat, ELit 0); (ELit 0, 1062417, 3%nat, ELit 0); (ELit 0, 1062420, 4%nat, ELit 0); (ELit 0, 1062424, 4%nat, ELit 3); (ELit 0, 1062432, 8%nat, ELit 1062440); (ELit 0, 1062440, 8%nat, ELit 0); (ELit 0, 1062448, 8%nat, ELit 480696); (ELit 0, 1062456, 8%nat, ELit 734084); (ELit 0, 1062464, 8%nat, ELit 243420); (ELit 0, 1062704, 8%nat, ELit 923240); (ELit 0, 1062712, 8%nat, ELit 242880); (ELit 0, 1062720, 8%nat, ELit 922456)].
(* [comment removed for export] *)
Lemma fz2_cert : scheck psegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 fz2_W fz2_RET fz2_srF fz2_exports fz2_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
