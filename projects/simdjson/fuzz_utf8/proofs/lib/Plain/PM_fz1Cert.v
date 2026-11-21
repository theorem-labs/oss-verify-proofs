(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's plain binary in the form of simdjson/fuzz_minifyimpl's proofs/lib/Plain/PM_fz1Cert.v: module paths; this harness's entry, its operator new and start facts (two client_img cells); the code ranges and final registers read from a probe of this run at LPS c0dd863a. *)
(* The certified run of fuzz_utf8's plain LLVMFuzzerTestOneInput, first call, from its entry to operator new (the
   static vector's guard, the guard's acquire and the vector's construction up to its allocation). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PIosKitA PIosKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
(* The instructions the run executes (probe). *)
Definition fz1_ranges : list (Z * nat) := [(243000, 32%nat); (243144, 11%nat); (243192, 3%nat); (245016, 19%nat); (245244, 8%nat); (247336, 8%nat); (249380, 18%nat); (249476, 38%nat); (249984, 22%nat); (317544, 2%nat); (318164, 9%nat); (318220, 25%nat); (330344, 3%nat); (330364, 10%nat); (330424, 5%nat)].
Definition fz1_IT : itab := APC.mk_itab_ranges psegs fz1_ranges.
Lemma fz1_IT_ok : itab_sound psegs fz1_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz1_ENTRY : Z := 245016.   (* PU_iface.PFUZZ_ENTRY = 0x3bd18 *)
Definition fz1_RET : Z := 823384.     (* ROpNew_iface.POPNEW = 0xc9058 *)
(* At entry: sp's range and alignment, the stack page below it, client_img's two cells, RNEED_LOCKS = 0,
   patexit 2 0 0, the read-only image, the harness statics none (ps_fa = None), the writable window. *)
Definition fz1_kn0 : list kentry :=
  [KRange (EVar 2) 140735332499456 18446744073709551456;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWord (SA (ELit 0) 827840) 8 (ELit 317544);
   KWord (SA (ELit 0) 827864) 8 (ELit 255132);
   KWord (SA (ELit 0) 1063003) 1 (ELit 0);
   KWord (SA (ELit 0) 1062416) 1 (ELit 0);
   KWord (SA (ELit 0) 1062417) 3 (ELit 0);
   KWord (SA (ELit 0) 1062420) 4 (ELit 0);
   KWord (SA (ELit 0) 1062424) 4 (ELit 2);
   KWord (SA (ELit 0) 1062432) 8 (ELit 1062440);
   KWord (SA (ELit 0) 1062440) 8 (ELit 0);
   KWord (SA (ELit 0) 1062448) 8 (ELit 480696);
   KWord (SA (ELit 0) 1062456) 8 (ELit 734084);
   KWord (SA (ELit 0) 1062464) 8 (ELit 0);
   KWord (SA (ELit 0) 1062704) 8 (ELit 923240);
   KWord (SA (ELit 0) 1062712) 8 (ELit 242880);
   KWord (SA (ELit 0) 1062720) 8 (ELit 0);
   KImg 65536 827392;
   KImg 922416 922672;
   KWr (SA (ELit 0) 827392) (ELit 241664)].
Definition fz1_sr0 : list expr := [ELit 0; ELit 242740; EVar 2; EVar 3; ELit 931272; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_ss0 : sym_state := SS fz1_ENTRY fz1_sr0 [] fz1_kn0 33%nat.
Definition fz1_W : list fpwin := [(EVar 2, -4096, 0); (ELit 0, 922416, 922672)].
Definition fz1_ssF : sym_state := match srun psegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 with Some (ss', _) => ss' | None => fz1_ss0 end.
(* The registers at operator new (probe). *)
Definition fz1_srF : list expr := [ELit 0; ELit 247368; EAlu ALU_ADD (EVar 2) (ELit (-256)); EVar 3; ELit 931272; EVar 5; EVar 6; EVar 7; ELit 1; ELit 922544; ELit 8; ELit 1; ELit 1; ELit 0; EVar 14; EVar 15; EVar 16; EVar 17; ELit 922552; ELit 0; ELit 2305843009213693951; ELit 9223372036854775800; ELit 0; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_exports : list (Z * list byte) := [].
Definition fz1_wexports : list wexp := [].
(* [comment removed for export] *)
Lemma fz1_cert : scheck_k psegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 fz1_W fz1_RET fz1_srF (s_know fz1_ssF) fz1_exports fz1_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
