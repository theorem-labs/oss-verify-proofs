(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: written for simdjson/fuzz_utf8's ubsan binary from simdjson/fuzz_minifyimpl's proofs/lib/Ubsan/PM_fz1Cert.v: this harness's first segment (entry to operator new), its code ranges, start facts, footprint and final registers, each read from a probe run of the same symbolic run at LPS c0dd863a. *)
(* The first segment of fuzz_utf8's first call, as a checked symbolic run: LLVMFuzzerTestOneInput's entry
   (0x3bca4) saves ra and s0..s9, finds the static vector's guard clear, takes the guard (0x5ac1c) and builds the
   vector (0x3b398): get_available_implementations' list and the fallback singleton (each behind its own guard in
   the harness's statics), required_instruction_sets through the vtable, push_back, up to the call of operator new
   (0xd320c) for the vector's 8-byte buffer.  The start facts are what fuzz_first's premises give (UM_fuzzF.fz1_know). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PIosKitA PIosKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Definition fz1_ranges : list (Z * nat) := [(242584, 33%nat); (242812, 10%nat); (242892, 13%nat); (242952, 3%nat); (244900, 19%nat); (245200, 8%nat); (247564, 11%nat); (248056, 8%nat); (250508, 18%nat); (250604, 47%nat); (251244, 22%nat); (355908, 2%nat); (356552, 9%nat); (356608, 25%nat); (371740, 3%nat); (371760, 10%nat); (371820, 5%nat)].
Definition fz1_IT : itab := APC.mk_itab_ranges usegs fz1_ranges.
Lemma fz1_IT_ok : itab_sound usegs fz1_IT.
Proof. apply mk_itab_ranges_ok. Qed.
Definition fz1_ENTRY : Z := 244900.   (* PFUZZ_ENTRY *)
Definition fz1_RET : Z := 864780.     (* POPNEW *)
Definition fz1_kn0 : list kentry :=
  [KRange (EVar 2) 140735332499456 18446744073709551456;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWord (SA (ELit 0) 869232) 8 (ELit 355908);
   KWord (SA (ELit 0) 869256) 8 (ELit 258352);
   KWord (SA (ELit 0) 1105163) 1 (ELit 0);
   KWord (SA (ELit 0) 1104576) 1 (ELit 0);
   KWord (SA (ELit 0) 1104577) 3 (ELit 0);
   KWord (SA (ELit 0) 1104580) 4 (ELit 0);
   KWord (SA (ELit 0) 1104584) 4 (ELit 2);
   KWord (SA (ELit 0) 1104592) 8 (ELit 1104600);
   KWord (SA (ELit 0) 1104600) 8 (ELit 0);
   KWord (SA (ELit 0) 1104608) 8 (ELit 522092);
   KWord (SA (ELit 0) 1104616) 8 (ELit 775480);
   KWord (SA (ELit 0) 1104624) 8 (ELit 0);
   KWord (SA (ELit 0) 1104864) 8 (ELit 965400);
   KWord (SA (ELit 0) 1104872) 8 (ELit 242464);
   KWord (SA (ELit 0) 1104880) 8 (ELit 0);
   KImg 65536 868352;
   KImg 964576 964832;
   KWr (SA (ELit 0) 868352) (ELit 241664)].
Definition fz1_sr0 : list expr := [ELit 0; ELit 242324; EVar 2; EVar 3; ELit 973432; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_ss0 : sym_state := SS fz1_ENTRY fz1_sr0 [] fz1_kn0 33%nat.
Definition fz1_W : list fpwin := [(EVar 2, -4096, 0); (ELit 0, 964576, 964832)].
Definition fz1_ssF : sym_state := match srun usegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 with Some (ss', _) => ss' | None => fz1_ss0 end.
Definition fz1_srF : list expr := [ELit 0; ELit 248088; EAlu ALU_ADD (EVar 2) (ELit (-304)); EVar 3; ELit 973432; EVar 5; EVar 6; EVar 7; ELit 1; ELit 0; ELit 8; ELit 1; ELit 0; ELit 964616; ELit 1; EVar 15; EVar 16; EVar 17; ELit 964712; ELit 0; ELit 18446744073709551608; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition fz1_exports : list (Z * list byte) := [].
Definition fz1_wexports : list wexp := [].
(* The run reaches operator new with the registers fz1_srF, writes only the stack below sp and the harness's
   statics, and its final facts (s_know fz1_ssF) are carried into the second segment by PM_fz2Cert. *)
Lemma fz1_cert : scheck_k usegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 fz1_W fz1_RET fz1_srF (s_know fz1_ssF) fz1_exports fz1_wexports = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
