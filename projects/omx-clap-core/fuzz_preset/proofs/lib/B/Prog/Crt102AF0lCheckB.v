(* rule 24: no function proved
   fuzz_preset, the crt102 walk: the CODE-RECORD BINDING CHECK at image B' (#102 pins: asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), at the B' instance B := YD2l.TfibB, for the code addresses this lane's stand-ins
   read through `as_code B`. The B' port of lib/A/Prog/Crt102AF0lCheck.v 76548b0b655e (the A' check against AF0l).

   Crt102EntryB's MARKED STAND-IN `pal_stack_malloc3 : SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code B) 3`
   (lib/B/Prog/Crt102EntryB.v 27ad45449ff3 at commit 9179085e57d, :199, SIGMA :=
   pa_sigma of B_prog_listing at the instance PA) reads the B' code record YF0l.Tfib_code once B is TfibB
   (as_code TfibB := Tfib_code, lib/Reusable/YD2l.v :14). crt102_stack_malloc3_TfibB is that hypothesis at
   PA := PI_prog_B, B := TfibB, by vm_compute: the witness the B' composition cites for it. The other four lemmas check
   the remaining pc fields this lane's frame and call rules bind (the frame classes 0 / 1, the free / malloc wrappers).

   INPUTS OF RECORD (by path; blobs of the base commit 100c8e45583c unless named):
   - listing (#102 B'): lib/B/Listing_prog.v c97cc46b3e13, lib/B/PAImg_prog.v 15fab93fe702 (PI_prog_B).
   - code record: lib/Reusable/YF0l.v 4a405a3dba65 (generated from the pin d663f82d7f488d30, twin c90d4fa54d43160b).
   - the B' asyms record, TAKEN BY PATH from the integration commit bedf6e890875: lib/Reusable/YD2l.v
     0d0bc856b447 (the #102 B' record; the base had 4deb698ee695, the old pin's cells) and the trace file its
     TfibB_syms needs, lib/Reusable/YCej.v ae866e8addb2 (generated from image B'; the base had 9d858604e7c0, the old
     pin's traces). Crt102PALibCheckB.v names them again with the rest of that file's inputs.
   NUMERALS. ADDRESS: none typed (every address is pa_sigma / pa_val of the listing or a field of TfibB's code record;
   the Eval line prints them). WORD: 0, 1, 3 (the frame classes). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YP0b YPsym YC4aP YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

(* which module each image name resolves to in this file's closure (printed into the build log) *)
Locate B_prog_listing.
Locate PI_prog_B.
Locate YD2l.TfibB.

(* PI_prog_B is stated over a run ceiling; the listing's pcs do not depend on it *)
Section s. Context {rc : YM05.RunCeil}.
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Notation TB := (YD2l.TfibB).

(* Crt102EntryB's pal_stack_malloc3 at PA := PI_prog_B, B := TfibB *)
Lemma crt102_stack_malloc3_TfibB : SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code TB) 3.
Proof. vm_compute. reflexivity. Qed.
(* the other two frame classes' __asan_stack_malloc_N: the listing's symbol = the code record's pc_stack_malloc N *)
Lemma crt102_stack_malloc0_TfibB : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code TB) 0.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_stack_malloc1_TfibB : SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code TB) 1.
Proof. vm_compute. reflexivity. Qed.
(* the wrappers the free / malloc traces start from *)
Lemma crt102_wrap_free_TfibB : SIGMA AS___wrap_free = pc_wrap_free (as_code TB).
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_wrap_malloc_TfibB : SIGMA AS___wrap_malloc = pc_wrap_malloc (as_code TB).
Proof. vm_compute. reflexivity. Qed.
(* the values themselves, so the log shows the numbers: each listing value beside the code-record value it is checked
   against, then the listing base and the two interceptor return pcs the free / malloc traces record *)
Eval vm_compute in ((SIGMA AS___asan_stack_malloc_3, pc_stack_malloc (as_code TB) 3),
  (SIGMA AS___asan_stack_malloc_0, pc_stack_malloc (as_code TB) 0),
  (SIGMA AS___asan_stack_malloc_1, pc_stack_malloc (as_code TB) 1),
  (SIGMA AS___wrap_free, pc_wrap_free (as_code TB)), (SIGMA AS___wrap_malloc, pc_wrap_malloc (as_code TB)),
  (BASE, pc_free_ra0 (as_code TB), pc_malloc_ra0 (as_code TB))).
End s.

Print Assumptions crt102_stack_malloc3_TfibB.
Print Assumptions crt102_stack_malloc0_TfibB.
Print Assumptions crt102_stack_malloc1_TfibB.
Print Assumptions crt102_wrap_free_TfibB.
Print Assumptions crt102_wrap_malloc_TfibB.
