(* The guard's check. Compiling this file IS the test: each [Fail] must fail.

   If any [Fail] below reports "The command has not failed!", the guard in IdentSkGuard.v has
   stopped working and an ASan link site can once again pick up the PLAIN sink by inference --
   silently, because the wrong constant still satisfies [ro_below_ofl]. Treat that message as a
   build break, not as noise.

   This file is paired with a control that runs the same two terms WITHOUT the guard and must
   therefore FAIL to compile. The control lives OUTSIDE the proofs tree, at
   a draft kept by the porting lane, precisely because it must not be
   built as an ordinary target -- a file meant to error cannot sit in the target set. Run it by
   hand against this same branch.

   A [Fail] that succeeds proves only that the term did not elaborate, which is equally true if
   the term is malformed or the context is wrong. The control is what distinguishes "the guard
   stopped the inference" from "nothing was ever being inferred here". The gate is: this file
   compiles AND the control does not. If both compile, the guard is dead; if neither does, the
   check is broken rather than the guard.

   The wide context is the point: these are the modules an ASan link site actually sits in. A
   narrower context could resolve differently and the check would not see the hazard. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI14 YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentSkGuard IdentSyms.

(* 1. A bare instance of the class must not resolve. *)
Fail Definition sk_bare : YI16.sink_head := _.

(* 2. The projection applied to an inferred instance must not resolve either.

   This must be a [Definition], not a [Check]. `Fail Check (@YI16.sk_ofl_head _).` does NOT fail
   even with the guard in place, because [Check] is happy to report a type with an unsolved hole
   in it -- the `_` simply stays an evar and nothing ever has to resolve it. The first version of
   this file used that form and the build said "The command has not failed!", which looked like a
   dead guard and was in fact a dead test. A [Definition] with a concrete type forces the hole to
   be solved, so it is the inference that is being tested rather than the parser. *)
Fail Definition sk_proj : Z := @YI16.sk_ofl_head _.

(* 2b. The SAME TWO TESTS for [sink_syms], the OTHER class the guard removes an instance of.

      Until 2026-10-29 this file tested only [sink_head], so `YI5c.src0_sink` was removed from
      resolution and never verified -- and an untested removal is exactly what regresses silently,
      because the next person to touch the Require closure can restore it by accident while every
      check still passes.


      This is also the class that matters most for the hazard as it has been found in the wild:
      the finding on fuzz_scene is about [sk_read] inside __stdio_exit and [sk_seek] inside
      __stdio_write, which were [sink_syms] FIELDS, not head fields. Since the YI5c restatement
      those FILE fields live in [file_sink_syms], reached only through
      the [sink_syms] field [sk_file]; [sk_file] is projected below for that reason, because
      `@YI14.sk_seek _` now fails to elaborate for a reason unrelated to the guard (its hole has the
      non-class type [file_sink_syms]). The class is declared in YI14, not YI16 -- only [sink_head]
      lives in YI16. *)
Fail Definition sk_syms_bare : YI14.sink_syms := _.
Fail Definition sk_syms_proj : option YI14.file_sink_syms := @YI14.sk_file _.

(* 3. And the explicit form must still elaborate -- otherwise the guard has removed the ability
      to state the thing at all, rather than the ability to leave it unstated. identity's ASan
      head is 0x5f8648 (asan), eight bytes above ofl_lock 0x5f8640, read from the .debug symtab. *)
Definition sk_explicit : YI16.sink_head := {| YI16.sk_ofl_head := 0x5f8648 |}.
