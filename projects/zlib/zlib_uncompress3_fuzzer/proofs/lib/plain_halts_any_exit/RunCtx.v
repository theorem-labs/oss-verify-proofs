(* the run's launch parameters -- input, stack top, mmap base -- as ONE
   instance binder.  A text the tool lifts to [run_segments S rc_inp rc_sp rc_mb] takes {RCa1 : RunCtx}; a Section
   that names them (inp / sp0 / mbase) declares one local instance [mkRunCtx inp sp0 mbase]; typeclass resolution
   then finds the instance wherever a lifted definition is used bare. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.

Class RunCtx := mkRunCtx { rc_inp : ProcInput; rc_sp : word; rc_mb : word }.

(* over the image, [cbn] / [simpl] left a segment list such
   as [R_segs] folded; over the run, [run_segments R_segs ..] delta-reduces to [R_segs ++ vdso_segments ..], and
   [cbn in H] then unfolds the image's segments into a cons list that no fact matches syntactically.  Keep the run's
   list folded under cbn / simpl, as the image's was; [unfold run_segments] still opens it where a proof needs to.
   Reduction behaviour only: no statement changes. *)
Arguments Run.run_segments : simpl never.
