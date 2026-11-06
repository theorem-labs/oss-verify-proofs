(* The implicit-instance guard of plugin-hostd/fuzz_reply's ASan core (lib/A)
   and of its walks, after boxreg's three-instance guard. The plain lineage declares #[global] instances of the sink
   classes with cgif-derived plain-image values (Reusable/YI5b.v src0_sink_head: ofl_head 0x51950; Reusable/YI5c.v
   src0_sink: ofl_lock 0x51948; src0_sink_laws), and A/AE2k.v exports the ASan sink_head. In a context that loads both,
   a bare binder of YI16.sink_head or YI14.sink_syms resolves to the PLAIN instance (fuzz_reply.asan's ofl_head is
   0x5f9b68), so a statement taking one by inference can be about the wrong image with a green build.
   This file removes all four instances from typeclass resolution for every file that Requires it, so each such binder
   must be passed with `@`. It depends only on Reusable YK11 / YM05 / YH02 / YI14 / YI16 / YI5b / YI5c and A/AE2k, so it compiles early and
   both the lib/A tops and the walk files can Require it. The checks below fail to resolve each bare binder; the same
   checks with all of lib/A loaded are A/ReplyGuardTest.v. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05 YH02 YI14 YI16 YI5b YI5c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AE2k.
Open Scope Z_scope.
(* Controls, before the guard: each type below is well formed and inhabited when its instance is passed with @, so a
   Fail after the guard can only fail at instance resolution (A/ReplyGuardTest.v repeats them in the wide context). *)
Example guard_head_values : @YI16.sk_ofl_head AE2k.tfib_sink_head = 0x5f9b68 /\ @YI16.sk_ofl_head YI5b.src0_sink_head = 0x51950.
Proof. split; reflexivity. Qed.
Example guard_lock_value : @YI14.sk_ofl_lock YI5c.src0_sink = 0x51948.
Proof. reflexivity. Qed.
Definition guard_laws_explicit : @YI14.sink_laws YH02.src0_msyms YI5b.src0_sink_head YI5c.src0_sink := YI5c.src0_sink_laws.
#[global] Remove Hints AE2k.tfib_sink_head YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
Fail Definition guard_bare_head : Z := YI16.sk_ofl_head.
Fail Definition guard_bare_lock : Z := YI14.sk_ofl_lock.
Fail Definition guard_bare_laws : @YI14.sink_laws YH02.src0_msyms YI5b.src0_sink_head YI5c.src0_sink := _.
