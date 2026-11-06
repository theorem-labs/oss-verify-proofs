(* Stop instance resolution from silently supplying the PLAIN build's sink to an ASan statement.

   The hazard, measured on this branch: exactly one [sink_head] instance is reachable from every
   context that loads lib/Prog/Seg/Agree.v -- A/AsanTop, A/IdentityTFIB, B/AsanUbsanTop,
   B/IdentityTFIB -- namely YI5b's [src0_sink_head], whose [sk_ofl_head] is [src0_D_ofl_head] =
   0x50640. That is the PLAIN image's overflow-list head. identity's ASan heads are 0x5f8648
   (asan) and 0x5f8948 (asan-ubsan), eight bytes above each image's [ofl_lock], read from the
   .debug symbol tables.

   So a bare [@YI16.sk_ofl_head _] in an ASan context does not merely risk the wrong instance: it
   resolves uniquely and deterministically to the plain one. [as_ofl_head KS = sk_ofl_head] is then
   false and the ASan statement is VACUOUS -- with a green build and a clean Print Assumptions.

   Nothing announces it. A/Prog/IdentBase.v's [ro_below_ofl] asserts [a < sk_ofl_head], and
   identity's .rodata ends at 0x2306c, which is below the plain head as well -- so the premise is
   provable with the wrong constant. The sites that would fail loudly (YE01's [ail_head], settled
   by reflexivity in AD1u) are not where the hazard lives.

   This file removes the three instances from resolution. Every current user of them names them
   explicitly, so removing the hints breaks nothing; what it breaks is the INFERENCE. After this,
   an ASan link site must pass its head with [@] -- identity's own [tfib_sink_head], from the
   core's AE2k -- or fail to elaborate.

   It lives in its own file, required by IdentSyms.v, rather than in IdentSyms.v itself: that file
   requires only ZArith, and writing the directive there would pull the plain sink layer into the
   Require closure of all 30 A and 31 B link files that import it -- the coupling this placement
   exists to avoid. Here the new dependency is visible in one place and reviewable.

   Checked by lib/A/Prog/SkGuardCheck.v, whose control twin must itself fail. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI5b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI5c.

#[global] Remove Hints YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
