(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan), made after a Theorem Labs lane's closing file
   proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v:160-175 (a working branch af735a950e2: grant_AMEMSET,
   grant_AMEMCPY, grant_ABCMP). The closing instances of three premise rows of scene's entry statement
   lib/A/P_LLVMFuzzerTestOneInput.v (a working branch f6ab6e97937), Section h:
     :274  Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
     :275  Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
     :276  Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
   Each lemma below has exactly the row's type under the statement's Section d Context {fx} {rc} and Section h
   Variable B, with SEGS and SIGMA the statement's notations (:153, :155), so the glue closes each row by `exact`.
   No code is walked here. Each lemma composes the walk theorem of the restaged release output:
     A/AE2r.v:567 asan_memset_realizes (literal pc 0x53e60), A/AE2q.v:144 asan_memcpy_realizes (0x539c4),
     A/AE2s.v:711 bcmp_icpt_contract (0x4430c); each is `forall B, AR_laws tfibsegs B -> TfibSyms B -> ...`.
   The bridges, each closed:
   - SIGMA: PI_scene's pa_sigma is scene_sigma (lib/A/Prog/SceneImg.v:61), which maps the three symbols to
     0x53e60, 0x539c4 and 0x4430c (lib/A/Prog/SceneAddr.v:23, :26, :27). scene_sigma_memset / _memcpy / _bcmp prove
     it by `vm_compute; reflexivity` against PI_scene (the script of lib/A/ScenePalfSm8.v). The values are the
     .symtab addresses of __asan_memset, __asan_memcpy and __interceptor_trampoline_bcmp in the unstripped
     fuzz_scene.asan pin (sha256 6ed872f7cc8c1e426ccbd2a7d1ae20b71d1cb347bd6c2cb9746780771da2a003).
   - SEGS: PI_scene's pa_segs is scene_segs (SceneImg.v:57) = Asan.M.loaded_segments (lib/A/Prog/SceneCode.v:18),
     which is tfibsegs (lib/A/AB1v.v:12); the two are equal by conversion (`change`).
   - AR_laws tfibsegs B: AR_laws_ok (lib/Reusable/YG0q.v:803), for every B, as Section h says (:220-222).
   - TfibSyms B (lib/A/AF0m.v:906): Section h carries no row that gives it, so it is a NAMED hypothesis of each
     lemma, HB. The glue's B is AD2l.TfibB and its HB is AD2l.TfibB_syms (lib/A/G_Close.v:201-202), so the glue
     closes each row as `exact (SceneIntrin.scene_AMEMSET B HB)`, and likewise for the other two. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YK11 YM05 YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneSyms SceneList ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require AB1v AF0m AE2q AE2r AE2s.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).

(* ---- the three runtime entries the listing calls, at the walks' literal pcs ---- *)
Lemma scene_sigma_memset : SIGMA SS___asan_memset = 0x53e60.
Proof. vm_compute; reflexivity. Qed.
Lemma scene_sigma_memcpy : SIGMA SS___asan_memcpy = 0x539c4.
Proof. vm_compute; reflexivity. Qed.
Lemma scene_sigma_bcmp : SIGMA SS___interceptor_trampoline_bcmp = 0x4430c.
Proof. vm_compute; reflexivity. Qed.

Section h.
Variable B : asyms.
Hypothesis HB : AF0m.TfibSyms B.

Lemma scene_AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Proof.
rewrite scene_sigma_memset. change SEGS with AB1v.tfibsegs.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE2r.asan_memset_realizes B (YG0q.AR_laws_ok AB1v.tfibsegs B) HB
  ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma scene_AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Proof.
rewrite scene_sigma_memcpy. change SEGS with AB1v.tfibsegs.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (AE2q.asan_memcpy_realizes B (YG0q.AR_laws_ok AB1v.tfibsegs B) HB
  ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

Lemma scene_ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Proof.
rewrite scene_sigma_bcmp. change SEGS with AB1v.tfibsegs.
exact (AE2s.bcmp_icpt_contract B (YG0q.AR_laws_ok AB1v.tfibsegs B) HB).
Qed.
End h.
End d.

About scene_sigma_memset.
About scene_sigma_memcpy.
About scene_sigma_bcmp.
About scene_AMEMSET.
About scene_AMEMCPY.
About scene_ABCMP.
Print Assumptions scene_sigma_memset.
Print Assumptions scene_sigma_memcpy.
Print Assumptions scene_sigma_bcmp.
Print Assumptions scene_AMEMSET.
Print Assumptions scene_AMEMCPY.
Print Assumptions scene_ABCMP.
