(* omx-clap-core/fuzz_preset, Spec: the COMPILED CHECK that every home of in_roP / arodata_okP is the leaf's term.
   (h-hpreset-7's control, 2026-10-29: "keep one compiled check that the re-exported names are the leaf's terms ...
   it is the only thing that proves the re-export is not a second definition in disguise".)
   constr_eq is SYNTACTIC (no unfolding): it succeeds only if the two sides are the same constant. A file that defined
   its own convertible copy again would pass a `reflexivity` check and FAIL this one. The one re-exporter is
   lib/A/PRH_Base.v; the source is lib/Spec/PresetRodata.v. The Locate lines print where each unqualified name
   resolves. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.

Locate in_roP.
Locate arodata_okP.

Lemma presetrodata_one_home : True.
Proof.
  constr_eq @PRH_Base.in_roP @PresetRodata.in_roP.
  constr_eq @PRH_Base.arodata_okP @PresetRodata.arodata_okP.
  constr_eq @in_roP @PresetRodata.in_roP.
  constr_eq @arodata_okP @PresetRodata.arodata_okP.
  exact I.
Qed.
