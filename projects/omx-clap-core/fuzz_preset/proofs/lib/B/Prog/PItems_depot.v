(* Theorem Labs, 2026-10: THE DEPOT HOLDS NO REPEAT in every ARcf state (lane PItemsB, owner). The cursor free's
   admission (YCbqGwild.wild_room_admits) needs `List.NoDup (st_depot S)` at the call state; AR_laws_x has no depot law
   yet, so parse_items' walk carries it as ONE named Section hypothesis ARX_DEPOT (lib/B/Prog/PItems_body_free.v):
     ARX_DEPOT : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (st_depot S).
   This file is its discharge at the relations of record: at ARcf it is ARmcf's amc_wf (Wf_cf (as_universe B) S,
   YG0ncf.v:122), whose wfc_depot (YG01cf.v:147) is YG01.depot_fits, whose first conjunct is the NoDup; at
   ARcfx = ARcf /\ xs_placed_cf the same through the conjunction. When the kit's AR_laws_x gains its field 25
   ARx_depot_nodup_law, ARX_DEPOT becomes that field's projection and these lemmas are its proof at ARcf.
   Pure projection: no image fact, no numeral that names an address.
   Rule 24: proves no function (kind: instance law). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YGcfNames YG00 YG01 YG01cf YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.

Section dep. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* at ARcf: amc_wf's wfc_depot, depot_fits' first conjunct *)
Lemma ARcf_depot_nodup : forall segs B ly S Hp W mem md,
  YG0ncf.ARcf segs B ly S Hp W mem md -> List.NoDup (st_depot S).
Proof.
intros segs B ly S Hp W mem md H.
exact (proj1 (wfc_depot _ _ _ _ _ (YG0ncf.amc_wf _ _ _ _ _ (proj1 H)))).
Qed.

(* at ARcfx = ARcf /\ xs_placed_cf, the relation of record for the image-B' TfibB closure *)
Lemma ARcfx_depot_nodup : forall segs B ly S Hp W mem md,
  YG0ncf.ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S -> List.NoDup (st_depot S).
Proof. intros segs B ly S Hp W mem md H. exact (ARcf_depot_nodup segs B ly S Hp W mem md (proj1 H)). Qed.

End dep.
