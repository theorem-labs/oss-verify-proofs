(* omx-clap-core/fuzz_preset, Spec: the READ-ONLY IMAGE BYTES predicates, in_roP and arodata_okP, and nothing else.

   WHY THIS FILE EXISTS (h-hpreset-7's ruling, 2026-10-29, with the unit owner; both ruled the same way). The two
   bodies were defined in lib/A/PRH_Base.v and copied, body for body, into TWO other files, because PRH_Base's
   Require closure drags the tactic override `Ltac lia ::=` and a file that wants these names override-free had no
   route to them. The route, measured by h-pre-b1 from the build's .Makefile.d:
     lib/A/PRH_Base.v <- lib/Prog/Ledger.v <- lib/Contract.v <- lib/Lib/Exec.v <- lib/Lib/PropExec.v <- lib/LiaTwx2.v
   and LiaTwx2.v is where `Ltac lia ::=` is set. The copies were:
     (1) lib/Reusable/YGcallMxmn.v - body for body, proved convertible with PRH_Base's in both directions by
         `exact H` in a scratch file (c-omx-alloc);
     (2) lib/Reusable/YGcallSnp.v  - `arodata_okP_x`, with a reflexivity check against PRH_Base's in
         lib/Reusable/YGcallSnpRo.v (c-omx-alloc, 2026-10-29 12:33Z).
   Both agreed with PRH_Base's when they were written and NOTHING KEPT THEM AGREEING. A kit name with two homes is
   not allowed, so both copies are deleted in the same commit that adds this file, and PRH_Base re-exports these two
   names as abbreviations (the lib/Spec/PresetLiveBounds.v pattern: one term, so every consumer and every lemma
   about them applies unchanged and nothing is re-proved).

   THIS FILE IS FREE OF LiaTwx2's OVERRIDE, and that is the whole point. It is NOT free of every override, and the
   difference was MEASURED, not assumed (2026-10-29, three compiled probes, each `Print Ltac lia` after its Requires):
   Stdlib alone prints `Zify.zify; (xlia zchecker)`; Requiring lib/Lib/LiaTwx2.v prints the `first [zify_prune; ...]`
   body "Redefined by: LiaTwx2"; Requiring THIS FILE prints the `YM05.rc_inst; tryif YM03.lf_arith_goal ...` body
   "Redefined by: YM05 YM03". That second override is the one every lib/Reusable file carries: YK11 (seg_rom)
   Requires YM03 and YG0f (asyms, as_owned_static, as_errno, reader) Requires YM05, and the bodies below need both.
   So a file that Requires this leaf gets the Reusable layer's lia, never LiaTwx2's. Its Require closure is the five
   lines below: Stdlib ZArith / List, LinuxProcessSemantics BvBase / MemImageType, lib/Reusable YK11, YG0f, YG0n
   (in_zr); none of them reaches lib/Lib/PropExec.v or lib/Lib/LiaTwx2.v. IF A FUTURE EDIT ADDS A REQUIRE, repeat
   the probe before you push: a leaf that silently acquires LiaTwx2 defeats the reason it exists.

   IMAGE-FREE: no address, no image number, no pin. The predicates are stated over the segment list and the relro
   range the caller supplies. (The shape comes from cgif lib/YC20.v:43-48, which preset's core does not carry.) *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG0f YG0n.
Local Open Scope Z_scope.

(* a is a read-only byte of the image: in a segment that is not writable, or in the relro range [rlo, rhi) *)
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
  (exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
  \/ (rlo <= a < rhi).

(* the reader agrees with the image on every read-only byte that is neither an owned static nor errno *)
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
  forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
