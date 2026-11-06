(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2 AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxMchr AsanPNodes AsanBNodes AsanTailCh AsanBodyCh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition genLQ (off : nat) (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  match genLAR L As with
  | Some (P, MP, als) =>
      let sigs := List.map (fun x => (s_facts (fst (fst x)), matchLA (fst (fst x)) (snd (fst x)) (snd x) P MP als)) (List.combine L As) in
      let pri (i : nat) : lin := nth (off + i) als (lconst 0) in
      let hull (l : lin) : list fact :=
        match List.map (fun o => irange (fst o) (lsubst (snd o) l)) sigs with
        | [] => []
        | r0 :: rr => let lo := fold_left Z.min (List.map fst rr) (fst r0) in let hi := fold_left Z.max (List.map snd rr) (snd r0) in
                      if (Z.leb 0 lo && Z.ltb hi 18446744073709551615)%bool then [FRange l lo hi] else []
        end in
      let cands := FRange (lsub (lscale 1048576 (pri 66%nat)) (pri 67%nat)) 0 (1048576 * 1021) :: hull (pri 66%nat) ++ hull (pri 67%nat) ++ hull (pri 51%nat) ++ hull (pri 68%nat) in
      let add := List.filter (fun f => (negb (fact_implied (s_facts P) f) && forallb (fun o => fact_implied (fst o) (fsubst (snd o) f)) sigs)%bool) cands in
      Some (SST (s_pc P) (s_regs P) (s_rgs P) (add ++ s_facts P) (s_next P) (s_resv P), MP, als)
  | None => None
  end.

Section BodyCh2.
Context {N : Type}.
Notation MC := (@mchain N).
Variable A1n : anode -> MC -> MC.
Variable A2n : anode2 -> MC -> MC.
Variable A3n : anode3 -> MC -> MC.
Variable BNn : bnode -> MC -> MC.
Variable VIA : positive.
Variable VCT : positive.
Variable OFF : nat.

Definition KFREEO_PJ (k : MC) : MC :=
  KLAZY BNn VIA
    (MJoinG (genLQ OFF)
       (SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (SEGFR 0xd4904 (fun k => BNn (BDrop 2) (BNn (BDrop 3) (BNn (BMergeS 2) (BNn (BSplitW 2 (lconst 1)) (A1n NMsetC k)))))
          (SEGFR 0x43e20 (KENQ A2n A3n BNn VCT) (SEGFR 0x8fe84 (fun x => x) MEnd))))) 0x8fe84
       (A2n (NGiveX [0; 1; 2; 3]%nat) (A2n (NExtDrop 0) k))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TAILF_EJ (jb ib : nat) (k : MC) : MC := A3n NCacheAdd (KFREEN A1n BNn VIA (KTAILF_J A1n A2n A3n BNn VCT jb ib k)).
Definition TAILF_PJ (jb ib : nat) (k : MC) : MC := A3n NCacheAdd (KFREEO_PJ (KTAILF_J A1n A2n A3n BNn VCT jb ib k)).
(* [comment removed for export] *)
Definition KFREEO_LJ (jl : nat) (qu mp : positive) (k : MC) : MC :=
  KLAZY BNn VIA
    (let os := [lconst 4096; lconst 6136; lconst 6144; LIN 6144 [(qu, 8)]; LIN 6152 [(qu, 8)]; LIN 0 [(mp, 4096)]] in
     let rest := MJoinG (genLQ OFF)
                   (SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (SEGFR 0xd4904 (fun k => BNn (BDrop 2) (BNn (BDrop 3) (BNn (BMergeS 2) (BNn (BSplitW 2 (lconst 1)) (A1n NMsetC k)))))
                      (SEGFR 0x43e20 (KENQ A2n A3n BNn VCT) (SEGFR 0x8fe84 (fun x => x) MEnd))))) 0x8fe84 k in
     MSplitG jl (0x7fff7000 - 1) (BNn (BPlaceE jl os) rest) (BNn (BPlaceE jl os) rest)).
(* [comment removed for export] *)
Definition TAILF_LJ (jl : nat) (qu mp : positive) (jb ib : nat) (k : MC) : MC := A3n NCacheAdd (KFREEO_LJ jl qu mp (KTAILF_J A1n A2n A3n BNn VCT jb ib k)).
End BodyCh2.
(* [comment removed for export] *)
