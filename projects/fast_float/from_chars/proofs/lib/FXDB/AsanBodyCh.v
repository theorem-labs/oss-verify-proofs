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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxMchr AsanPNodes AsanBNodes AsanTailCh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FB60000 : nat := 60000.
(* [comment removed for export] *)
Definition genLAR (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  match genLA L As with
  | Some (P, MP, als) =>
      let sigs := List.map (fun x => (s_facts (fst (fst x)), matchLA (fst (fst x)) (snd (fst x)) (snd x) P MP als)) (List.combine L As) in
      let lost := List.filter (fun f => (negb (fact_implied (s_facts P) f) && forallb (fun p => fact_implied (fst p) (fsubst (snd p) f)) sigs)%bool)
                              (match L with x :: _ => s_facts (fst x) | [] => [] end) in
      Some (SST (s_pc P) (s_regs P) (s_rgs P) (s_facts P ++ lost) (s_next P) (s_resv P), MP, als)
  | None => None
  end.
Section BodyCh.
Context {N : Type}.
Notation MC := (@mchain N).
Variable A1n : anode -> MC -> MC.
Variable A2n : anode2 -> MC -> MC.
Variable A3n : anode3 -> MC -> MC.
Variable BNn : bnode -> MC -> MC.
Variable HARN : MC -> MC.                  (* [comment removed for export] *)
Variable VIA : positive.
Variable VCT : positive.                   (* [comment removed for export] *)                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_CL : list Z := [0x8fe54; 0x8fe7c; 0x5329c; 0x639d4; 0x82908; 0x81f7c; 0x73c38; 0xd51d0; 0xcbc0c; 0xc6014].
Definition P_CL : plan := PRun FB60000 STOPS_CL [].
(* [comment removed for export] *)
Fixpoint HRUN (k : nat) (kx : MC) : MC :=
  match k with
  | O => kx
  | Datatypes.S k' => HARN (MSegK 20 P_CL (KCons 0x8fe54 0 (HRUN k' kx) (KCons 0x8fe7c 0 kx KNil)))
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KCALLS0 (n : nat) (kx : MC) : MC :=
  MSplitP 2 (HARN
    (MSegK 20 P_CL (KCons 0xcc8cc 29 (MIoctl 1 0x5413 (MSegK 20 PT_RETRY (KCons 0xcbc0c 66 (T_KWL
       (MSegK 20 P_CL (KCons 0x8fe54 0 (HRUN (Nat.pred n) kx) (KCons 0x8fe7c 0 kx KNil)))) KNil))) KNil))).
Definition KCALLS (n : nat) (kx : MC) : MC :=
  MSplitP 2 (MSegK 20 P_CL (KCons 0x8fe54 0 (HARN
    (MSegK 20 P_CL (KCons 0xcc8cc 29 (MIoctl 1 0x5413 (MSegK 20 PT_RETRY (KCons 0xcbc0c 66 (T_KWL
       (MSegK 20 P_CL (KCons 0x8fe54 0 (HRUN (Nat.pred n) kx) (KCons 0x8fe7c 0 kx KNil)))) KNil))) KNil))) KNil)).

(* [comment removed for export] *)
Definition STOPS_FR : list Z := [0x82908; 0x81f7c; 0xd4904; 0x43e20; 0x8fe84; 0x401d8; 0x73c38; 0xcbc0c; 0xc6014].
Fixpoint planFR (k : nat) : plan :=
  match k with
  | O => PRun FB60000 STOPS_FR []
  | Datatypes.S k' => let p := planFR k' in
      PRun FB60000 STOPS_FR [(0x7344c, PLoopW 200 [0x73458] [(0x73458, p)]); (0x73480, PLoopW 200 [0x73490] [(0x73490, p)])]
  end.
Definition SEGFR (pc : Z) (node : MC -> MC) (k : MC) : MC := MSegK 40 (planFR 3) (KCons pc 0 (node k) KNil).
Definition KMSFR (k : MC) : MC := MSplitR 11 0 (A1n NMset k) (A1n NMsetC k).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KGN (k : MC) : MC := A3n (NPsr 68) (MSplitR 41 0 (A2n NEnq k) (A2n NEnq k)).
Definition KDRAIN (room : bool) (kd : MC) (k : MC) : MC :=
  BNn (if room then BPsrLin 45 1 42 1 15 0 else BPsrLin 45 0 42 1 15 8192) (MSplitR 44 1048576 (A2n NEnq k) kd).
(* [comment removed for export] *)
Definition KENQ (k : MC) : MC :=
  A3n (NPsr 66) (MSplitR 41 0
     (BNn (BPsrMov 42 43) (A3n (NPsr 67) (MSplitR 41 0
        (KDRAIN false (A3n (NPsr 51) (MSplitR 41 0 (BNn (BIrV VCT) (MAlt MVoid (KGN k))) (KGN k))) k)
        (BNn (BIxfP 1048576 43 42) (MAlt MVoid (A2n NEnq k))))))
     (A3n NQjPos (A3n (NPsr 67) (KDRAIN true (KGN k) k)))).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SEGFRI (node : MC -> MC) (k : MC) : MC := MSegK 40 (PRun FB60000 (0x73434 :: STOPS_FR) []) (KCons 0x73434 0 (node k) KNil).
(* [comment removed for export] *)
Definition SEGGX (k : MC) : MC := MSegK 40 (PRun FB60000 (0x6da58 :: STOPS_FR) []) (KCons 0x6da58 0 k KNil).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KLAZY (k : MC) : MC :=
  MJoinG genLAR (MSplit (lvar VIA) 0
           (BNn (BNormWI 0x176108 false) (SEGFRI (BNn BIms) (SEGFRI (BNn BIms) (SEGFRI (BNn BIms) (SEGFRI (BNn BIms)
              (SEGGX (BNn (BNormWI 0x176108 false) (BNn (BNormWI 0x128640 false) (BNn (BNormWI 0x128648 false) (BNn (BNormWI 0xe7880 false) MEnd))))))))))
           (SEGGX (BNn (BNormWI 0x176108 false) (BNn (BNormWI 0xe7880 false) MEnd)))) 0x6da58 k.
(* [comment removed for export] *)
Definition KFREEN (k : MC) : MC := KLAZY (SEGFR 0x82908 (A1n NUnw) (SEGFR 0x8fe84 (fun x => x) k)).
Definition KFREEO_P (k : MC) : MC :=
  KLAZY
    (SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (SEGFR 0xd4904 (fun k => BNn (BDrop 2) (BNn (BDrop 3) (BNn (BMergeS 2) (BNn (BSplitW 2 (lconst 1)) (A1n NMsetC k)))))
      (SEGFR 0x43e20 KENQ (SEGFR 0x8fe84 (fun x => x) (A2n (NGiveX [0; 1; 2; 3]%nat) (A2n (NExtDrop 0) k))))))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KTAILB_J (jb ib : nat) (n : nat) : MC :=
  let os := [lconst 6144; LIN 6136 [(VCT, 65536)]] in
  let rest := SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (SEGFR 0xd4904 KMSFR (SEGFR 0x43e20 KENQ
                (MSegK 40 (jplanF 8) (KCons 0xcbc0c 66 (T_KWF n (MSegK 40 (jplanF 8) (KCons 0xc6014 94 MExit KNil))) (KCons 0xc6014 94 MExit KNil)))))) in
  BNn (BSplitW32 ib 6128) (MSplitG jb (0x7fff7000 - 1) (BNn (BPlaceE jb os) rest) (BNn (BPlaceE jb os) rest)).
Definition KTAILB (n : nat) : MC := KTAILB_J 0 4 n.
(* [comment removed for export] *)
Definition KFREEO_L (qu mp : positive) (k : MC) : MC :=
  KLAZY
    (* [comment removed for export] *)
    (let os := [lconst 4096; lconst 6136; lconst 6144; LIN 6144 [(qu, 8)]; LIN 6152 [(qu, 8)]; LIN 0 [(mp, 4096)]] in
     let rest := SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (SEGFR 0xd4904 (fun k => BNn (BDrop 2) (BNn (BDrop 3) (BNn (BMergeS 2) (BNn (BSplitW 2 (lconst 1)) (A1n NMsetC k)))))
                   (SEGFR 0x43e20 KENQ (SEGFR 0x8fe84 (fun x => x) k)))) in
     MSplitG 0 (0x7fff7000 - 1) (BNn (BPlaceE 0 os) rest) (BNn (BPlaceE 0 os) rest)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BODY_P (n : nat) : MC := MJoinG genLAR (KCALLS n MEnd) 0x8fe7c (KFREEO_P (KTAILB n)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BODY_L (qu mp : positive) (n : nat) : MC := MJoinG genLAR (KCALLS n MEnd) 0x8fe7c (KFREEO_L qu mp (KTAILB_J 1 13 n)).
Definition BODY_E (n : nat) : MC := MJoinG genLAR (KCALLS0 n MEnd) 0x8fe7c (KFREEN (KTAILB n)).
(* [comment removed for export] *)
Variable HARN1 : MC -> MC.
Definition KCALLS0_1 (n : nat) (kx : MC) : MC :=
  MSplitP 2 (HARN1
    (MSegK 20 P_CL (KCons 0xcc8cc 29 (MIoctl 1 0x5413 (MSegK 20 PT_RETRY (KCons 0xcbc0c 66 (T_KWL
       (MSegK 20 P_CL (KCons 0x8fe54 0 (HRUN (Nat.pred n) kx) (KCons 0x8fe7c 0 kx KNil)))) KNil))) KNil))).
Definition KCALLS_1 (n : nat) (kx : MC) : MC :=
  MSplitP 2 (MSegK 20 P_CL (KCons 0x8fe54 0 (HARN1
    (MSegK 20 P_CL (KCons 0xcc8cc 29 (MIoctl 1 0x5413 (MSegK 20 PT_RETRY (KCons 0xcbc0c 66 (T_KWL
       (MSegK 20 P_CL (KCons 0x8fe54 0 (HRUN (Nat.pred n) kx) (KCons 0x8fe7c 0 kx KNil)))) KNil))) KNil))) KNil)).
Definition BODY_P1 (ib : nat) (n : nat) : MC := MJoinG genLAR (KCALLS_1 n MEnd) 0x8fe7c (KFREEO_P (KTAILB_J 0 ib n)).
Definition BODY_L1 (qu mp : positive) (ib : nat) (n : nat) : MC := MJoinG genLAR (KCALLS_1 n MEnd) 0x8fe7c (KFREEO_L qu mp (KTAILB_J 1 ib n)).
Definition BODY_E1 (ib : nat) (n : nat) : MC := MJoinG genLAR (KCALLS0_1 n MEnd) 0x8fe7c (KFREEN (KTAILB_J 0 ib n)).
(* [comment removed for export] *)
Definition STOPS_FR2 : list Z := 0x8fcb8 :: STOPS_FR.
Fixpoint planFR2 (k : nat) : plan :=
  match k with
  | O => PRun FB60000 STOPS_FR2 []
  | Datatypes.S k' => let p := planFR2 k' in
      PRun FB60000 STOPS_FR2 [(0x7344c, PLoopW 200 [0x73458] [(0x73458, p)]); (0x73480, PLoopW 200 [0x73490] [(0x73490, p)])]
  end.
Definition SEGFR2 (pc : Z) (k : MC) : MC := MSegK 40 (planFR2 3) (KCons pc 0 k KNil).
(* [comment removed for export] *)
Definition KTAILF_J (jb ib : nat) (k : MC) : MC :=
  let os := [lconst 6144; LIN 6136 [(VCT, 65536)]] in
  let rest := SEGFR 0x82908 (A1n NUnw) (SEGFR 0x81f7c (A1n NPut) (SEGFR 0xd4904 KMSFR (SEGFR 0x43e20 KENQ (SEGFR2 0x8fcb8 k)))) in
  BNn (BSplitW32 ib 6128) (MSplitG jb (0x7fff7000 - 1) (BNn (BPlaceE jb os) rest) (BNn (BPlaceE jb os) rest)).
(* [comment removed for export] *)
Definition KEXIT (n : nat) : MC :=
  MSegK 40 (jplanF 8) (KCons 0xcbc0c 66 (T_KWF n (MSegK 40 (jplanF 8) (KCons 0xc6014 94 MExit KNil))) (KCons 0xc6014 94 MExit KNil)).
(* [comment removed for export] *)
Definition TAILF_E (ib : nat) (k : MC) : MC := KFREEN (KTAILF_J 0 ib k).
Definition TAILF_P (ib : nat) (k : MC) : MC := KFREEO_P (KTAILF_J 0 ib k).
Definition TAILF_L (qu mp : positive) (ib : nat) (k : MC) : MC := KFREEO_L qu mp (KTAILF_J 1 ib k).
(* [comment removed for export] *)
Definition CALLW : list Z := [0xe2c38; 0xe2c40; 0xe2c48; 0xe2c58; 0xe2c60; 0xe2c70; 0xe2c80; 0xe2cc0; 0xe2cc8; 0x639f50].
Definition WNORM (lit : bool) (k : MC) : MC := fold_right (fun a k' => BNn (BNormWI a lit) k') k CALLW.
(* [comment removed for export] *)
Definition HEAD_0 (tail : MC -> MC) (n : nat) : MC := MJoinG genLAR (KCALLS0_1 n MEnd) 0x8fe7c (tail (KEXIT n)).
Definition HEAD_1 (tail : MC -> MC) (n : nat) : MC := MJoinG genLAR (KCALLS_1 n MEnd) 0x8fe7c (tail (KEXIT n)).
End BodyCh.
(* [comment removed for export] *)
