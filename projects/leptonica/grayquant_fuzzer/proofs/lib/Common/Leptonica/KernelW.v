(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs DitherLib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.

Section KW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout} {PINS : LeptPins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition kw_region (C : lctx) (A Ar : AS) (s : Z) (r : Z * Z) : Prop :=
  (c_top C - LSTK <= fst r /\ fst r + snd r <= s)
  \/ (exists (p : word) n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ u p <= fst r /\ fst r + snd r <= u p + n).

Lemma in_regions_dec : forall (regs : list (Z * Z)) (a : word),
  {r | In r regs /\ inreg (fst r) (snd r) a} + {forall r, In r regs -> ~ inreg (fst r) (snd r) a}.
Proof.
  induction regs as [|r tl IH]; intros a; [right; intros r []|].
  destruct (Z_le_gt_dec (fst r) (u a)) as [H1|H1]; [destruct (Z_lt_ge_dec (u a) (fst r + snd r)) as [H2|H2]|].
  - left. exists r. split; [left; reflexivity | unfold inreg; lia].
  - destruct (IH a) as [(r' & I' & R')|N]; [left; exists r'; split; [right; exact I' | exact R'] | right].
    intros r0 [<-|I0]; [unfold inreg; lia | exact (N r0 I0)].
  - destruct (IH a) as [(r' & I' & R')|N]; [left; exists r'; split; [right; exact I' | exact R'] | right].
    intros r0 [<-|I0]; [unfold inreg; lia | exact (N r0 I0)].
Qed.

Lemma rinv_WP : forall C A Ar m md m' (s : Z) (regs : list (Z * Z)), Cok C -> W C A m md -> sub_live Ar A -> s <= c_top C ->
  rinv regs m m' -> (forall r, In r regs -> kw_region C A Ar s r) ->
  W C A m' md /\ POSTM C Ar s m m'.
Proof.
  intros C A Ar m md m' s regs CK HW SUB Hs [GR EQ] KR.
  assert (CH : forall a, m' a <> m a -> scratch C s a \/ (exists p n, live A p = Some n /\ live Ar p = None /\ live (c_A0 C) p = None /\ u p <= u a < u p + n)).
  { intros a NE. destruct (in_regions_dec regs a) as [(r & Ir & Rr)|N]; [|exfalso; exact (NE (EQ a N))].
    unfold inreg in Rr. destruct (KR r Ir) as [[K1 K2]|(p & n & L & L0 & L00 & K1 & K2)].
    - left. unfold scratch. lia.
    - right. exists p, n. split; [exact L|]. split; [exact L0|]. split; [exact L00|]. lia. }
  split.
  - apply (W_local C A m md m' s CK HW Hs); [|exact GR].
    intros a NE. destruct (CH a NE) as [X|(p & n & L & _ & L00 & R)]; [left; exact X | right; exists p, n; split; [exact L | split; [exact L00 | exact R]]].
  - apply (POSTM_local C Ar A m md m' s CK HW SUB).
    intros a NE. destruct (CH a NE) as [X|(p & n & L & L0 & _ & R)]; [left; exact X | right; exists p, n; split; [exact L | split; [exact L0 | exact R]]].
Qed.
End KW.
