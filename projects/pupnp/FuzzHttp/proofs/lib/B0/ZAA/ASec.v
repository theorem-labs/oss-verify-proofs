(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout.
Import ListNotations.
Open Scope Z_scope.

Notation INSTANCE := 724696%Z.
Notation SEC := 724760%Z.
Notation GSTATS := 725384%Z.
Notation SEC_MTX := 725376%Z.
Notation SEC_VARS := 724784%Z.
Notation SEC_BSL := 724864%Z.
Notation GSTATS_A := 725400%Z.
Notation K_PARR_STEP := 131072%Z.
Notation K_MAX_CHUNKS := 1048576%Z.

Record schunk := mkSC { sc_beg : Z; sc_msize : Z; sc_size : Z }.
Record asec := mkSEC { se_chunks : list schunk; se_nres : Z }.

Definition se_n (S : asec) : Z := Z.of_nat (length (se_chunks S)).

Definition rup4k (x : Z) : Z := ((x + 4095) / 4096) * 4096.

Definition sec_msize (size : Z) : Z := rup4k size + 4096.

Section R.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation PARR := (al_parr AL).

Definition b8 (z : Z) : byte := Z_to_bv 8 z.

Definition chunk_ok (c : schunk) : Prop :=
  sc_beg c mod 4096 = 0 /\ 0x609000 <= sc_beg c /\ 0 < sc_size c /\ sc_msize c = sec_msize (sc_size c)
  /\ ((0 <= sc_beg c /\ sc_beg c + sc_msize c < 0x7fff8000) \/ 0x10007fff8000 <= sc_beg c)
  /\ sc_beg c + sc_msize c <= alloc_ceiling
  /\ Forall (fun rg => apart (sc_beg c) (sc_msize c) (fst rg) (snd rg)) (al_regions AL).

Definition apart_chunks (c d : schunk) : Prop :=
  sc_beg c + sc_msize c <= sc_beg d \/ sc_beg d + sc_msize d <= sc_beg c.

Inductive chunks_sep : list schunk -> Prop :=
| csep_nil : chunks_sep []
| csep_cons : forall c l, Forall (apart_chunks c) l -> chunks_sep l -> chunks_sep (c :: l).

Definition sec_wf (S : asec) : Prop :=
  0 <= se_nres S /\ se_nres S mod 16384 = 0 /\ 8 * se_nres S <= 2^23 /\ se_n S <= se_nres S /\ se_n S <= K_MAX_CHUNKS
  /\ Forall chunk_ok (se_chunks S) /\ chunks_sep (se_chunks S).

Definition sec_alloc (S : asec) (a size : Z) : asec :=
  mkSEC (se_chunks S ++ [mkSC a (sec_msize size) size])
        (if se_n S =? se_nres S then se_nres S + 16384 else se_nres S).

Definition remove_at (l : list schunk) (i : nat) : list schunk :=
  match rev l with
  | [] => []
  | last :: rrest => let l' := rev rrest in
      if (i =? length l')%nat then l' else firstn i l' ++ last :: skipn (S i) l'
  end.
Definition sec_dealloc (S : asec) (i : nat) : asec := mkSEC (remove_at (se_chunks S) i) (se_nres S).

#[using="Type"] Example remove_at_ex1 : map sc_beg (remove_at [mkSC 1 0 0; mkSC 2 0 0; mkSC 3 0 0; mkSC 4 0 0] 1) = [1; 4; 3].
Proof. reflexivity. Qed.
#[using="Type"] Example remove_at_ex2 : map sc_beg (remove_at [mkSC 1 0 0; mkSC 2 0 0; mkSC 3 0 0] 2) = [1; 2].
Proof. reflexivity. Qed.

Fixpoint nearest_below (acc : Z) (l : list Z) (p : Z) : Z :=
  match l with
  | [] => acc
  | ch :: l' => nearest_below (if (ch <=? p) && (p - ch <? p - acc) then ch else acc) l' p
  end.
Fixpoint sec_find (l : list schunk) (p : Z) : option schunk :=
  match l with
  | [] => None
  | c :: l' => if (sc_beg c <=? p) && (p <? sc_beg c + sc_msize c) then Some c else sec_find l' p
  end.

Definition sec_block_begin (S : asec) (p : Z) : Z :=
  match sec_find (se_chunks S) p with Some c => sc_beg c + 4096 | None => 0 end.

Definition sec_env (m : mem) : Prop :=
  rw_cells asegs m SEC [C8 (wz 4096); C8 (wz PARR); C8 (wz PARR)]
  /\ rw_cells asegs m 699672 [C8 (wz 707608)] /\ rw_cells asegs m 707608 [C8 (wz 103685)].

Definition sec_vars (S : asec) (m : mem) : Prop :=
  (exists j24 j32 j40 jsb jpad na nf cur mx,
     rw_cells asegs m SEC_VARS [C8 j24; C8 j32; C8 j40; C8 (wz (se_nres S)); C8 (wz (se_n S)); C1 jsb; CB 7 jpad;
                                 C8 na; C8 nf; C8 cur; C8 mx])
  /\ (exists bsl, u64arr asegs m SEC_BSL bsl /\ length bsl = 64%nat)
  /\ rw_cells asegs m SEC_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]]
  /\ (exists g16 g24, rw_cells asegs m GSTATS_A [C8 g16; C8 g24]).

Definition parr_rep (S : asec) (m : mem) : Prop :=
  exists ws, u64arr asegs m PARR ws /\ Z.of_nat (length ws) = se_nres S
             /\ firstn (length (se_chunks S)) ws = map (fun c => wz (sc_beg c)) (se_chunks S).

Definition hdr_cells (c : schunk) (i : Z) : list cell :=
  [C8 (wz (sc_beg c)); C8 (wz (sc_msize c)); C8 (wz (sc_size c)); C8 (wz i)].

Definition hdrs_rep (S : asec) (m : mem) : Prop :=
  forall i c, nth_error (se_chunks S) i = Some c -> rw_cells asegs m (sc_beg c) (hdr_cells c (Z.of_nat i)).

Definition RSEC (S : asec) (m : mem) : Prop :=
  sec_wf S /\ sec_env m /\ sec_vars S m /\ parr_rep S m /\ hdrs_rep S m.

Definition sec_fp (S : asec) : list (Z * Z) :=
  (SEC, SEC + 620) :: (GSTATS_A, GSTATS_A + 16) :: (PARR, PARR + 8 * se_nres S)
  :: map (fun c => (sc_beg c, sc_beg c + 32)) (se_chunks S).

End R.
