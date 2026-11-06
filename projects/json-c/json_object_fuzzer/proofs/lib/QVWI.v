(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n QDlz QOTP QxTK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qt8n QDlz QOTP.
Import QxTK.
Import ListNotations. Import AX2. Import APC. Import AP. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LIMIT : Z := target_alloc_limit.

Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition HSnone (h : nat) : option acs := None.
Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 5000.

Fixpoint plan_head (d : nat) (p : plan) : plan :=
match d with
| O => PContra
| S d' =>
match p with
| PRun stops k => PRun stops (plan_head d' k)
| PX x args k => PX x args (plan_head d' k)
| PSys y k => PSys y (plan_head d' k)
| PFresh r l b k => PFresh r l b (plan_head d' k)
| PMmap a b => PMmap (plan_head d' a) (plan_head d' b)
| PMmapIn a b c => PMmapIn (plan_head d' a) (plan_head d' b) (plan_head d' c)
| PMprotect a b => PMprotect (plan_head d' a) (plan_head d' b)
| PBrk2 a b => PBrk2 (plan_head d' a) (plan_head d' b)
| PSplit e m a b => PSplit e m (plan_head d' a) (plan_head d' b)
| PFact K k => PFact K (plan_head d' k)
| PHavoc rs k => PHavoc rs (plan_head d' k)
| PBump m k => PBump m (plan_head d' k)
| PDropRange b n k => PDropRange b n (plan_head d' k)
| PExt i a k => PExt i a (plan_head d' k)
| PJoin b o n k => PJoin b o n (plan_head d' k)
| PGcKeep ws k => PGcKeep ws (plan_head d' k)
| PCase2 e m a b => PCase2 e m (plan_head d' a) (plan_head d' b)
| PDiamond j rs k => PDiamond j rs (plan_head d' k)
| PIntro lo hi k => PIntro lo hi (plan_head d' k)
| PGhost b n k => PGhost b n (plan_head d' k)
| PUnvis b n k => PUnvis b n (plan_head d' k)
| PFog i z k => PFog i z (plan_head d' k)
| PFogNew i z k => PFogNew i z (plan_head d' k)
| PHavocBrk lo hi k => PHavocBrk lo hi (plan_head d' k)
| PShDisj a b c e k => PShDisj a b c e (plan_head d' k)
| PCaseDisj a b k1 k2 => PCaseDisj a b (plan_head d' k1) (plan_head d' k2)
| other => other
end
end.
Definition regs8 (cs : acs) : list (nat * expr) := map (fun i => (i, reg cs i)) [1; 2; 8; 9; 10; 11; 12; 13; 14; 15]%nat.

Definition summarize (r : cres) : Z * Z * nat * nat * plan * list (nat * expr) * shape :=
match r with
| COk s => (100, 0, 0%nat, 0%nat, PContra, [], s)
| CErr c p cs => (c, pc cs, length (kn cs), nxt cs, plan_head 3 p, regs8 cs, SNil)
end.
Definition summarize2 (r : cres2) := (summarize (fst r), map (fun l => (fst l, pc (snd l), nxt (snd l), length (kn (snd l)))) (snd r)).

Definition kn_hist (k : list kentry) : list nat :=
let c (f : kentry -> bool) := length (List.filter f k) in
[c (fun K => match K with KWord _ _ _ => true | _ => false end);
c (fun K => match K with KZero _ _ => true | _ => false end);
c (fun K => match K with KBlob _ _ _ => true | _ => false end);
c (fun K => match K with KImg _ _ => true | _ => false end);
c (fun K => match K with KAlign _ _ => true | _ => false end);
c (fun K => match K with KRange _ _ _ => true | _ => false end);
c (fun K => match K with KWr _ _ => true | _ => false end);
c (fun K => match K with KDisj _ _ _ _ => true | _ => false end);
c (fun K => match K with KFill _ _ _ => true | _ => false end);
c (fun K => match K with KUnk _ _ => true | _ => false end)].

Fixpoint bump_bucket (b : Z) (l : list (Z * nat)) : list (Z * nat) :=
match l with
| [] => [(b, 1%nat)]
| (b', n) :: r => if Z.eqb b b' then (b', S n) :: r else (b', n) :: bump_bucket b r
end.
Definition kn_word_buckets (k : list kentry) : list (Z * nat) :=
fold_left (fun acc K => match K with
| KWord (SA (ELit 0) off) _ _ => bump_bucket (off / 65536 * 65536) acc
| KWord (SA _ off) _ _ => bump_bucket (-1) acc
| _ => acc
end) k [].
Definition errstate (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
Definition summarize3 (r : cres2) :=
(summarize2 r, match errstate (fst r) with Some cs => (kn_hist (kn cs), kn_word_buckets (kn cs)) | None => ([], []) end).
End Mq0.

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
Import ListNotations. Import AX2. Import APC. Import AP. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.

Definition node_joinv (cs : acs) (args : list expr) : option acs :=
match args with
| [b; ELit n] =>
let '(bb, bo) := split_lit b in
if (fresh_ok nx0 cs && Z.ltb 0 n && Z.leb n 8 && know_bytes_cov segs true (kn cs) bb bo (Z.to_nat n))%bool then
let ss := a_ss cs in
let v := s_next ss in
Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss)
(KWord (SA bb bo) (Z.to_nat n) (EVar v) :: kn_cutout (s_know ss) bb bo (ELit n)) (S v)))
else None
| _ => None
end.

Definition node_smear47 (cs : acs) (args : list expr) : option acs :=
match args with
| [] =>
if Z.eqb (pc cs) 0x6a0a4 then
match erange (kn cs) (reg cs 10) with
| Some (lo, hi) =>
if (Z.leb (2^46) lo && Z.ltb hi (2^47))%bool then
Some (set_pc (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg cs
10 (ELit (2^47 - 1))) 11 (ELit 0x5555555555555555)) 12 (ELit 0x3333333333333333))
13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff)) 0x6a114)
else None
| None => None
end
else None
| _ => None
end.

Definition XNtok (id : nat) (args : list expr) (cs : acs) : option acs :=
match id with
| 1%nat => node_joinv cs args
| 2%nat => node_smear47 cs args
| _ => None
end.
End WithSegs.
