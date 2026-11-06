(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2X SymExec2SoundX SymRunX SymPackX RefMemcpyLib AgentLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Cells CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXL_snpDisc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Abbreviation RSEGS := Asan.M.loaded_segments.

Definition SNP_ENTRY : Z := 0x60014.
Definition SNP_RET : Z := 0x63bd0.     (* [comment removed for export] *)
Definition SNP_FR : Z := 6144.
Definition SNP_HEAD : Z := 0xf2060000f1f1f1f1.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition snp_sr : list expr :=
  Eval cbv in (map (fun i => match i with
     | 0 => ELit 0 | 2 => EVar 0 | 10 => EAlu ALU_ADD (EVar 1) (ELit 32) | 11 => ELit 22 | 12 => ELit 0x251a0 | 13 => ELit 18446744073709551615
     | _ => EVar (3 + i) end)%nat (seq 0 32)).

Fixpoint kn_of_cells (a : Z) (cs : list cell) : list kentry :=
  match cs with
  | [] => []
  | C8 w :: r => KWord (SA (ELit 0) a) 8 (ELit (bv_unsigned w)) :: kn_of_cells (a + 8) r
  | C4 w :: r => KWord (SA (ELit 0) a) 4 (ELit (bv_unsigned w mod 2^32)) :: kn_of_cells (a + 4) r
  | C2 w :: r => KWord (SA (ELit 0) a) 2 (ELit (bv_unsigned w mod 2^16)) :: kn_of_cells (a + 2) r
  | C1 b :: r => KWord (SA (ELit 0) a) 1 (ELit (bv_unsigned b)) :: kn_of_cells (a + 1) r
  | CB n _ :: r => kn_of_cells (a + Z.of_nat n) r
  end.
Definition CELLS : list kentry := Eval vm_compute in (flat_map (fun ac => kn_of_cells (fst ac) (snd ac)) aconst_cells).

Definition snp_kn0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff7f801800 0x7fffffffffc0;
   KAlign (EVar 1) 64; KRange (EVar 1) 0x67f000 0x7fffff800000;
   KWr (SA (EVar 0) (-6144)) 6144;
   KWr (SA (EVar 1) 32) 22;
   KDisj (SA (EVar 0) (-6144)) 6144 (SA (EVar 1) 0) 64;
   KImg 0x10000 0x115000;
   KWord (SA (ELit 0) 0x67d4f0) 8 (EVar 2)] ++ CELLS.

(* [comment removed for export] *)
Definition E0 (r : Z) : env :=
  Env (fun n => match n with 0%nat => Z_to_bv 64 (0x7fffbffffc80 + r) | 1%nat => Z_to_bv 64 0x102080dc4100 | 2%nat => Z_to_bv 64 0x1234567
                           | 4%nat => Z_to_bv 64 0xa60c4 | _ => Z_to_bv 64 0 end) (fun _ => []).

Fixpoint has_v1 (e : expr) : bool :=
  match e with
  | EVar 1 => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => has_v1 a || has_v1 b
  | EExt _ _ _ a => has_v1 a
  | _ => false
  end.
(* [comment removed for export] *)
Definition read_kn (s : sidecond) : list kentry :=
  match s with
  | SCReadBase a n sx _ => [KWord a n (ELit (if (has_v1 (a_base a) && Nat.eqb n 8)%bool then SNP_HEAD else 0))]
  | _ => []
  end.
Fixpoint kdedup (l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => if existsb (fun K' => match K, K' with KWord a n _, KWord a' n' _ => saddr_eqb a a' && Nat.eqb n n' | _, _ => false end) r then kdedup r else K :: kdedup r
  end.
Definition disc1 (r : Z) (kn : list kentry) := discover RSEGS (E0 r) [SNP_RET] 600 8000 true (SS SNP_ENTRY snp_sr [] kn 35) [] [].
Definition reads_of (d : list (Z * bool) * sym_state * list sidecond * nat) : list kentry := flat_map read_kn (snd (fst d)).
(* [comment removed for export] *)
Definition snp_reads (r : Z) : list kentry :=
  let k1 := kdedup (reads_of (disc1 r snp_kn0)) in
  let k2 := kdedup (k1 ++ reads_of (disc1 r (snp_kn0 ++ k1))) in
  kdedup (k2 ++ reads_of (disc1 r (snp_kn0 ++ k2))).
Definition snp_kn (reads : list kentry) : list kentry := snp_kn0 ++ reads.
Definition snp_script (r : Z) (reads : list kentry) : list bool := map snd (fst (fst (fst (disc1 r (snp_kn reads))))).
Definition snp_run (scr : list bool) (reads : list kentry) :=
  sym_exec RSEGS 8000 true [SNP_RET] (SCR scr [] []) (SS SNP_ENTRY snp_sr [] (snp_kn reads) 35) [].
Definition snp_regions : list sregion := [(SA (EVar 0) (-6144), 6144); (SA (EVar 1) 32, 22)].
Definition sc_kind (s : sidecond) : nat := match s with SCBr _ _ _ _ => 0 | SCFlat _ _ => 1 | SCDisj _ _ _ _ => 2 | SCInside _ _ _ _ => 3 | SCStoreOk _ _ => 4 | SCReadBase _ _ _ _ => 5 | SCEq _ _ => 6 end%nat.
