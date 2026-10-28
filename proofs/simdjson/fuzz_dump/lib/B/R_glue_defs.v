(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Mem Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition ahdr (m : mem) (M n : Z) : Prop :=
  exists (b1 : byte) (ctx : word), bv_unsigned b1 mod 4 = 1
    /\ rw_cells bsegs m M [C1 (Z_to_bv 8 2); C1 b1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx].

Definition qhdr3 (m : mem) (M n : Z) : Prop :=
  exists (b1 : byte) (ctx fid : word), bv_unsigned b1 mod 4 = 1
    /\ rw_cells bsegs m M [C1 (Z_to_bv 8 3); C1 b1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx; C8 fid].

Definition lch (m : mem) (AB M : Z) : Prop :=
  rw_cells bsegs m AB [C8 (Z_to_bv 64 K_kAllocBegMagic); C8 (Z_to_bv 64 M)].
Definition lch_if (m : mem) (AB M n : Z) : Prop := 16 < rz_size n -> lch m AB M.

Definition farun (k : Z) : list byte := repeat (Z_to_bv 8 K_kAsanHeapLeftRedzoneMagic) (Z.to_nat k).
Definition fdrun (k : Z) : list byte := repeat (Z_to_bv 8 K_kAsanHeapFreeMagic) (Z.to_nat k).
Definition zrun (k : Z) : list byte := repeat z8 (Z.to_nat k).
Definition ru8 (n : Z) : Z := 8 * ((n + 7) / 8).

Definition pshadow_alloc (m : mem) (AB S n : Z) : Prop :=
  bytes_at bsegs m (shad AB) (farun (rz_size n / 8) ++ ushadow n)
  /\ bytes_at bsegs m (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)).
Definition pshadow_quar (m : mem) (AB S n : Z) : Prop :=
  bytes_at bsegs m (shad AB) (farun (rz_size n / 8) ++ fdrun (ru8 n / 8) ++ farun ((S - rz_size n - ru8 n) / 8)).
Definition pshadow_idle (m : mem) (AB S : Z) : Prop := bytes_at bsegs m (shad AB) (farun (S / 8)).

Definition i_sec_page : Z := INST + 0x40.
Definition i_sec_chunks : Z := INST + 0x48.
Definition i_sec_nres : Z := INST + 0x70.
Definition i_sec_nchunks : Z := INST + 0x78.
Definition i_sec_sorted : Z := INST + 0x80.
Definition i_sec_mutex : Z := INST + 0x2a8.

Definition shdr (m : mem) (mb msz sz k : Z) : Prop :=
  rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 msz); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 k)].

Definition sec_core (m : mem) (PAB nres nch : Z) : Prop :=
  rw_cells bsegs m i_sec_chunks [C8 (Z_to_bv 64 PAB)] /\ rw_cells bsegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nch)]
  /\ rw_cells bsegs m i_sec_mutex [C1 (Z_to_bv 8 0)].

Definition i_q_max : Z := INST + 0x318.
Definition i_q_min : Z := INST + 0x320.
Definition i_q_cmax : Z := INST + 0x328.
Definition i_q_cmutex : Z := INST + 0x370.
Definition i_q_rmutex : Z := INST + 0x371.
Definition i_q_global : Z := INST + 0x378.
Definition qcacheT (T : Z) : Z := T + 0x50.

Definition qbatch (m : mem) (b nxt : Z) (ents : list (Z * Z)) : Prop :=
  rw_cells bsegs m b [C8 (Z_to_bv 64 nxt); C8 (Z_to_bv 64 (8192 + fold_right (fun e acc => snd e + acc) 0 ents));
                      C8 (Z_to_bv 64 (Z.of_nat (length ents)))]
  /\ (exists ws, u64arr bsegs m (b + 0x18) ws /\ length ws = 1021%nat
                 /\ firstn (length ents) ws = map (fun e => Z_to_bv 64 (fst e)) ents)
  /\ (length ents <= 1021)%nat.

Fixpoint qchain (m : mem) (bs : list (Z * list (Z * Z))) : Prop :=
  match bs with
  | [] => True
  | (b, ents) :: rest => qbatch m b (match rest with [] => 0 | (b', _) :: _ => b' end) ents /\ qchain m rest
  end.
Definition qcache_rep (m : mem) (Q : Z) (bs : list (Z * list (Z * Z))) : Prop :=
  rw_cells bsegs m Q [C8 (Z_to_bv 64 (Z.of_nat (length bs)));
                      C8 (Z_to_bv 64 (match bs with [] => 0 | (b, _) :: _ => b end));
                      C8 (Z_to_bv 64 (last (map fst bs) 0));
                      C8 (Z_to_bv 64 (fold_right (fun b acc => 8192 + fold_right (fun e a => snd e + a) 0 (snd b) + acc) 0 bs))]
  /\ qchain m bs.
