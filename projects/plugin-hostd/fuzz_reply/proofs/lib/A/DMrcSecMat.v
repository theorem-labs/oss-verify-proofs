(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecMat.v (commit 237eb205ab7b, H4 srrm M walk (image-specific files); file sha256 f5aea1b9cc6b) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4, row srrm-walk of the SRr_stepM engine rows; integrator a Theorem Labs lane):
   the MATERIALIZED-PAGE facts of the secondary recycle walk, form F2 (a Theorem Labs lane 06:07Z), and the posts that carry them.
   rule 24: no function proved here (kind: statement heads; the walks are DMrcSecWalkM*.v, the prefix DMrcSecF7M.v).

   WHAT.  For the walk from cgif's QuarantineCallback::Recycle entry to its return, with mat0 the materialized pages at
   the entry and mat the materialized pages at a later point:
   - [mat_rec] (F2a): every page in mat was in mat0, or is the page of a READ-WINDOW address [RDW], or is a page of
     the dead map's shadow window [WINSv] outside the madvised interior [PBv, PEv);
   - [mat_mid]: no page of the interior [PBv, PEv) is materialized (after the madvise);
   - [mat_gone] (F2b): no page of the interior and no page of the map [map, map + len) is materialized (after the
     munmap).
   [RDW] is a UNION OF ZONES, each a static or secondary extent of the state, so a consumer relates it to its base
   (a Theorem Labs lane's E2): the stack, the image window, the thread object, the cache context, the pointer array, the dead
   map, the last map.  A walk proves, at each M run, that the run's read window (YP09R.in_rrange of its first
   symbolic memory) lies in RDW; if a run reads outside RDW, that is a STOP for the integrator, not a widening.
   [at_MUN_M] / [at_RET_M] are DMrcSecGv.at_MUN / at_RET with these facts added; [memset_nwM_t] is the statement of
   the memset leaf YFfm.memset_stretch_nw with the materialized pages of its continuation bounded by the stretch
   [d, d + len) (proved in YFfmM.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFl3 AFeq AFew AFeu AFfm AFk7.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcSecGv.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The madvised interior of the dead map's shadow (DMrcSecWalk.v:364: PB = round_up (SHAv map), PE = round_down (SHEv
   map len)) and the shadow window itself (DMrcSecGv.WINS). *)
Definition PBv (map : Z) : Z := DMrcSecGv.SHAv map + 4095 - (DMrcSecGv.SHAv map + 4095) mod 4096.
Definition PEv (map len : Z) : Z := DMrcSecGv.SHEv map len - DMrcSecGv.SHEv map len mod 4096.
Definition WINSv (map len : Z) (a : Z) : Prop := DMrcSecGv.SHAv map <= a < DMrcSecGv.SHEv map len.

(* The walk's read zones. *)
Definition RDW (ly : alayout) (map len lst : Z) (a : Z) : Prop :=
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END) \/
(ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256) \/
(ly_Q ly <= a < ly_Q ly + kPtrArrayResv) \/ (map <= a < map + len) \/ (lst <= a < lst + 8192).

(* F2a. *)
Definition mat_rec (ly : alayout) (map len lst : Z) (mat0 mat : list word) : Prop :=
forall p, In p mat ->
In p mat0 \/ (exists a, RDW ly map len lst a /\ p = page_base_of a) \/
(exists a, WINSv map len a /\ p = page_base_of a /\ page_outside_range (PBv map) (PEv map len) p = true).

(* After the madvise. *)
Definition mat_mid (map len : Z) (mat : list word) : Prop :=
forall p, In p mat -> page_outside_range (PBv map) (PEv map len) p = true.

(* F2b, after the munmap. *)
Definition mat_gone (map len : Z) (mat : list word) : Prop :=
forall p, In p mat -> page_outside_range (PBv map) (PEv map len) p = true /\ page_outside_range map (map + len) p = true.

(* The generic per-piece form (the prefix pieces YFf5M / YFfbM / DMrcSecGxWalkM): every page in mat was in mat0 or is
   the page of an address in the zone Zn.  The composition shows each piece's Zn lies in RDW. *)
Definition mat_win (Zn : Z -> Prop) (mat0 mat : list word) : Prop :=
forall p, In p mat -> In p mat0 \/ exists a, Zn a /\ p = page_base_of a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The memset leaf with its materialized pages bounded (statement; proof YFfmM.memset_stretch_nwM). *)
Definition memset_nwM_t (W : world tfibsegs) : Prop :=
forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFIB_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
(forall p, In p mat' -> In p (m_vm_materialized md) \/ exists a, d <= a < d + len /\ p = page_base_of a) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The posts of the four arms (DMrcSecGv.at_MUN / at_RET plus the page facts), with DMrcSecGv's Section variables. *)
Section d.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (map len idx n qi lst vra vs0 vs1 vs2 : Z).
Variable own : bool.
Variable mat0 : list word.

Definition at_RET_M (md' : Model) (W' : world tfibsegs) (c' : config) : Prop :=
DMrcSecGv.at_RET W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own md' W' c' /\
mat_rec ly map len lst mat0 (m_vm_materialized (cfg_model c')) /\ mat_gone map len (m_vm_materialized (cfg_model c')).

Definition at_MUN_M (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs1 mem1 mat1,
c' = mkCfg (pend_at regs1 (w64 0x65a14) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat1 md0) /\
getr regs1 17 = w64 215 /\ getr regs1 10 = w64 map /\ getr regs1 11 = w64 len /\
mat_rec ly map len lst mat0 mat1 /\ mat_mid map len mat1 /\
let md1 := with_vm_backing (m_vm_lazy md0) mat1 md0 in
SRr tfibsegs W (mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x65a18) (unfill (w64 map) (w64 len) mem1) (seg_rom tfibsegs))
(munmap_model (w64 map) (w64 len) md1))
(at_RET_M (munmap_model (w64 map) (w64 len) md1)).

(* The M post implies the plain one (so every existing consumer of at_MUN keeps working). *)
Lemma at_RET_M_plain : forall md' W' c', at_RET_M md' W' c' ->
DMrcSecGv.at_RET W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own md' W' c'.
Proof. intros md' W' c' [H _]. exact H. Qed.
End d.
End c.
