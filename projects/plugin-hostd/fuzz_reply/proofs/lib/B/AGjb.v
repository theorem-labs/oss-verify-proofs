(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjb.v (commit 30a1993588f, c5 + memnorm; file sha256 1b72804d331a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/AGjb.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* cgif_file's frame-free facts for the hit arm of Allocate on the k path (0 <= n <= 48), the twin of AGix's
   section o, ported from YFjb.v (the same scripts without the walk's frame): the model facts of the pop (the final
   state's parts) and the allocator memory the walk writes (YFjb.WR_owned without its stack window). The
   size-independent facts (the constant cells' zone, the depot's memory facts and the depot callee) are AGix's
   section c and are not repeated here (this file does not need AGix). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFhy AGhy AGj6 YFi3 AGjc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
(* A one-frame trace: AGj6's range lemmas take the walk's trace (and its length bound) as arguments their
   statements do not use. *)
Lemma dtrlen : (1 <= length [0] <= 30)%nat.
Proof. cbn. lia. Qed.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order. *)
Set Default Proof Using "All".
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
(* The allocator memory the hit-k walk writes, besides Allocate's stack window and the new block (the k twin of
   AGif0cgif.hit_writes, over AGj6's geometry: redzone 16, the header word and the partial shadow byte of req_size n). *)
Definition hit_writes_k (ly : alayout) (n cl v : Z) (odd : bool) (a : Z) : Prop :=
AGj6.WINT ly cl a \/ ((AGj6.Kv ly cl v <= a < AGj6.Kv ly cl v + 16) \/ (AGj6.Uv ly cl v - 16 <= a < AGj6.Uv ly cl v)) \/
AGj6.PBW ly n cl v odd a \/ AGj6.DZONE ly a \/ (AGj6.SUv ly cl v <= a < AGj6.SUv ly cl v + AGj6.N8D n / 8).
(* ---------------------------------------------------------------------------------------------------------------- *)
(* Section o: the pop's model facts and the memory the hit-k walk writes, for the cached chunk at class-region offset *)
(* off = 16 * v of class cl, size n <= 48 (redzone 16), depot trace tr.                                            *)
Section o.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v : Z) (S : astate) (l : list Z) (off : Z) (tr : list Z).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Nrange : 0 <= n <= 48.
Let T : Z := ly_T ly.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation R8v := (@AGj6.R8v n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation SUv := (@AGj6.SUv ly cl v).
Local Abbreviation WINT := (@AGj6.WINT ly cl).
Local Abbreviation PBW := (@AGj6.PBW ly n cl v).
Local Abbreviation DZONE := (@AGj6.DZONE ly).
Local Abbreviation case0_sizes := (@AGj6.case0_sizes n Nrange).
Local Abbreviation RZ_num := (@AGj6.RZ_num n Nrange).
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Lemma Hn0 : 0 <= n. Proof. lia. Qed.
Lemma FPn : from_primary n = true. Proof. pose proof case0_sizes as (_ & _ & _ & _ & F & _). exact F. Qed.
Lemma cls_geom :
0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16 /\
RZ + NPv <= class_size cl /\ RZ + R8v <= class_size cl.
Proof.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
pose proof case0_sizes as (_ & RS & R8 & NP & FP & NS & RQ).
pose proof (primary_geometry n ltac:(zlia) FP) as (G1 & G2 & G3 & G4 & G5). rewrite <- Hcl_class in *.
pose proof (class_ok cl ltac:(zlia)) as (K1 & K2 & K3 & K4 & K5 & K6).
rewrite RS, RQ, NS in G2. repeat split; try zlia.
Qed.
Let Kc : chunk := new_chunk cl off n.
Let SF (z : Z) : astate := st_final S cl l off n tr z.
Lemma upd_chunk_fresh : forall lst, (forall k, In k lst -> sptr_eqb (ck_beg k) (ck_beg Kc) = false) -> upd_chunk lst Kc = lst ++ [Kc].
Proof.
induction lst as [|k t IH]; intros H; [reflexivity|]. cbn [upd_chunk app]. rewrite (H k (or_introl eq_refl)). f_equal. apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.
Lemma SF_same : forall z,
st_regions (SF z) = st_regions S /\ st_cache_inited (SF z) = st_cache_inited S /\ st_secs (SF z) = st_secs S /\
st_sec_arr (SF z) = st_sec_arr S /\ st_sec_reserved (SF z) = st_sec_reserved S /\ st_qthread (SF z) = st_qthread S /\
st_qglobal (SF z) = st_qglobal S /\ st_fs (SF z) = st_fs S /\ st_internal_inited (SF z) = st_internal_inited S /\
st_nev (SF z) = st_nev S /\ st_cache (SF z) = zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S) /\
st_depot (SF z) = (if z =? 0 then st_depot S else st_depot S ++ [tr]).
Proof.
intros z. unfold SF, st_final, depot_after, st_popped. destruct (z =? 0); cbn; repeat split; reflexivity.
Qed.
End o.
End d.
