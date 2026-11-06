(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjb.v (commit 95e6f1d72b6, file sha256 cf1aee190bf2; written for cgif_file_fuzzer.asan-ubsan 1c29845fe605) onto libreac/fuzz_decode's asan image (pin 5973b76807d8, unstripped twin 4cb0a852e826); module paths changed, names TfibSyms -> GrantSyms; its 3 image addresses moved by code-verified function pairs (2 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; no other numeral changed. *)
(* cgif_file's frame-free facts for the hit arm of Allocate on the k path (0 <= n <= 48), the twin of AGix's
   section o, ported from YFjb.v (the same scripts without the walk's frame): the model facts of the pop (the final
   state's parts) and the allocator memory the walk writes (YFjb.WR_owned without its stack window). The
   size-independent facts (the constant cells' zone, the depot's memory facts and the depot callee) are AGix's
   section c and are not repeated here (this file does not need AGix). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1w AE3d AFhy AGhy AGj6 AFi3 AGjc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
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
Hypothesis TS : GrantSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
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
Let WF := am_wf B ly S rd0 HARm.
Lemma Hn0 : 0 <= n. Proof. lia. Qed.
Lemma FPn : from_primary n = true. Proof. pose proof case0_sizes as (_ & _ & _ & _ & F & _). exact F. Qed.
Local Abbreviation cl_range := (AGjc.cl_range B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation off_facts := (AGjc.off_facts B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Kv_geom := (AGjc.Kv_geom B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation cached_vs_chunk := (AGjc.cached_vs_chunk B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation shadow_present := (AGjc.shadow_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hcl := (AGjc.Hcl' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv := (AGjc.Hv' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hcnt := (AGjc.Hcnt' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
Local Abbreviation Hv2 := (AGjc.Hv2' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FPn Hinited Hcache Hcl_class Hcnt_def Hoff_def).
(* AGj6's range lemmas also take the walk's regs0, trace and depot post, which their statements do not use. *)
Local Abbreviation derived_ranges := (@AGj6.derived_ranges _ ly (bvmap_empty : bvmap 5 word) mem0 n [0] cl cnt v Hcl Hv Hcnt Hv2 LY IMG dtrlen
(fun (_ : Z) (_ : word -> option byte) => True) Nrange).
Local Abbreviation high_facts := (@AGj6.high_facts _ ly (bvmap_empty : bvmap 5 word) mem0 n [0] v Hv LY IMG dtrlen
(fun (_ : Z) (_ : word -> option byte) => True)).
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
(* The redzone part of the chunk's shadow is present (the walk's HSKpres). *)
Lemma SKPRES : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Proof.
intros a Ha. pose proof cls_geom as (K1 & _ & _ & _ & _ & K6).
apply shadow_present. pose proof (Z.div_le_mono (RZ + R8v) (class_size cl) 8 ltac:(lia) K6). lia.
Qed.
Let Kc : chunk := new_chunk cl off n.
Let SF (z : Z) : astate := st_final S cl l off n tr z.
Lemma Kc_fresh : forall k, In k (st_chunks S) -> sptr_eqb (ck_beg k) (ck_beg Kc) = false.
Proof.
intros k Hk. pose proof off_facts as (_ & _ & _ & _ & _ & NI & _).
destruct (sptr_eqb (ck_beg k) (ck_beg Kc)) eqn:E; [|reflexivity]. exfalso.
unfold Kc, new_chunk in E. cbn [ck_beg] in E. destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; cbn in E; try discriminate.
apply Z.eqb_eq in E. apply NI. apply in_or_app. right. apply in_or_app. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. rewrite E in IN.
replace (prim_class (region_off cl + off)) with cl in IN.
2:{ pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof cls_geom as (K1 & _). pose proof cl_range.
unfold prim_class. rewrite region_off_eq by zlia. symmetry. rewrite Z.shiftr_div_pow2 by zlia.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S cl WF ltac:(zlia)). unfold kUserMapSize, EV_MAX in *.
rewrite Z.div_add_l by zlia. rewrite Z.div_small by zlia. zlia. }
rewrite region_off_eq in IN by (pose proof cl_range; zlia). replace (cl * 2 ^ 32 + off - cl * 2 ^ 32) with off in IN by zlia. exact IN.
Qed.
Lemma upd_chunk_fresh : forall lst, (forall k, In k lst -> sptr_eqb (ck_beg k) (ck_beg Kc) = false) -> upd_chunk lst Kc = lst ++ [Kc].
Proof.
induction lst as [|k t IH]; intros H; [reflexivity|]. cbn [upd_chunk app]. rewrite (H k (or_introl eq_refl)). f_equal. apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.
Lemma SF_chunks : forall z, st_chunks (SF z) = st_chunks S ++ [Kc].
Proof.
intros z. unfold SF, st_final. cbn [st_chunks set_chunks]. replace (st_chunks (depot_after z tr (st_popped S cl l))) with (st_chunks S).
- apply upd_chunk_fresh. exact Kc_fresh.
- unfold depot_after, st_popped. destruct (z =? 0); reflexivity.
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
Lemma SF_sec_extents : forall z, sec_extents ly (SF z) = sec_extents ly S.
Proof.
intros z. unfold sec_extents. rewrite SF_chunks. rewrite flat_map_app. cbn. rewrite app_nil_r. reflexivity.
Qed.
Lemma SF_sec_live : forall z, sec_live_bytes (SF z) = sec_live_bytes S.
Proof.
intros z. unfold sec_live_bytes. rewrite SF_chunks. rewrite fold_right_app. cbn. reflexivity.
Qed.
Lemma SF_ledger : forall z md, ALedger tfibsegs ly S md -> ALedger tfibsegs ly (SF z) md.
Proof.
intros z md L. pose proof (SF_same z) as (R1 & _ & _ & _ & Rres & _ & _ & _ & _ & Rnev & _).
destruct L as [L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
constructor; try assumption.
- destruct L3 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
destruct P1 as (Q1 & Q2 & Q3). unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in *. rewrite R1. exact (conj Q1 (conj Q2 Q3)).
- rewrite SF_sec_extents. exact L6.
- rewrite SF_sec_extents. exact L7.
-   rewrite SF_sec_extents, Rres. unfold prim_committed in *. rewrite R1. exact L8.
-   rewrite SF_sec_extents. exact L11.
Qed.
(* (d) The allocator memory the hit-k walk writes (hit_writes_k) is owned (YFjb.WR_owned without the stack). *)
Lemma hit_owned_k : forall odd a, 0 <= a < 2 ^ 64 -> (odd = true -> NPv mod 8 <> 0) ->
hit_writes_k ly n cl v odd a -> aowned B ly S a.
Proof.
intros odd a Ra Hodd Hw. pose proof derived_ranges as DR. pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5). pose proof cls_geom as (K1 & _ & _ & _ & K5 & K6).
pose proof high_facts as (F1 & F2 & _).
assert (OWN_SH : forall g, Kv <= g < Kv + class_size cl -> aowned B ly S (shadow_addr g)).
{ intros g Hg. apply (own_shadow_prim B ly S rd0 g HARm). zlia. }
assert (OWN_K : forall b, Kv <= b < Kv + RZ -> aowned B ly S b).
{ intros b Hb. apply (own_prim_nonuser B ly S rd0 b HARm); [zlia|]. intros k Hk _.
pose proof (cached_vs_chunk k Hk) as D. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). zlia. }
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
unfold hit_writes_k, WINT, PBW in Hw. destruct Hw as [Hw|[[Hw|Hw]|[[Ho Hw]|[Hw|Hw]]]].
- apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto|]. cbn [fst snd].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_cache, t_unwinding in *. unfold T in Hw. zlia.
- apply OWN_K. clear - Hw RZr; zlia.
- apply OWN_K. clear - Hw RZr DR; zlia.
- replace a with (shadow_addr (Kv + RZ + N8D)) by (unfold shadow_addr, PBv, SHBv, SHADOW_OFF in *; zlia). apply OWN_SH.
pose proof (Hodd Ho) as E8. pose proof (Z.div_mod NPv 8 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound NPv 8 ltac:(zlia)) as MB. clear - E8 DM MB K5 RZr NPr. unfold N8D in *. zlia.
- unfold DZONE in Hw. destruct Hw as [Hw|[Hw|Hw]].
+ apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa0610, 0x5c3410 - 0xa0610). split; [cbn; tauto|]. unfold in_zr; cbn. zlia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a HARm); [unfold core_extents; cbn; tauto| cbn [fst snd]; exact Hw].
+ apply (own_core B ly S rd0 (ly_SB ly, kStoreBlockSize) a HARm); [unfold core_extents; cbn; tauto| cbn [fst snd]; exact Hw].
- replace a with (shadow_addr (Kv + 8 * (a - SKv))).
2:{ unfold shadow_addr, SKv, SHBv, SHADOW_OFF in *. rewrite (Z.mul_comm 8 (a - (2147450880 + Kv / 8))), Z.div_add by zlia. zlia. }
apply OWN_SH. unfold SKv, SHBv in *. pose proof (Z.div_mod Kv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound Kv 8 ltac:(zlia)).
pose proof (div8_bounds NPv ltac:(zlia)). unfold N8D in *. rewrite Z.div_mul in Hw by zlia. clear - Hw H H0 H1 K5 RZr RZ8 NPr DR V3. zlia.
Qed.
End o.
End d.
