(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YF06.v, with its module paths changed; 224 of its 270 lines of code are new or changed and 135 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/SecGrantP.v at 58849afb919 (cold/c-asan-realloc-primary), with its module paths changed. *)
(* Omitted for preset: the YFia import, sec_grant_exists_AR_regression_stmt with its Check, and sec_grant_exists_AR_regression (cgif lines 132-137, 348-359). They state cgif's image (tfibsegs, through YF0x, top 0x5fb000), which is false for preset's image (segment 003 ends at 0x600000). *)
(* The LPS placement lemma of a secondary mmap, with the object bound and the live-count limit as parameters.

   On the LPS a fresh mmap may land at ANY free address, or the kernel answers ENOMEM (Sys/Mm/Mmap.v:959-966 of
   checker image cc9ae43a). Under forced_only the run refuses the grant only when no address satisfies the
   guard. The lemmas here give a guard witness (grant_ok_na_pin) on the live ledger, so the run never refuses a
   secondary mmap.

   The proof is YF06.sec_grant_exists (YF06.v:144-183) with its two literals made parameters:
     nob  the object bound, cgif's NOB = 2 ^ 29 (YF06.v:74, :132-133, :171);
     lim  the live-count limit, cgif's SEC_LIVE_N = 16384 (YF06.v:143).
   The side conditions on (nob, lim) are the ones the counting argument uses:
     536870912 <= nob          each relevant lazy zone is at most 257 pieces of size nob (YF06.v:124-125);
     nob mod 4096 = 0          the candidates bottomup_floor + j * (2 * nob) are page aligned;
     0x2aaaaaaab000 + (257 * 25 + lim) * (2 * nob) + nob <= 0x7fff7f800000
                               the window: at most 257 * 25 + lim obstacles, each blocks one candidate, and the
                               lowest ceiling of any RunCeil is 0x7fff7f800000 (YG0f.v:15).
   The largest lim is 80,953 at nob = 2 ^ 29 and 37,264 at nob = 2 ^ 30.

   [sec_grant_exists_cover_P]  the core: the ledger facts (ledger_cover) over a list zs of mapped extents
                               besides the lazy zones, at most lim of them, each of size at most nob.
   [sec_grant_exists_P]        YF06.sec_grant_exists with nob and lim as parameters (zs = sec_extents).
   [sec_grant_exists_live_P]   the live-count form: zs = sec_extents ly S ++ xs, where xs are mapped extents that
                               are not secondaries of a chunk, and the premise is
                               length (st_sec_arr S) + length xs <= lim. st_sec_arr counts every mapped
                               secondary, freed-but-quarantined ones included (an entry leaves it only at
                               sec_dealloc). No premise on st_nev, EV_MAX or sec_arr_small.
   [sec_grant_exists_AR_P]     YFia.sec_grant_exists_AR (YFia.v:48), parametric in the realizes record AR, its
                               state invariant Wf, the ledger LG and its extra extents xs.
   [sec_grant_exists_regression] and [sec_grant_exists_AR_regression] are the released statements
   YF06.sec_grant_exists and YFia.sec_grant_exists_AR, unchanged, proved from the parametric forms. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0v YK00 YK13 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG00 YG0a YG01 YG0n YG0h YG08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YF06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The four ledger facts the counting argument uses (ALedger's al_img, al_reserved, al_top and al_cover, the
   cover taken over the lazy zones and a list zs). *)
Definition ledger_cover (segs : list Segment) (ly : alayout) (md : Model) (zs : list (Z * Z)) : Prop :=
(forall sg, In sg segs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\
Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly)) /\
vm_reserved (m_vmmaps md) = segments_reserved segs /\
YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
(forall e, In e (vm_maps (m_vmmaps md)) ->
Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
(lazy_zones ly ++ zs)).

(* The chunk facts the live-count form uses: the request bound and the page offset of a secondary. *)
Definition ck_sec_ok (mmax : Z) (k : chunk) : Prop :=
0 <= ck_req k < mmax /\ forall r o, ck_beg k = PSec r o -> o = kPage.
(* The state facts the live-count form uses (cgif: wf_chunks_nodup, wf_chunks, ws_arr_chunks). List.NoDup is
   Stdlib's, as in YG01.wf_chunks_nodup (stdpp's NoDup is in scope here). *)
Definition sec_chunks_ok (mmax : Z) (S : astate) : Prop :=
List.NoDup (map ck_beg (st_chunks S)) /\ Forall (ck_sec_ok mmax) (st_chunks S) /\
(forall k r, In k (st_chunks S) -> ck_beg k = PSec r kPage -> In r (st_sec_arr S)).

(* (1), the core. *)
Definition sec_grant_exists_cover_P_stmt : Prop :=
forall (nob lim : Z) (segs : list Segment) (ly : alayout) (md : Model) (zs : list (Z * Z)) (nZ : Z),
536870912 <= nob -> nob mod 4096 = 0 ->
0x2aaaaaaab000 + (257 * 25 + lim) * (2 * nob) + nob <= 0x7fff7f800000 ->
layout_ok ly -> ledger_cover segs ly md zs ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd e)) ->
Z.of_nat (length zs) <= lim ->
Forall (fun e => 0 <= snd e <= nob) zs ->
0 < nZ <= nob ->
exists a, grant_ok_na_pin md a nZ = true.

(* (1), YF06.sec_grant_exists with nob and lim as parameters. *)
Definition sec_grant_exists_P_stmt : Prop :=
forall (nob lim : Z) (segs : list Segment) (ly : alayout) (S : astate) (md : Model) (nZ : Z),
536870912 <= nob -> nob mod 4096 = 0 ->
0x2aaaaaaab000 + (257 * 25 + lim) * (2 * nob) + nob <= 0x7fff7f800000 ->
layout_ok ly -> ALedger segs ly S md ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd e)) ->
Z.of_nat (length (sec_extents ly S)) <= lim ->
Forall (fun e => 0 <= snd e <= nob) (sec_extents ly S) ->
0 < nZ <= nob ->
exists a, grant_ok_na_pin md a nZ = true.

(* (1), the live-count form. *)
Definition sec_grant_exists_live_P_stmt : Prop :=
forall (nob lim mmax : Z) (segs : list Segment) (ly : alayout) (S : astate) (md : Model) (xs : list (Z * Z)) (nZ : Z),
536870912 <= nob -> nob mod 4096 = 0 ->
0x2aaaaaaab000 + (257 * 25 + lim) * (2 * nob) + nob <= 0x7fff7f800000 ->
(forall n, 0 <= n < mmax -> sec_map_size n <= nob) ->
layout_ok ly -> ledger_cover segs ly md (sec_extents ly S ++ xs) ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd e)) ->
sec_chunks_ok mmax S ->
Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length xs) <= lim ->
Forall (fun e => 0 <= snd e <= nob) xs ->
0 < nZ <= nob ->
exists a, grant_ok_na_pin md a nZ = true.

(* (2): the released statement YF06.sec_grant_exists, unchanged. *)
Definition sec_grant_exists_regression_stmt : Prop :=
forall segs ly S md nZ,
layout_ok ly -> ALedger segs ly S md ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd e)) ->
Z.of_nat (length (sec_extents ly S)) <= SEC_LIVE_N ->
Forall (fun e => 0 <= snd e <= NOB) (sec_extents ly S) ->
0 < nZ <= NOB ->
exists a, grant_ok_na_pin md a nZ = true.
Check (sec_grant_exists : sec_grant_exists_regression_stmt).

(* (3): the AR form. A harness passes its realizes record applied to its other arguments as AR (for example
   fun ly S => ARmcf B ly S Hp rd), its state invariant as Wf, its ledger as LG, and as xs the mapped extents
   its ledger covers besides the lazy zones and sec_extents (cgif: none). *)
Definition sec_grant_exists_AR_P_stmt : Prop :=
forall (nob lim mmax : Z) (segs : list Segment) (Wf : astate -> Prop) (AR : alayout -> astate -> Prop)
(LG : alayout -> astate -> Model -> Prop) (xs : alayout -> astate -> list (Z * Z)),
536870912 <= nob -> nob mod 4096 = 0 ->
0x2aaaaaaab000 + (257 * 25 + lim) * (2 * nob) + nob <= 0x7fff7f800000 ->
(forall n, 0 <= n < mmax -> sec_map_size n <= nob) ->
(forall ly S, AR ly S -> layout_ok ly) ->
(forall ly S, AR ly S -> Wf S) ->
(forall S, Wf S -> sec_chunks_ok mmax S) ->
(forall ly S md, LG ly S md -> ledger_cover segs ly md (sec_extents ly S ++ xs ly S)) ->
forall ly S md nZ,
AR ly S -> LG ly S md -> amwf md ->
Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length (xs ly S)) <= lim ->
Forall (fun e => 0 <= snd e <= nob) (xs ly S) ->
0 < nZ <= nob ->
exists a, grant_ok_na_pin md a nZ = true.



Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

(* ---- Obstacles at a parametric object bound: YF06.v:76-118 with NOB a parameter N. ---- *)
Definition obstaclesP (N : Z) (zs : list (Z * Z)) : list (Z * Z) := flat_map (pieces N) (List.filter relevantb zs).
Lemma obstaclesP_app : forall N l1 l2, obstaclesP N (l1 ++ l2) = obstaclesP N l1 ++ obstaclesP N l2.
Proof. intros. unfold obstaclesP. rewrite filter_app, flat_map_app. reflexivity. Qed.
Lemma obstaclesP_len : forall N zs k, 0 < N -> 0 <= k ->
Forall (fun z => relevantb z = true -> 0 <= snd z <= k * N) zs ->
Z.of_nat (length (obstaclesP N zs)) <= k * Z.of_nat (length zs).
Proof.
intros N zs k HN Hk. induction zs as [|z zs IH]; intros F; [cbn; lia|].
inversion F as [|z' zs' Fz Fzs]; subst. cbn [obstaclesP List.filter flat_map length].
specialize (IH Fzs). unfold obstaclesP in IH. rewrite Nat2Z.inj_succ.
destruct (relevantb z) eqn:R.
- cbn [flat_map]. rewrite length_app, Nat2Z.inj_add.
pose proof (pieces_len_le N z k HN (Fz eq_refl)). lia.
- lia.
Qed.
Lemma obstaclesP_size : forall N zs, Forall (fun o => snd o <= N) (obstaclesP N zs).
Proof.
intros N zs. unfold obstaclesP. apply Forall_flat_map. apply Forall_forall. intros z _. apply pieces_size.
Qed.
Lemma obstaclesP_free : forall N zs a n (lo len : Z), 0 < N ->
0 < n -> 0 < len -> bottomup_floor <= a -> a + n <= ASAN_CEIL ->
(forall o, In o (obstaclesP N zs) -> ~ oconf a n o) ->
Exists (fun z => fst z <= lo /\ lo + len <= fst z + snd z) zs ->
lo + len <= a \/ a + n <= lo.
Proof.
intros N zs a n lo len HN Hn Hlen Ha Hc Hfree Hex.
apply Exists_exists in Hex as (z & Hz & Z1 & Z2).
destruct (Z_le_gt_dec (lo + len) a) as [|G1]; [left; lia|].
destruct (Z_le_gt_dec (a + n) lo) as [|G2]; [right; lia|]. exfalso.
assert (HX : exists x, fst z <= x < fst z + snd z /\ a <= x < a + n).
{ destruct (Z_le_gt_dec lo a); [exists a | exists lo]; lia. }
destruct HX as (x & Hxz & Hxa).
assert (R : relevantb z = true).
{ unfold relevantb. apply andb_true_iff. split; apply Z.ltb_lt; lia. }
destruct (pieces_cover N z a n x HN ltac:(lia) Hxz Hxa) as (o & Ho & Hconf).
apply (Hfree o); [| exact Hconf]. unfold obstaclesP. apply in_flat_map. exists z. split; [| exact Ho].
apply filter_In. split; [exact Hz | exact R].
Qed.
(* YF06.lazy_zones_relevant bounds each relevant zone by 257 * 2 ^ 29, hence by 257 * N for N >= 2 ^ 29. *)
Lemma lazy_zones_relevantP : forall N ly, 536870912 <= N -> layout_ok ly ->
Forall (fun z => relevantb z = true -> 0 <= snd z <= 257 * N) (lazy_zones ly).
Proof.
intros N ly HN LY. apply Forall_impl with (2 := lazy_zones_relevant ly LY).
intros z Hz R. specialize (Hz R). unfold NOB in Hz. lia.
Qed.

(* (1), the core *)
Theorem sec_grant_exists_cover_P : sec_grant_exists_cover_P_stmt.
Proof.
intros nob lim segs ly md zs nZ HN HNal HW LY (IMG & RES & TOP & COV) NZ ZSN ZSS HnZ.
pose proof (YM05.ceil_le_top _ TOP) as Htop. pose proof bottomup_floor_val as Hfv.
set (obs := obstaclesP nob (lazy_zones ly ++ zs)).
assert (LEN : Z.of_nat (length obs) <= 257 * 25 + lim).
{ subst obs. rewrite obstaclesP_app, length_app, Nat2Z.inj_add.
pose proof (obstaclesP_len nob (lazy_zones ly) 257 ltac:(lia) ltac:(lia) (lazy_zones_relevantP nob ly HN LY)) as A.
pose proof (lazy_zones_len ly LY) as B.
pose proof (obstaclesP_len nob zs 1 ltac:(lia) ltac:(lia) ltac:(apply Forall_impl with (2 := ZSS); intros e He _; lia)) as C. lia. }
destruct (pick_candidateZ nob nZ obs (seq 0 (Datatypes.S (length obs))) ltac:(lia) (obstaclesP_size _ _) (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
as (j & Hj & Hfree).
apply in_seq in Hj.
set (a := cand nob j).
assert (Ha : bottomup_floor <= a <= bottomup_floor + (257 * 25 + lim) * (2 * nob)).
{ subst a. unfold cand. split; [nia|]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_r; [lia|]. lia. }
assert (Hce : a + nZ <= ASAN_CEIL) by (ceil; unfold ASAN_CEIL in *; rewrite Hfv in Ha; lia).
exists (Z_to_bv 64 a).
unfold grant_ok_na_pin. rewrite !u64_lit by (ceil; unfold ASAN_CEIL in Hce; lia).
assert (E1 : a mod page_size = 0).
{ subst a. unfold cand. rewrite Hfv. unfold page_size.
pose proof (Z.div_mod nob 4096 ltac:(lia)) as E. rewrite HNal, Z.add_0_r in E.
set (q := nob / 4096) in E. rewrite E.
replace (Z.of_nat j * (2 * (4096 * q))) with ((Z.of_nat j * 2 * q) * 4096) by ring.
rewrite Z.add_mod by lia. rewrite Z_mod_mult. reflexivity. }
rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by (unfold ASAN_CEIL in Hce; lia).
rewrite YK13.region_free_app.
rewrite RES.
replace (Z_to_bv 64 a) with (w64 a) by reflexivity. replace (Z_to_bv 64 nZ) with (w64 nZ) by reflexivity.
assert (IMGb : forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd).
{ intros sg Hsg. pose proof (IMG sg Hsg) as [I1 I2]. pose proof (lo_img ly LY) as (J0 & J1 & J2 & J3). rewrite J0 in I1, I2. unfold kImgLo in *. lia. }
rewrite (YG0h.region_free_reserved segs a nZ IMGb) by (ceil; unfold kImgEnd, ASAN_CEIL in *; lia).
rewrite (YG0h.region_free_intro); [reflexivity|].
intros e He. unfold YG0h.uw, w64. rewrite !u64_lit by (ceil; unfold ASAN_CEIL in *; lia).
apply (obstaclesP_free nob (lazy_zones ly ++ zs) a nZ);
[lia | lia | exact (NZ e He) | lia | exact Hce | exact Hfree | exact (COV e He)].
Qed.

Lemma ledger_cover_of_ALedger : forall segs ly S md, ALedger segs ly S md -> ledger_cover segs ly md (sec_extents ly S).
Proof.
intros segs ly S md L. split; [exact (al_img _ _ _ _ L)|]. split; [exact (al_reserved _ _ _ _ L)|].
split; [exact (al_top _ _ _ _ L) | exact (al_cover _ _ _ _ L)].
Qed.

(* (1) *)
Theorem sec_grant_exists_P : sec_grant_exists_P_stmt.
Proof.
intros nob lim segs ly S md nZ HN HNal HW LY L NZ SECN SECS HnZ.
exact (sec_grant_exists_cover_P nob lim segs ly md (sec_extents ly S) nZ HN HNal HW LY (ledger_cover_of_ALedger segs ly S md L)
NZ SECN SECS HnZ).
Qed.

(* (2) *)
Theorem sec_grant_exists_regression : sec_grant_exists_regression_stmt.
Proof.
intros segs ly S md nZ LY L NZ SECN SECS HnZ.
exact (sec_grant_exists_P NOB SEC_LIVE_N segs ly S md nZ ltac:(unfold NOB; lia) ltac:(reflexivity)
ltac:(unfold NOB, SEC_LIVE_N; lia) LY L NZ SECN SECS HnZ).
Qed.

(* ---- The live-count form. ---- *)
(* Every secondary chunk has its own index in st_sec_arr, so the live secondaries are at most the length of
   st_sec_arr (YG09.nsec_le_arr, from the three facts of sec_chunks_ok alone). *)
Lemma sec_extents_count_arr : forall ly S,
List.NoDup (map ck_beg (st_chunks S)) ->
Forall (fun k => forall r o, ck_beg k = PSec r o -> o = kPage) (st_chunks S) ->
(forall k r, In k (st_chunks S) -> ck_beg k = PSec r kPage -> In r (st_sec_arr S)) ->
Z.of_nat (length (sec_extents ly S)) <= Z.of_nat (length (st_sec_arr S)).
Proof.
intros ly S ND PK ARR.
set (idx := fun l : list chunk => flat_map (fun k => match ck_beg k with PSec r _ => [r] | _ => [] end) l).
assert (L : length (sec_extents ly S) = length (idx (st_chunks S))).
{ unfold sec_extents, idx. generalize (st_chunks S) as l. intros l.
induction l as [|k l IH]; cbn [flat_map]; [reflexivity|]. rewrite !length_app, IH. destruct (ck_beg k); reflexivity. }
rewrite L. apply Nat2Z.inj_le. apply NoDup_incl_length.
- assert (G : forall l, Forall (fun k => forall r o, ck_beg k = PSec r o -> o = kPage) l -> List.NoDup (map ck_beg l) ->
List.NoDup (idx l) /\ (forall r, In r (idx l) -> In (PSec r kPage) (map ck_beg l))).
{ induction l as [|k t IH]; intros Hc Hn; [split; [constructor | intros r []]|].
inversion Hc as [|k' t' Hk Ht]; subst. cbn [map] in Hn. inversion Hn as [|b' m' Hni Hnt]; subst.
destruct (IH Ht Hnt) as [I1 I2].
unfold idx in *. cbn [flat_map map]. destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbn [app].
+ split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
+ split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
+ assert (Ho : o = kPage) by (apply (Hk r o); first [exact Eb | reflexivity]). subst o. split.
* constructor; [|exact I1]. intros Hin. apply Hni. first [exact (I2 r Hin) | rewrite Eb; exact (I2 r Hin)].
* intros r' [<-|Hr]; [left; first [reflexivity | exact Eb] | right; exact (I2 r' Hr)].
+ split; [exact I1 | intros r Hr; right; exact (I2 r Hr)]. }
exact (proj1 (G _ PK ND)).
- intros r Hr. unfold idx in Hr. apply in_flat_map in Hr as (k & Hk & Hr).
pose proof (proj1 (Forall_forall _ _) PK k Hk) as Pk.
destruct (ck_beg k) as [|off|r' o|cid pos] eqn:Eb; try (destruct Hr as [<-|[]]); try destruct Hr.
assert (Ho : o = kPage) by (eapply Pk; first [exact Eb | reflexivity]). subst o.
exact (ARR k _ Hk Eb).
Qed.
Lemma sec_map_size_nonneg : forall n, 0 <= n -> 0 <= sec_map_size n.
Proof.
intros n Hn. unfold sec_map_size, needed_size.
pose proof (needed_primary_bounds n Hn) as (N1 & N2 & N3). pose proof (rz_size_bounds n) as [R1 R2].
destruct (from_primary n);
[pose proof (round_up_ge (needed_primary n) kPage ltac:(unfold kPage; lia)) as G
|pose proof (round_up_ge (needed_primary n + rz_size n) kPage ltac:(unfold kPage; lia)) as G];
unfold kPage in *; lia.
Qed.
Lemma sec_extents_sizes_P : forall nob mmax ly S,
(forall n, 0 <= n < mmax -> sec_map_size n <= nob) -> Forall (ck_sec_ok mmax) (st_chunks S) ->
Forall (fun e => 0 <= snd e <= nob) (sec_extents ly S).
Proof.
intros nob mmax ly S HSZ CK. apply Forall_forall. intros e He.
unfold sec_extents in He. apply in_flat_map in He as (k & Hk & He).
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hr _].
destruct (ck_beg k); try destruct He as [<-|[]]; try destruct He.
cbn [snd]. pose proof (sec_map_size_nonneg (ck_req k) ltac:(lia)). pose proof (HSZ (ck_req k) Hr). lia.
Qed.

(* (1), live-count form *)
Theorem sec_grant_exists_live_P : sec_grant_exists_live_P_stmt.
Proof.
intros nob lim mmax segs ly S md xs nZ HN HNal HW HSZ LY LC NZ (ND & CK & ARR) LIVE XS HnZ.
apply (sec_grant_exists_cover_P nob lim segs ly md (sec_extents ly S ++ xs) nZ HN HNal HW LY LC NZ).
- assert (PK : Forall (fun k => forall r o, ck_beg k = PSec r o -> o = kPage) (st_chunks S)).
{ apply Forall_impl with (2 := CK). intros k [_ H]. exact H. }
pose proof (sec_extents_count_arr ly S ND PK ARR). rewrite length_app, Nat2Z.inj_add. lia.
- apply Forall_app. split; [exact (sec_extents_sizes_P nob mmax ly S HSZ CK) | exact XS].
- exact HnZ.
Qed.

(* (3) *)
Theorem sec_grant_exists_AR_P : sec_grant_exists_AR_P_stmt.
Proof.
intros nob lim mmax segs Wf0 AR LG xs HN HNal HW HSZ HLY HWF HSC HLG ly S md nZ M L [_ NZ] LIVE XS HnZ.
exact (sec_grant_exists_live_P nob lim mmax segs ly S md (xs ly S) nZ HN HNal HW HSZ (HLY ly S M) (HLG ly S md L) NZ
(HSC S (HWF ly S M)) LIVE XS HnZ).
Qed.

(* ---- cgif's instance of (3): the facts its ARm / WfP give, and the released AR statement. ---- *)
Lemma ck_sec_ok_of_chunk_ok : forall S k, chunk_ok S k -> ck_sec_ok MALLOC_MAX k.
Proof.
intros S k [Hr Hb]. split; [exact Hr|]. intros r o E. rewrite E in Hb. destruct Hb as (_ & Ho & _). exact Ho.
Qed.
Lemma ck_sec_ok_mono : forall m m' k, m <= m' -> ck_sec_ok m k -> ck_sec_ok m' k.
Proof. intros m m' k Hm [Hr Hp]. split; [lia | exact Hp]. Qed.
Lemma sec_arr_of_wf_sec : forall S, wf_sec S ->
forall k r, In k (st_chunks S) -> ck_beg k = PSec r kPage -> In r (st_sec_arr S).
Proof. intros S WS k r Hk Hb. apply (proj2 (ws_arr_chunks _ WS r)). exists k. split; assumption. Qed.
Lemma sec_chunks_ok_of_WfP : forall U pp cc bb S, WfP U pp cc bb S -> sec_chunks_ok MALLOC_MAX S.
Proof.
intros U pp cc bb S W. split; [exact (wf_chunks_nodup _ _ _ _ _ W)|]. split.
- apply Forall_impl with (2 := wf_chunks _ _ _ _ _ W). intros k. apply ck_sec_ok_of_chunk_ok.
- exact (sec_arr_of_wf_sec S (wf_secondary _ _ _ _ _ W)).
Qed.
Lemma sec_map_size_le_NOB : forall n, 0 <= n < MALLOC_MAX -> sec_map_size n <= NOB.
Proof.
intros n Hn. pose proof (YG08.sec_map_size_bound n ltac:(lia)) as SB. pose proof (req_size_bounds n ltac:(lia)) as RB.
unfold NOB, MALLOC_MAX in *. lia.
Qed.
Lemma ledger_cover_of_ALedger_nil : forall segs ly S md, ALedger segs ly S md -> ledger_cover segs ly md (sec_extents ly S ++ []).
Proof. intros segs ly S md L. rewrite app_nil_r. exact (ledger_cover_of_ALedger segs ly S md L). Qed.

End P.
