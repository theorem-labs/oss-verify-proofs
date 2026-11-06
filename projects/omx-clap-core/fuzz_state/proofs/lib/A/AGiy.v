(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGiy.v (a working branch 57e82b93d43, file sha256 ef93dce7a612) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* cgif_file's view facts: from ARm of the allocator state at the memory mem0, the machine facts the hit-g walk reads
   (the parts of AGif0cgif.hview, assembled in AGif1) for the cached chunk at the top of the per-thread cache of class cl.
   Ported from YFiy.v: the same scripts, restated without the walk's frame (no regs0, sp, DPOST or trace). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import EVroom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFhy AGhy AGis.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Lemma In_combine_seq_last : forall (l0 : list Z) (x : Z) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
induction l0 as [|y l0 IH]; intros x s; cbn.
- left. f_equal. lia.
- right. replace (s + Datatypes.S (length l0))%nat with (Datatypes.S s + length l0)%nat by lia. apply IH.
Qed.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order (the
   argument lists are fixed by the section headers). *)
Set Default Proof Using "All".
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
(* The cached chunk's offset is 32-aligned (class sizes are multiples of 32). *)
Lemma off_aligned : forall B ly S rd n l off, ARm B ly S rd -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S (chunk_class n)) = l ++ [off] -> off mod 32 = 0.
Proof.
intros B ly S rd n l off HARm Hn0 FP Hcache.
pose proof (primary_geometry n Hn0 FP) as (G & _).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) (chunk_class n) ltac:(lia)) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(rewrite !in_app_iff; cbn; tauto)) as [_ O2].
pose proof (class_ok (chunk_class n) ltac:(lia)) as (K1 & K2 & _).
apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
rewrite Hq, Hr. replace (q * (r * 32)) with ((q * r) * 32) by lia. apply Z_mod_mult.
Qed.
Section h.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v : Z) (S : astate) (l : list Z) (off : Z).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pv := (@AGis.Pv ly cl).
Local Abbreviation PVv := (@AGis.PVv ly cl cnt).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation SHBv := (@AGis.SHBv).
Local Abbreviation SKv := (@AGis.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGis.SSLOTv ly cl).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Let m0 := mrestrict (w_H W) mem0.
Lemma cl_range : 1 <= cl <= 30.
Proof. pose proof (primary_geometry n Hn0 FP) as (G & _). rewrite <- Hcl_class in G. exact G. Qed.
Lemma cls_geom : 0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16.
Proof. pose proof cl_range as CR. pose proof (class_ok cl ltac:(lia)) as (K1 & K2 & K3 & K4 & _). repeat split; lia. Qed.
Lemma cls_wf : cls_ok cl (reg S cl) (cache S cl) (st_cache_inited S) (chunk_offs S cl) (batch_offs S cl).
Proof. exact (wf_classes _ _ _ _ _ WF cl ltac:(pose proof cl_range; zlia)). Qed.
(* The user part's bound 2^32 - 2^29 is kFreeArrayOffset (the region's free array): YG06.mapped_user_bound gives it for
   every EV_MAX <= 14336 (cgif_file 8192, fuzz_state 11776). *)
Lemma off_facts :
0 <= off /\ off + class_size cl <= rg_alloc_user (reg S cl) /\ off mod class_size cl = 0 /\ off mod 16 = 0 /\
rg_alloc_user (reg S cl) <= rg_mapped_user (reg S cl) <= 2 ^ 32 - 2 ^ 29 /\
~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl)) /\
1 <= cnt <= 16 /\ cnt = Z.of_nat (length l) + 1 /\ pc_max (cache S cl) = max_cached cl.
Proof.
pose proof cls_wf as CL. pose proof cls_geom as (K1 & K2 & K3 & K4). pose proof cl_range as CR.
pose proof (wr_elems _ _ _ _ _ _ CL) as EL. pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. pose proof (wr_alloc _ _ _ _ _ _ CL) as AL.
pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. rewrite Hinited in WC. destruct WC as [WM WL].
pose proof (mapped_user_bound (as_universe B) 0 0 0 S cl WF ltac:(zlia)) as MB. unfold kUserMapSize, EV_MAX in MB.
rewrite Hcache in EL, ND, WL.
assert (IN : In off (fa_elems (class_size cl) (rg_free (reg S cl)) ++ (l ++ [off]) ++ chunk_offs S cl ++ batch_offs S cl)).
{ apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) EL off IN) as [O1 O2].
assert (XS : off + class_size cl <= rg_alloc_user (reg S cl)).
{ pose proof O2 as O2'. apply Z.mod_divide in O2' as [qx Hqx]; [|zlia]. pose proof AA as AA'. apply Z.mod_divide in AA' as [qa Hqa]; [|zlia].
assert (Hq : qx < qa) by (apply (Z.mul_lt_mono_pos_r (class_size cl)); zlia).
pose proof (Z.mul_le_mono_nonneg_r (qx + 1) qa (class_size cl) ltac:(zlia) ltac:(zlia)). zlia. }
assert (M16 : off mod 16 = 0).
{ apply Z.mod_divide in O2 as [q Hq]; [|zlia]. apply Z.mod_divide in K2 as [q' Hq']; [|zlia]. apply Z.mod_divide; [zlia|]. exists (q * (q' * 2)). zlia. }
rewrite length_app in Hcnt_def, WL. cbn [length] in Hcnt_def, WL.
assert (NI : ~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl))).
{ apply NoDup_remove_2. replace ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ off :: chunk_offs S cl ++ batch_offs S cl)
with (fa_elems (class_size cl) (rg_free (reg S cl)) ++ (l ++ [off]) ++ chunk_offs S cl ++ batch_offs S cl); [exact ND|].
rewrite <- !app_assoc. reflexivity. }
repeat split; try zlia. exact NI.
Qed.
Lemma off32 : off mod 32 = 0.
Proof. apply (off_aligned B ly S rd0 n l off HARm Hn0 FP). rewrite <- Hcl_class. exact Hcache. Qed.
Lemma Kv_base : Kv = region_base ly cl + off.
Proof. unfold Kv, SB, region_base. pose proof cl_range. rewrite region_off_eq by zlia. zlia. Qed.
Lemma Kv_geom : kHighMemBeg <= Kv /\ Kv + class_size cl <= ASAN_CEIL /\ Kv mod 16 = 0 /\
ly_prim ly <= Kv /\ Kv + class_size cl <= ly_prim ly + kPrimResvSize.
Proof.
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _). pose proof (region_in_prim ly cl LY ltac:(pose proof cl_range; zlia)) as (R1 & R2 & R3 & R4 & R5).
rewrite Kv_base. repeat split; zlia.
Qed.
Lemma Hcl' : 1 <= cl <= 31. Proof. pose proof cl_range. zlia. Qed.
Lemma Hcnt' : 1 <= cnt <= 16. Proof. pose proof off_facts; tauto. Qed.
Lemma Hv' : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof. pose proof off_facts as (O1 & O2 & _ & _ & O5 & _). pose proof cls_geom as (K1 & _). zlia. Qed.
Lemma Hv2' : v mod 2 = 0.
Proof.
pose proof off32 as M. rewrite Hoff_def in M. apply Z.mod_divide in M as [q Hq]; [|lia].
replace v with (q * 2) by lia. apply Z_mod_mult.
Qed.
Ltac clean2 := pose proof Hcl' as Hcl; pose proof Hv' as Hv; pose proof Hcnt' as Hcnt.
Lemma cached_vs_chunk : forall k, In k (st_chunks S) -> ck_base B ly k + ck_extent k <= Kv \/ Kv + class_size cl <= ck_base B ly k.
Proof. clean2.
intros k Hk.
pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & _). pose proof Kv_geom as (V1 & V2 & V3 & V4 & V5). pose proof cls_geom as (K1 & _).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
-
cbv zeta in GG. destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). unfold kFreeArrayOffset in C9.
set (c' := prim_class o) in *. set (x' := o - region_off c') in *.
rewrite C4, C5. rewrite Kv_base. unfold region_base.
destruct (Z.eq_dec c' cl) as [E|NE].
+
rewrite E in *.
assert (NEQ : x' <> off).
{ intros EQ. apply NI. apply in_app_iff. right. apply in_app_iff. left.
pose proof (In_chunk_offs S k o Hk Eb) as IN. fold c' in IN. fold x' in IN. rewrite E, EQ in IN. exact IN. }
apply Z.mod_divide in C7 as [q Hq]; [|zlia]. apply Z.mod_divide in O3 as [q' Hq']; [|zlia].
assert (q <> q') by (intros ->; apply NEQ; zlia).
destruct (Z_lt_le_dec q q').
* left. pose proof (Z.mul_le_mono_nonneg_r (q + 1) q' (class_size cl) ltac:(zlia) ltac:(zlia)). zlia.
* right. pose proof (Z.mul_le_mono_nonneg_r (q' + 1) q (class_size cl) ltac:(zlia) ltac:(zlia)). zlia.
+
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c' WF ltac:(zlia)) as MB. pose proof ev_user_room as EVR. unfold kUserMapSize, kFreeArrayOffset in MB, EVR.
pose proof (class_ok c' ltac:(zlia)) as (K1' & _).
rewrite !region_off_eq by zlia.
destruct (Z_lt_le_dec c' cl).
* left. assert (c' * 2 ^ 32 + 2 ^ 32 <= cl * 2 ^ 32) by nia. zlia.
* right. assert (cl * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by nia. zlia.
-
destruct GG as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
pose proof (am_placed B ly S rd0 HARm) as [_ PD].
pose proof (pairwise_In zdisjoint (sec_extents ly S ++ static_extents ly) (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize)
(sec_extents ly S) (static_extents ly) eq_refl PD S5 ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite S3, S4. unfold kPage in *. zlia.
Qed.
Lemma find_chunk_at_none : forall lst g, (forall k, In k lst -> ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)) -> find_chunk_at B ly lst g = None.
Proof.
induction lst as [|k t IH]; intros g H; [reflexivity|]. cbn [find_chunk_at].
destruct (Z.leb_spec (ck_base B ly k) g); destruct (Z.ltb_spec g (ck_base B ly k + ck_extent k)); cbn [andb];
try (apply IH; intros k' Hk'; apply H; right; exact Hk').
exfalso. apply (H k (or_introl eq_refl)). zlia.
Qed.
Lemma shadow250 : forall g, g mod 8 = 0 -> Kv <= g < Kv + class_size cl -> rd0 (shadow_addr g) = Some 250.
Proof. clean2.
intros g Hg8 Hg.
apply (am_shadow B ly S rd0 HARm g 250 Hg8). unfold ashadow.
rewrite find_chunk_at_none.
2:{ intros k Hk. pose proof (cached_vs_chunk k Hk). zlia. }
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _).
rewrite (in_rangesb_In g (fa_poison_ranges ly S) (region_base ly cl) (rg_mapped_user (reg S cl))); [reflexivity| |rewrite Kv_base in Hg; zlia].
unfold fa_poison_ranges. apply in_app_iff. left. apply in_flat_map. exists cl. split; [apply In_zseq; pose proof cl_range; zlia|]. left. reflexivity.
Qed.
(* The shadow of the chunk lies in the high-shadow band, below kHighMemBeg. *)
Lemma SK_range : 0x2008fff7000 <= SKv /\ SKv + class_size cl / 8 <= kHighMemBeg.
Proof.
pose proof Kv_geom as (V1 & V2 & V3 & _). pose proof cls_geom as (K1 & K2 & _). ceil.
unfold SKv, SHBv.
pose proof (Z.div_mod Kv 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound Kv 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (class_size cl) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (class_size cl) 8 ltac:(lia)) as M2.
unfold kHighMemBeg in *. lia.
Qed.
Lemma shadow_present : forall s, SKv <= s < SKv + class_size cl / 8 -> rd0 s = Some 250 /\ apresent (w_H W) mem0 s.
Proof. clean2.
intros s Hs.
pose proof Kv_geom as (V1 & V2 & V3 & _). pose proof cls_geom as (K1 & K2 & _).
assert (E : s = shadow_addr (Kv + 8 * (s - SKv))).
{ unfold shadow_addr. rewrite (Z.mul_comm 8 (s - SKv)), Z.div_add by zlia. unfold SKv, SHBv, SHADOW_OFF. zlia. }
assert (R : rd0 s = Some 250).
{ rewrite E. apply shadow250; [| unfold SKv, SHBv in *; pose proof (Z.div_mod Kv 8 ltac:(zlia));
pose proof (Z.div_le_mono (8 * (s - (2147450880 + Kv / 8)) + 7) (class_size cl) 8 ltac:(zlia)); nia].
rewrite Z.add_mod, Z.mul_comm, Z_mod_mult by zlia. replace (Kv mod 8) with 0; [reflexivity|].
symmetry. apply Z.mod_divide in V3 as [q Hq]; [|zlia]. apply Z.mod_divide; [zlia|]. exists (2 * q). zlia. }
split; [exact R|].
pose proof (aview_byte (w_H W) mem0 s 250 R) as R'. eapply mbyte_off_apresent; [apply off_img_high | exact R'].
pose proof SK_range as (D4 & D5). unfold TFIB_IMG_END, kHighMemBeg in *. lia.
Qed.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent (w_H W) mem0 a.
Proof.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) _ Hin) | exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 HARm) _ Hin)]. }
destruct (range_vis_mbyte B ly (w_H W) mem0 e len (a - aeval B ly e) RV ltac:(zlia)) as [b Hb].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb by zlia. exact (mbyte_off_apresent (w_H W) mem0 a b Hhi Hb).
Qed.
(* The whole cached chunk is present (YFiy.KPRES over the class size). *)
Lemma chunk_present : forall a, Kv <= a < Kv + class_size cl -> apresent (w_H W) mem0 a.
Proof. clean2.
intros a Ha. pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & _). pose proof Kv_geom as (V1 & V2 & _). pose proof cls_geom as (K1 & _).
apply (vis_present (ASp (region_off cl)) (rg_mapped_user (reg S cl))).
- right. unfold aareas. apply in_app_iff. left. apply in_flat_map. exists cl. split; [apply In_zseq; pose proof cl_range; zlia|]. left. reflexivity.
- cbn [aeval]. fold (region_base ly cl). pose proof Kv_base. unfold region_base in *. zlia.
- apply off_img_high. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly S).
Proof. intros r Hr. unfold ajunk. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. exact Hr. Qed.
Lemma T_zone : zone3 T kThreadObjSize.
Proof.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
exact (zone3_intro ly T kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)).
Qed.
(* The thread's junk words (cache stats, stats) are present. *)
Lemma junk_present : forall a, T + t_cache_stats <= a < T + t_unwinding -> apresent (w_H W) mem0 a.
Proof.
intros a Ha. pose proof T_zone as ZT.
assert (OI : off_img a) by (apply (zone3_off_img _ _ a ZT); unfold kThreadObjSize, t_cache_stats, t_unwinding in *; lia).
destruct (Z_lt_le_dec a (T + t_stats)) as [H1|H1].
- destruct (range_vis_mbyte B ly (w_H W) mem0 (AT t_cache_stats) (t_stats - t_cache_stats) (a - (T + t_cache_stats))
(proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) (AT t_cache_stats, t_stats - t_cache_stats) (in_thread_junk _ (or_intror (or_introl eq_refl))))
ltac:(unfold t_cache_stats, t_stats, t_unwinding in *; cbn; lia)) as [b Hb].
cbn [aeval] in Hb. replace (ly_T ly + t_cache_stats + (a - (T + t_cache_stats))) with a in Hb by (unfold T; lia).
exact (mbyte_off_apresent (w_H W) mem0 a b OI Hb).
- destruct (range_vis_mbyte B ly (w_H W) mem0 (AT t_stats) (t_unwinding - t_stats) (a - (T + t_stats))
(proj1 (Forall_forall _ _) (am_junk B ly S rd0 HARm) (AT t_stats, t_unwinding - t_stats) (in_thread_junk _ (or_intror (or_intror (or_introl eq_refl)))))
ltac:(unfold t_cache_stats, t_stats, t_unwinding in *; cbn; lia)) as [b Hb].
cbn [aeval] in Hb. replace (ly_T ly + t_stats + (a - (T + t_stats))) with a in Hb by (unfold T; lia).
exact (mbyte_off_apresent (w_H W) mem0 a b OI Hb).
Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. exact (tfib_const_lookup_sym B TS ly S (w_H W) mem0 e w e' HARm E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (tfib_const_lookup B TS ly S (w_H W) mem0 a w x HARm E). Qed.
Lemma cell_state : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof.
intros c e w x Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem0 e w (ANum x)).
exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 HARm) _ Hin).
Qed.
Lemma In_acells_cache : forall c, In c (cache_cells S cl) -> In c (acells B ly S).
Proof.
intros c Hc. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists cl.
split; [apply In_zseq; pose proof cl_range; zlia | exact Hc].
Qed.
Lemma cache_vals : val_mem tfibsegs m0 Pv 4 cnt /\ val_mem tfibsegs m0 (Pv + 8) 8 (class_size cl) /\ val_mem tfibsegs m0 PVv 4 v.
Proof. clean2.
pose proof off_facts as (O1 & O2 & O3 & O4 & O5 & NI & C1 & C2 & PM).
assert (EP : forall d, aeval B ly (aoff (AT (t_cache + 80 * cl)) d) = Pv + d) by (intros d; cbn; unfold Pv, T; zlia).
assert (EP0 : aeval B ly (AT (t_cache + 80 * cl)) = Pv) by (cbn; unfold Pv, T; zlia).
unfold cache_cells in *.
split; [|split].
- rewrite <- EP0. eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; left; reflexivity|].
rewrite Hcache, length_app. cbn [length]. unfold z4, c4. f_equal. f_equal. f_equal. zlia.
- rewrite <- (EP 8). eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; left; reflexivity|].
reflexivity.
- replace PVv with (aeval B ly (aoff (AT (t_cache + 80 * cl)) (16 + 4 * Z.of_nat (length l)))) by (rewrite EP; unfold PVv; zlia).
eapply cell_state; [apply In_acells_cache; unfold cache_cells; rewrite Hinited; right; right; right|].
+ apply in_map_iff. exists (length l, off). split; [reflexivity|]. rewrite Hcache.
rewrite length_app. cbn [length]. apply (In_combine_seq_last l off 0).
+ cbn [fst snd]. unfold z4, c4. f_equal. f_equal. f_equal. rewrite Hoff_def. rewrite Z.mul_comm, Z.div_mul by zlia. reflexivity.
Qed.
Lemma unwinding_val : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply cell_state; [|reflexivity]. unfold acells. do 8 (apply in_or_app; right). left. reflexivity.
Qed.
(* The instance's fields the seed reads: primary.space at +0x20 and the two words at +0xe20 (constant cells). *)
Lemma inst_cells : val_mem tfibsegs m0 (TFIB_INST + 0x20) 8 (ly_space ly) /\
val_mem tfibsegs m0 (TFIB_INST + 0xe20) 8 0x10000000000 /\ val_mem tfibsegs m0 (TFIB_INST + 0xe28) 8 0x108000010.
Proof.
split; [|split].
- replace (TFIB_INST + 0x20) with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace (ly_space ly) with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
Qed.
(* The remaining parts of the hit-g view (AGif0cgif.hview; assembled in AGif1). *)
Lemma v_facts : 0 <= v /\ v mod 2 = 0 /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof. pose proof Hv' as [V0 V1]. pose proof Hv2' as V2. split; [exact V0|]. split; [exact V2|]. exact V1. Qed.
Lemma shadow_vals : forall s, SKv <= s < SKv + class_size cl / 8 -> apresent (w_H W) mem0 s /\ val_mem tfibsegs m0 s 1 250.
Proof.
intros s Hs. destruct (shadow_present s Hs) as [R P]. split; [exact P|].
intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. exact (aview_byte _ _ _ _ R).
Qed.
End h.
End f.
