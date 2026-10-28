(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l ACej ACeh ACem ACek ACei ACfm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition RT_stack_malloc_ra : Z := 0x80500.
Definition RT_memset_ra : Z := 0x80618.
Definition RT_malloc_ra : Z := 0x80818.
Definition RT_rdpal_ra : Z := 0x80844.
Definition RT_free1_ra : Z := 0x80878.
Definition RT_newgif_ra : Z := 0x809f8.
Definition RT_free2_ra : Z := 0x80a08.
Definition RT_rfc1_ra : Z := 0x80a20.
Definition RT_addframe_ra : Z := 0x80a34.
Definition RT_free3_ra : Z := 0x80a3c.
Definition RT_free4_ra : Z := 0x80a44.
Definition RT_rfc2_ra : Z := 0x80a5c.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SB].
Definition rt_regions0 : smem := [ stack_region 128; got_region; bcell_region 32; uar_got_region; uar_cell_region ].
Definition rt_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2^26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_rt0 : sstate := mkSS A_LLVMF sr_atoms rt_regions0 None (mkFacts rt_atoms0 [] []).
Record rtcx := mkRTCX {
c_ly : alayout; c_S : astate; c_W : world tfibsegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_p : Z; c_n : Z; c_fpos : Z; c_sp1 : Z; c_E0 : env;
c_T : Z     }.
Definition ACC0 : Z := 0.
Definition ACC_pal (MT : ameter_ops) : Z := mo_malloc MT 196605.
Definition RT_NEED1 (MT : ameter_ops) : Z := ACC_pal MT + mo_free MT.
Definition rt_base (B : asyms) (MT : ameter_ops) (cx : rtcx) : Prop :=
afn_pre tfibsegs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
raZ (c_regs cx) = RA_LLVMF /\
getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
frames (c_S cx) = [] /\ st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
arodata_ok B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -128) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
mo_ok MT (c_S cx) (c_T cx) /\ RT_NEED1 MT <= c_T cx.
Definition rt_F (cx : rtcx) : Z := frame_addr (c_ly cx) 2 (c_fpos cx).
Definition rt_FL (cx : rtcx) : Z := flag_addr (c_ly cx) 2 (c_fpos cx).
Definition rt_E (cx : rtcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 70 = Z_to_bv 64 (c_sp1 cx) /\ ew E 75 = Z_to_bv 64 (rt_F cx) /\ ew E 87 = Z_to_bv 64 (rt_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + rt_F cx / 8).
Definition RTFP : list (Z * Z) := [YI16.sink_token].
Definition rt_from (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (POST : rtcx -> world tfibsegs -> config -> Prop) (ss : sstate)
(INV : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop) : Prop :=
forall (cx : rtcx) (E : env) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B MT cx -> rt_E cx E ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [(2, c_fpos cx)] ->
mo_le MT (c_S cx) S3 acc ->
INV cx E k acc ly3 S3 W3 ms3 md3 ->
st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
SRr tfibsegs W3 (mkCfg ms3 md3) (POST cx).
Definition INV_0 (B : asyms) (MT : ameter_ops) (kmax : Z) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= kmax /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
Definition PB (cx : rtcx) (i b : Z) : Prop :=
0 <= b < 256 /\ val_mem tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx + i) 1 b.
Definition hdr_prov (cx : rtcx) (attr gen w16 h16 ngp : Z) : Prop :=
exists b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13,
PB cx 0 b0 /\ PB cx 1 b1 /\ PB cx 2 b2 /\ PB cx 3 b3 /\ PB cx 4 b4 /\ PB cx 5 b5 /\ PB cx 6 b6 /\ PB cx 7 b7 /\
PB cx 8 b8 /\ PB cx 9 b9 /\ PB cx 10 b10 /\ PB cx 11 b11 /\ PB cx 12 b12 /\ PB cx 13 b13 /\
w16 = b0 + 256 * b1 /\ h16 = b2 + 256 * b3 /\
attr mod 2 ^ 32 = b4 + 256 * b5 + 65536 * b6 + 16777216 * b7 /\
gen mod 2 ^ 32 = b8 + 256 * b9 + 65536 * b10 + 16777216 * b11 /\
ngp = b12 + 256 * b13.
Definition pal_prov (cx : rtcx) (pal ngp : Z) (m : word -> option byte) : Prop :=
forall i, 0 <= i < 3 * ngp -> exists b, PB cx (14 + i) b /\ val_mem tfibsegs m (pal + i) 1 b.
Definition hdr_fail (cx : rtcx) : Prop :=
c_n cx < 14 \/
exists attr gen w16 h16 ngp, hdr_prov cx attr gen w16 h16 ngp /\
((Z.land attr 4 = 0 /\ c_n cx < 14 + 3 * ngp) \/ 100000000 < w16 * h16).
Definition rt_postP (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(cx : rtcx) : world tfibsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
mo_le MT (c_S cx) S' (c_T cx) /\
PX ly' (ablocks B ly' S') W' mem' md'.
Definition rt_post (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (cx : rtcx) : world tfibsegs -> config -> Prop :=
rt_postP B MT FP (fun _ _ _ _ _ => hdr_fail cx) cx.
Lemma inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hin & _). exact Hin. Qed.
Lemma rt_val_mem_frame : forall (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.
Lemma PB_of_now : forall B STK FP cx own ly3 S3 W3 mem3 md3 k i b,
AR_laws tfibsegs B ->
ajournal tfibsegs B STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) -> In (c_p cx, c_n cx) (ablocks B ly3 S3) -> req_size (c_n cx) = c_n cx ->
0 <= i < c_n cx -> FP = [] -> 0 <= b < 256 ->
val_mem tfibsegs (mrestrict (w_H W3) mem3) (c_p cx + i) 1 b -> PB cx i b.
Proof.
intros B STK FP cx own ly3 S3 W3 mem3 md3 k i b LAWS HJ Hin0 Hin3 Hrq Hi -> Hb Hv. split; [exact Hb|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
eapply rt_val_mem_frame; [|exact Hv]. intros x Hx. cbn in Hx. replace x with (c_p cx + i) by lia.
symmetry. apply (mbyte_of_aview tfibsegs). apply (F2 (c_p cx) (c_n cx) i Hin0 Hin3); [rewrite Hrq; exact Hi | apply inFP_nil].
Qed.
Definition rt_ch (cx : rtcx) : list (Z * Z * Z) :=
if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].
Lemma rt_ch_spine : forall cx, spine (rt_ch cx) = (if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [raZ (c_regs cx)] else []).
Proof. intros cx. unfold rt_ch. destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); reflexivity. Qed.
Lemma rt_ctx_in : forall cx (site : Z) (L : list (list Z)),
raZ (c_regs cx) = RA_LLVMF -> In [site] L -> In [site; RA_LLVMF] L -> In (site :: spine (rt_ch cx)) L.
Proof.
intros cx site L Hra H1 H2. rewrite rt_ch_spine. destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); [rewrite Hra; exact H2 | exact H1].
Qed.
Lemma rt_E_havoc : forall cx E N vs, (89 <= N)%nat -> rt_E cx E -> rt_E cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & E70 & E75 & E87 & E88). unfold rt_E. rewrite !ew_havoc_old by lia.
split; [|split; [exact E70 | split; [exact E75 | split; [exact E87 | exact E88]]]].
intros n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn.
Qed.
Lemma rt_E_ewset : forall cx E n w, (89 <= n)%nat -> rt_E cx E -> rt_E cx (ewset E n w).
Proof.
intros cx E n w HN (AG & E70 & E75 & E87 & E88). unfold rt_E. rewrite !ew_ewset_other by lia.
split; [|split; [exact E70 | split; [exact E75 | split; [exact E87 | exact E88]]]].
intros m Hm. rewrite ew_ewset_other by lia. apply AG. exact Hm.
Qed.
Lemma denot_havoc_below : forall E k l e, sv_atoms_lt k e = true -> sv_denot (havoc E k l) e = sv_denot E e.
Proof. intros E k l e He. apply (sv_denot_agree k E); [apply env_agree_havoc_ge; [lia | apply env_agree_refl] | exact He]. Qed.
Lemma denot_ewset_below : forall E k w e, sv_atoms_lt k e = true -> sv_denot (ewset E k w) e = sv_denot E e.
Proof.
intros E k w e He. apply (sv_denot_agree k E); [|exact He]. split; [|reflexivity]. intros n Hn. apply ew_ewset_other. lia.
Qed.
Lemma rt_trace_in : forall (pcf ra : Z) (regsT : bvmap 5 word) (cx : rtcx),
raZ (c_regs cx) = RA_LLVMF -> raZ regsT = ra ->
((pcf = 0x52a6c /\ ra = 0x80878) \/ (pcf = 0x52a6c /\ ra = 0x80a08) \/ (pcf = 0x52a6c /\ ra = 0x80a3c) \/
(pcf = 0x52a6c /\ ra = 0x80a44) \/ (pcf = 0x52bcc /\ ra = 0x80818)) ->
In (call_trace0 pcf regsT (rt_ch cx)) Tfib_universe.
Proof.
intros pcf ra regsT cx Hra0 Hra Hpc.
rewrite call_trace_of_spine, rt_ch_spine, Hra, Hra0.
destruct Hpc as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]];
(destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); apply TRACES_LLVMFuzzerTestOneInput_U; vm_compute; repeat (first [left; reflexivity | right])).
Qed.
Section RT.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rt_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- replace (spZ regs - 8) with (spZ regs + -8) in H8 by lia. replace (spZ regs - 16) with (spZ regs + -16) in H16 by lia.
apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk);
[replace (spZ regs - 8) with (spZ regs + -8) by lia; exact H8 | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact H16
| exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.
Lemma rt_entry : forall W ly S regs mem md p n,
afn_pre tfibsegs B LLVMF_STK ly S W regs mem md [] ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
st_ok tfibsegs (Ereg regs rt_extra) ss_rt0 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_LLVMF) mem (seg_rom tfibsegs))).
Proof.
intros W ly S regs mem md p n HPRE H10 H11 Hpn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
rewrite restrict_mkst_fx.
set (E := Ereg regs rt_extra).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hn : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
unfold ss_rt0. apply (entry_st_ok_full tfibsegs); change (Ereg regs rt_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold rt_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 647064) at 1.
apply (chunk_ok_val tfibsegs E _ 0 647064 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 679928) at 1.
apply (chunk_ok_val tfibsegs E _ 0 679928 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_uar.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 647152) at 1.
apply (chunk_ok_val tfibsegs E _ 0 647152 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_uar_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 679936) at 1.
apply (chunk_ok_val tfibsegs E _ 0 679936 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 tfibsegs (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold rt_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rt_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 Hn. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RT.
End c.
