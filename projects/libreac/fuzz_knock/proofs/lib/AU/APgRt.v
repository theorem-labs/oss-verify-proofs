(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan harness walk (LLVMFuzzerTestOneInput 0x7eed0, fuzz_knock.asan sha256 61768cf4739b...) from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v lines 36-154 and 166-249, ACf9.v lines 24-102, 116-159, 423-427 and 507-516, and ACer.v lines 176-197 at c8557374ad2e, with their module paths changed, in the form a Theorem Labs lane's knock context record proposes (internal path, sha256 b9c440352b6bfde4..; its names knsegs / KnockLib / Hwx_kn / kn_segs_low are tfibsegs / TfibLib / Hwx_tfa / tfib_segs_low here). The knock changes, each measured on that image: D1 the harness frame is class 1 (128 bytes, 16 shadow bytes; `li a0,128` at 0x7ef40, `jal __asan_stack_malloc_1` at 0x7ef44) where cgif's is class 2 (256, 32): rt_F, rt_FL, rt_from, awrRT_rec, keptRT, rt_prelude, fs_rwF (window 0..16); D2 sp1 = 32 * ((sp - 192) / 32) (`addi sp,sp,-192` at 0x7eed0, `andi sp,sp,-32` at 0x7ef10; cgif -128); D3 stack region 208 (rt_regions0); D4 no RT_NEED1 / ACC_pal (cgif's 3 * 65535-byte palette malloc + free; knock's harness and callees allocate nothing), so rt_base has no HNEED conjunct and macc_go / macc are left out; D5 rt_post's PX is True (cgif's hdr_prov / pal_prov / hdr_fail are its GIF header parser, left out); D7 rt_trace_in (ACf5.v:155-165, cgif's traced library calls) left out; rt_entry's GOT and cell literals are knock's (615888 = 0x965d0, 648504 = 0x9e538, 615976 = 0x96628, 648512 = 0x9e540); rt_prelude asserts EV_LIB = 0 (A/ACfm.v). Kept from the donor: env slots 0..32 = the 32 registers and slot 32 = SB (rt_E), slots 70 = sp1, 75 = F, 87 = flag address, 88 = SB + F/8, atoms (2, 11, 32), LLVMF_STK 32768. Owner after this draft: a Theorem Labs lane (harness walk). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgRt.v of this library (fuzz_knock.asan-ubsan, sha256 f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), made the way derive_y.py makes lib/AU from lib/A (as proofs/cgif/cgif_file_fuzzer/lib/YCf5.v is made from A/ACf5.v at c8557374ad2e): the framework imports move to the lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm), and rt_entry's four constant-cell literals are the asan-ubsan image's: 615960 = 0x96618 (.got slot of __asan_shadow_memory_dynamic_address, ld at 0x7ef28), 648568 = 0x9e578 (__asan_shadow_memory_dynamic_address), 616048 = 0x96670 (.got slot of __asan_option_detect_stack_use_after_return, ld at 0x7ef24), 648576 = 0x9e580 (__asan_option_detect_stack_use_after_return), for the asan image's 615888 / 648504 / 615976 / 648512 (lib/AU/YCeh.v:21-24; asan-ubsan fuzz_knock.nm.txt:695, :443). Every definition keeps its lib/A body over the lib/AU names, so the Section equations of lib/AU/APgMain7.v (rt_base_def .. rt_post_def) hold by eq_refl; rt_base's last conjunct stays ACC0 <= c_T cx. The S0 code this record describes (0x7eed0-0x7f000: frame class 1, `li a0,128` at 0x7ef40, `jal __asan_stack_malloc_1` at 0x7ef44, `addi sp,sp,-192`, `andi sp,sp,-32`) is the same 77 words in both images up to the two GOT lo12 fields and the a5/a6 -> a6/a7 renaming (internal path). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SB].
(* D3: [sp0-208, sp0) *)
Definition rt_regions0 : smem := [ stack_region 208; got_region; bcell_region 32; uar_got_region; uar_cell_region ].
(* donor atoms unchanged: sp in [2^46, 2^47] 16-aligned; n = a1 in [0, 2^26 - 1] (kills 0x7effc -> 0x7f2e4, the asan image's 0x7effc -> 0x7f294 [a Theorem Labs lane plan :33, :89-90]); env slot 32 = SB *)
Definition rt_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2^26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_rt0 : sstate := mkSS A_LLVMF sr_atoms rt_regions0 None (mkFacts rt_atoms0 [] []).
Record rtcx := mkRTCX {
c_ly : alayout; c_S : astate; c_W : world tfibsegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_p : Z; c_n : Z; c_fpos : Z; c_sp1 : Z; c_E0 : env;
c_T : Z }.
Definition ACC0 : Z := 0.
(* D2 (sp - 192), D4 (no RT_NEED1; its lower bound on c_T is kept as the last conjunct ACC0 <= c_T cx, which INV_X's acc <= c_T cx and rt_post's mo_le need), D6 (A_EMPTY of the A image) *)
Definition rt_base (B : asyms) (MT : ameter_ops) (cx : rtcx) : Prop :=
afn_pre tfibsegs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
raZ (c_regs cx) = RA_LLVMF /\
getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
frames (c_S cx) = [] /\ st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
arodata_ok B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -192) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
mo_ok MT (c_S cx) (c_T cx) /\
ACC0 <= c_T cx.
(* D1: class 1 *)
Definition rt_F (cx : rtcx) : Z := frame_addr (c_ly cx) 1 (c_fpos cx).
Definition rt_FL (cx : rtcx) : Z := flag_addr (c_ly cx) 1 (c_fpos cx).
Definition rt_E (cx : rtcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 70 = Z_to_bv 64 (c_sp1 cx) /\ ew E 75 = Z_to_bv 64 (rt_F cx) /\ ew E 87 = Z_to_bv 64 (rt_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + rt_F cx / 8).
Definition RTFP : list (Z * Z) := [YI16.sink_token].
(* D1: own = frames S3 = [(1, fpos)] *)
Definition rt_from (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (POST : rtcx -> world tfibsegs -> config -> Prop) (ss : sstate)
(INV : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop) : Prop :=
forall (cx : rtcx) (E : env) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B MT cx -> rt_E cx E ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [(1, c_fpos cx)] ->
mo_le MT (c_S cx) S3 acc ->
INV cx E k acc ly3 S3 W3 ms3 md3 ->
st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
SRr tfibsegs W3 (mkCfg ms3 md3) (POST cx).
Definition INV_0 (B : asyms) (MT : ameter_ops) (kmax : Z) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= kmax /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
(* input-byte provenance, used by S1's shadow-checked reads through PB_of_now [a Theorem Labs lane plan :44-47] *)
Definition PB (cx : rtcx) (i b : Z) : Prop :=
0 <= b < 256 /\ val_mem tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx + i) 1 b.
Definition rt_postP (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(cx : rtcx) : world tfibsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
mo_le MT (c_S cx) S' (c_T cx) /\
PX ly' (ablocks B ly' S') W' mem' md'.
(* D5 *)
Definition rt_post (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (cx : rtcx) : world tfibsegs -> config -> Prop :=
rt_postP B MT FP (fun _ _ _ _ _ => True) cx.
Definition rt_ch (cx : rtcx) : list (Z * Z * Z) :=
if spZ (c_regs cx) + 16 <? ly_top (c_ly cx) then [(spZ (c_regs cx), raZ (c_regs cx), s0Z (c_regs cx))] else [].
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
constructor; [|constructor]. rewrite <- (Z.add_0_l 615960) at 1.
apply (chunk_ok_val tfibsegs E _ 0 615960 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 648568) at 1.
apply (chunk_ok_val tfibsegs E _ 0 648568 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_uar.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 616048) at 1.
apply (chunk_ok_val tfibsegs E _ 0 616048 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_uar_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 648576) at 1.
apply (chunk_ok_val tfibsegs E _ 0 648576 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 tfibsegs (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold rt_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0. clear. unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rt_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 Hn. clear. unfold SB, zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RT.
(* The Section equations rt_base_def,
   rt_F_def, rt_FL_def, rt_E_def, rt_from_def, rt_postP_def and rt_post_def of APgMain7.v (sha256 da919ad73224; internal record), each stated here word for word over this
   file's names and closed by reflexivity: the instance of that file's Section variables at this record meets every
   equation by eq_refl. rt_base_def writes the last conjunct ACC0 <= c_T cx with ACC0's value 0. *)
Lemma rt_base_eq : rt_base = fun (B : asyms) (MT : ameter_ops) (cx : rtcx) =>
afn_pre tfibsegs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
raZ (c_regs cx) = RA_LLVMF /\
getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
frames (c_S cx) = [] /\ st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
arodata_ok B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -192) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
mo_ok MT (c_S cx) (c_T cx) /\
0 <= c_T cx.
Proof. reflexivity. Qed.
Lemma rt_F_eq : rt_F = fun (cx : rtcx) => frame_addr (c_ly cx) 1 (c_fpos cx).
Proof. reflexivity. Qed.
Lemma rt_FL_eq : rt_FL = fun (cx : rtcx) => flag_addr (c_ly cx) 1 (c_fpos cx).
Proof. reflexivity. Qed.
Lemma rt_E_eq : rt_E = fun (cx : rtcx) (E : env) =>
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 70 = Z_to_bv 64 (c_sp1 cx) /\ ew E 75 = Z_to_bv 64 (rt_F cx) /\ ew E 87 = Z_to_bv 64 (rt_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + rt_F cx / 8).
Proof. reflexivity. Qed.
Lemma rt_from_eq : rt_from = fun (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (POST : rtcx -> world tfibsegs -> config -> Prop) (ss : sstate)
(INV : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop) =>
forall (cx : rtcx) (E : env) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B MT cx -> rt_E cx E ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [(1, c_fpos cx)] ->
mo_le MT (c_S cx) S3 acc ->
INV cx E k acc ly3 S3 W3 ms3 md3 ->
st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
SRr tfibsegs W3 (mkCfg ms3 md3) (POST cx).
Proof. reflexivity. Qed.
Lemma rt_postP_eq : rt_postP = fun (B : asyms) (MT : ameter_ops) (FP : list (Z * Z))
(PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop) (cx : rtcx) (W' : world tfibsegs) (c' : config) =>
exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
mo_le MT (c_S cx) S' (c_T cx) /\
PX ly' (ablocks B ly' S') W' mem' md'.
Proof. reflexivity. Qed.
Lemma rt_post_eq : rt_post = fun (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (cx : rtcx) =>
rt_postP B MT FP (fun _ _ _ _ _ => True) cx.
Proof. reflexivity. Qed.
End c.
Ltac awrRT_rec AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 88%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 75%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear; cbn; unfold LLVMF_STK, ASTACK; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - 208 <= ?sp1 <= sp0 - 192 |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1; cbn; unfold LLVMF_STK, ASTACK; lia | clear -Hsp1; cbn; lia |] end
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrRT: no rule for the head region" ];
awrRT_rec AG fpos F EFA
end.
Ltac awrRT AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrRT_rec AG fpos F EFA.
Ltac keptRT HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; lia | unfold LLVMF_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; lia | unfold LLVMF_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob ];
keptRT HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | eassumption
| left; rewrite_frame_addr; change (fs_frame_bytes 1) with 128; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; PrT ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | eassumption
| right; rewrite_frame_addr; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; unfold SB; lia
| intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; first [lia | PrT] ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ ?wlo ?whi _) =>
lazymatch goal with Hb : ew _ n = Z_to_bv 64 ?b |- _ =>
let L := rnLAWS in
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true =>
first [ eapply (region_kept_block_aj tfibsegs _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | lia | rqs_goal; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| eapply (region_kept_frame_aj tfibsegs _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | rewrite_frame_addr; lia | rewrite_frame_addr; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ] ] end
| eapply (region_kept_block_ajw2 tfibsegs _ L _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | exact (proj1 HJx) | eassumption | evalE AG | eassumption | lia | rqs_goal; lia | lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| match goal with |- ?g => idtac "KEPTRT-FAIL" g end; fail ] end
end.
Ltac relowRT HS AG E10 E11 E32 E10n E11n E32n :=
try clear E10n; try clear E11n; try clear E32n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end;
lazymatch type of E32 with _ = ?v => assert (E32n : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact E32) end end.
Ltac rt_hand RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (?PP ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : rt_base _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end);
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1];
split; [assumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T]
| exact HS ] end end.
Ltac rt_prelude :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws tfibsegs ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx E k acc ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HMLE HINV HS;
destruct cx as [ly S W regs mem md p n fpos sp1 E0 T];
pose proof HBASE as HBASE0;
unfold rt_base in HBASE; unfold rt_E in HEE; red in HINV; unfold rt_F, rt_FL in HBASE, HEE, HJ3, HINV;
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T] in HBASE, HEE, HJ3, Hfrs3, HMLE, HINV;
destruct HBASE as (HPRE & Hra & Hp & Hn & Hpn & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & EX32 & Usp & HMOK & HT0);
destruct HEE as (AG & E70 & RF & E87 & E88);
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : LLVMF_STK = 32768) by reflexivity;
assert (HEV : EV_LIB = 0) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (Hn26 : 0 <= n < 2 ^ 26) by (clear - Hpn; destruct Hpn as [[-> _] | [Hn' _]]; lia);
assert (E10 : ew E0 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact Hp);
assert (E11 : ew E0 11 = Z_to_bv 64 n) by (rewrite (EE 11%nat 11%bv eq_refl); exact Hn);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof EX32 as E32;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p0; unfold flag_addr; pose proof (EFA3 c p0) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as Hfin3_img;
destruct (frames_bounds tfibsegs _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 1) with 128 in *; change (128 / 8) with 16 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 1 fpos) in *; set (FL := flag_addr ly 1 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia);
let Hsp1r := fresh "Hsp1r" in
destruct (sp1_facts (spZ regs + -192) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16;
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia); clear Hsp1r;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in
aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
Ltac fs_roF HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac fs_rwF HS E88 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 16) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 16 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E88, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rebv HS E70 RF B70 B75 :=
try clear B70; try clear B75;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E70 with ew _ 70 = Z_to_bv 64 ?v => assert (B70 : bv_unsigned (ew Ev 70) = v) by (rewrite E70; apply unsigned_lit_small; unfold LLVMF_STK in *; lia) end;
lazymatch type of RF with ew _ 75 = Z_to_bv 64 ?v => assert (B75 : bv_unsigned (ew Ev 75) = v) by (rewrite RF; apply unsigned_lit_small; lia) end end.
Ltac rdkeep RD H2 m2 etac :=
lazymatch type of RD with ?rk = 0 -> forall i, 0 <= i < ?nk -> exists b, PB ?cx (?o + i) b /\ aview _ ?Hh ?m (?a + i) = Some b =>
let RD2 := fresh "RD" in
assert (RD2 : rk = 0 -> forall i, 0 <= i < nk -> exists b, PB cx (o + i) b /\ aview tfibsegs H2 m2 (a + i) = Some b)
by (let Hz := fresh "Hz" in intros Hz i Hi;
let b := fresh "b" in let HP := fresh "HP" in let HA := fresh "HA" in
destruct (RD Hz i Hi) as (b & HP & HA); exists b; split; [exact HP|]; rewrite <- HA; etac);
clear RD; rename RD2 into RD
| ?ty => fail "rdkeep: unexpected shape" ty end.
