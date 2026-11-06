(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are
   restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc's ASan harness walk
   (LLVMFuzzerTestOneInput 0x7e68c, fuzz_qdisc.asan sha256
   980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgRt.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed
   (h-small-a3). rule 24 (reuse): no function is proved here; this is the walk's context record and its
   tactics.

   THE QDISC CHANGES, each measured on the pinned image with capstone 5.0.7:
   Q1 NO FAKE FRAME. knock's harness calls __asan_stack_malloc_1 and owns a class-1 fake frame; qdisc's
      harness has no address-taken local, calls no allocator and owns nothing (its 484 bytes hold three
      `jal`: 0x7e7cc reac_qdisc_etf_catchup_slots, 0x7e7d8 check_slots and the never-reached report calls).
      So rtcx drops c_fpos, rt_F / rt_FL / RTFP's frame entry and env slots 70 / 75 / 87 / 88 are gone,
      rt_from threads own = [] and frames S3 = [], and keptRT has no own-frame case.
   Q2 NO sp1 ATOM. knock's prologue ends `andi sp,sp,-0x20`, which is not an offset of sp0, so it needs a
      fresh atom 70. qdisc's prologue is `addi sp,sp,-0x60` only (0x7e68c), so sp stays SOff 2 (-96) and
      c_sp1 is gone with it.
   Q3 STACK REGION 96 (the 12 callee-saved words at 8(sp)..0x58(sp), 0x7e690-0x7e6b8), where knock trims to
      208 / -104.
   Q4 NO UAR CELL. knock's stack_malloc path reads __asan_option_detect_stack_use_after_return; qdisc's
      program never loads it (lib/A/ACeh.v:25), so rt_regions0 carries the stack, the .got slot of the
      shadow cell and the shadow cell only.
   Q5 EV_LIB = 0 and LLVMF_STK = 32768 are lib/A/ACfm.v's, as knock's. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* The image-A addresses the harness and its two callees sit at (capstone 5.0.7 over fuzz_qdisc.asan,
   sha256 980e2b845852...; the unstripped twin d77ead7cec5c... names them). A_QD_MAGIC is the 8-byte
   .rodata cell both callees load to divide by 10 ^ 6: `auipc a1,0xfff92` 0x7e8b4 + `ld a1,-0x564(a1)`
   in check_slots and `auipc a0,0xfff92` 0x7e990 + `ld a0,-0x640(a0)` in catchup both form 0x10350, and
   the 8 bytes there are 0x431BDE82D7B634DB = QPgCSpec.QD_MAGIC (read from the pinned file). *)
Definition A_QD_SLOTS : Z := 0x7e94c.
Definition A_QD_CHECK : Z := 0x7e870.
Definition A_QD_MAGIC : Z := 0x10350.
(* the return sites of the harness's two `jal` (0x7e7cc and 0x7e7d8) *)
Definition RA_QD_SLOTS : Z := 0x7e7d0.
Definition RA_QD_CHECK : Z := 0x7e7dc.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SB].
(* Q3, Q4 *)
Definition rt_regions0 : smem := [ stack_region 96; got_region; bcell_region 32 ].
(* sp in [2^46, 2^47] 16-aligned; n = a1 in [0, 2^26 - 1] (the harness's own size refusal is proved, not
   assumed: 0x7e6c8 `bltu a3,a2` leaves to 0x7e81c when n = 0 or n >= 2^26); env slot 32 = SB *)
Definition rt_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2^26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_rt0 : sstate := mkSS A_LLVMF sr_atoms rt_regions0 None (mkFacts rt_atoms0 [] []).
(* Q1, Q2: no c_fpos, no c_sp1 *)
Record rtcx := mkRTCX {
c_ly : alayout; c_S : astate; c_W : world tfibsegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_p : Z; c_n : Z; c_E0 : env;
c_T : Z }.
Definition ACC0 : Z := 0.
Definition rt_base (B : asyms) (MT : ameter_ops) (cx : rtcx) : Prop :=
afn_pre tfibsegs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
raZ (c_regs cx) = RA_LLVMF /\
getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
frames (c_S cx) = [] /\ st_nev (c_S cx) + EV_LIB <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
arodata_ok B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
mo_ok MT (c_S cx) (c_T cx) /\
ACC0 <= c_T cx.
Definition rt_E (cx : rtcx) (E : env) : Prop :=
forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n.
Definition RTFP : list (Z * Z) := [YI16.sink_token].
(* Q1: own = [] and frames S3 = [] *)
Definition rt_from (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (POST : rtcx -> world tfibsegs -> config -> Prop) (ss : sstate)
(INV : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop) : Prop :=
forall (cx : rtcx) (E : env) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B MT cx -> rt_E cx E ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [] ->
mo_le MT (c_S cx) S3 acc ->
INV cx E k acc ly3 S3 W3 ms3 md3 ->
st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
SRr tfibsegs W3 (mkCfg ms3 md3) (POST cx).
Definition INV_0 (B : asyms) (MT : ameter_ops) (kmax : Z) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= kmax /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
(* input-byte provenance, used by the loop's shadow-checked reads *)
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
(* one byte of the input, as a val_mem [knock A/APgLoop0.v:77-84, the donor's A/ACew.v:89-95] *)
Lemma val_mem1_of_aview : forall H m a v, aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256) by lia.
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* the walk's byte provenance, as the loop's reads need it [knock A/APgLoop0.v:104-120 PB_at_now] *)
Lemma PB_at_now : forall B STK cx own ly3 S3 W3 mem3 md3 k i,
AR_laws tfibsegs B -> AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ->
ajournal tfibsegs B STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) -> In (c_p cx, c_n cx) (ablocks B ly3 S3) -> req_size (c_n cx) = c_n cx ->
0 <= i < c_n cx ->
exists b, PB cx i b /\ aview tfibsegs (w_H W3) mem3 (c_p cx + i) = Some b.
Proof.
intros B STK cx own ly3 S3 W3 mem3 md3 k i LAWS HAR0 HJ Hin0 Hin3 Hrq Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR0 Hin0) as (_ & _ & _ & _ & Hpres & _). rewrite Hrq in Hpres.
destruct (aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) as [b|] eqn:Ev;
[| exfalso; exact (aview_some_of_apresent tfibsegs _ _ _ (proj1 (Hpres (c_p cx + i) ltac:(lia))) Ev)].
destruct (aview_byte tfibsegs _ _ _ b Ev) as (bb & _ & _ & Hb).
exists b. split.
- split; [exact Hb | apply val_mem1_of_aview; exact Ev].
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 (c_p cx) (c_n cx) i Hin0 Hin3); [exact Ev | rewrite Hrq; exact Hi | apply inFP_nil].
Qed.
(* the executor reads an offset of an atom modulo 2 ^ 64 [knock A/APgStep.v:77-78 U_offx] *)
Lemma U_offx : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n c) = (x + c) mod 2 ^ 64.
Proof. intros E n x c Hn Hx. rewrite U_SOff, Hn, unsigned_lit_small by lia. reflexivity. Qed.
(* 0x7e6c8 `bltu a3,a2` with a3 = n - 2 ^ 26 and a2 = 1 - 2 ^ 26, both wrapped: with 0 <= n < 2 ^ 26 the
   wrapped a3 is n - 2 ^ 26 + 2 ^ 64, so the branch to the return-0 block is taken exactly when n = 0.
   (The other half of the C test, n >= FUZZ_INPUT_MAX = 2 ^ 26, the contract has already excluded.) *)
Lemma qd_size_wrap : forall n, 0 <= n < 2 ^ 26 -> (n + -67108864) mod 2 ^ 64 = n + 18446744073642442752.
Proof.
intros n Hn. rewrite <- (Z.mod_add (n + -67108864) 1 (2 ^ 64)) by lia.
replace (n + -67108864 + 1 * 2 ^ 64) with (n + 18446744073642442752) by lia.
apply Z.mod_small. lia.
Qed.
Lemma rt_E_havoc : forall cx E N vs, (33 <= N)%nat -> rt_E cx E -> rt_E cx (havoc E N vs).
Proof. intros cx E N vs HN AG n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn. Qed.
Lemma rt_E_ewset : forall cx E n w, (33 <= n)%nat -> rt_E cx E -> rt_E cx (ewset E n w).
Proof. intros cx E n w HN AG m Hm. rewrite ew_ewset_other by lia. apply AG. exact Hm. Qed.
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
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
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
- unfold rt_regions0, stack_region, got_region, bcell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 612552) at 1.
apply (chunk_ok_val tfibsegs E _ 0 612552 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 645240) at 1.
apply (chunk_ok_val tfibsegs E _ 0 645240 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents.
unfold rt_regions0, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0. clear. unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok rt_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E11, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 Hn. clear. unfold SB, zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End RT.
End c.
(* Q1, Q3: the only writable region of the walk is the 96-byte save area of region 2; every other region
   (the two cells, the input bytes, the frame-rate table) has wlo = whi and is paid by awr_ok_cons_ro. *)
Ltac awrRT AG :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first [ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear; cbn; unfold LLVMF_STK, ASTACK; lia | clear; cbn; lia |] ]
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first [ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrRT: no rule for the head region" ]
end.
(* a branch condition on an offset of an atom, turned into a Z fact *)
Ltac hc_off H n v c En :=
lazymatch type of H with context [U ?E' (SOff n c)] =>
rewrite (U_offx E' n v c ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En) ltac:(lia)) in H end.
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
cbn [c_E0]; assumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_E0 c_T]
| exact HS ] end end.
(* the prelude of every segment lemma: knock's rt_prelude (A/APgRt.v:299-342) without its frame block *)
Ltac rt_prelude :=
let LAWS := rnLAWS in
let cx := fresh "cx" in
intros cx E k acc ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HMLE HINV HS;
destruct cx as [ly S W regs mem md p n E0 T];
pose proof HBASE as HBASE0;
unfold rt_base in HBASE; unfold rt_E in HEE;
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_E0 c_T] in HBASE, HEE, HJ3, Hfrs3, HMLE, HINV;
destruct HBASE as (HPRE & Hra & Hp & Hn & Hpn & Hfr0 & Hev & Hlive & HROD & EE & EX32 & Usp & HMOK & HT0);
rename HEE into AG;
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
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in
aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
