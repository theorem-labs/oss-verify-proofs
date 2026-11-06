(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgMainRt.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f; symbols of
   the unstripped twin 635d02c7e8fa2e1653012207b6ddd2f2c5dd3b8e578ee9607cdc35b94e5260bb). What differs: the core
   imports are image B's lib/AU twins (ACef -> YCef, AF0l -> YF0l, ACej -> YCej, ACeh -> YCeh, ACem -> YCem,
   ACep -> YCep, ACfm -> YCfm); the return sites RT_*_ra are image B's (the call sites of LLVMFuzzerTestOneInput
   0x806b4 in image B, each the address after its `jal`); rt_trace_in names image B's traced calls (malloc_ra0
   0x52df0 with ra 0x80844, free_ra0 0x52c90 with ra 0x80968); rt_entry's GOT and cell literals are image B's
   (.got slot 0x99170 = 627056 -> the shadow-base variable 0xa16f8 = 661240, .got slot 0x991c8 = 627144 -> the
   frame-option variable 0xa1700 = 661248, lib/AU/YCeh.v). The A file's notes P1 .. P6 below name image A's
   numbers; image B's are the ones this file states. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) from
   proofs/libreac/fuzz_knock/lib/A/APgRt.v at origin/ossv/recipes 6ebe35ba632 (the context record, rt_from, the
   class-1 tactics) and proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v at c8557374ad2e (the meter need of a harness that
   calls malloc and free, rt_trace_in), with their module paths changed. rule 24 (reuse): no function is proved
   here; this is the walk's context record and its tactics.

   THE PIN CHANGES, each measured on the pinned image with capstone 5.0.7 (symbol names from the unstripped twin
   435309a6b12c4d3e09a8484ec253b5fab600e4f00c28694ac28db2fc7a4475ab):
   P1 the harness frame on the side stack is class 1 (`addi a0,zero,0x60` 0x80720, `jal 3ca58` 0x80724), as knock's:
      rt_F / rt_FL / rt_from / awrRT_rec / keptRT / rt_prelude / fs_rwF are knock's class-1 forms.
   P2 the prologue is `addi sp,sp,-0x80` (0x806b4) and `andi sp,sp,-0x20` (0x806f4), as cgif's: sp1 = 32 *
      ((sp - 128) / 32), the stack region of the entry state is 128 bytes, and sp0 - 144 <= sp1 <= sp0 - 128.
   P3 the harness makes ONE malloc (0x80824, ra 0x80828) and ONE free (0x80930, ra 0x80934) per call (fuzz.h:84-97
      fuzz_str, fuzz_pin.c:102), so the event budget is 2 (RT_EV, lib/A/PPgLib.v's PIN_EV_LIB) and rt_base carries
      cgif's meter need: PIN_NEED MT = mo_malloc MT (2 ^ 26) + mo_free MT (the malloc asks for k + 1 <= 2 ^ 26 bytes).
   P4 the record carries the input bytes c_pl (the top claim's pl: n = |pl| and the n bytes at p are pl), which the
      flags byte, the rest and the spec string are functions of (lib/Prog/pin_spec.v pin_flags / pin_rest / pin_str).
   P5 rt_trace_in names pin's two traced calls: malloc_ra0 0x52df0 with ra 0x80828, free_ra0 0x52c90 with ra 0x80934.
   P6 the GOT / cell literals of rt_entry are pin's: 0x99050 = 626768, 0xa15f8 = 660984, 0x990a8 = 626856,
      0xa1600 = 660992. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the return sites of the harness's calls in image B (the address after each `jal` of LLVMFuzzerTestOneInput) *)
Definition RT_stack_malloc_ra : Z := 0x80728.
Definition RT_memchr_ra : Z := 0x80834.
Definition RT_malloc_ra : Z := 0x80844.
Definition RT_memcpy_ra : Z := 0x80860.
Definition RT_strlen_ra : Z := 0x80888.
Definition RT_row_ra : Z := 0x80a54.
Definition RT_parse_ra : Z := 0x80938.
Definition RT_known_ra : Z := 0x80944.
Definition RT_chkrow_ra : Z := 0x80954.
Definition RT_label_ra : Z := 0x80960.
Definition RT_free_ra : Z := 0x80968.
(* P3: one malloc and one free *)
Definition RT_EV : Z := 2.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SB].
(* P2: [sp0-128, sp0) *)
Definition rt_regions0 : smem := [ stack_region 128; got_region; bcell_region 32; uar_got_region; uar_cell_region ].
(* sp in [2^46, 2^47] 16-aligned; n = a1 in [0, 2^26 - 1]; env slot 32 = SB *)
Definition rt_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2^26 - 1) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_rt0 : sstate := mkSS A_LLVMF sr_atoms rt_regions0 None (mkFacts rt_atoms0 [] []).
(* P4: c_pl *)
Record rtcx := mkRTCX {
c_ly : alayout; c_S : astate; c_W : world tfibsegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_p : Z; c_n : Z; c_pl : list byte; c_fpos : Z; c_sp1 : Z; c_E0 : env;
c_T : Z }.
Definition ACC0 : Z := 0.
(* P3 *)
Definition PIN_NEED (MT : ameter_ops) : Z := mo_malloc MT (2 ^ 26) + mo_free MT.
Definition rt_base (B : asyms) (MT : ameter_ops) (cx : rtcx) : Prop :=
afn_pre tfibsegs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
raZ (c_regs cx) = RA_LLVMF /\
getr (c_regs cx) 10 = w64 (c_p cx) /\ getr (c_regs cx) 11 = w64 (c_n cx) /\
((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
c_n cx = Z.of_nat (length (c_pl cx)) /\
garr8 tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
frames (c_S cx) = [] /\ st_nev (c_S cx) + RT_EV <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_LIB <= LIVE_MAX /\
arodata_ok B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -128) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
mo_ok MT (c_S cx) (c_T cx) /\ PIN_NEED MT <= c_T cx.
(* P1: class 1 *)
Definition rt_F (cx : rtcx) : Z := frame_addr (c_ly cx) 1 (c_fpos cx).
Definition rt_FL (cx : rtcx) : Z := flag_addr (c_ly cx) 1 (c_fpos cx).
Definition rt_E (cx : rtcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 70 = Z_to_bv 64 (c_sp1 cx) /\ ew E 75 = Z_to_bv 64 (rt_F cx) /\ ew E 87 = Z_to_bv 64 (rt_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + rt_F cx / 8).
Definition RTFP : list (Z * Z) := [YI16.sink_token].
(* own = frames S3 = [(1, fpos)] *)
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
(* input-byte provenance *)
Definition PB (cx : rtcx) (i b : Z) : Prop :=
0 <= b < 256 /\ val_mem tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx + i) 1 b.
Definition rt_postP (B : asyms) (MT : ameter_ops) (FP : list (Z * Z)) (PX : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(cx : rtcx) : world tfibsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k /\ k <= RT_EV /\
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
(* P5 [cgif A/ACf5.v:155-165]: the call traces of the harness's malloc and free, at image B's return sites *)
Lemma rt_trace_in : forall (pcf ra : Z) (regsT : bvmap 5 word) (cx : rtcx),
raZ (c_regs cx) = RA_LLVMF -> raZ regsT = ra ->
((pcf = 0x52df0 /\ ra = 0x80844) \/ (pcf = 0x52c90 /\ ra = 0x80968)) ->
In (call_trace0 pcf regsT (rt_ch cx)) Tfib_universe.
Proof.
intros pcf ra regsT cx Hra0 Hra Hpc.
rewrite call_trace_of_spine, rt_ch_spine, Hra, Hra0.
destruct Hpc as [[-> ->] | [-> ->]];
(destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); apply memZL_In; vm_compute; reflexivity).
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
constructor; [|constructor]. rewrite <- (Z.add_0_l 627056) at 1.
apply (chunk_ok_val tfibsegs E _ 0 627056 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 661240) at 1.
apply (chunk_ok_val tfibsegs E _ 0 661240 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_uar.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 627144) at 1.
apply (chunk_ok_val tfibsegs E _ 0 627144 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_uar_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 661248) at 1.
apply (chunk_ok_val tfibsegs E _ 0 661248 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 tfibsegs (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold rt_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob.
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
(* knock's class-1 awrRT, with pin's sp1 window sp0 - 144 <= sp1 <= sp0 - 128 (P2) *)
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
lazymatch goal with Hsp1 : sp0 - 144 <= ?sp1 <= sp0 - 128 |- _ =>
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
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T]
| exact HS ] end end.
Ltac rt_prelude :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws tfibsegs ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx E k acc ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HMLE HINV HS;
destruct cx as [ly S W regs mem md p n pl fpos sp1 E0 T];
pose proof HBASE as HBASE0;
unfold rt_base in HBASE; unfold rt_E in HEE; red in HINV; unfold rt_F, rt_FL in HBASE, HEE, HJ3, HINV;
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in HBASE, HEE, HJ3, Hfrs3, HMLE, HINV;
destruct HBASE as (HPRE & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & EX32 & Usp & HMOK & HT0);
destruct HEE as (AG & E70 & RF & E87 & E88);
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : LLVMF_STK = 32768) by reflexivity;
assert (HEV : RT_EV = 2) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
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
destruct (sp1_facts (spZ regs + -128) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16;
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia); clear Hsp1r;
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

(* ====== the walk tactics of fuzz_knock lib/A/APgMain1.v:66-260 (6ebe35ba632), shared by every segment here ====== *)
(* ============================== Part 1: local copies of donor walk tactics ============================== *)
(* [A/ACf9.v:246-279, 339-340, 347-348] *)
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Lemma denot_havoc_win : forall E k ws e, sv_atoms_on (win_free k (length ws)) e = true -> sv_denot (havoc E k ws) e = sv_denot E e.
Proof. intros E k ws e He. apply (sv_denot_agree_on (win_free k (length ws)) E); [apply env_agree_on_havoc | exact He]. Qed.
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_havoc_above by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_havoc_above in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
Section loc. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* [A/ACew.v:89-94] *)
Lemma val_mem1_of_aview : forall H m a v, aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
assert (Rb : 0 <= bv_unsigned b < 256) by (pose proof (bv_unsigned_in_range 8 b) as X; exact X).
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Rb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [A/ACf9.v:489-505] *)
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
(* [A/ACf1.v:112-123] *)
Lemma rt_chunk1_of_val : forall E (m : word -> option byte) base off k v,
val_mem tfibsegs m (base + off) 1 v -> 0 <= v < 256 -> ew E k = Z_to_bv 64 v ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 (SOff k 0))).
Proof.
intros E m base off k v Hv Hr Hk i Hi. cbn [YP09.c_len YP09.c_val YP09.cv_len Z.of_N] in Hi.
assert (i = 0) as -> by lia.
exists (Z_to_bv 8 (YO0f.le_byte v 1 0)). split.
- cbn [YP09.c_off YP09.c_val YP09.cbyte]. rewrite sv_denot_SOff0, Hk. f_equal. unfold YP09.byte_of_word.
rewrite unsigned_lit_small by lia. f_equal. unfold YO0f.le_byte. change (Z.of_nat 1) with 1. cbn [Z.of_nat]. rewrite ?Z.mul_0_r, ?Z.shiftr_0_r.
change (2 ^ (8 * 1)) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
- cbn [YP09.c_off]. rewrite Z.add_0_r. pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.
(* [A/ACf1.v:192-223] *)
Lemma rt_ad_split : forall E x pre r post, all_disjoint E x (pre ++ r :: post) -> extent_disjoint E x r /\ all_disjoint E x (pre ++ post).
Proof. intros E x pre r post. induction pre as [|y pre IH]; cbn [app all_disjoint]; [tauto|]. intros [Hy Hr]. destruct (IH Hr) as [A B']. tauto. Qed.
Lemma rt_ed_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. unfold extent_disjoint. intros E a b H. lia. Qed.
Lemma rt_pd_move : forall E pre r post, pairwise_disjoint E (pre ++ r :: post) -> all_disjoint E r (pre ++ post) /\ pairwise_disjoint E (pre ++ post).
Proof.
intros E pre r post. induction pre as [|x pre IH]; cbn [app pairwise_disjoint all_disjoint]; [tauto|].
intros [Hx Hrest]. destruct (IH Hrest) as [Hr Hp]. destruct (rt_ad_split E x pre r post Hx) as [Hxr Hxa].
split; [split; [apply rt_ed_sym; exact Hxr | exact Hr] | split; [exact Hxa | exact Hp]].
Qed.
Lemma rt_wf_move : forall pre r post, regions_wf (pre ++ r :: post) = true -> regions_wf (r :: pre ++ post) = true.
Proof.
intros pre r post. induction pre as [|x pre IH]; cbn [app regions_wf]; [tauto|]. intros H.
apply andb_prop in H as [Hx H]. specialize (IH H). cbn [regions_wf] in IH. apply andb_prop in IH as [Hr Hp].
rewrite Hr, Hx, Hp. reflexivity.
Qed.
Lemma rt_forall_move : forall {A} (P : A -> Prop) pre r post, Forall P (pre ++ r :: post) -> Forall P (r :: pre ++ post).
Proof.
intros A P pre r post H. rewrite Forall_forall in *. intros x Hx. apply H.
destruct Hx as [<- | Hx]; [apply in_or_app; right; left; reflexivity|].
apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
Qed.
Lemma rt_st_ok_move : forall E ss ms pre r post,
st_ok tfibsegs E ss ms -> ss_mem ss = pre ++ r :: post ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r :: pre ++ post) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms pre r post (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (W & O & D) & H9) Hm.
rewrite Hm in W, O, D.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact (rt_wf_move pre r post W)|]. split; [exact (rt_forall_move _ pre r post O)|].
destruct (rt_pd_move E pre r post D) as [A B']. split; [exact A | exact B'].
Qed.
(* knock: the byte bounds of the four header registers at the join *)
Lemma U_lit0 : forall E, U E (SLit 0) = 0.
Proof. intros E. rewrite U_SLit. reflexivity. Qed.
Lemma U_zext8_lt : forall E x, 0 <= U E (SExt false 8 x) < 2 ^ 16.
Proof. intros E x. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. pose proof (Z.mod_pos_bound (U E x) 256 ltac:(lia)). lia. Qed.
Lemma U_sll8_zext8_lt : forall E x, 0 <= U E (SAlu ALU_SLL (SExt false 8 x) (SLit 8)) < 2 ^ 16.
Proof.
intros E x. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext, U_SLit. change (2 ^ Z.of_N 8) with 256.
change (Z.land (zcanon 8) 63) with 8. pose proof (Z.mod_pos_bound (U E x) 256 ltac:(lia)).
rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End loc.
(* [cgif A/ACf1.v:124-161, 243-251, 267-281, 396-409]; cgif's segment list is tfibsegs here *)
Ltac in_region HS R E10x AG :=
  lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv R HS eq_refl) as HS3;
  specialize (HS3 ltac:(
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    ewpeel; rewrite E10x, unsigned_lit_small by lia;
    split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
    repeat (apply Forall_cons; [ eapply rt_chunk1_of_val; [ apply val_mem1_of_aview; eassumption | eassumption | ewpeel; eassumption ] | ]); apply Forall_nil));
  specialize (HS3 ltac:(
    lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
    repeat split; zone_lia));
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rd_run HS HJ AG fpos F EFA E10x E32x Hpin3 Hrq :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
  try (lazymatch goal with |- range_addressable _ _ _ _ => obl_pay HJ E10x E32x Hpin3 Hrq end);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac rd_run_to HS HJ AG fpos F EFA E10x E32x Hpin3 Hrq stop :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
  try (lazymatch goal with |- range_addressable _ _ _ _ => obl_pay HJ E10x E32x Hpin3 Hrq end);
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac br_go HS Hc E11x :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
  lazymatch type of E11x with _ = Z_to_bv 64 ?nv =>
  hc_bool Hc ltac:(fun H => hc_atom H 11%nat nv E11x ltac:(lia)); hc_prop Hc end.
Ltac move_region HS i :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let pre := eval vm_compute in (firstn i rs) in
  let r := eval vm_compute in (nth i rs got_region) in
  let post := eval vm_compute in (skipn (S i) rs) in
  let HS3 := fresh "HS3" in
  pose proof (rt_st_ok_move Ex ssx msx pre r post HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
Ltac pin_reg HS rr a v Hv Ea :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
  remember (U Ev e) as v eqn:Hv;
  let Q := fresh "Q" in
  assert (Q : getr (ms_regs ms) rr = sv_denot Ev e) by exact (st_ok_restrict_reg tfibsegs Hh Ev ssx ms rr HS);
  add_atom_win HS a (Z_to_bv 64 v) Ea;
  lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msv2 =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pin_rege Ev2 ssx2 msv2 rr (SOff a 0) HS ltac:(intros X; discriminate X)
    ltac:(rewrite sv_denot_SOff0, Ea; cbn [ms_regs restrict mkst]; rewrite Q, Hv; symmetry; apply denot_lit_U)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end; clear Q end.
Ltac in_bytes HJ cx LAWS HAR Hpin Hpin3 Hrq FP0 i0 n0 :=
  let HJc := fresh "HJc" in pose proof HJ as HJc; rewrite FP0 in HJc;
  let rec go j k :=
    lazymatch k with
    | O => idtac
    | S ?k' =>
      let bj := fresh "b" in let PBj := fresh "PB" in let Aj := fresh "A" in let Rj := fresh "R" in
      destruct (PB_at_now _ _ cx _ _ _ _ _ _ _ j LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; lia)) as (bj & PBj & Aj);
      cbn [c_p] in Aj; pose proof (proj1 PBj) as Rj;
      let j' := eval vm_compute in (j + 1) in go j' k'
    end in
  go i0 n0; clear HJc.
Ltac rb HS AG E10 E11 E32 E10n E11n E32n :=
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; relowRT HS AG E10 E11 E32 E10n E11n E32n.
