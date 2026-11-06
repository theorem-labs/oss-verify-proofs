(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: SEGMENT S1 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput,
   cut C1 (0x82b78) to cut C2 (0x82ca8): the n' / n'' computation and its three spills, __wrap_malloc at 0x82b9c
   (ra 0x82ba0), the fill loop over reac_scene_placeholder and the xor loop over the rest of the input.  The
   statement is lib/A/P_LLVMFuzzerTestOneInput_seg.v's `seg_S1_stmt`, which this file does not restate and does
   not change; `scene_seg_S1` proves it.  The step kit is the position-abstract one (A/Prog/ScenePaLib.v,
   A/Prog/PaJournal.v); the malloc station is the shape of the S5 lane's M3 (amalloc04_rule_triv over AMALLOC),
   and each loop is a step lemma over a named invariant, closed by induction on the turns left. *)

(*   THE WALK, in the order `scene_seg_S1` takes it:
     - 0x82b78-0x82b84: `s1_entry` rebuilds C1 as the symbolic state `s1_ss0`.  Its three regions are the three
       one-word spill slots S1 writes ([s1+0x18] expect, [s1+0x38] n'', [s1+0x48] flags) and NOTHING else, so
       `frame_of` keeps every other byte: the 13 saved words of `sc_saves` [sp0-104, sp0) the caller chain is
       read from, and the spill words [s1+0x20] / [s1+0x28] / [s1+0x30] / [s1+0x50] C2 carries on.
     - the branch 0x82b84 (`andi a0,a6,1; beqz`) is split; each arm runs to the call 0x82b9c and enters the
       shared continuation at the call with a0 = n'' (`s1_nn_val`) and s8 = n'.
     - 0x82b9c: `amalloc04_rule_triv` (YCbp.v:30) with the caller chain from `s1_chain`, the trace from HTRACE
       at RT_malloc1_ra = BASE + 0x328, the live / event budgets from HLIVE / HEV and the window from HSTK.
     - 0x82ba0 `beqz a0`, to the abort block: refuted, the rule's post gives 4096 <= res.
     - 0x82ba8 `beqz s8`: n' = 0 skips the fill loop; else 0x82bac-0x82bb8 set a1 = 0, a2 = the placeholder's
       address (its GOT word, `s1_got_pl`), a3 = 0x458, and `s1_fill_loop` runs n' turns of `s1_fill_step`.
     - 0x82c20-0x82c2c (`MID`): s4 = F, s5 = min(rest, n') (`bltu s5,s8` split), s7 = s2; 0x82c30 `beqz s5`
       (`MIDX`): a zero count goes to C2, else `s1_xor_loop` runs cnt turns of `s1_xor_step`.
     - 0x82ca8 (`EXIT`): cut_C2, from the journal at k = 1, the malloc post (the block (res, n'')), the bytes the
       call kept (`acall_kept`: the stack above sp1, the frame and its shadow outside the new block) and the
       bytes the runs kept (`frame_of`).  C2's body contents are read off the final memory (`s1_bytes`).
   THE FOUR ASAN REPORT BRANCHES of S1 are all inside the two loop turns, and each is decided NOT TAKEN by the
   token run at its check site (the check's shadow load gives an obligation `range_addressable` of the byte
   checked, which the turn discharges; an undischarged obligation would leave the report arm open): in
   `s1_fill_step`, 0x82bd4 -> 0x82c14 -> 0x82c1c (report_load1, the placeholder byte, by `ro_usable` on HZS_PL
   and `obl_of_range`) and 0x82bf4 -> 0x82c08 -> 0x82c10 -> 0x83194 (report_store1, the body byte, by
   `obl_of_block` on the new block); in `s1_xor_step`, 0x82c4c -> 0x82c8c -> 0x82c94 -> 0x83198 (report_load1,
   the input byte, by `range_addressable_of_block` on the input block (p, n)) and 0x82c60 -> 0x82c98 -> 0x82ca4
   (report_load1, the body byte, by `range_addressable_of_block` on the new block).  The two loop turns were
   proved by a Theorem Labs lane against the invariants and statements below, which are frozen. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG0s YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import ScenePaLib SceneBase SceneFrame SceneRo.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC1h YC4b YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section s1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance PI_scene.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Notation RHI := (@pa_relro_hi _ scene_listing PI_scene).
Context {RO : ro_below_ofl (SK := SK) SEGS RLO RHI}.
Variable B : asyms.
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Let LAWS := AR_laws_ok SEGS B.
Let RUN := paj_run (PI := PI_scene) B LAWS.
Let RUNTO := paj_run_to (PI := PI_scene) B LAWS.
Let BR := paj_branch (PI := PI_scene).
Let RUNP := SRr_run_pi_AJ (L := scene_listing) (PL := PL_scene) (PI := PI_scene) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := scene_listing) (PL := PL_scene) (PI := PI_scene) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (L := scene_listing) (PL := PL_scene) (PI := PI_scene) B LAWS.

(* ---- the symbolic state at C1 ---- *)
(* S1 writes exactly three slots of the caller frame: [s1+0x18] (expect), [s1+0x38] (n'') and [s1+0x48]
   (the flags byte), and each is its OWN region, whose window is exactly that one word.  The three windows
   are then the run's whole write set, so `frame_of` keeps every other byte of the frame -- in particular
   the 13 callee-saved words of `sc_saves` at [sp0-104, sp0), which the caller chain of every call in this
   segment is read from, AND the three spill words [s1+0x20] / [s1+0x28] / [s1+0x30] that S0 wrote and C2
   carries on.  (One region [s1+0x18, s1+0x50) would lose those three.) *)
Definition S1_pc1 : Z := AF_LLVMFuzzerTestOneInput + SEG_C1_off.
Definition s1_r_exp : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition s1_r_nn : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 56 64 [].
Definition s1_r_fl : YP09.region := YP09.mkRegion (Some 9%nat) 72 80 72 80 [].
Definition s1_facts0 : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) ] [] [].
Definition s1_ss0 : sstate := mkSS S1_pc1 sr_atoms [s1_r_exp; s1_r_nn; s1_r_fl] None s1_facts0.
(* the runtime shadow base lives in s10, which is register x26, i.e. atom 26, from C1 to C2 *)
Definition s1_Bx : sv := SOff 26 0.
Definition s1_SH : list shent := [].
Definition s1_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Lemma s1_alu_and1 : forall x, 0 <= x < M64 ->
alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 1) = Z_to_bv 64 (x mod 2).
Proof.
intros x Hx. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
rewrite (zcanon_id x) by exact Hx. change (zcanon 1) with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma s1_cond_and1 : forall (Ez : env) (v : Z), ew Ez 16 = w64 v -> 0 <= v < 256 ->
branch_taken BC_EQ (sv_denot Ez (SAlu ALU_AND (SOff 16 0) (SLit 1))) (sv_denot Ez (SLit 0)) = (v mod 2 =? 0).
Proof.
intros Ez v H16 Hv. cbn [branch_taken sv_denot].
rewrite H16. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite s1_alu_and1 by (unfold M64; lia).
pose proof (Z.mod_pos_bound v 2 ltac:(lia)) as Hm.
destruct (Z.eqb_spec (v mod 2) 0) as [Hz | Hz].
- rewrite Hz. apply bv_eqb_eq. reflexivity.
- apply Bool.not_true_is_false. intros Hc. apply bv_eqb_eq in Hc.
apply (f_equal bv_unsigned) in Hc. rewrite !unsigned_lit_small in Hc by lia. lia.
Qed.


Variable WK : swalk.
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
Hypothesis HEV : 6 <= sw_ev WK.
Hypothesis HLIVE : 2 * 65535 <= sw_live WK.
Hypothesis HTRACE : rt_trace_in_stmt SEGS (sw_ra WK) (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
(BASE + AF_LLVMFuzzerTestOneInput + 0x328) (BASE + AF_LLVMFuzzerTestOneInput + 0x51c)
(BASE + AF_LLVMFuzzerTestOneInput + 0x640) (BASE + AF_LLVMFuzzerTestOneInput + 0x634)
(BASE + AF_LLVMFuzzerTestOneInput + 0x7b0) (BASE + AF_LLVMFuzzerTestOneInput + 0x7b8) (as_universe B).
(* ---- the write permission for the three one-word regions of the segment, at any point of it: the run asks
   for it again after every station, and only each region's base and window matter (the chunks it has
   collected do not), so one lemma serves every run of the entry block. ---- *)
Lemma s1_awr : forall (Ez : env) (c1 c2 c3 : list YP09.chunk) (sp0 sp1v : Z) (FP : list (Z * Z))
(bl0 blc : list (Z * Z)) (ly : alayout) (own : list (Z * Z)),
bv_unsigned (ew Ez 9) = sp1v -> - sw_stk WK <= sp1v - sp0 + 24 -> sp1v - sp0 + 80 <= 0 ->
awr_ok Ez [YP09.mkRegion (Some 9%nat) 24 32 24 32 c1; YP09.mkRegion (Some 9%nat) 56 64 56 64 c2;
YP09.mkRegion (Some 9%nat) 72 80 72 80 c3] (sw_stk WK) sp0 FP bl0 blc ly own.
Proof.
intros Ez c1 c2 c3 sp0 sp1v FP bl0 blc ly own U9 Hlo Hhi.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1v - sp0));
[ reflexivity | cbn [YP09.r_base]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1v - sp0));
[ reflexivity | cbn [YP09.r_base]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1v - sp0));
[ reflexivity | cbn [YP09.r_base]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
apply awr_ok_nil.
Qed.

(* ---- S1's entry block: cut C1 rebuilt as the walk's symbolic state at 0x82b78, with the two premises a run
   asks for besides it (the shadow table is empty here: the block up to the malloc call has no ASan check),
   and the write permission for the three spill words the block stores. ---- *)
Lemma s1_entry : forall (cx : rtcx SEGS) ly3 S3 W3 (regs3 : bvmap 5 word) mem3 md3 bs,
sc_base SEGS B ameter_triv WK cx ->
cut_C1 SEGS B ameter_triv WK scene_geom_asan cx ly3 S3 W3 regs3 mem3 md3 bs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs3 [])) s1_ss0
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + S1_pc1)) mem3 (seg_rom SEGS))) /\
sh_ok SEGS s1_Bx s1_SH (Eimg (Ereg regs3 [])) (mrestrict (w_H W3) mem3) /\
awr_ok (Eimg (Ereg regs3 [])) (ss_mem s1_ss0) (sw_stk WK) (spZ (c_regs cx)) []
(ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(sg_cid scene_geom_asan, c_fpos cx)].
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs HBASE HC1.
destruct HBASE as (HB0 & Hsp1).
destruct HB0 as (HPRE & Hra & H10 & H11 & Hpn & Hfrs & Hnev & Hlive & Hrod & Hsink & Hfd & Hfs & Hmok).
destruct HC1 as (HJ & Hab & Hbb & HFR & HSV & HSBG & HSHi & HSHk & HOPEN & HIMG & HIN & HMAC &
V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_shb & V_blki & V_blk & V_exp & V_mac & V_shexp & V_flags & V_u16 & V_rest & V_cur & V_step & V_s7v).
cbn [vat scene_geom_asan sg1_sp1] in V_sp1.
unfold RV_s1 in V_sp1.
destruct HIMG as (Hsp & Hgp & Htp & Hrod3).
destruct HJ as (HJ3 & Hfrs3 & Hmle).
pose proof HPRE as (HAR0 & Hra1 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & Hstk00 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ3 as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfr3 & Hnev3 & Hk3 & F1 & F2 & F3 & F4 & Hgone3 & Hpres3 & Hstatic3 & F5 & HQT3).
pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hmb.
assert (Hsp1lo : spZ (c_regs cx) - 256 <= c_sp1 cx) by (rewrite Hsp1; lia).
assert (Hsp1hi : c_sp1 cx <= spZ (c_regs cx) - 224) by (rewrite Hsp1; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 []) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 [] 9%nat 9%bv eq_refl); exact V_sp1).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
split; [|split].
- rewrite restrict_mkst_fx. unfold s1_ss0.
apply (pa_entry_st_ok_full E S1_pc1 sr_atoms regs3 [s1_r_exp; s1_r_nn; s1_r_fl] s1_facts0 (mrestrict (w_H W3) mem3)).
  + subst E; apply regs_ok_Eimg_Ereg.
  + vm_compute; reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil;
unfold s1_r_exp, s1_r_nn, s1_r_fl, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite U9; (split; [lia|]); (split; [lia|]); (split; [|constructor]);
intros o Ho; apply (apresent_writable SEGS); apply Hpres3; lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s1_r_exp, s1_r_nn, s1_r_fl.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9. repeat split; lia.
  + unfold s1_facts0. split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
split; [|exact I]. split; [lia|]. split; [|lia].
rewrite Hsp1. change (2 ^ 5) with 32. rewrite Z.mul_comm. apply Z_mod_mult.
- apply Forall_nil.
- unfold s1_ss0; cbn [ss_mem].
apply (s1_awr E [] [] [] (spZ (c_regs cx)) (c_sp1 cx)); [exact U9 | lia | lia].
Qed.

(* ---- the caller chain at any state of the segment: cgif_file_fuzzer A/ACf5.v:172-186 rt_chain, over the
   13 saved words the cut carries (`sc_saves`).  Every call of the walk needs it for `chain_pre`. ---- *)
Lemma s1_chain : forall (cx : rtcx SEGS) (W' : world SEGS) (mem' : word -> option byte) (sp' : Z),
afn_pre SEGS B (sw_stk WK) (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] ->
(forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H (c_W cx)) (c_mem cx) a) ->
sc_saves SEGS cx W' mem' ->
alloc_ceiling <= spZ (c_regs cx) -> sp' + 16 <= spZ (c_regs cx) ->
achain (c_ly cx) (aview SEGS (w_H W') mem') sp' (spZ (c_regs cx)) (rt_ch cx).
Proof.
intros cx W' mem' sp' HPRE Hkept HSV Hceil Hsp'.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk00 & Hceil' & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (HSV 0 ltac:(lia)) as Hs8. pose proof (HSV 1 ltac:(lia)) as Hs16.
cbn [Z.to_nat nth sc_saved_regs] in Hs8, Hs16.
replace (spZ (c_regs cx) - 8 - 8 * 0) with (spZ (c_regs cx) - 8) in Hs8 by lia.
replace (spZ (c_regs cx) - 8 - 8 * 1) with (spZ (c_regs cx) - 16) in Hs16 by lia.
assert (Hal8 : spZ (c_regs cx) mod 8 = 0).
{ pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as Hd16.
rewrite Hal16, Z.add_0_r in Hd16. rewrite Hd16.
replace (16 * (spZ (c_regs cx) / 16)) with (2 * (spZ (c_regs cx) / 16) * 8) by lia.
apply Z_mod_mult. }
unfold rt_ch.
destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
- apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W') mem')
(spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp' Hch ltac:(lia) Hkept
Hs8 Hs16 Hra4 Hceil Hal8 ltac:(lia) Hsp').
- left. split; [right; left; lia | reflexivity].
Qed.

(* ================================================================================================================
   THE WALK, C1 (0x82b78) -> C2 (0x82ca8)
   ================================================================================================================ *)
(* reac_scene_placeholder, the source of the fill loop (P_LLVMFuzzerTestOneInput.v:128-129). *)
Definition s1_PL : Z := 0x20e80.
Definition s1_PLN : Z := 8904.
(* Its bytes are in the image's file pages, so EVERY state reads them: `mbyte` falls back to `seg_rom`
   whenever the state's own memory has no byte there, and the restriction can only remove a byte that the
   image still gives.  Decided on the image, so the fill loop's load needs no hypothesis of its own. *)
Lemma s1_pl_rom : forall i, 0 <= i < s1_PLN -> seg_rom SEGS (Z_to_bv 64 (s1_PL + i)) <> None.
Proof.
assert (Hb : forallb (fun k => match seg_rom SEGS (Z_to_bv 64 (s1_PL + Z.of_nat k)) with
Some _ => true | None => false end) (seq 0 8904) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. intros i Hi. unfold s1_PLN in Hi.
assert (Hin : In (Z.to_nat i) (seq 0 8904)).
{ apply in_seq. split; [apply Nat.le_0_l|]. rewrite Nat.add_0_l.
change 8904%nat with (Z.to_nat 8904). apply Z2Nat.inj_lt; lia. }
specialize (Hb _ Hin). rewrite Z2Nat.id in Hb by lia.
destruct (seg_rom SEGS (Z_to_bv 64 (s1_PL + i))); [discriminate | discriminate Hb].
Qed.
Lemma s1_byte_some : forall (m : word -> option byte) (a : Z),
seg_rom SEGS (Z_to_bv 64 a) <> None -> exists v, 0 <= v < 256 /\ val_mem SEGS m a 1 v.
Proof.
intros m a Ha. destruct (mbyte SEGS m a) as [b|] eqn:Hb.
- exists (bv_unsigned b). pose proof (u8_range b) as Hr. split; [exact Hr|].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
assert (Hle : YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
{ unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (cbn; lia). apply Z.mod_small; lia. }
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb.
f_equal. rewrite Hle. symmetry. apply Z_to_bv_bv_unsigned.
- exfalso. unfold mbyte in Hb. destruct (m (Z_to_bv 64 a)); [discriminate | exact (Ha Hb)].
Qed.

(* A present byte, as a one-byte value. *)
Lemma s1_val_mem_byte : forall (m : word -> option byte) (a : Z) (b : byte),
mbyte SEGS m a = Some b -> val_mem SEGS m a 1 (bv_unsigned b).
Proof.
intros m a b Hb k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
pose proof (u8_range b) as Hr.
assert (Hle : YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
{ unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (cbn; lia). apply Z.mod_small; lia. }
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb.
f_equal. rewrite Hle. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma s1_nth_map_seq : forall {A : Type} (g : nat -> A) (N j : nat) (d : A), (j < N)%nat ->
nth j (map g (seq 0 N)) d = g j.
Proof.
intros A g N j d Hj. rewrite (nth_indep _ d (g 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
(* C2's body contents are existential: read them off a state where every byte of the block is present. *)
Definition s1_bytes (m : word -> option byte) (p n : Z) : list byte :=
map (fun k => match mbyte SEGS m (p + Z.of_nat k) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n)).
Lemma s1_garr8_present : forall (m : word -> option byte) (p n : Z), 0 <= n ->
(forall j, 0 <= j < n -> mbyte SEGS m (p + j) <> None) ->
Z.of_nat (length (s1_bytes m p n)) = n /\ garr8 SEGS m p (u8s (s1_bytes m p n)).
Proof.
intros m p n Hn Hp. unfold s1_bytes. split.
- rewrite length_map, length_seq. lia.
- intros j Hj. unfold u8s in *. rewrite length_map, length_map, length_seq in Hj.
rewrite map_map, (s1_nth_map_seq _ _ _ 0 Hj).
specialize (Hp (Z.of_nat j) ltac:(lia)).
destruct (mbyte SEGS m (p + Z.of_nat j)) as [b|] eqn:Hb; [|exfalso; exact (Hp eq_refl)].
split; [exact (s1_val_mem_byte m _ b Hb) | apply u8_range].
Qed.
(* The walk kit's read-only window is the listing's: the SHARED statement's Section h carried these two
   (lib/A/P_LLVMFuzzerTestOneInput.v:196-197 HWRLO / HWRHI at 0c703db40b0, a Theorem Labs lane 03:35Z) until the 04:04Z ruling made
   them segment-Section bindings; the composition discharges both by reflexivity. *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* The GOT word of reac_scene_placeholder (listing object A_OBJ 4, 0x9c388 in .got, read by `auipc`/`ld`
   0x82bb0-0x82bb4) holds the placeholder's address.  In the minimal form a Theorem Labs lane ruled for the shared
   statement's HRO_TT (03:48Z): only the two negative conditions on the eight bytes are taken, and the image
   half -- the word is in the relocation-read-only window and its file bytes are 0x20e80 -- is decided below.
   OWNER: the glue, as for HRO_TT -- two Theorem Labs lanes (B's tables) with a third (the start-up
   certificate), the owners P_LLVMFuzzerTestOneInput.v:247-248 names for the static-image facts of this walk. *)
Hypothesis HOWN_PLGOT : forall i, 0 <= i < 8 ->
~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4).
Lemma s1_got_rom : forall k, (k < 8)%nat ->
seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 4) + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte s1_PL 8 k)).
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity |]). exfalso. lia. Qed.
Lemma s1_got_pl : forall (Hh : word -> bool) (mem : word -> option byte),
arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS Hh mem) ->
val_mem SEGS (mrestrict Hh mem) (VAL (A_OBJ 4)) 8 s1_PL.
Proof.
intros Hh mem HRO k Hk.
assert (EV : VAL (A_OBJ 4) = 0x9c388) by (vm_compute; reflexivity).
assert (Hk8 : 0 <= Z.of_nat k < 8) by lia.
destruct (HOWN_PLGOT (Z.of_nat k) Hk8) as (Hno & Hne).
assert (Hin : (exists s, In s SEGS /\ seg_writable s = false /\
Z.of_N (seg_base s) <= VAL (A_OBJ 4) + Z.of_nat k < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/
(sw_rlo WK <= VAL (A_OBJ 4) + Z.of_nat k < sw_rhi WK)).
{ right. rewrite HWRLO, HWRHI, EV.
assert (ERLO : RLO = 0x9b1b0) by reflexivity. assert (ERHI : RHI = 0x9c410) by reflexivity.
rewrite ERLO, ERHI. lia. }
pose proof (HRO _ Hin Hno Hne) as Hv.
rewrite (s1_got_rom k Hk) in Hv. cbn [option_map] in Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict Hh mem) (VAL (A_OBJ 4) + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
(* The placeholder's shadow is the runtime's zero range (P_LLVMFuzzerTestOneInput.v:235 HZS_PL). *)
Hypothesis HZS_PL : in_zs B s1_PL s1_PLN.

(* ---- the registers every station of the segment carries, and the bytes the entry block writes ---- *)
Definition s1_rk (sp0 sp1 sF F np s7v cur rest : Z) (regs : bvmap 5 word) : Prop :=
getr regs 2 = w64 sp1 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 sp0 /\ getr regs 9 = w64 sp1 /\ getr regs 18 = w64 s7v /\ getr regs 19 = w64 sF /\
getr regs 21 = w64 rest /\ getr regs 22 = w64 cur /\ getr regs 23 = w64 F /\ getr regs 24 = w64 np /\
getr regs 25 = w64 (F + 32) /\ getr regs 26 = w64 SHADOW_OFF /\ getr regs 27 = w64 (F + 144).
Definition s1_prot (sp1 a : Z) : Prop :=
sp1 + 24 <= a < sp1 + 32 \/ sp1 + 56 <= a < sp1 + 64 \/ sp1 + 72 <= a < sp1 + 80.
(* `seqz a0,s8 / add a0,s8,a0` (0x82b90-0x82b94): a0 = n' + (n' =? 0) = n''. *)
Lemma s1_nn_val : forall (Ez : env) (v : Z), 0 <= v < 2 ^ 64 -> ew Ez 24 = w64 v ->
sv_denot Ez (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1))) = w64 (if v =? 0 then 1 else v).
Proof.
intros Ez v Hv H24. cbn [sv_denot]. rewrite H24. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. rewrite !zalu64_sound.
unfold zalu64. rewrite !Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id v) by (unfold M64; lia). change (zcanon 1) with 1.
destruct (Z.ltb_spec v 1) as [Hlt | Hge].
- assert (Hv0 : v = 0) by lia. subst v. vm_compute. reflexivity.
- destruct (Z.eqb_spec v 0) as [-> | Hne]; [lia|].
change (zcanon (zcanon 0)) with 0. rewrite Z.add_0_r. reflexivity.
Qed.
(* `andi a6,1` as the cut's flag byte: the two forms of the low bit. *)
Lemma s1_land1 : forall v, 0 <= v -> Z.land v 1 = v mod 2.
Proof.
intros v Hv. pose proof (Z.land_ones v 1 ltac:(lia)) as H.
change (Z.ones 1) with 1 in H. change (2 ^ 1) with 2 in H. exact H.
Qed.
(* A doubleword a run has left in a region's chunk, read back as a semantic word. *)
Lemma s1_chunk_word : forall (Ez : env) (m : word -> option byte) (base off : Z) (e : sv) (v : Z),
YP09.chunk_ok SEGS Ez m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot Ez e = w64 v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS m (base + off) 8 v.
Proof.
intros Ez m base off e v HC He Hv k Hk.
destruct (HC (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2.
rewrite Hb2. injection Hb1 as Hb1. rewrite <- Hb1, He.
rewrite <- (le_byte_of_word (w64 v) k Hk). unfold w64.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* `beqz r` on a register atom, and `bltu r1,r2` on two register atoms, as integer tests. *)
Lemma s1_beq0 : forall (Ez : env) (i : nat) (x : Z), ew Ez i = w64 x -> 0 <= x < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot Ez (SOff i 0)) (sv_denot Ez (SLit 0)) = (x =? 0).
Proof.
intros Ez i x H Hx. cbn [branch_taken sv_denot]. rewrite H. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
destruct (Z.eqb_spec x 0) as [-> | Hne]; [apply bv_eqb_eq; reflexivity |].
apply Bool.not_true_is_false. intros Hc. apply bv_eqb_eq in Hc.
apply (f_equal bv_unsigned) in Hc. rewrite !unsigned_lit_small in Hc by lia. lia.
Qed.
Lemma s1_bltu : forall (Ez : env) (i j : nat) (x y : Z), ew Ez i = w64 x -> ew Ez j = w64 y ->
0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot Ez (SOff i 0)) (sv_denot Ez (SOff j 0)) = (x <? y).
Proof.
intros Ez i j x y Hi Hj Hx Hy. unfold branch_taken. rewrite bv_ltu_unsigned. cbn [sv_denot].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, Hi, Hj. unfold w64.
rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
(* A run whose state has no region writes nothing. *)
Lemma s1_norun_keep : forall (Ez : env) (W : world SEGS) (m m' : word -> option byte),
frame_of Ez [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros Ez W m m' HFr a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin. cbn in Hin. destruct Hin.
Qed.
Lemma s1_atom_val : forall (Ez : env) (k : nat) (v : Z), ew Ez k = w64 v -> 0 <= v < 2 ^ 64 ->
sv_denot Ez (SOff k 0) = w64 v.
Proof.
intros Ez k v H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
Qed.
Lemma s1_rk_kept : forall sp0 sp1 sF F np s7v cur rest (regs regs' : bvmap 5 word),
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
s1_rk sp0 sp1 sF F np s7v cur rest regs -> s1_rk sp0 sp1 sF F np s7v cur rest regs'.
Proof.
intros sp0 sp1 sF F np s7v cur rest regs regs' HK (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
unfold s1_rk. repeat split; rewrite HK by (cbn; tauto); assumption.
Qed.
Lemma s1_rk_pres : forall sp0 sp1 sF F np s7v cur rest (regs regs' : bvmap 5 word),
aregs_preserved regs regs' -> s1_rk sp0 sp1 sF F np s7v cur rest regs -> s1_rk sp0 sp1 sF F np s7v cur rest regs'.
Proof.
intros sp0 sp1 sF F np s7v cur rest regs regs' HP. apply s1_rk_kept.
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- getr _ ?rr = _ => let z := eval vm_compute in (bv_unsigned rr) in
exact (HP z ltac:(unfold acallee_saved; lia)) end |]).
destruct Hr.
Qed.
(* the GOT word of reac_scene_placeholder (listing object 4), as a read-only region *)
Definition s1_got_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit s1_PL))].
Lemma s1_atom_reg : forall (Ez : env) (k : nat), sv_denot Ez (SOff k 0) = ew Ez k.
Proof. intros Ez k. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* A run whose only region is the read-only GOT word writes nothing. *)
Lemma s1_got_keep : forall (Ez : env) (W : world SEGS) (m m' : word -> option byte),
frame_of Ez [s1_got_region] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros Ez W m m' HFr a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin Hx. cbn [windows map s1_got_region YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [E1 | []]. injection E1 as <- <- <-. lia.
Qed.
(* The three windows of the entry block are exactly the bytes it may write. *)
Lemma s1_win : forall (Ez : env) (c1 c2 c3 : list YP09.chunk) (sp1v : Z),
bv_unsigned (ew Ez 9) = sp1v ->
forall b wlo whi a,
In (b, wlo, whi) (windows [YP09.mkRegion (Some 9%nat) 24 32 24 32 c1;
YP09.mkRegion (Some 9%nat) 56 64 56 64 c2; YP09.mkRegion (Some 9%nat) 72 80 72 80 c3]) ->
base_val Ez b + wlo <= a < base_val Ez b + whi -> s1_prot sp1v a.
Proof.
intros Ez c1 c2 c3 sp1v U9 b wlo whi a Hin Hr.
cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [E1 | [E1 | [E1 | []]]]; injection E1 as <- <- <-;
cbn [base_val] in Hr; rewrite U9 in Hr; unfold s1_prot; lia.
Qed.
(* ---- register / memory keeping between two states of one world ---- *)
Definition s1_keep_regs (keep : list (bv 5)) (regs regs' : bvmap 5 word) : Prop :=
forall r, In r keep -> getr regs' r = getr regs r.
Definition s1_keep_mem (W : world SEGS) (body n : Z) (mem mem' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + n) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a.
(* what the fill loop leaves alone (it writes a0, a1, a4; the two inline ASan checks write a5 and a6) *)
Definition s1_fill_keep : list (bv 5) :=
[1; 2; 3; 4; 8; 9; 12; 13; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* what the xor loop leaves alone (it writes a0 .. a5, s5 and s6) *)
Definition s1_xor_keep : list (bv 5) :=
[1; 2; 3; 4; 8; 9; 16; 17; 18; 19; 20; 23; 24; 25; 26; 27]%bv.

(* ================================================================================================================
   THE TWO LOOPS, as step lemmas over named invariants.  Both run in the world W of the state after
   __wrap_malloc returned, with the layout (ly, S) of that state: no call happens inside a loop, so only the
   memory (and the model's lazy backing) changes from turn to turn.
   ================================================================================================================ *)
(* The loop context: the journal from the entry, the new block (body, nn) and its write permission
   (awr_byte case 3, as `sc_blk_ok` states it for C2). *)
Definition s1_lctx (cx : rtcx SEGS) (ly : alayout) (S : astate) (W : world SEGS) (body nn : Z)
(mem : word -> option byte) (md : Model) : Prop :=
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly S W mem md 1 /\
In (body, nn) (ablocks B ly S) /\ 1 <= nn <= 65535 /\
(forall a, body <= a < body + nn ->
awr_byte (sw_stk WK) (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) ly [(8, c_fpos cx)] a).
(* FILL, at the loop head 0x82bbc, turn i of n' (here the block is (body, n'), n' >= 1):
   a1 = i, a2 = &reac_scene_placeholder, a3 = 0x458, a7 = body, s8 = n', s10 = the shadow base. *)
Definition s1_fill_inv (cx : rtcx SEGS) (ly : alayout) (S : astate) (W : world SEGS) (body np i : Z)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
s1_lctx cx ly S W body np mem md /\ 0 <= i < np /\
getr regs 11 = w64 i /\ getr regs 12 = w64 s1_PL /\ getr regs 13 = w64 0x458 /\
getr regs 17 = w64 body /\ getr regs 24 = w64 np /\ getr regs 26 = w64 SHADOW_OFF.
(* XOR, at the loop head 0x82c40, turn j of cnt = min(rest, n'): the input cursor cur + j is in a0 and s6,
   body + j in a1 and a2, the count left in s5.  The input bytes [cur, cur + cnt) lie in a block (p, n) of the
   same layout, apart from the new block. *)
Definition s1_xor_inv (cx : rtcx SEGS) (ly : alayout) (S : astate) (W : world SEGS) (body nn p n cur cnt j : Z)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
s1_lctx cx ly S W body nn mem md /\ 0 <= j < cnt /\ cnt <= nn /\
In (p, n) (ablocks B ly S) /\ p <= cur /\ cur + cnt <= p + n /\ (p + n <= body \/ body + nn <= p) /\
getr regs 10 = w64 (cur + j) /\ getr regs 22 = w64 (cur + j) /\
getr regs 11 = w64 (body + j) /\ getr regs 12 = w64 (body + j) /\
getr regs 21 = w64 (cnt - j) /\ getr regs 26 = w64 SHADOW_OFF.
(* One turn of FILL, 0x82bbc .. 0x82c04: the placeholder load's ASan check (0x82bc4-0x82bd4, report branch
   0x82bd4 -> 0x82c14 -> 0x82c1c) and the body store's (0x82be4-0x82bf4, report branch 0x82bf4 -> 0x82c08 ->
   0x82c10 -> 0x83194) are each decided NOT TAKEN by an obligation `range_addressable` of the one byte
   checked; the back edge `bne s8,a1` 0x82c00 goes to the next turn or out through `j` 0x82c04. *)
Lemma s1_fill_step : forall cx ly S W body np i regs mem md (Q : world SEGS -> config -> Prop),
s1_fill_inv cx ly S W body np i regs mem md ->
(forall regs' mem' md', i + 1 < np -> s1_fill_inv cx ly S W body np (i + 1) regs' mem' md' ->
s1_keep_regs s1_fill_keep regs regs' -> s1_keep_mem W body np mem mem' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x344)) mem' (seg_rom SEGS)) md') Q) ->
(forall regs' mem' md', i + 1 = np -> s1_lctx cx ly S W body np mem' md' ->
s1_keep_regs s1_fill_keep regs regs' -> s1_keep_mem W body np mem mem' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x3a8)) mem' (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x344)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W body np i regs mem md Q HI HNEXT HEXIT.
pose proof HI as (HL & Hi & R11 & R12 & R13 & R17 & R24 & R26).
pose proof HL as (HJ & Hin & Hnp & Hawr).
pose proof (proj1 HJ) as HAR.
assert (Hrq : req_size np = np) by (unfold req_size; destruct (Z.eqb_spec np 0); lia).
destruct (al_blocks _ _ LAWS ly S W mem md body np HAR Hin) as (Hb16 & Hb4096 & Hbceil & _ & _).
rewrite Hrq in Hbceil.
pose proof ASAN_CEIL_range as ((Hac1 & Hac2) & _). unfold ASAN_CEIL in Hac1, Hac2.
(* the back edge `bne s8,a1` 0x82c00, with s8 = n' and a1 = i + 1 *)
assert (BNE : forall Ez, ew Ez 24 = w64 np -> ew Ez 11 = w64 (i + 1) ->
branch_taken BC_NE (sv_denot Ez (SOff 24 0)) (sv_denot Ez (SOff 11 0)) = negb (np =? i + 1)).
{ intros Ez H24 H11. cbn [branch_taken sv_denot]. rewrite H24, H11. unfold w64.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
destruct (Z.eqb_spec np (i + 1)) as [Heq | Hne].
- rewrite Heq, (proj2 (bv_eqb_eq (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (i + 1))) eq_refl). reflexivity.
- destruct (bv_eqb (Z_to_bv 64 np) (Z_to_bv 64 (i + 1))) eqn:Hb; [|reflexivity].
exfalso. apply bv_eqb_eq in Hb. apply (f_equal bv_unsigned) in Hb.
rewrite !unsigned_lit_small in Hb by lia. lia. }
(* ---- the store 0x82bfc and the back edge, from a fresh entry state whose only region is the stored byte
   body + i (a0), with its window: a plain run (no ASan check is left in the turn). ---- *)
assert (TAIL : forall regs1 mem1 md1,
s1_lctx cx ly S W body np mem1 md1 ->
getr regs1 10 = w64 (body + i) -> getr regs1 11 = w64 (i + 1) ->
s1_keep_regs s1_fill_keep regs regs1 -> s1_keep_mem W body np mem mem1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + 0x384)) mem1 (seg_rom SEGS)) md1) Q).
{ intros regs1 mem1 md1 HL1 Q10 Q11 KR1 KM1.
pose proof HL1 as (HJ1 & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem1 md1 body np (proj1 HJ1) Hin) as (_ & _ & _ & _ & Hbp1 & _).
remember (Eimg (Ereg regs1 [])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r)
by (intros n r Hn; subst E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U10 : bv_unsigned (ew E1 10) = body + i)
by (rewrite (EE1 10%nat 10%bv eq_refl), Q10; unfold w64; apply unsigned_lit_small; lia).
assert (HAG1 : env_agree 32 (Ereg regs1 []) E1)
by (split; [intros n Hn; subst E1; apply Eimg_low; unfold A_TEXT; lia | subst E1; reflexivity]).
assert (E24 : ew E1 24 = w64 np)
by (rewrite (EE1 24%nat 24%bv eq_refl), (KR1 24%bv ltac:(unfold s1_fill_keep; cbn; tauto)); exact R24).
assert (E11 : ew E1 11 = w64 (i + 1)) by (rewrite (EE1 11%nat 11%bv eq_refl); exact Q11).
assert (HS1 : st_ok_pi SEGS VAL E1 (mkSS 900 sr_atoms [YP09.mkRegion (Some 10%nat) 0 1 0 1 []] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + 900)) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E1. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbp1 (body + i + o) ltac:(rewrite Hrq; lia))).
- cbn. tauto.
- unfold facts_ok; cbn; tauto. }
paj_run_sh RUNP HS1 HJ1.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
intros a (r & Hr & Ha). destruct Hr as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha. apply Hawr. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
rename HFr into HFrT1. clear HF HG.
lazymatch type of HFrT1 with frame_of ?Ex ?rs ?m1 ?m2 =>
let rs' := eval vm_compute in rs in change (frame_of Ex rs' m1 m2) in HFrT1 end.
psrr_branch_pi RUNP BR HS1.
- (* taken: the next turn *)
rewrite (BNE E1 E24 E11) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
paj_run_to_sh RUNTOP HS1 HJ1 0x344.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
intros a (r & Hr & Ha). destruct Hr as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha. apply Hawr. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
rename HFr into HFrT2. clear HF HG.
lazymatch type of HFrT2 with frame_of ?Ex ?rs ?m1 ?m2 =>
let rs' := eval vm_compute in rs in change (frame_of Ex rs' m1 m2) in HFrT2 end.
lazymatch type of HS1 with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
pose proof (regs_kept_of_st_ok_pi E1 ssx (restrict (w_H W) msx) regs1 [] s1_fill_keep HS1 HAG1
ltac:(vm_compute; reflexivity)) as RKT;
pose proof (regs_kept_of_st_ok_pi E1 ssx (restrict (w_H W) msx) regs1 [] [10; 11]%bv HS1 HAG1
ltac:(vm_compute; reflexivity)) as RKT2;
cbn [ms_regs restrict] in RKT, RKT2;
pmkst HS1;
apply HNEXT; [lia | | intros r Hr; rewrite (RKT r Hr); exact (KR1 r Hr) |]
end.
+ unfold s1_fill_inv. split; [exact (conj HJ1 (conj Hin (conj Hnp Hawr)))|]. split; [lia|].
repeat split.
  * rewrite (RKT2 11%bv ltac:(cbn; tauto)). exact Q11.
  * rewrite (RKT 12%bv ltac:(unfold s1_fill_keep; cbn; tauto)), (KR1 12%bv ltac:(unfold s1_fill_keep; cbn; tauto)). exact R12.
  * rewrite (RKT 13%bv ltac:(unfold s1_fill_keep; cbn; tauto)), (KR1 13%bv ltac:(unfold s1_fill_keep; cbn; tauto)). exact R13.
  * rewrite (RKT 17%bv ltac:(unfold s1_fill_keep; cbn; tauto)), (KR1 17%bv ltac:(unfold s1_fill_keep; cbn; tauto)). exact R17.
  * rewrite (RKT 24%bv ltac:(unfold s1_fill_keep; cbn; tauto)), (KR1 24%bv ltac:(unfold s1_fill_keep; cbn; tauto)). exact R24.
  * rewrite (RKT 26%bv ltac:(unfold s1_fill_keep; cbn; tauto)), (KR1 26%bv ltac:(unfold s1_fill_keep; cbn; tauto)). exact R26.
+ intros a Ha Hn. rewrite <- (KM1 a Ha Hn).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + np) HFrT2) by
(exact Ha || exact Hn || (intros b wlo whi x Hw Hx; cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hw;
destruct Hw as [Ew | []]; injection Ew as <- <- <-; cbn [base_val] in Hx; rewrite U10 in Hx; lia)).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + np) HFrT1) by
(exact Ha || exact Hn || (intros b wlo whi x Hw Hx; cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hw;
destruct Hw as [Ew | []]; injection Ew as <- <- <-; cbn [base_val] in Hx; rewrite U10 in Hx; lia)).
reflexivity.
- (* not taken: out through `j` 0x82c04 *)
rewrite (BNE E1 E24 E11) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
paj_run_to_sh RUNTOP HS1 HJ1 0x3a8.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end.
intros a (r & Hr & Ha). destruct Hr as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha. apply Hawr. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
rename HFr into HFrT2. clear HF HG.
lazymatch type of HFrT2 with frame_of ?Ex ?rs ?m1 ?m2 =>
let rs' := eval vm_compute in rs in change (frame_of Ex rs' m1 m2) in HFrT2 end.
lazymatch type of HS1 with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
pose proof (regs_kept_of_st_ok_pi E1 ssx (restrict (w_H W) msx) regs1 [] s1_fill_keep HS1 HAG1
ltac:(vm_compute; reflexivity)) as RKT;
cbn [ms_regs restrict] in RKT;
pmkst HS1;
apply HEXIT; [lia | exact (conj HJ1 (conj Hin (conj Hnp Hawr))) | intros r Hr; rewrite (RKT r Hr); exact (KR1 r Hr) |]
end.
intros a Ha Hn. rewrite <- (KM1 a Ha Hn).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + np) HFrT2) by
(exact Ha || exact Hn || (intros b wlo whi x Hw Hx; cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hw;
destruct Hw as [Ew | []]; injection Ew as <- <- <-; cbn [base_val] in Hx; rewrite U10 in Hx; lia)).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + np) HFrT1) by
(exact Ha || exact Hn || (intros b wlo whi x Hw Hx; cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hw;
destruct Hw as [Ew | []]; injection Ew as <- <- <-; cbn [base_val] in Hx; rewrite U10 in Hx; lia)).
reflexivity. }
(* ---- the turn up to the store: one token run from the loop head, with fresh atoms for the two checked
   addresses (32 = &placeholder[i], 33 = body + i, each the alias of its `add`) and for the byte read (34).
   The facts on a1 decide `bltu a3,a0` 0x82bc0; each check is decided by its obligation. ---- *)
destruct (Z_lt_ge_dec i 8904) as [HiA | HiB].
- (* i < 8904: a4 = placeholder[i] *)
destruct (mbyte SEGS (mrestrict (w_H W) mem) (s1_PL + i)) as [bb|] eqn:Hbb.
2:{ exfalso. unfold mbyte in Hbb. destruct (mrestrict (w_H W) mem (Z_to_bv 64 (s1_PL + i))); [discriminate|].
exact (s1_pl_rom i ltac:(unfold s1_PLN; lia) Hbb). }
pose proof (u8_range bb) as Hbbr.
remember (Eimg (Ereg regs [w64 (s1_PL + i); w64 (body + i); w64 (bv_unsigned bb)])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r)
by (intros n r Hn; subst E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E11 : ew E0 11 = w64 i) by (rewrite (EE0 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew E0 12 = w64 s1_PL) by (rewrite (EE0 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew E0 13 = w64 0x458) by (rewrite (EE0 13%nat 13%bv eq_refl); exact R13).
assert (E17 : ew E0 17 = w64 body) by (rewrite (EE0 17%nat 17%bv eq_refl); exact R17).
assert (E26 : ew E0 26 = w64 SHADOW_OFF) by (rewrite (EE0 26%nat 26%bv eq_refl); exact R26).
assert (E32 : ew E0 32 = w64 (s1_PL + i))
by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = w64 (body + i))
by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E0 34 = w64 (bv_unsigned bb))
by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (UV : forall n v, ew E0 n = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 n) = v)
by (intros n v H Hv; rewrite H; unfold w64; apply unsigned_lit_small; exact Hv).
assert (UBx : U E0 (SOff 26 0) = SHADOW_OFF) by (apply (U_atom E0 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
assert (U32 : U E0 (SOff 32 0) = s1_PL + i) by (apply (U_atom E0 32 _ E32); unfold s1_PL; lia).
assert (U33 : U E0 (SOff 33 0) = body + i) by (apply (U_atom E0 33 _ E33); lia).
pose proof (ro_usable SEGS B LAWS ly S W mem md s1_PL s1_PLN HAR HZS_PL) as HRAPL.
assert (HS : st_ok_pi SEGS VAL E0
(mkSS 836 sr_atoms [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]] None
(mkFacts [(11%nat, mkAF 0 8903 0); (13%nat, mkAF 1112 1112 0); (26%nat, mkAF 2147450880 2147450880 0);
(32%nat, mkAF 134784 143687 0); (33%nat, mkAF 4096 140737479966720 0)] []
[(SAlu ALU_ADD (SOff 12 0) (SOff 11 0), SOff 32 0); (SAlu ALU_ADD (SOff 17 0) (SOff 11 0), SOff 33 0)]))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 836)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (UV 32%nat (s1_PL + i) E32) by (unfold s1_PL; lia).
split; [unfold s1_PL; lia|]. split; [unfold s1_PL; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. intros k Hk. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in Hk |- *.
assert (Hk0 : k = 0) by lia. subst k. exists bb. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot].
rewrite (UV 34%nat (bv_unsigned bb) E34) by lia. rewrite !Z.add_0_r.
rewrite unsigned_lit_small by lia. rewrite Z.shiftr_0_r. apply Z_to_bv_bv_unsigned.
  + rewrite !Z.add_0_r. exact Hbb.
- cbn. tauto.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (UV 11%nat i E11), (UV 13%nat 0x458 E13), (UV 26%nat SHADOW_OFF E26), (UV 32%nat (s1_PL + i) E32),
(UV 33%nat (body + i) E33) by (unfold s1_PL, SHADOW_OFF; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold s1_PL, SHADOW_OFF.
repeat split; try lia.
  + apply U_inj. rewrite U_SAlu, (U_atom E0 12 s1_PL E12), (U_atom E0 11 i E11), U32 by (unfold s1_PL; lia).
cbn [zalu_raw]. apply zcanon_id. unfold M64, s1_PL. lia.
  + apply U_inj. rewrite U_SAlu, (U_atom E0 17 body E17), (U_atom E0 11 i E11), U33 by lia.
cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (SHOK : sh_ok SEGS (SOff 26 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK s1_span.
all: lazymatch goal with
| |- range_addressable _ _ (U _ (SOff 33 0)) _ => rewrite U33;
eapply (obl_of_block SEGS B LAWS ly S W mem md E0 (SOff 26 0) (body + i) 1 body np HAR Hin);
[exact UBx | lia | rewrite Hrq; lia]
| |- range_addressable _ _ (U _ (SOff 32 0)) _ => rewrite U32;
eapply (obl_of_range SEGS (w_H W) mem E0 (SOff 26 0) (s1_PL + i) 1 s1_PL s1_PLN HRAPL);
[exact UBx | lia | unfold s1_PLN; lia]
| |- range_addressable _ _ _ _ => fail "s1_fill_step: unexpected obligation"
| |- awr_ok _ _ _ _ _ _ _ _ _ => apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]
| _ => idtac
end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
assert (HAGx : env_agree 32 (Ereg regs [w64 (s1_PL + i); w64 (body + i); w64 (bv_unsigned bb)]) Ex)
by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; rewrite HE0; apply Eimg_low; unfold A_TEXT; lia
| rewrite ?ed_ewset; rewrite HE0; reflexivity]);
pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs _ s1_fill_keep HS HAGx
ltac:(vm_compute; reflexivity)) as RKA;
cbn [ms_regs restrict] in RKA
end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
pmkst HS.
apply TAIL.
  + exact (conj HJ (conj Hin (conj Hnp Hawr))).
  + rewrite Ra0. exact E33.
  + rewrite Ra1, (UV 11%nat i E11) by lia. reflexivity.
  + intros r Hr. rewrite (RKA r Hr). reflexivity.
  + intros a Ha Hn.
refine (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + np) HFr _ a Ha Hn).
intros b wlo whi x Hw Hx. cbn [ss_mem windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hw.
destruct Hw as [Ew | []]. injection Ew as <- <- <-. lia.
- (* i >= 8904: a4 = 0 *)
remember (Eimg (Ereg regs [w64 0; w64 (body + i)])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r)
by (intros n r Hn; subst E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E11 : ew E0 11 = w64 i) by (rewrite (EE0 11%nat 11%bv eq_refl); exact R11).
assert (E13 : ew E0 13 = w64 0x458) by (rewrite (EE0 13%nat 13%bv eq_refl); exact R13).
assert (E17 : ew E0 17 = w64 body) by (rewrite (EE0 17%nat 17%bv eq_refl); exact R17).
assert (E26 : ew E0 26 = w64 SHADOW_OFF) by (rewrite (EE0 26%nat 26%bv eq_refl); exact R26).
assert (E33 : ew E0 33 = w64 (body + i))
by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (UV : forall n v, ew E0 n = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 n) = v)
by (intros n v H Hv; rewrite H; unfold w64; apply unsigned_lit_small; exact Hv).
assert (UBx : U E0 (SOff 26 0) = SHADOW_OFF) by (apply (U_atom E0 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
assert (U33 : U E0 (SOff 33 0) = body + i) by (apply (U_atom E0 33 _ E33); lia).
assert (HS : st_ok_pi SEGS VAL E0
(mkSS 836 sr_atoms [] None
(mkFacts [(11%nat, mkAF 8904 65534 0); (13%nat, mkAF 1112 1112 0); (26%nat, mkAF 2147450880 2147450880 0);
(33%nat, mkAF 4096 140737479966720 0)] []
[(SAlu ALU_ADD (SOff 17 0) (SOff 11 0), SOff 33 0)]))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 836)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (UV 11%nat i E11), (UV 13%nat 0x458 E13), (UV 26%nat SHADOW_OFF E26),
(UV 33%nat (body + i) E33) by (unfold SHADOW_OFF; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
repeat split; try lia.
apply U_inj. rewrite U_SAlu, (U_atom E0 17 body E17), (U_atom E0 11 i E11), U33 by lia.
cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (SHOK : sh_ok SEGS (SOff 26 0) (@nil shent) E0 (mrestrict (w_H W) mem)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK s1_span.
all: lazymatch goal with
| |- range_addressable _ _ (U _ (SOff 33 0)) _ => rewrite U33;
eapply (obl_of_block SEGS B LAWS ly S W mem md E0 (SOff 26 0) (body + i) 1 body np HAR Hin);
[exact UBx | lia | rewrite Hrq; lia]
| |- range_addressable _ _ _ _ => fail "s1_fill_step: unexpected obligation"
| |- awr_ok _ _ _ _ _ _ _ _ _ => apply awr_ok_nil
| _ => idtac
end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
assert (HAGx : env_agree 32 (Ereg regs [w64 0; w64 (body + i)]) Ex)
by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; rewrite HE0; apply Eimg_low; unfold A_TEXT; lia
| rewrite ?ed_ewset; rewrite HE0; reflexivity]);
pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs _ s1_fill_keep HS HAGx
ltac:(vm_compute; reflexivity)) as RKA;
cbn [ms_regs restrict] in RKA
end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
pmkst HS.
apply TAIL.
  + exact (conj HJ (conj Hin (conj Hnp Hawr))).
  + rewrite Ra0. exact E33.
  + rewrite Ra1, (UV 11%nat i E11) by lia. reflexivity.
  + intros r Hr. rewrite (RKA r Hr). reflexivity.
  + intros a Ha Hn.
refine (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + np) HFr _ a Ha Hn).
intros b wlo whi x Hw Hx. cbn [ss_mem windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hw. destruct Hw.
Qed.
(* One turn of XOR, 0x82c40 .. 0x82c88: the input load's check (0x82c40-0x82c4c, report branch 0x82c4c ->
   0x82c8c -> 0x82c94 -> 0x83198) and the body load's (0x82c50-0x82c60, report branch 0x82c60 -> 0x82c98 ->
   0x82ca4) are each decided NOT TAKEN by an obligation `range_addressable`; the store 0x82c78 is unchecked
   (the 0x82c60 check covers its byte); the back edge `bnez s5` 0x82c84 goes to the next turn or out through
   `j` 0x82c88 to C2. *)
Lemma s1_xor_step : forall cx ly S W body nn p n cur cnt j regs mem md (Q : world SEGS -> config -> Prop),
s1_xor_inv cx ly S W body nn p n cur cnt j regs mem md ->
(forall regs' mem' md', j + 1 < cnt -> s1_xor_inv cx ly S W body nn p n cur cnt (j + 1) regs' mem' md' ->
s1_keep_regs s1_xor_keep regs regs' -> s1_keep_mem W body nn mem mem' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x3c8)) mem' (seg_rom SEGS)) md') Q) ->
(forall regs' mem' md', j + 1 = cnt -> s1_lctx cx ly S W body nn mem' md' ->
s1_keep_regs s1_xor_keep regs regs' -> s1_keep_mem W body nn mem mem' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x430)) mem' (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x3c8)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W body nn p n cur cnt j regs mem md Q HI HNEXT HEXIT.
destruct HI as (HL & Hj & Hcnt & Hpn & Hpc & Hcc & Hdisj & R10 & R22 & R11 & R12 & R21 & R26).
pose proof HL as (HJ & Hbody & Hnn & HAWB).
pose proof HJ as (HAR & _).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpb & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hbody) as (_ & Hb4096 & Hbceil & Hbapp & Hbb & _).
assert (Hrqn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (Hrqb : nn <= req_size nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia).
assert (BYTE : forall a, apresent (w_H W) mem a -> exists v, 0 <= v < 256 /\ val_mem SEGS (mrestrict (w_H W) mem) a 1 v).
{ intros a [Hh [b Hb]]. pose proof (u8_range b) as Hr. exists (bv_unsigned b). split; [exact Hr|].
  intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
  assert (Hle : YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
  { unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
    replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
    rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (cbn; lia). apply Z.mod_small; lia. }
  cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh, Hb.
  f_equal. rewrite Hle. symmetry. apply Z_to_bv_bv_unsigned. }
destruct (BYTE (cur + j) (proj1 (Hpb (cur + j) ltac:(lia)))) as (vin & Hvin & Vin).
destruct (BYTE (body + j) (proj1 (Hbb (body + j) ltac:(lia)))) as (vb & Hvb & Vb).
clear BYTE.
remember (Eimg (Ereg regs [Z_to_bv 64 vin; Z_to_bv 64 vb])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 vin; Z_to_bv 64 vb]) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 vin)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vb)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U10 : bv_unsigned (ew E 10) = cur + j)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = cur + j)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = body + j)
  by (rewrite (EE 11%nat 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = body + j)
  by (rewrite (EE 12%nat 12%bv eq_refl), R12; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = cnt - j)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL E
  (mkSS 968 sr_atoms
    [YP09.mkRegion (Some 12%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
     YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
    (mkFacts [(10%nat, mkAF 4096 140737479966720 0); (11%nat, mkAF 4096 140737479966720 0);
              (12%nat, mkAF 4096 140737479966720 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 968)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U12. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). replace (body + j + o) with (body + j) by lia.
        exact (proj1 (Hbb (body + j) ltac:(lia))).
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (body + j) 0 1 (SOff 33 0) vb).
        -- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- cbn. lia.
        -- lia.
        -- rewrite Z.add_0_r. exact Vb.
    + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (cur + j) 0 1 (SOff 32 0) vin).
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- cbn. lia.
      -- lia.
      -- rewrite Z.add_0_r. exact Vin.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U12, U22. repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U11, U12, U26. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff 26 0) [mkSHE 12 0 1] E (mrestrict (w_H W) mem)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 26 0) 12 (body + j) 1 (body + j) 0 1).
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md body nn); [exact HAR | exact Hbody | lia | lia].
  - apply (U_atom E 26 SHADOW_OFF); [rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity | unfold SHADOW_OFF; lia].
  - apply (U_atom E 12 (body + j)); [rewrite (EE 12%nat 12%bv eq_refl), R12; reflexivity | lia].
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
(* the write permission of the two regions: only the body byte's window is writable *)
assert (AWR : forall (E' : env) cs, bv_unsigned (ew E' 12) = body + j ->
  awr_ok E' [YP09.mkRegion (Some 12%nat) 0 1 0 1 cs; YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]]
    (sw_stk WK) (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) ly [(8, c_fpos cx)]).
{ intros E' cs U12'. eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat (body + j)); [reflexivity | exact U12' | |].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (body + j) by lia. apply HAWB. lia.
  - apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (UB : U E (SOff 26 0) = SHADOW_OFF)
  by (apply (U_atom E 26 SHADOW_OFF); [rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity | unfold SHADOW_OFF; lia]).
assert (UA10 : U E (SOff 10 0) = cur + j)
  by (apply (U_atom E 10 (cur + j)); [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]).
assert (UA11 : U E (SOff 11 0) = body + j)
  by (apply (U_atom E 11 (body + j)); [rewrite (EE 11%nat 11%bv eq_refl), R11; reflexivity | lia]).
(* 0x82c40 .. 0x82c84: both checks decided by the token run, the loads, the xor and the store; it stops at bnez s5 *)
paj_run_tok RUN HS HJ SHOK s1_span.
{ rewrite UB, UA11. cbn [ms_mem mkst]. change (rd_of SEGS (mrestrict (w_H W) mem)) with (aview SEGS (w_H W) mem).
  apply (range_addressable_of_block SEGS B LAWS ly S W mem md body nn); [exact HAR | exact Hbody | lia | lia]. }
{ rewrite UB, UA10. cbn [ms_mem mkst]. change (rd_of SEGS (mrestrict (w_H W) mem)) with (aview SEGS (w_H W) mem).
  apply (range_addressable_of_block SEGS B LAWS ly S W mem md p n); [exact HAR | exact Hpn | lia | lia]. }
{ cbn [ss_mem]. apply AWR. exact U12. }
rename HFr into HFr1. clear HF HG.
set (mdv := with_vm_backing (m_vm_lazy md) mat md) in *; clearbody mdv.
assert (KW1 : forall b0 wlo whi a0,
  In (b0, wlo, whi) (windows [YP09.mkRegion (Some 12%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
     YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]]) ->
  base_val E b0 + wlo <= a0 < base_val E b0 + whi -> body <= a0 < body + nn).
{ intros b0 wlo whi a0 Hin Hr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U12 in Hr; lia. }
(* 0x82c84 bnez s5, s5 = cnt - (j + 1): taken back to the loop head 0x82c40, else `j` 0x82c88 to C2 0x82ca8 *)
psrr_branch_tok RUN BR HS SHOK s1_span;
rewrite branch_ne_U, U_SOff, U_SLit in Hc; cbn [ew ewset Nat.eqb] in Hc; rewrite U21 in Hc;
rewrite (zcanon_id (cnt - j + -1)) in Hc by (unfold M64; lia); change (zcanon 0) with 0 in Hc;
[ apply Bool.negb_true_iff, Z.eqb_neq in Hc; paj_run_to_tok RUNTO HS HJ SHOK s1_span 968
| apply Bool.negb_false_iff, Z.eqb_eq in Hc; paj_run_to_tok RUNTO HS HJ SHOK s1_span 1072 ];
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
  apply AWR; cbn [ew ewset Nat.eqb]; exact U12
| | lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ownx) end;
  apply AWR; cbn [ew ewset Nat.eqb]; exact U12
| ].
(* both arms: the registers, the kept registers and the kept memory of the final state *)
all: rename HFr into HFr2; clear HF HG;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv2 := m) in *; clearbody mdv2 end;
  pmkst HS;
  prreg HS (10%bv : bv 5) Q10; prreg HS (22%bv : bv 5) Q22; prreg HS (11%bv : bv 5) Q11;
  prreg HS (12%bv : bv 5) Q12; prreg HS (21%bv : bv 5) Q21;
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (HAG2 : env_agree 32 (Ereg regs [Z_to_bv 64 vin; Z_to_bv 64 vb]) E2)
      by (eapply env_agree_trans; [exact HAE | split; [intros k Hk; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]) end;
  pose proof (regs_kept_of_st_ok SEGS _ _ (restrict (w_H W) ms0) regs [Z_to_bv 64 vin; Z_to_bv 64 vb] s1_xor_keep HS HAG2 eq_refl) as RK;
  cbn [ms_regs restrict] in RK;
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + nn) HFr2) as K2;
  lazymatch type of K2 with ?P -> _ => assert (KW2 : P);
    [ intros b0 wlo whi a0 Hin Hr; vm_compute in Hin; destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
      cbn [base_val ew ewset Nat.eqb] in Hr; rewrite ?U12 in Hr; cbv beta; lia
    | specialize (K2 KW2) ] end;
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => body <= x < body + nn) HFr1 KW1) as K1.
- apply (HNEXT (ms_regs ms0) (ms_mem ms0) mdv2).
  + lia.
  + unfold s1_xor_inv. split; [exact (conj HJ (conj Hbody (conj Hnn HAWB)))|].
    do 6 (split; [first [lia | exact Hpn | exact Hdisj] |]).
    split; [rewrite Q10, U10; unfold w64; f_equal; lia|].
    split; [rewrite Q22, U22; unfold w64; f_equal; lia|].
    split; [rewrite Q11, U11; unfold w64; f_equal; lia|].
    split; [rewrite Q12, U12; unfold w64; f_equal; lia|].
    split; [rewrite Q21, U21; unfold w64; f_equal; lia|].
    rewrite (RK 26%bv ltac:(cbv; tauto)). exact R26.
  + intros r Hr. exact (RK r Hr).
  + intros a Ha Hna. rewrite (K2 a Ha Hna), (K1 a Ha Hna). reflexivity.
- apply (HEXIT (ms_regs ms0) (ms_mem ms0) mdv2).
  + lia.
  + exact (conj HJ (conj Hbody (conj Hnn HAWB))).
  + intros r Hr. exact (RK r Hr).
  + intros a Ha Hna. rewrite (K2 a Ha Hna), (K1 a Ha Hna). reflexivity.
Qed.
(* The loops closed by induction on the turns left. *)
Lemma s1_keep_regs_trans : forall keep r1 r2 r3,
s1_keep_regs keep r1 r2 -> s1_keep_regs keep r2 r3 -> s1_keep_regs keep r1 r3.
Proof. intros keep r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.
Lemma s1_keep_mem_trans : forall W body n m1 m2 m3,
s1_keep_mem W body n m1 m2 -> s1_keep_mem W body n m2 m3 -> s1_keep_mem W body n m1 m3.
Proof. intros W body n m1 m2 m3 H12 H23 a Ha Hn. rewrite (H23 a Ha Hn). exact (H12 a Ha Hn). Qed.
Lemma s1_fill_loop : forall cx ly S W body np (Q : world SEGS -> config -> Prop) (m : nat) i regs mem md,
np - i <= Z.of_nat m ->
s1_fill_inv cx ly S W body np i regs mem md ->
(forall regs' mem' md', s1_lctx cx ly S W body np mem' md' ->
s1_keep_regs s1_fill_keep regs regs' -> s1_keep_mem W body np mem mem' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x3a8)) mem' (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x344)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W body np Q m. induction m as [|m IH]; intros i regs mem md Hm HI HK.
- destruct HI as (_ & Hi & _). lia.
- apply (s1_fill_step cx ly S W body np i regs mem md Q HI).
+ intros regs' mem' md' Hlt HI' HKR HKM.
apply (IH (i + 1) regs' mem' md' ltac:(lia) HI').
intros regs'' mem'' md'' HC'' HKR' HKM'. apply HK; [exact HC'' | | ].
* exact (s1_keep_regs_trans _ _ _ _ HKR HKR').
* exact (s1_keep_mem_trans _ _ _ _ _ _ HKM HKM').
+ intros regs' mem' md' Heq HC' HKR HKM. exact (HK regs' mem' md' HC' HKR HKM).
Qed.
Lemma s1_xor_loop : forall cx ly S W body nn p n cur cnt (Q : world SEGS -> config -> Prop) (m : nat) j regs mem md,
cnt - j <= Z.of_nat m ->
s1_xor_inv cx ly S W body nn p n cur cnt j regs mem md ->
(forall regs' mem' md', s1_lctx cx ly S W body nn mem' md' ->
s1_keep_regs s1_xor_keep regs regs' -> s1_keep_mem W body nn mem mem' ->
SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x430)) mem' (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x3c8)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W body nn p n cur cnt Q m. induction m as [|m IH]; intros j regs mem md Hm HI HK.
- destruct HI as (_ & Hj & _). lia.
- apply (s1_xor_step cx ly S W body nn p n cur cnt j regs mem md Q HI).
+ intros regs' mem' md' Hlt HI' HKR HKM.
apply (IH (j + 1) regs' mem' md' ltac:(lia) HI').
intros regs'' mem'' md'' HC'' HKR' HKM'. apply HK; [exact HC'' | | ].
* exact (s1_keep_regs_trans _ _ _ _ HKR HKR').
* exact (s1_keep_mem_trans _ _ _ _ _ _ HKM HKM').
+ intros regs' mem' md' Heq HC' HKR HKM. exact (HK regs' mem' md' HC' HKR HKM).
Qed.

(* `getr (ms_regs ms) r = _` after a run: the register's symbolic value, computed once, as the goal. *)
Ltac s1_getr HS r :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
refine (eq_trans (st_ok_pi_restrict_reg H E ss ms r HS) _);
lazymatch goal with |- _ = ?rhs => change (sv_denot E e = rhs) end
end.

(* a register that a run left as the atom of a register k of the block's entry state:
   `getr (ms_regs ms) r = v` from `Hv : getr regs k = v` *)
Ltac s1_regk HS EE Hv :=
lazymatch goal with |- getr _ ?r = _ =>
s1_getr HS r;
lazymatch goal with |- sv_denot _ (SOff ?k 0) = _ =>
rewrite s1_atom_reg, (EE k (Z_to_bv 5 (Z.of_nat k)) eq_refl); exact Hv end end.
(* the restricted `frame_of` of the run that produced the goal's machine state, renamed *)
Ltac s1_lastfr K :=
lazymatch goal with |- SRr _ ?W (mkCfg ?m _) _ =>
lazymatch goal with H : frame_of _ _ _ (mrestrict (w_H W) (ms_mem m)) |- _ => rename H into K end end.
Theorem scene_seg_S1 : seg_S1_stmt (SK := SK) SEGS B ameter_triv WK scene_geom_asan.
Proof.
unfold seg_S1_stmt. intros cx POST HBASE HC2.
unfold sc_from_C1. intros ly3 S3 W3 regs3 mem3 md3 bs HC1.
pose proof (s1_entry cx ly3 S3 W3 regs3 mem3 md3 bs HBASE HC1) as (HS & SHOK & HAWR).
pose proof HBASE as (HB0 & Hsp1eq).
pose proof HB0 as (HAFN & Hra0 & Hp0 & Hn0 & Hpn & Hfrs0 & Hev0 & Hlive0 & HROD0 & HSNK0 & HFD0 & HSORT0 & HMOK0).
pose proof HC1 as (HJ0 & Hab & Hbb & HFRM & HSAV & HSHBG & HSHBI & HSHBL & HOPMAC & HIMG & HIN & HMACB &
V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_shb & V_blki & V_blk & V_exp & V_mac & V_shexp & V_flags & V_u16 &
V_rest & V_cur & V_step & V_s7v).
destruct HJ0 as (HJ & Hfrs3 & HMLE).
destruct HIMG as (Hsp3 & Hgp3 & Htp3 & HROD3).
cbn [vat sg1_sp0 sg1_sp1 sg1_F sg1_Fsp sg1_shF sg1_shbase sg1_blki sg1_blk sg1_expect sg1_mac sg1_shexp
sg1_flags sg1_u16 sg1_rest sg1_cur sg1_step sg1_s7v sg_cid sg_off_blki sg_off_blk sg_off_expect sg_off_mac
scene_geom_asan] in V_sp0, V_sp1, V_F, V_Fsp, V_shF, V_shb, V_blki, V_blk, V_exp, V_mac, V_shexp, V_flags,
V_u16, V_rest, V_cur, V_step, V_s7v.
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s5, RV_s6, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11, RV_a5, RV_a6 in
V_sp0, V_sp1, V_F, V_shF, V_shb, V_blki, V_blk, V_exp, V_flags, V_u16, V_rest, V_cur, V_s7v.
(* ---- the facts of the entry state the whole walk uses ---- *)
pose proof HAFN as (HAR0 & Hra1 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & Hstk00 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (Has : ASTACK = 16384) by reflexivity.
cbn [sg_cid scene_geom_asan] in Hfrs3.
pose proof HJ as (HARc & HlyJ & Hsecs3 & Hwle3 & Hio3 & Hfr3 & Hnev3 & Hk3 &
JK1 & JK2 & JK3 & JK4 & Hgone3 & Hpres3 & Hstk3 & JK5 & HQT3).
assert (Hfin3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HlyJ) as (_ & EFA & EFL).
assert (EFA3 : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS scene_geom_asan cx) by (rewrite EFA; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HARc Hfin3) as (HF4096 & HFceil & HFapp).
rewrite EFA3 in HF4096, HFceil, HFapp.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp.
assert (Hsp1rng : spZ (c_regs cx) - 256 < c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1eq. pose proof (Z.div_mod (spZ (c_regs cx) - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)). lia. }
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs3 [])) 9) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat regs3 [] 9%nat 9%bv eq_refl), V_sp1. apply unsigned_lit_small. lia. }
assert (E16 : ew (Eimg (Ereg regs3 [])) 16 = w64 (sc_flags bs))
by (rewrite (ew_Eimg_Ereg_nat regs3 [] 16%nat 16%bv eq_refl); exact V_flags).
assert (Hb0 : 0 <= bs 0 < 256) by (destruct (HIN 0 ltac:(lia)) as ((Hf1 & Hf2) & _); lia).
assert (Hfl256 : 0 <= sc_flags bs < 256) by (unfold sc_flags; lia).
assert (Hu16 : 0 <= sc_u16 bs <= 65535).
{ unfold sc_u16. destruct (HIN 1 ltac:(lia)) as ((Ha1 & Ha2) & _).
destruct (HIN 2 ltac:(lia)) as ((Hb1 & Hb2) & _). lia. }
assert (Hnpb : 0 <= sc_nprime scene_geom_asan bs <= 65535).
{ unfold sc_nprime. cbn [sg_scene_n scene_geom_asan]. destruct (Z.land (bs 0) 1 =? 0); lia. }
assert (Hnnb : 1 <= sc_nn scene_geom_asan bs <= 65535).
{ unfold sc_nn. destruct (Z.eqb_spec (sc_nprime scene_geom_asan bs) 0); lia. }
assert (HAG : env_agree 32 (Ereg regs3 []) (Eimg (Ereg regs3 [])))
by (split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* ---- the rest of the segment, from the call of __wrap_malloc at 0x82b9c ---- *)
assert (MAIN : forall (regsA : bvmap 5 word) (memA : word -> option byte) (mdA : Model),
s1_rk (spZ (c_regs cx)) (c_sp1 cx) (shadow_addr (sc_F SEGS scene_geom_asan cx)) (sc_F SEGS scene_geom_asan cx)
(sc_nprime scene_geom_asan bs) (sc_s7v bs mod 2 ^ 64) (sc_cur SEGS cx) (sc_rest SEGS cx) regsA ->
getr regsA 10 = w64 (sc_nn scene_geom_asan bs) ->
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly3 S3 W3 memA mdA 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ s1_prot (c_sp1 cx) a ->
aview SEGS (w_H W3) memA a = aview SEGS (w_H W3) mem3 a) ->
rdword (aview SEGS (w_H W3) memA) (c_sp1 cx + 24) = Some (sc_F SEGS scene_geom_asan cx + 224) ->
rdword (aview SEGS (w_H W3) memA) (c_sp1 cx + 56) = Some (sc_nn scene_geom_asan bs) ->
rdword (aview SEGS (w_H W3) memA) (c_sp1 cx + 72) = Some (sc_flags bs) ->
SRr SEGS W3 (mkCfg (mkst regsA (Z_to_bv 64 (BASE + 0x324)) memA (seg_rom SEGS)) mdA) POST).
{ intros regsA memA mdA RK Ra0A HJA KA Wexp Wnn Wfl.
pose proof RK as (RA2 & RA3 & RA4 & RA8 & RA9 & RA18 & RA19 & RA21 & RA22 & RA23 & RA24 & RA25 & RA26 & RA27).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
assert (HAF : AF_LLVMFuzzerTestOneInput = 0) by reflexivity.
assert (Hsp1al16 : c_sp1 cx mod 16 = 0).
{ rewrite Hsp1eq. replace (32 * ((spZ (c_regs cx) - 224) / 32)) with (((spZ (c_regs cx) - 224) / 32 * 2) * 16) by lia.
apply Z_mod_mult. }
assert (Hom : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity).
assert (Hoff : -240 <= c_sp1 cx - spZ (c_regs cx) <= -224)
by (destruct (proj1 (Z.mod_divide (c_sp1 cx - spZ (c_regs cx)) 16 ltac:(lia)) Hom) as [q Hq]; lia).
remember (Eimg (Ereg regsA [])) as EA eqn:HEA.
assert (HEIA : img_env VAL A_LIM EA) by (subst EA; apply Eimg_env).
assert (HAGA : env_agree 32 (Ereg regsA []) EA)
by (subst EA; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HSA : st_ok_pi SEGS VAL EA (mkSS 804 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regsA (Z_to_bv 64 (BASE + 804)) memA (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HSA HJA.
{ apply awr_ok_nil. }
pose proof (regs_kept_of_st_ok SEGS EA _ (restrict (w_H W3) ms) regsA []
[2; 3; 4; 8; 9; 10; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HSA HAGA eq_refl) as RKA.
cbn [ms_regs restrict] in RKA.
prreg HSA (1%bv : bv 5) Rra.
(* the call run writes nothing *)
assert (KAm : forall a, 0 <= a < 2 ^ 64 -> ~ s1_prot (c_sp1 cx) a ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hna. rewrite <- (KA a Ha Hna).
apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin. cbn in Hin. destruct Hin. }
assert (Rsp' : spZ (ms_regs ms) = c_sp1 cx).
{ unfold spZ at 1. rewrite (RKA 2%bv ltac:(cbn; tauto)), RA2. unfold w64. apply unsigned_lit_small. lia. }
assert (Rs0' : s0Z (ms_regs ms) = spZ (c_regs cx)).
{ unfold s0Z. rewrite (RKA 8%bv ltac:(cbn; tauto)), RA8. unfold w64. apply unsigned_lit_small. lia. }
assert (Rra' : raZ (ms_regs ms) = BASE + AF_LLVMFuzzerTestOneInput + 0x328).
{ unfold raZ. rewrite Rra, HAF. apply unsigned_lit_small. lia. }
assert (Hach : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (spZ (c_regs cx)) (rt_ch cx)).
{ apply (achain_ly_top (c_ly cx)).
- pose proof HlyJ as LY. destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _). exact LT.
- apply (s1_chain cx W3 (ms_mem ms) (c_sp1 cx) HAFN); [ | | lia | lia].
+ intros a Ha. rewrite (KAm a ltac:(lia) ltac:(unfold s1_prot; lia)).
apply JK1; lia.
+ intros j Hj. rewrite <- (HSAV j Hj). apply rdword_ext. intros k Hk.
apply KAm; [lia | unfold s1_prot; lia]. }
pmkst HSA.
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ eapply (amalloc04_rule_triv (SK := SK) SEGS B pa_segs_low (pal_env B TL) LAWS ML AMALLOC W3 (ms_regs ms) (ms_mem ms)
(sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 _ 0
(sc_nn scene_geom_asan bs) (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 808)) (rt_ch cx) HJA).
- rewrite (RKA 10%bv ltac:(cbn; tauto)). exact Ra0A.
- unfold MALLOC_MAX. lia.
- rewrite Hbb. lia.
- rewrite Rsp'. lia.
- exact Hom.
- lia.
- lia.
- rewrite (RKA 3%bv ltac:(cbn; tauto)). exact RA3.
- rewrite (RKA 4%bv ltac:(cbn; tauto)). exact RA4.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- lia.
- apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (rt_ch cx) (ms_regs ms) Hach);
[rewrite Rsp'; lia | exact Rs0' | rewrite Rra'; lia].
- apply (HTRACE (pc_malloc_ra0 (as_code B)) (BASE + AF_LLVMFuzzerTestOneInput + 0x328) (ms_regs ms) cx Hra0 Rra').
left. split; [reflexivity | left; reflexivity].
- exact I. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres & Eab4 & HK4 & _).
(* ---- what the call leaves: the new block (res, n''), the frame, the stack above sp1 ---- *)
change (0 + 1) with 1 in HJ4.
pose proof HJ4 as (HAR4 & Hly4 & _).
pose proof HK4 as (HK4up & HK4blk & HK4img & HK4frm & HK4pres & HK4win).
cbv beta in HK4blk, HK4frm.
assert (Ereq : req_size (sc_nn scene_geom_asan bs) = sc_nn scene_geom_asan bs)
by (unfold req_size; destruct (Z.eqb_spec (sc_nn scene_geom_asan bs) 0); lia).
rewrite Ereq in HK4blk, HK4frm.
assert (Hin4 : In (res, sc_nn scene_geom_asan bs) (ablocks B ly4 S4))
by (rewrite Eab4; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (sc_nn scene_geom_asan bs) HAR4 Hin4)
as (Hres16 & Hres4096' & Hresceil & Hresapp & Hrespres & _).
assert (HresA : res + sc_nn scene_geom_asan bs <= 2147446784 \/ 17594333495296 <= res).
{ pose proof Hresapp as HA'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HA'. rewrite Ereq in HA'. lia. }
assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 Hly4) as (_ & EFA4 & _).
assert (EFA4' : frame_addr ly4 8 (c_fpos cx) = sc_F SEGS scene_geom_asan cx) by (rewrite EFA4; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 res _ 8 (c_fpos cx) HAR4 Hin4 Hfin4) as HsepBF.
unfold zdisjoint in HsepBF. cbn [fst snd] in HsepBF. rewrite EFA4', Ereq in HsepBF.
change (fs_frame_bytes 8) with 16384 in HsepBF.
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HARc Hfin3) as (HF32 & _ & _ & _).
rewrite EFA3 in HF32.
assert (HF8lo : 512 <= sc_F SEGS scene_geom_asan cx / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : sc_F SEGS scene_geom_asan cx / 8 + 2048 <= 17592184995840).
{ assert (HFc2 : sc_F SEGS scene_geom_asan cx + 2048 * 8 <= 0x7fffff800000) by lia.
assert (Hd := Z.div_le_mono (sc_F SEGS scene_geom_asan cx + 2048 * 8) 0x7fffff800000 8 ltac:(lia) HFc2).
rewrite Z.div_add in Hd by lia. change (0x7fffff800000 / 8) with 17592184995840 in Hd. lia. }
assert (HF8 : forall k, 0 <= k -> (sc_F SEGS scene_geom_asan cx + 8 * k) / 8 = sc_F SEGS scene_geom_asan cx / 8 + k).
{ intros k Hk. destruct (proj1 (Z.mod_divide (sc_F SEGS scene_geom_asan cx) 32 ltac:(lia)) HF32) as [q Hq].
rewrite Hq. replace (q * 32 + 8 * k) with ((4 * q + k) * 8) by lia. replace (q * 32) with ((4 * q) * 8) by lia.
rewrite !Z.div_mul by lia. reflexivity. }
(* the bytes the call kept *)
assert (KAA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) memA a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin. cbn in Hin. destruct Hin. }
assert (KST4 : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) memA a).
{ intros a Ha. rewrite <- (KAA a ltac:(lia)). apply HK4up; lia. }
assert (KFR4 : forall a, (sc_F SEGS scene_geom_asan cx <= a < sc_F SEGS scene_geom_asan cx + 16384 \/
shadow_addr (sc_F SEGS scene_geom_asan cx) <= a < shadow_addr (sc_F SEGS scene_geom_asan cx) + 2048) ->
~ (res <= a < res + sc_nn scene_geom_asan bs) ->
aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hna. rewrite (HK4frm 8 (c_fpos cx) a Hfin3).
- apply KAm; unfold shadow_addr, SHADOW_OFF in Ha; [lia | unfold s1_prot; lia].
- unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes 8) with 16384.
change (16384 / 8) with 2048. exact Ha.
- exact Hna. }
(* ---- C2 (0x82ca8): the cut, from the state the loops leave ---- *)
assert (EXIT : forall regs mem md,
getr regs 2 = w64 (c_sp1 cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
getr regs 19 = w64 (shadow_addr (sc_F SEGS scene_geom_asan cx)) ->
getr regs 20 = w64 (sc_F SEGS scene_geom_asan cx) ->
getr regs 23 = w64 (sc_s7v bs mod 2 ^ 64) -> getr regs 24 = w64 (sc_nprime scene_geom_asan bs) ->
getr regs 25 = w64 (sc_F SEGS scene_geom_asan cx + 32) -> getr regs 26 = w64 SHADOW_OFF ->
getr regs 27 = w64 (sc_F SEGS scene_geom_asan cx + 144) -> getr regs 17 = w64 res ->
s1_lctx cx ly4 S4 W4 res (sc_nn scene_geom_asan bs) mem md ->
s1_keep_mem W4 res (sc_nn scene_geom_asan bs) mem4 mem ->
SRr SEGS W4 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x430)) mem (seg_rom SEGS)) md) POST).
{ intros regs mem md R2 R3 R4 R8 R9 R19 R20 R23 R24 R25 R26 R27 R17 HLC KBm.
pose proof HLC as (HJm & _ & _ & _).
pose proof (proj1 HJm) as HARm.
assert (STK : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) memA a).
{ intros a Ha. rewrite (KBm a ltac:(lia) ltac:(lia)). apply KST4. lia. }
assert (STK3 : forall a, c_sp1 cx <= a < 2 ^ 64 -> ~ s1_prot (c_sp1 cx) a ->
aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hp. rewrite (STK a Ha), <- (KAA a ltac:(lia)). apply KAm; [lia | exact Hp]. }
assert (FRM : forall a, (sc_F SEGS scene_geom_asan cx <= a < sc_F SEGS scene_geom_asan cx + 16384 \/
shadow_addr (sc_F SEGS scene_geom_asan cx) <= a < shadow_addr (sc_F SEGS scene_geom_asan cx) + 2048) ->
aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. assert (Hna : ~ (res <= a < res + sc_nn scene_geom_asan bs)) by (unfold shadow_addr, SHADOW_OFF in Ha; lia).
rewrite (KBm a ltac:(unfold shadow_addr, SHADOW_OFF in Ha; lia) Hna). exact (KFR4 a Ha Hna). }
assert (Hftok : aftok [] (ablocks B (c_ly cx) (c_S cx)) (res, sc_nn scene_geom_asan bs))
by (eapply (aftok_new_block SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia]).
assert (Hfresh : ~ In (res, sc_nn scene_geom_asan bs) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. destruct (Hftok Hc 0 ltac:(cbn [snd]; rewrite Ereq; lia)) as (r & [] & _). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (sc_nn scene_geom_asan bs) HARm Hin4) as (_ & _ & _ & _ & Hpresm & _).
assert (Hnn0 : 0 <= sc_nn scene_geom_asan bs) by lia.
destruct (s1_garr8_present (mrestrict (w_H W4) mem) res (sc_nn scene_geom_asan bs) Hnn0) as (Hlen & Hga).
{ intros j Hj. pose proof (proj1 (Hpresm (res + j) ltac:(rewrite Ereq; lia))) as Hp.
pose proof (aview_some_of_apresent SEGS _ _ _ Hp) as Hv. unfold aview in Hv.
intros Hn. apply Hv. rewrite Hn. reflexivity. }
destruct (al_frames _ _ LAWS ly4 S4 W4 mem md 8 (c_fpos cx) HARm Hfin4) as (_ & _ & HFpm & HFSpm).
rewrite EFA4' in HFpm, HFSpm. change (fs_frame_bytes 8) with 16384 in HFpm, HFSpm.
replace (Z_to_bv 64 (BASE + 0x430)) with (w64 (sg_pc_c2 scene_geom_asan))
by (cbn [sg_pc_c2 scene_geom_asan]; unfold w64, SEG_C2_off; rewrite HAF, Z.add_0_r; reflexivity).
change (mkCfg (mkst regs (w64 (sg_pc_c2 scene_geom_asan)) mem (seg_rom SEGS)) md)
with (cfg_at SEGS (sg_pc_c2 scene_geom_asan) regs mem md).
apply (HC2 ly4 S4 W4 regs mem md bs res (s1_bytes (mrestrict (w_H W4) mem) res (sc_nn scene_geom_asan bs))).
unfold cut_C2.
cbn [sg_cid sg_off_blki sg_off_blk sg_off_expect sg_off_mac sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi
sg_mac_n sg2_sp0 sg2_sp1 sg2_F sg2_Fsp sg2_shF sg2_shbase sg2_blki sg2_blk sg2_expect sg2_mac sg2_shexp sg2_body
sg2_nprime sg2_Fb sg2_nn sg2_flags sg2_step sg2_s7v scene_geom_asan vat].
unfold RV_s0, RV_s1, RV_s3, RV_s4, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11, RV_a7.
split; [split; [exact HJm | split; [rewrite Hfrs4, Hfrs3; reflexivity | exact I]] |].
split; [rewrite Eab4, Hab; reflexivity |].
split.
{ rewrite (blocks_bytes_bsum B ly4 S4), Eab4, bsum_app, <- (blocks_bytes_bsum B ly3 S3), Hbb.
change (bsum [(res, sc_nn scene_geom_asan bs)]) with (sc_nn scene_geom_asan bs + 0). rewrite Ereq. lia. }
split.
{ unfold sc_blk_ok. split; [lia|]. split.
{ apply zone2_of_app; [exact Hresapp | exact (blk_off_imgP B ly4 S4 W4 mem4 md4 res _ HAR4 Hin4)]. }
split; [exact Hresceil|]. split; [exact Hres16|]. split; [|exact Hftok].
intros blc lyq ownq i Hb Hi. right; right; left. exists res, (sc_nn scene_geom_asan bs).
split; [exact Hb|]. split; [exact Hfresh | lia]. }
split; [exact Hlen |]. split; [exact Hga |].
split.
{ unfold sc_frame. cbn [sg_cid scene_geom_asan]. change (fs_frame_bytes 8) with 16384.
destruct HFRM as (HFLAG & _ & _). cbn [sg_cid scene_geom_asan] in HFLAG. change (fs_frame_bytes 8) with 16384 in HFLAG.
split; [rewrite <- HFLAG; apply rdword_ext; intros k Hk; apply FRM; left; lia|].
split; [intros a Ha; exact (proj1 (HFpm a Ha))|].
change (16384 / 8) with 2048. intros a Ha.
replace a with (shadow_addr (sc_F SEGS scene_geom_asan cx) + (a - shadow_addr (sc_F SEGS scene_geom_asan cx))) by lia.
assert (Ha' : 0 <= a - shadow_addr (sc_F SEGS scene_geom_asan cx) < 16384 / 8) by (change (16384 / 8) with 2048; lia).
exact (proj1 (HFSpm _ Ha')). }
split.
{ intros j Hj. rewrite <- (HSAV j Hj). apply rdword_ext. intros k Hk. apply STK3; [lia | unfold s1_prot; lia]. }
split.
{ unfold sc_shbg in HSHBG |- *. cbn [sg_sh_bg scene_geom_asan] in HSHBG |- *.
rewrite Forall_forall in HSHBG |- *. intros t Ht. specialize (HSHBG t Ht). cbn [In] in Ht.
destruct Ht as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in HSHBG |- *;
unfold sc_shr in HSHBG |- *; intros o Ho; rewrite FRM by (right; lia); apply HSHBG; exact Ho. }
split.
{ unfold sc_shr in HSHBI |- *. intros o Ho. rewrite FRM by (right; lia). apply HSHBI. exact Ho. }
split.
{ unfold sc_shr in HSHBL |- *. intros o Ho. rewrite FRM by (right; lia). apply HSHBL. exact Ho. }
split.
{ unfold sc_open in HOPMAC |- *. cbn [sg_mac_n sg_off_mac scene_geom_asan] in HOPMAC.
destruct HOPMAC as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
intros i Hi. rewrite <- (Hc i Hi). change ((6 + 7) / 8) with 1 in Hi.
assert (Ea : shadow_of_addr SHADOW_OFF (sc_F SEGS scene_geom_asan cx + 112) + i =
shadow_addr (sc_F SEGS scene_geom_asan cx) + (14 + i)).
{ unfold shadow_of_addr, shadow_addr. replace (sc_F SEGS scene_geom_asan cx + 112) with (sc_F SEGS scene_geom_asan cx + 8 * 14) by lia.
rewrite HF8 by lia. lia. }
rewrite Ea. apply FRM. right. lia. }
split.
{ unfold sc_img. split; [unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia|].
split; [exact R3|]. split; [exact R4|].
assert (HRODP : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
by (rewrite <- HWRLO, <- HWRHI; unfold arodata_okP, in_roP; exact HROD0).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm HRODP) as HRODm.
rewrite HWRLO, HWRHI. unfold arodata_okP, in_roP in HRODm. exact HRODm. }
split; [exact HIN |]. split; [exact Hnnb |].
split.
{ intros j Hj. destruct (HMACB j Hj) as (Hv & Hr). split; [|exact Hr].
apply (val_mem_kept SEGS (w_H W3) (w_H W4) mem3 mem); [| exact Hv].
unfold sc_macb in Hj. cbn [length] in Hj. intros k Hk. apply FRM. left. lia. }
split; [exact R8 |]. split; [exact R9 |]. split; [exact R20 |].
split; [rewrite <- V_Fsp; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [exact R19 |]. split; [exact R26 |]. split; [exact R25 |]. split; [exact R27 |].
split; [rewrite <- Wexp; apply rdword_ext; intros k Hk; apply STK; lia |].
split; [rewrite <- V_mac; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [rewrite <- V_shexp; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [exact R17 |]. split; [exact R24 |].
split; [rewrite <- V_Fsp; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [rewrite <- Wnn; apply rdword_ext; intros k Hk; apply STK; lia |].
split; [rewrite <- Wfl; apply rdword_ext; intros k Hk; apply STK; lia |].
split; [rewrite <- V_step; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
exact R23. }
assert (Hn26 : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
assert (Hrestb : 0 <= sc_rest SEGS cx < 2 ^ 26) by (unfold sc_rest; lia).
(* ---- 0x82c30 `beqz s5`: a zero count goes straight to C2, else 0x82c34-0x82c3c set up the xor loop ---- *)
assert (MIDX : forall cnt regs mem md,
cnt = Z.min (sc_rest SEGS cx) (sc_nprime scene_geom_asan bs) ->
getr regs 2 = w64 (c_sp1 cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
getr regs 19 = w64 (shadow_addr (sc_F SEGS scene_geom_asan cx)) ->
getr regs 20 = w64 (sc_F SEGS scene_geom_asan cx) -> getr regs 21 = w64 cnt ->
getr regs 22 = w64 (sc_cur SEGS cx) ->
getr regs 23 = w64 (sc_s7v bs mod 2 ^ 64) -> getr regs 24 = w64 (sc_nprime scene_geom_asan bs) ->
getr regs 25 = w64 (sc_F SEGS scene_geom_asan cx + 32) -> getr regs 26 = w64 SHADOW_OFF ->
getr regs 27 = w64 (sc_F SEGS scene_geom_asan cx + 144) -> getr regs 17 = w64 res ->
s1_lctx cx ly4 S4 W4 res (sc_nn scene_geom_asan bs) mem md ->
s1_keep_mem W4 res (sc_nn scene_geom_asan bs) mem4 mem ->
SRr SEGS W4 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x3b8)) mem (seg_rom SEGS)) md) POST).
{ intros cnt regs mem md Hcnt N2 N3 N4 N8 N9 N19 N20 N21 N22 N23 N24 N25 N26 N27 N17 HLC KBm.
pose proof HLC as (HJm & HLCr).
assert (Hcnt0 : 0 <= cnt <= sc_nprime scene_geom_asan bs) by (rewrite Hcnt; lia).
assert (Hcntb : 0 <= cnt < 2 ^ 64) by lia.
remember (Eimg (Ereg regs [])) as EM eqn:HEM.
assert (HEIM : img_env VAL A_LIM EM) by (subst EM; apply Eimg_env).
assert (EEM : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EM n = getr regs r)
by (intros n r Hn; subst EM; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E21 : ew EM 21 = w64 cnt) by (rewrite (EEM 21%nat 21%bv eq_refl); exact N21).
assert (HSM : st_ok_pi SEGS VAL EM (mkSS 952 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W4) (mkst regs (Z_to_bv 64 (BASE + 952)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
[subst EM; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | unfold facts_ok; cbn; tauto]. }
psrr_branch_pi RUNP BR HSM.
- (* cnt = 0: `beqz s5` taken, to C2 *)
rewrite (s1_beq0 EM 21 cnt E21 Hcntb) in Hc. apply Z.eqb_eq in Hc.
paj_run_to_sh RUNTOP HSM HJm 1072.
{ apply awr_ok_nil. }
s1_lastfr KX1.
pmkst HSM.
apply EXIT.
+ s1_regk HSM EEM N2.
+ s1_regk HSM EEM N3.
+ s1_regk HSM EEM N4.
+ s1_regk HSM EEM N8.
+ s1_regk HSM EEM N9.
+ s1_regk HSM EEM N19.
+ s1_regk HSM EEM N20.
+ s1_regk HSM EEM N23.
+ s1_regk HSM EEM N24.
+ s1_regk HSM EEM N25.
+ s1_regk HSM EEM N26.
+ s1_regk HSM EEM N27.
+ s1_regk HSM EEM N17.
+ split; [exact HJm | exact HLCr].
+ intros a Ha Hna. rewrite (s1_norun_keep _ _ _ _ KX1 a Ha). exact (KBm a Ha Hna).
- (* cnt <> 0: the xor loop over cnt turns *)
rewrite (s1_beq0 EM 21 cnt E21 Hcntb) in Hc. apply Z.eqb_neq in Hc.
assert (Hn11 : 11 < c_n cx) by (unfold sc_rest in Hcnt; lia).
destruct Hpn as [[Hnz _] | [_ Hinp0]]; [lia |].
assert (Hinp4 : In (c_p cx, c_n cx) (ablocks B ly4 S4))
by (rewrite Eab4, Hab; apply in_or_app; left; exact Hinp0).
assert (Hdisj : c_p cx + c_n cx <= res \/ res + sc_nn scene_geom_asan bs <= c_p cx).
{ apply in_split in Hinp0 as (l1 & l2 & E1).
pose proof (sep_blocks_pos SEGS B LAWS ly4 S4 W4 mem4 md4 (c_p cx, c_n cx) (res, sc_nn scene_geom_asan bs) l1 l2 [] HAR4) as Hd.
rewrite Eab4, Hab, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Ereq in Hd.
assert (Hrq : 0 <= c_n cx) by lia. pose proof (req_size_pos (c_n cx) Hrq) as Hrqp. lia. }
assert (Hcntnn : cnt <= sc_nn scene_geom_asan bs) by (unfold sc_nn; destruct (Z.eqb_spec (sc_nprime scene_geom_asan bs) 0); lia).
paj_run_to_sh RUNTOP HSM HJm 968.
{ apply awr_ok_nil. }
s1_lastfr KX2.
pmkst HSM.
apply (s1_xor_loop cx ly4 S4 W4 res (sc_nn scene_geom_asan bs) (c_p cx) (c_n cx) (sc_cur SEGS cx) cnt POST (Z.to_nat cnt) 0).
+ lia.
+ unfold s1_xor_inv. split; [split; [exact HJm | exact HLCr] |].
split; [lia |]. split; [exact Hcntnn |]. split; [exact Hinp4 |].
split; [unfold sc_cur; lia |]. split; [unfold sc_cur, sc_rest in *; lia |]. split; [exact Hdisj |].
split; [s1_getr HSM (10%bv : bv 5); rewrite s1_atom_reg, (EEM 22%nat 22%bv eq_refl), N22, Z.add_0_r; reflexivity |].
split; [s1_getr HSM (22%bv : bv 5); rewrite s1_atom_reg, (EEM 22%nat 22%bv eq_refl), N22, Z.add_0_r; reflexivity |].
split; [s1_getr HSM (11%bv : bv 5); rewrite s1_atom_reg, (EEM 17%nat 17%bv eq_refl), N17, Z.add_0_r; reflexivity |].
split; [s1_getr HSM (12%bv : bv 5); rewrite s1_atom_reg, (EEM 17%nat 17%bv eq_refl), N17, Z.add_0_r; reflexivity |].
split; [s1_getr HSM (21%bv : bv 5); rewrite s1_atom_reg, (EEM 21%nat 21%bv eq_refl), N21, Z.sub_0_r; reflexivity |].
s1_regk HSM EEM N26.
+ intros regs' mem' md' HLC' HKR HKM.
apply EXIT.
* rewrite (HKR 2%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N2.
* rewrite (HKR 3%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N3.
* rewrite (HKR 4%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N4.
* rewrite (HKR 8%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N8.
* rewrite (HKR 9%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N9.
* rewrite (HKR 19%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N19.
* rewrite (HKR 20%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N20.
* rewrite (HKR 23%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N23.
* rewrite (HKR 24%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N24.
* rewrite (HKR 25%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N25.
* rewrite (HKR 26%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N26.
* rewrite (HKR 27%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N27.
* rewrite (HKR 17%bv ltac:(unfold s1_xor_keep; cbn; tauto)). s1_regk HSM EEM N17.
* exact HLC'.
* intros a Ha Hna. rewrite (HKM a Ha Hna), (s1_norun_keep _ _ _ _ KX2 a Ha). exact (KBm a Ha Hna). }
(* ---- 0x82c20 .. 0x82c2c: s4 = s7 (F); `bltu s5,s8` / `mv s5,s8` leave s5 = min(rest, n'); s7 = s2 ---- *)
assert (MID : forall regs mem md,
s1_rk (spZ (c_regs cx)) (c_sp1 cx) (shadow_addr (sc_F SEGS scene_geom_asan cx)) (sc_F SEGS scene_geom_asan cx)
(sc_nprime scene_geom_asan bs) (sc_s7v bs mod 2 ^ 64) (sc_cur SEGS cx) (sc_rest SEGS cx) regs ->
getr regs 17 = w64 res ->
s1_lctx cx ly4 S4 W4 res (sc_nn scene_geom_asan bs) mem md ->
s1_keep_mem W4 res (sc_nn scene_geom_asan bs) mem4 mem ->
SRr SEGS W4 (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x3a8)) mem (seg_rom SEGS)) md) POST).
{ intros regs mem md RKm N17 HLC KBm.
pose proof HLC as (HJm & HLCr).
pose proof RKm as (N2 & N3 & N4 & N8 & N9 & N18 & N19 & N21 & N22 & N23 & N24 & N25 & N26 & N27).
remember (Eimg (Ereg regs [])) as EM eqn:HEM.
assert (HEIM : img_env VAL A_LIM EM) by (subst EM; apply Eimg_env).
assert (EEM : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EM n = getr regs r)
by (intros n r Hn; subst EM; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E21 : ew EM 21 = w64 (sc_rest SEGS cx)) by (rewrite (EEM 21%nat 21%bv eq_refl); exact N21).
assert (E24 : ew EM 24 = w64 (sc_nprime scene_geom_asan bs)) by (rewrite (EEM 24%nat 24%bv eq_refl); exact N24).
assert (Hrb : 0 <= sc_rest SEGS cx < 2 ^ 64) by lia.
assert (Hnb : 0 <= sc_nprime scene_geom_asan bs < 2 ^ 64) by lia.
assert (HSM : st_ok_pi SEGS VAL EM (mkSS 936 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W4) (mkst regs (Z_to_bv 64 (BASE + 936)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
[subst EM; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | unfold facts_ok; cbn; tauto]. }
paj_run_sh RUNP HSM HJm.
{ apply awr_ok_nil. }
s1_lastfr KM1.
psrr_branch_pi RUNP BR HSM.
- (* rest < n': s5 keeps rest *)
rewrite (s1_bltu EM 21 24 _ _ E21 E24 Hrb Hnb) in Hc. apply Z.ltb_lt in Hc.
paj_run_to_sh RUNTOP HSM HJm 952.
{ apply awr_ok_nil. }
s1_lastfr KM2.
pmkst HSM.
apply (MIDX (sc_rest SEGS cx)).
+ rewrite Z.min_l by lia. reflexivity.
+ s1_regk HSM EEM N2.
+ s1_regk HSM EEM N3.
+ s1_regk HSM EEM N4.
+ s1_regk HSM EEM N8.
+ s1_regk HSM EEM N9.
+ s1_regk HSM EEM N19.
+ s1_regk HSM EEM N23.
+ s1_regk HSM EEM N21.
+ s1_regk HSM EEM N22.
+ s1_regk HSM EEM N18.
+ s1_regk HSM EEM N24.
+ s1_regk HSM EEM N25.
+ s1_regk HSM EEM N26.
+ s1_regk HSM EEM N27.
+ s1_regk HSM EEM N17.
+ split; [exact HJm | exact HLCr].
+ intros a Ha Hna. rewrite (s1_norun_keep _ _ _ _ KM2 a Ha), (s1_norun_keep _ _ _ _ KM1 a Ha). exact (KBm a Ha Hna).
- (* n' <= rest: `mv s5,s8` *)
rewrite (s1_bltu EM 21 24 _ _ E21 E24 Hrb Hnb) in Hc. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HSM HJm 952.
{ apply awr_ok_nil. }
s1_lastfr KM2.
pmkst HSM.
apply (MIDX (sc_nprime scene_geom_asan bs)).
+ rewrite Z.min_r by lia. reflexivity.
+ s1_regk HSM EEM N2.
+ s1_regk HSM EEM N3.
+ s1_regk HSM EEM N4.
+ s1_regk HSM EEM N8.
+ s1_regk HSM EEM N9.
+ s1_regk HSM EEM N19.
+ s1_regk HSM EEM N23.
+ s1_regk HSM EEM N24.
+ s1_regk HSM EEM N22.
+ s1_regk HSM EEM N18.
+ s1_regk HSM EEM N24.
+ s1_regk HSM EEM N25.
+ s1_regk HSM EEM N26.
+ s1_regk HSM EEM N27.
+ s1_regk HSM EEM N17.
+ split; [exact HJm | exact HLCr].
+ intros a Ha Hna. rewrite (s1_norun_keep _ _ _ _ KM2 a Ha), (s1_norun_keep _ _ _ _ KM1 a Ha). exact (KBm a Ha Hna). }
(* ---- 0x82ba0 .. 0x82bb8: the result check, a7 = body, the n' = 0 skip, the fill loop's set-up ---- *)
assert (AWRB : forall a, res <= a < res + sc_nn scene_geom_asan bs ->
awr_byte (sw_stk WK) (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly4 S4) ly4 [(8, c_fpos cx)] a).
{ intros a Ha. replace a with (res + (a - res)) by lia.
eapply (awr_new_block SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia | exact Hin4 | rewrite Ereq; lia]. }
assert (RK4 : s1_rk (spZ (c_regs cx)) (c_sp1 cx) (shadow_addr (sc_F SEGS scene_geom_asan cx)) (sc_F SEGS scene_geom_asan cx)
(sc_nprime scene_geom_asan bs) (sc_s7v bs mod 2 ^ 64) (sc_cur SEGS cx) (sc_rest SEGS cx) regs4).
{ apply (s1_rk_pres _ _ _ _ _ _ _ _ (ms_regs ms) regs4 HP4).
apply (s1_rk_kept _ _ _ _ _ _ _ _ regsA (ms_regs ms)); [intros r Hr; apply RKA; cbn in Hr |- *; tauto | exact RK]. }
pose proof RK4 as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
assert (HROD4 : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W4) mem4)).
{ assert (HRODP : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
by (rewrite <- HWRLO, <- HWRHI; unfold arodata_okP, in_roP; exact HROD0).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HRODP) as H.
rewrite HWRLO, HWRHI. unfold arodata_okP, in_roP in H. exact H. }
pose proof (s1_got_pl (w_H W4) mem4 HROD4) as HGOT4.
pose proof (pa_obj_img 4 ltac:(lia)) as HVO.
remember (Eimg (Ereg regs4 [])) as E4 eqn:HE4.
assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
assert (HAG4 : env_agree 32 (Ereg regs4 []) E4)
by (subst E4; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs4 r)
by (intros n r Hn; subst E4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (UG : bv_unsigned (ew E4 (A_OBJ 4)) = VAL (A_OBJ 4)) by (apply HEI4; split; vm_compute; lia).
assert (HS4 : st_ok_pi SEGS VAL E4 (mkSS 808 sr_atoms [s1_got_region] None (mkFacts [] [] []))
(restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 808)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E4. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, s1_got_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite UG. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E4 _ (VAL (A_OBJ 4)) 0 8 (SLit s1_PL) s1_PL);
[reflexivity | change (8 * Z.of_N 8) with 64; unfold s1_PL; lia | cbn; lia | rewrite Z.add_0_r; exact HGOT4].
- cbn. tauto.
- unfold facts_ok; cbn; tauto. }
paj_run_sh RUNP HS4 HJ4.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
s1_lastfr KP1.
assert (E10 : ew E4 10 = w64 res) by (rewrite (EE4 10%nat 10%bv eq_refl); exact Ha04).
assert (Hresb : 0 <= res < 2 ^ 64) by lia.
psrr_branch_pi RUNP BR HS4.
{ (* 0x82ba0 `beqz a0`, to the abort block: the wrapper returned a block at 4096 or above *)
exfalso. rewrite (s1_beq0 E4 10 res E10 Hresb) in Hc. apply Z.eqb_eq in Hc. lia. }
clear Hc. paj_run_sh RUNP HS4 HJ4.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
s1_lastfr KP2.
assert (E24 : ew E4 24 = w64 (sc_nprime scene_geom_asan bs)) by (rewrite (EE4 24%nat 24%bv eq_refl); exact Q24).
assert (Hnb : 0 <= sc_nprime scene_geom_asan bs < 2 ^ 64) by lia.
psrr_branch_pi RUNP BR HS4.
- (* n' = 0: `beqz s8` 0x82ba8 skips the fill loop *)
rewrite (s1_beq0 E4 24 _ E24 Hnb) in Hc. apply Z.eqb_eq in Hc.
paj_run_to_sh RUNTOP HS4 HJ4 936.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
s1_lastfr KP3.
pmkst HS4.
apply MID.
+ apply (s1_rk_kept _ _ _ _ _ _ _ _ regs4); [| exact RK4].
exact (regs_kept_of_st_ok SEGS E4 _ _ regs4 [] [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS4 HAG4 eq_refl).
+ s1_regk HS4 EE4 Ha04.
+ split; [exact HJ4 | split; [exact Hin4 | split; [exact Hnnb | exact AWRB]]].
+ intros a Ha Hna. rewrite (s1_got_keep _ _ _ _ KP3 a Ha), (s1_got_keep _ _ _ _ KP2 a Ha), (s1_got_keep _ _ _ _ KP1 a Ha).
reflexivity.
- (* n' <> 0: a1 = 0, a2 = &reac_scene_placeholder, a3 = 0x458, then n' turns of the fill loop *)
rewrite (s1_beq0 E4 24 _ E24 Hnb) in Hc. apply Z.eqb_neq in Hc.
assert (Hnnp : sc_nn scene_geom_asan bs = sc_nprime scene_geom_asan bs)
by (unfold sc_nn; rewrite (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
paj_run_to_sh RUNTOP HS4 HJ4 836.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
s1_lastfr KP3.
pmkst HS4.
apply (s1_fill_loop cx ly4 S4 W4 res (sc_nprime scene_geom_asan bs) POST (Z.to_nat (sc_nprime scene_geom_asan bs)) 0).
+ lia.
+ unfold s1_fill_inv. split.
{ rewrite <- Hnnp. split; [exact HJ4 | split; [exact Hin4 | split; [exact Hnnb | exact AWRB]]]. }
split; [lia |].
split; [s1_getr HS4 (11%bv : bv 5); reflexivity |].
split; [s1_getr HS4 (12%bv : bv 5); reflexivity |].
split; [s1_getr HS4 (13%bv : bv 5); reflexivity |].
split; [s1_regk HS4 EE4 Ha04 |].
split; [s1_regk HS4 EE4 Q24 |].
s1_regk HS4 EE4 Q26.
+ intros regs' mem' md' HLC' HKR HKM.
assert (HK0 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs4 r).
{ intros r Hr. rewrite (HKR r ltac:(unfold s1_fill_keep; cbn in Hr |- *; tauto)).
exact (regs_kept_of_st_ok SEGS E4 _ _ regs4 [] [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS4 HAG4 eq_refl r Hr). }
apply MID.
* exact (s1_rk_kept _ _ _ _ _ _ _ _ regs4 regs' HK0 RK4).
* rewrite (HKR 17%bv ltac:(unfold s1_fill_keep; cbn; tauto)). s1_regk HS4 EE4 Ha04.
* rewrite Hnnp. exact HLC'.
* intros a Ha Hna. rewrite (HKM a Ha ltac:(rewrite <- Hnnp; exact Hna)).
rewrite (s1_got_keep _ _ _ _ KP3 a Ha), (s1_got_keep _ _ _ _ KP2 a Ha), (s1_got_keep _ _ _ _ KP1 a Ha).
reflexivity. }
(* ---- the entry block 0x82b78-0x82b84 ---- *)
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 []))) by apply Eimg_env.
unfold cfg_at, YG0d.w64. cbn [sg_pc_c1 scene_geom_asan].
rewrite <- (Z.add_assoc BASE AF_LLVMFuzzerTestOneInput SEG_C1_off).
change (AF_LLVMFuzzerTestOneInput + SEG_C1_off) with S1_pc1.
paj_run_sh RUNP HS HJ.
{ exact HAWR. }
rename HFr into HFr1. clear HF HG.
psrr_branch_pi RUNP BR HS.
- (* the flag's low bit is 0: n' is the input's u16 (s8 is unchanged) *)
rewrite (s1_cond_and1 _ (sc_flags bs) E16 Hfl256) in Hc. apply Z.eqb_eq in Hc.
assert (Hnp : sc_nprime scene_geom_asan bs = sc_u16 bs).
{ unfold sc_nprime. cbn [sg_scene_n scene_geom_asan].
rewrite s1_land1 by lia. unfold sc_flags in Hc. rewrite Hc. reflexivity. }
paj_run_to_sh RUNTOP HS HJ 0x324.
{ apply (s1_awr _ _ _ _ (spZ (c_regs cx)) (c_sp1 cx)); [exact U9 | lia | lia]. }
assert (E24 : ew (Eimg (Ereg regs3 [])) 24 = w64 (sc_u16 bs))
by (rewrite (ew_Eimg_Ereg_nat regs3 [] 24%nat 24%bv eq_refl); exact V_u16).
pose proof (regs_kept_of_st_ok SEGS (Eimg (Ereg regs3 [])) _ (restrict (w_H W3) ms0) regs3 []
[2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl) as HK.
cbn [ms_regs restrict] in HK.
pose proof (st_ok_pi_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 9%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 15 0))]) HS eq_refl) as HR0.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 9%nat) 56 64 56 64 [YP09.mkChunk 56 (CVal 8
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1))))]) HS eq_refl) as HR1.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
(YP09.mkRegion (Some 9%nat) 72 80 72 80 [YP09.mkChunk 72 (CVal 8 (SOff 16 0))]) HS eq_refl) as HR2.
destruct HR0 as (_ & _ & _ & HK0). destruct HR1 as (_ & _ & _ & HK1). destruct HR2 as (_ & _ & _ & HK2).
cbn [ms_mem restrict YP09.r_chunks YP09.r_base base_val] in HK0, HK1, HK2.
rewrite U9 in HK0, HK1, HK2.
rewrite Forall_forall in HK0, HK1, HK2.
specialize (HK0 _ (or_introl eq_refl)). specialize (HK1 _ (or_introl eq_refl)).
specialize (HK2 _ (or_introl eq_refl)).
assert (Ra0 : getr (ms_regs ms0) 10%bv = w64 (sc_nn scene_geom_asan bs)).
{ refine (eq_trans (st_ok_pi_restrict_reg (w_H W3) (Eimg (Ereg regs3 [])) _ ms0 (10%bv) HS) _).
change (sv_denot (Eimg (Ereg regs3 []))
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1))) = w64 (sc_nn scene_geom_asan bs)).
rewrite (s1_nn_val _ (sc_u16 bs) ltac:(lia) E24). unfold sc_nn. rewrite Hnp. reflexivity. }
pmkst HS.
apply (MAIN (ms_regs ms0) (ms_mem ms0)).
+ unfold s1_rk. repeat split.
  * rewrite (HK 2%bv ltac:(cbn; tauto)). unfold spZ in Hsp3. rewrite <- Hsp3.
unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  * rewrite (HK 3%bv ltac:(cbn; tauto)). exact Hgp3.
  * rewrite (HK 4%bv ltac:(cbn; tauto)). exact Htp3.
  * rewrite (HK 8%bv ltac:(cbn; tauto)). exact V_sp0.
  * rewrite (HK 9%bv ltac:(cbn; tauto)). exact V_sp1.
  * rewrite (HK 18%bv ltac:(cbn; tauto)). exact V_s7v.
  * rewrite (HK 19%bv ltac:(cbn; tauto)). exact V_shF.
  * rewrite (HK 21%bv ltac:(cbn; tauto)). exact V_rest.
  * rewrite (HK 22%bv ltac:(cbn; tauto)). exact V_cur.
  * rewrite (HK 23%bv ltac:(cbn; tauto)). exact V_F.
  * rewrite (HK 24%bv ltac:(cbn; tauto)), Hnp. exact V_u16.
  * rewrite (HK 25%bv ltac:(cbn; tauto)). exact V_blki.
  * rewrite (HK 26%bv ltac:(cbn; tauto)). exact V_shb.
  * rewrite (HK 27%bv ltac:(cbn; tauto)). exact V_blk.
+ exact Ra0.
+ exact HJ.
+ intros a Ha Hna.
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr1
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 24 (SOff 15 0)); [exact HK0 | | lia].
cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regs3 [] 15%nat 15%bv eq_refl), V_exp.
unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 56
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1)))); [exact HK1 | | lia].
rewrite (s1_nn_val _ (sc_u16 bs) ltac:(lia) E24). unfold sc_nn. rewrite Hnp. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 72 (SOff 16 0)); [exact HK2 | | lia].
cbn [sv_denot]. rewrite E16. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
- (* the flag's low bit is 1: n' is 8904 *)
rewrite (s1_cond_and1 _ (sc_flags bs) E16 Hfl256) in Hc.
assert (Hnp : sc_nprime scene_geom_asan bs = 8904).
{ unfold sc_nprime. cbn [sg_scene_n scene_geom_asan]. rewrite s1_land1 by lia.
unfold sc_flags in Hc. rewrite Hc. reflexivity. }
assert (Hnn : sc_nn scene_geom_asan bs = 8904) by (unfold sc_nn; rewrite Hnp; reflexivity).
paj_run_to_sh RUNTOP HS HJ 0x324.
{ apply (s1_awr _ _ _ _ (spZ (c_regs cx)) (c_sp1 cx)); [exact U9 | lia | lia]. }
pose proof (regs_kept_of_st_ok SEGS (Eimg (Ereg regs3 [])) _ (restrict (w_H W3) ms0) regs3 []
[2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 25; 26; 27]%bv HS HAG eq_refl) as HK.
cbn [ms_regs restrict] in HK.
pose proof (st_ok_pi_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 9%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 15 0))]) HS eq_refl) as HR0.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 9%nat) 56 64 56 64 [YP09.mkChunk 56 (CVal 8 (SLit 8904))]) HS eq_refl) as HR1.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
(YP09.mkRegion (Some 9%nat) 72 80 72 80 [YP09.mkChunk 72 (CVal 8 (SOff 16 0))]) HS eq_refl) as HR2.
destruct HR0 as (_ & _ & _ & HK0). destruct HR1 as (_ & _ & _ & HK1). destruct HR2 as (_ & _ & _ & HK2).
cbn [ms_mem restrict YP09.r_chunks YP09.r_base base_val] in HK0, HK1, HK2.
rewrite U9 in HK0, HK1, HK2.
rewrite Forall_forall in HK0, HK1, HK2.
specialize (HK0 _ (or_introl eq_refl)). specialize (HK1 _ (or_introl eq_refl)).
specialize (HK2 _ (or_introl eq_refl)).
assert (Ra0 : getr (ms_regs ms0) 10%bv = w64 (sc_nn scene_geom_asan bs)).
{ refine (eq_trans (st_ok_pi_restrict_reg (w_H W3) (Eimg (Ereg regs3 [])) _ ms0 (10%bv) HS) _).
change (sv_denot (Eimg (Ereg regs3 [])) (SLit 8904) = w64 (sc_nn scene_geom_asan bs)).
rewrite Hnn. reflexivity. }
assert (R24 : getr (ms_regs ms0) 24%bv = w64 (sc_nprime scene_geom_asan bs)).
{ refine (eq_trans (st_ok_pi_restrict_reg (w_H W3) (Eimg (Ereg regs3 [])) _ ms0 (24%bv) HS) _).
change (sv_denot (Eimg (Ereg regs3 [])) (SLit 8904) = w64 (sc_nprime scene_geom_asan bs)).
rewrite Hnp. reflexivity. }
pmkst HS.
apply (MAIN (ms_regs ms0) (ms_mem ms0)).
+ unfold s1_rk. repeat split.
  * rewrite (HK 2%bv ltac:(cbn; tauto)). unfold spZ in Hsp3. rewrite <- Hsp3.
unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  * rewrite (HK 3%bv ltac:(cbn; tauto)). exact Hgp3.
  * rewrite (HK 4%bv ltac:(cbn; tauto)). exact Htp3.
  * rewrite (HK 8%bv ltac:(cbn; tauto)). exact V_sp0.
  * rewrite (HK 9%bv ltac:(cbn; tauto)). exact V_sp1.
  * rewrite (HK 18%bv ltac:(cbn; tauto)). exact V_s7v.
  * rewrite (HK 19%bv ltac:(cbn; tauto)). exact V_shF.
  * rewrite (HK 21%bv ltac:(cbn; tauto)). exact V_rest.
  * rewrite (HK 22%bv ltac:(cbn; tauto)). exact V_cur.
  * rewrite (HK 23%bv ltac:(cbn; tauto)). exact V_F.
  * exact R24.
  * rewrite (HK 25%bv ltac:(cbn; tauto)). exact V_blki.
  * rewrite (HK 26%bv ltac:(cbn; tauto)). exact V_shb.
  * rewrite (HK 27%bv ltac:(cbn; tauto)). exact V_blk.
+ exact Ra0.
+ exact HJ.
+ intros a Ha Hna.
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr1
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 24 (SOff 15 0)); [exact HK0 | | lia].
cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regs3 [] 15%nat 15%bv eq_refl), V_exp.
unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 56 (SLit 8904)); [exact HK1 | | lia].
rewrite Hnn. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 72 (SOff 16 0)); [exact HK2 | | lia].
cbn [sv_denot]. rewrite E16. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
Qed.
End s1.
