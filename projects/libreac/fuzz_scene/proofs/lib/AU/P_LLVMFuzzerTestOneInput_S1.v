(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: SEGMENT S1 of the ASan+UBSan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput, cut C1 (0x82c28) to cut C2 (0x82d94): the n' / n'' computation and its three spills
   ([s1+0x18] F, [s1+0x20] n'', [s1+0x58] flags), __wrap_malloc at 0x82c4c (ra 0x82c50) with the NULL abort
   refuted, the fill loop over reac_scene_placeholder and the xor loop over the rest of the input, each closed by
   induction on its turns.  The statement is lib/AU/P_LLVMFuzzerTestOneInput_seg.v's `seg_S1_stmt`, which this
   file does not restate and does not change (rule 24: one segment, not the function); `llvmf_S1` proves it.
   The asan twin of this segment is a working branch 7b2b57c5429 (lib/A/P_LLVMFuzzerTestOneInput_S1.v),
   whose walk shape (MAIN at the call, three one-word stack regions, the NULL refutation) this file mirrors. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import ScenePaLib SceneBase SceneFrame SceneRo.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC1h YC45 YC4b YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section s1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* fully qualified: the tree also holds lib/U/Reusable/YI16.v, and a short `YI16` can resolve to it (measured by a Theorem Labs lane) *)
Context {SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head}.
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

(* ---- the symbolic state at C1.  S1 writes exactly three slots of the caller frame: [s1+0x18] (F, 0x82c28),
   [s1+0x20] (n'', 0x82c48) and [s1+0x58] (the flags byte, 0x82c2c), and each is its OWN one-word region (the
   shape of the asan twin's s1_r_exp / s1_r_nn / s1_r_fl).  The three windows are the run's whole write set, so
   `frame_of` keeps every other byte: the spills [s1+0x10], [s1+0x28], [s1+0x30], [s1+0x38] that C2 reads back,
   and the 13 callee-saved words of `sc_saves` at [sp0-104, sp0) the caller chain of the malloc call is read
   from.  c_sp1 + 0x60 <= sp0 - 224 + 96 = sp0 - 128 < sp0 - 104. ---- *)
Definition S1_pc1 : Z := AF_LLVMFuzzerTestOneInput + SEG_C1_off.
Definition s1_r_F : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition s1_r_nn : YP09.region := YP09.mkRegion (Some 9%nat) 32 40 32 40 [].
Definition s1_r_fl : YP09.region := YP09.mkRegion (Some 9%nat) 88 96 88 96 [].
Definition s1_facts0 : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) ] [] [].
Definition s1_ss0 : sstate := mkSS S1_pc1 sr_atoms [s1_r_F; s1_r_nn; s1_r_fl] None s1_facts0.
(* the bytes the three stack regions may write, around sp1 *)
Definition s1_prot (sp1 a : Z) : Prop :=
sp1 + 24 <= a < sp1 + 32 \/ sp1 + 32 <= a < sp1 + 40 \/ sp1 + 88 <= a < sp1 + 96.
(* the runtime shadow base lives in s10 = x26 (atom 26) from C1 to C2 *)
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
(BASE + AF_LLVMFuzzerTestOneInput + 0x3ac) (BASE + AF_LLVMFuzzerTestOneInput + 0x5cc)
(BASE + AF_LLVMFuzzerTestOneInput + 0x708) (BASE + AF_LLVMFuzzerTestOneInput + 0x6fc)
(BASE + AF_LLVMFuzzerTestOneInput + 0x8bc) (BASE + AF_LLVMFuzzerTestOneInput + 0x8c4) (as_universe B).
(* The walk kit's read-only window is the listing's: the cut states arodata_okS over (sw_rlo WK) / (sw_rhi WK)
   while RO is ro_below_ofl over pa_relro_lo / pa_relro_hi.  A Theorem Labs lane's final ruling (04:xxZ): these two lines
   go verbatim in EACH segment's own Section, beside Variable WK; the top discharges them by eq_refl. *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* The statement's HRO_PLGOT (at be134c66f29, Section h), verbatim: the two negative
   conditions arodata_okS needs to read the fill loop's GOT word (object 4, VAL (A_OBJ 4) = 0x9c6b8), whose value
   0x20e80 = &reac_scene_placeholder.  Kept here because a segment file does not Require the statement file; the
   composition discharges it.  (The statement's HRO_PL is not needed by S1: the fill loop never reads the
   placeholder byte's VALUE, only its presence, HIMG_PL below.) *)
Hypothesis HRO_PLGOT : forall i, 0 <= i < 8 ->
~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4).
(* the placeholder's static zero shadow: the statement's own HZS_PL (lib/AU/P_LLVMFuzzerTestOneInput.v Section h,
   `in_zs B A_reac_scene_placeholder LLVMF_SCENE_BYTES`, A_reac_scene_placeholder = 0x20e80, LLVMF_SCENE_BYTES =
   8904).  8904 = 8 * 1113 whole granules, so its redzone cells (HB_C_PL) are not needed by S1. *)
Hypothesis HZS_PL : in_zs B 0x20e80 8904.
(* Every byte of reac_scene_placeholder [0x20e80, 0x20e80 + 8904) is a ROM byte.  Presence is all the fill loop
   needs (aview falls back to seg_rom; the loaded byte is dead, C2's bb being existential).  Decided on the image
   in ONE vm_compute over a forallb of the 8904 addresses (the asan twin's s1_pl_rom, at
   7b2b57c5429 lib/A/P_LLVMFuzzerTestOneInput_S1.v:246).  Measured: a scratch copy of this file with it compiled in
   43.6 s against 43 s without it; the costly form is a separate closed term per address, not this one. *)
Lemma HIMG_PL : forall i, 0 <= i < 8904 -> seg_rom SEGS (Z_to_bv 64 (0x20e80 + i)) <> None.
Proof.
assert (Hb : forallb (fun k => match seg_rom SEGS (Z_to_bv 64 (0x20e80 + Z.of_nat k)) with
Some _ => true | None => false end) (seq 0 8904) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. intros i Hi.
assert (Hin : In (Z.to_nat i) (seq 0 8904)).
{ apply in_seq. split; [apply Nat.le_0_l|]. rewrite Nat.add_0_l.
change 8904%nat with (Z.to_nat 8904). apply Z2Nat.inj_lt; lia. }
specialize (Hb _ Hin). rewrite Z2Nat.id in Hb by lia.
destruct (seg_rom SEGS (Z_to_bv 64 (0x20e80 + i))); [discriminate | discriminate Hb].
Qed.
(* the GOT word's 8 ROM bytes spell 0x20e80, per byte on closed terms (the method of a Theorem Labs lane's s2u_tt) *)
Lemma HIMG_PLGOT : forall i, 0 <= i < 8 ->
seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 4) + i)) = Some (Z_to_bv 8 (Z.shiftr 0x20e80 (8 * i))).
Proof.
intros i Hi.
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; f_equal; apply bv_eq; reflexivity.
Qed.

(* ---- S1's entry block: cut C1 rebuilt as the walk's symbolic state at 0x82c28, with the two premises the
   token run asks for besides it (the shadow table is empty here: nothing between C1 and the malloc call runs
   an ASan check), and the write permission for the three spill slots. ---- *)
Lemma s1_entry : forall (cx : rtcx SEGS) ly3 S3 W3 (regs3 : bvmap 5 word) mem3 md3 bs,
sc_base SEGS B ameter_triv WK cx ->
cut_C1 SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly3 S3 W3 regs3 mem3 md3 bs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs3 [])) s1_ss0
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + S1_pc1)) mem3 (seg_rom SEGS))) /\
sh_ok SEGS s1_Bx s1_SH (Eimg (Ereg regs3 [])) (mrestrict (w_H W3) mem3) /\
awr_ok (Eimg (Ereg regs3 [])) (ss_mem s1_ss0) (sw_stk WK) (spZ (c_regs cx)) []
(ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)].
Proof.
intros cx ly3 S3 W3 regs3 mem3 md3 bs HBASE HC1.
destruct HBASE as (HB0 & Hsp1).
destruct HB0 as (HPRE & Hra & H10 & H11 & Hpn & Hfrs & Hnev & Hlive & Hrod & Hsink & Hfd & Hfs & Hmok).
destruct HC1 as (HJ & Hab & Hbb & HFR & HSV & HSBG & HSHi & HSHk & HOPEN & HIMG & HIN & HMAC &
V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_shb & V_blki & V_blk & V_exp & V_mac & V_shexp & V_flags & V_u16 & V_rest & V_cur & V_step & V_s7v).
cbn [vat scene_geom_asan_ubsan sg1_sp1] in V_sp1.
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
apply (pa_entry_st_ok_full E S1_pc1 sr_atoms regs3 [s1_r_F; s1_r_nn; s1_r_fl] s1_facts0 (mrestrict (w_H W3) mem3)).
  + subst E; apply regs_ok_Eimg_Ereg.
  + vm_compute; reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold s1_r_F, s1_r_nn, s1_r_fl, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite U9; (split; [lia|]); (split; [lia|]); (split; [|constructor]);
    intros o Ho; apply (apresent_writable SEGS); apply Hpres3; lia.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val s1_r_F s1_r_nn s1_r_fl]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + unfold s1_facts0. split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
split; [|exact I]. split; [lia|]. split; [|lia].
rewrite Hsp1. change (2 ^ 5) with 32. rewrite Z.mul_comm. apply Z_mod_mult.
- apply Forall_nil.
- unfold s1_ss0, s1_r_F, s1_r_nn, s1_r_fl; cbn [ss_mem].
do 3 (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
[ reflexivity | cbn [YP09.r_base]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]).
apply awr_ok_nil.
Qed.

(* ---- the caller chain at any state of the segment, over the 13 saved words `sc_saves` carries.  Every call
   of the walk needs it for `chain_pre`. ---- *)
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

(* ---- the write permission for the three one-word regions of the segment, at any point of it: a run asks for
   it again after every station, and only each region's base and window matter (not the chunks collected). ---- *)
Lemma s1_awr : forall (Ez : env) (c1 c2 c3 : list YP09.chunk) (sp0 sp1v : Z) (FP : list (Z * Z))
(bl0 blc : list (Z * Z)) (ly : alayout) (own : list (Z * Z)),
bv_unsigned (ew Ez 9) = sp1v -> - sw_stk WK <= sp1v - sp0 + 24 -> sp1v - sp0 + 96 <= 0 ->
awr_ok Ez [YP09.mkRegion (Some 9%nat) 24 32 24 32 c1; YP09.mkRegion (Some 9%nat) 32 40 32 40 c2;
YP09.mkRegion (Some 9%nat) 88 96 88 96 c3] (sw_stk WK) sp0 FP bl0 blc ly own.
Proof.
intros Ez c1 c2 c3 sp0 sp1v FP bl0 blc ly own U9 Hlo Hhi.
do 3 (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1v - sp0));
[ reflexivity | cbn [YP09.r_base]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]).
apply awr_ok_nil.
Qed.

(* ================================================================================================================
   The interface between the three pieces of the walk.  `s1_cmem` is what every state of the segment keeps about
   memory, `s1_spills` the seven spilled words of the caller frame, `s1_regs0` / `s1_regs1` the register rows, and
   `s1_stateA` / `s1_stateB` / `s1_stateC2` the three machine-level points inside the segment:
     A  0x82c54, the instruction after the NULL test of the malloc return (a0 = body);
     B  0x82cd8, the head of the xor block (t2 = body, a2 = ~body, the fill loop done);
     C2 0x82d94, the segment's exit cut.
   ================================================================================================================ *)
Definition s1F (cx : rtcx SEGS) : Z := sc_F SEGS scene_geom_asan_ubsan cx.
Definition s1_cmem (cx : rtcx SEGS) (bs : Z -> Z) (W' : world SEGS) (mem' : word -> option byte) : Prop :=
sc_frame SEGS scene_geom_asan_ubsan cx W' mem' /\
sc_saves SEGS cx W' mem' /\
sc_shbg SEGS scene_geom_asan_ubsan cx W' mem' /\
sc_shr SEGS scene_geom_asan_ubsan cx W' mem'
(sg_sh_blki_lo scene_geom_asan_ubsan) (sg_sh_blki_hi scene_geom_asan_ubsan) 0xf8 /\
sc_shr SEGS scene_geom_asan_ubsan cx W' mem'
(sg_sh_blk_lo scene_geom_asan_ubsan) (sg_sh_blk_hi scene_geom_asan_ubsan) 0xf8 /\
sc_open SEGS scene_geom_asan_ubsan cx W' mem'
(sg_off_mac scene_geom_asan_ubsan) (sg_mac_n scene_geom_asan_ubsan) /\
garr8 SEGS (mrestrict (w_H W') mem')
(s1F cx + sg_off_mac scene_geom_asan_ubsan) (sc_macb bs) /\
arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W') mem').
Definition s1_spills (cx : rtcx SEGS) (bs : Z -> Z) (W' : world SEGS) (mem' : word -> option byte) : Prop :=
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x10)
= Some (shadow_addr (s1F cx) + sg_off_expect scene_geom_asan_ubsan / 8) /\
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x18) = Some (s1F cx) /\
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x20) = Some (sc_nn scene_geom_asan_ubsan bs) /\
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x28) = Some (s1F cx) /\
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x30)
= Some (s1F cx + sg_off_expect scene_geom_asan_ubsan) /\
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x38)
= Some (s1F cx + sg_off_mac scene_geom_asan_ubsan) /\
rdword (aview SEGS (w_H W') mem') (c_sp1 cx + 0x58) = Some (sc_flags bs).
(* the callee-saved row every later cut reads: sp / gp / tp, s0, s1, s2, s3, s4, s7, s8, s9, s10, s11 *)
Definition s1_regs0 (cx : rtcx SEGS) (bs : Z -> Z) (regs' : bvmap 5 word) : Prop :=
spZ regs' = c_sp1 cx /\ getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
getr regs' 8 = w64 (spZ (c_regs cx)) /\ getr regs' 9 = w64 (c_sp1 cx) /\
getr regs' 18 = w64 (s1F cx) /\ getr regs' 19 = w64 (shadow_addr (s1F cx)) /\
getr regs' 20 = w64 (sc_s7v bs mod 2 ^ 64) /\ getr regs' 23 = w64 (sc_step bs mod 2 ^ 64) /\
getr regs' 24 = w64 (sc_nprime scene_geom_asan_ubsan bs) /\
getr regs' 25 = w64 (s1F cx + sg_off_blki scene_geom_asan_ubsan) /\
getr regs' 26 = w64 SHADOW_OFF /\
getr regs' 27 = w64 (s1F cx + sg_off_blk scene_geom_asan_ubsan).
(* ... plus the two the xor block consumes and C2 does not keep *)
Definition s1_regs1 (cx : rtcx SEGS) (bs : Z -> Z) (regs' : bvmap 5 word) : Prop :=
s1_regs0 cx bs regs' /\ getr regs' 21 = w64 (sc_rest SEGS cx) /\ getr regs' 22 = w64 (sc_cur SEGS cx).
Definition s1_jmem (cx : rtcx SEGS) (bs : Z -> Z) (body : Z) (ly' : alayout) (S' : astate)
(W' : world SEGS) (mem' : word -> option byte) (md' : Model) : Prop :=
sc_j SEGS B ameter_triv WK scene_geom_asan_ubsan cx ly' S' W' mem' md' 1 /\
ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ++ [(body, sc_nn scene_geom_asan_ubsan bs)] /\
blocks_bytes S' <= blocks_bytes (c_S cx) + req_size (sc_nn scene_geom_asan_ubsan bs) /\
s1_cmem cx bs W' mem' /\ s1_spills cx bs W' mem'.
Definition s1_stateA (cx : rtcx SEGS) (bs : Z -> Z) (body : Z) (ly' : alayout) (S' : astate)
(W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
s1_jmem cx bs body ly' S' W' mem' md' /\ s1_regs1 cx bs regs' /\ getr regs' 10 = w64 body.
Definition s1_stateB (cx : rtcx SEGS) (bs : Z -> Z) (body : Z) (ly' : alayout) (S' : astate)
(W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
s1_jmem cx bs body ly' S' W' mem' md' /\ s1_regs1 cx bs regs' /\
getr regs' 7 = w64 body /\ getr regs' 12 = w64 (2 ^ 64 - 1 - body).
Definition s1_stateC2 (cx : rtcx SEGS) (bs : Z -> Z) (body : Z) (ly' : alayout) (S' : astate)
(W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
s1_jmem cx bs body ly' S' W' mem' md' /\ s1_regs0 cx bs regs' /\ getr regs' 7 = w64 body.
(* the facts about the fresh block that no state changes *)
Definition s1_blk (cx : rtcx SEGS) (bs : Z -> Z) (body : Z) : Prop :=
sc_blk_ok SEGS B WK cx body (sc_nn scene_geom_asan_ubsan bs) /\
1 <= sc_nn scene_geom_asan_ubsan bs <= 65535 /\ body mod 16 = 0 /\ 4096 <= body /\
body + req_size (sc_nn scene_geom_asan_ubsan bs) <= alloc_ceiling.
(* the pcs of the segment, as offsets in LLVMFuzzerTestOneInput *)
Definition S1_pcA : Z := AF_LLVMFuzzerTestOneInput + 0x3b0.
Definition S1_pcB : Z := AF_LLVMFuzzerTestOneInput + 0x434.
Definition S1_pcC2 : Z := AF_LLVMFuzzerTestOneInput + SEG_C2_off.

(* ================================================================================================================
   The two loops, each a self-contained CPS lemma.  `s1_fill_block` walks 0x82c54 -> 0x82cd8 (the fill loop over
   reac_scene_placeholder); `s1_xor_block` walks 0x82cd8 -> 0x82d94 (the xor loop over the rest of the input).
   Each takes its entry state and a continuation from its exit state, and is proved by fuel induction (model:
   cgif YC8a.v tcbb_loop).
   ================================================================================================================ *)
Lemma s1_fill_block : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop) (bs : Z -> Z) (body : Z)
ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md',
sc_base SEGS B ameter_triv WK cx ->
s1_stateA cx bs body ly' S' W' regs' mem' md' -> s1_blk cx bs body ->
(forall ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
s1_stateB cx bs body ly2 S2 W2 regs2 mem2 md2 ->
SRr SEGS W2 (cfg_at SEGS (BASE + S1_pcB) regs2 mem2 md2) POST) ->
SRr SEGS W' (cfg_at SEGS (BASE + S1_pcA) regs' mem' md') POST.
Proof.
intros cx POST bs body ly' S' W' regs' mem' md' Hbase HA Hblk HNEXT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof Hbase as Hbase'.
destruct Hbase as (HB0 & Hsp1).
pose proof HB0 as (HPRE & Hra & H10c & H11c & Hpn & Hfrs0 & Hnev & Hlive & Hrod & Hsink & Hfd & Hfs & Hmok).
pose proof HPRE as (HAR0 & Hra1 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & Hstk00 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hblk as (Hbok & Hnnr & Hbody16 & Hbody4096 & Hbodyceil).
pose proof Hbok as (Hb4096z & Hbzone2 & Hbceilz & Hb16z & Hawrb & Haftok).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HSTKw : 16624 <= sw_stk WK) by lia.
pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 224) 32) as Hdm.
pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)) as Hmb.
assert (Hsp1lo : spZ (c_regs cx) - 256 <= c_sp1 cx) by (rewrite Hsp1; lia).
assert (Hsp1hi : c_sp1 cx <= spZ (c_regs cx) - 224) by (rewrite Hsp1; lia).
assert (Hrq : req_size (sc_nn scene_geom_asan_ubsan bs) = sc_nn scene_geom_asan_ubsan bs)
by (unfold req_size; destruct (Z.eqb_spec (sc_nn scene_geom_asan_ubsan bs) 0); lia).
assert (HFB : fs_frame_bytes (sg_cid scene_geom_asan_ubsan) = 16384) by (vm_compute; reflexivity).
(* ---- memory agreement outside the written byte range ---- *)
assert (AVEQ : forall (H : word -> bool) (m m2 : word -> option byte) (a : Z),
m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte SEGS (mrestrict H m2) a = mbyte SEGS (mrestrict H m) a).
{ intros H m m2 a Hx. unfold mbyte, mrestrict. rewrite Hx. reflexivity. }
assert (AVW : forall (H : word -> bool) (m m2 : word -> option byte) (a : Z),
m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m2 a = aview SEGS H m a).
{ intros H m m2 a Hx. unfold aview. rewrite (AVEQ H m m2 a Hx). reflexivity. }
assert (RDW : forall (H : word -> bool) (m m2 : word -> option byte) (a : Z),
(forall x, a <= x < a + 8 -> aview SEGS H m2 x = aview SEGS H m x) ->
rdword (aview SEGS H m2) a = rdword (aview SEGS H m) a).
{ intros H m m2 a Hk. unfold rdword.
rewrite (Hk a ltac:(lia)), (Hk (a+1) ltac:(lia)), (Hk (a+2) ltac:(lia)), (Hk (a+3) ltac:(lia)),
(Hk (a+4) ltac:(lia)), (Hk (a+5) ltac:(lia)), (Hk (a+6) ltac:(lia)), (Hk (a+7) ltac:(lia)).
reflexivity. }
(* ---- the segment-level facts every state of the block keeps ---- *)
assert (TRANS : forall (W2 : world SEGS) (m m2 : word -> option byte) ly2 S2 md2,
s1_jmem cx bs body ly2 S2 W2 m md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W2) m2) ->
s1_cmem cx bs W2 m2 /\ s1_spills cx bs W2 m2).
{ intros W2 m m2 ly2 S2 md2 HJM MK HROD2.
pose proof HJM as (HJ2 & Hab2 & Hbb2 & HCM2 & HSP2).
pose proof HJ2 as (HJJ & Hfrs2 & Hmle2).
pose proof (proj1 HJJ) as HAR2.
pose proof HJJ as (_ & Hly2 & _).
destruct (al_layout SEGS B LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly2 HAR0 Hly2) as (_ & Efa & _).
assert (Hin2 : In (body, sc_nn scene_geom_asan_ubsan bs) (ablocks B ly2 S2))
by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
assert (Hfin2 : In (sg_cid scene_geom_asan_ubsan, c_fpos cx) (frames S2))
by (rewrite Hfrs2; left; reflexivity).
assert (EFA : frame_addr ly2 (sg_cid scene_geom_asan_ubsan) (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx)
by (rewrite Efa; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 m md2 body (sc_nn scene_geom_asan_ubsan bs)
(sg_cid scene_geom_asan_ubsan) (c_fpos cx) HAR2 Hin2 Hfin2) as HSEP.
pose proof (frames_bounds SEGS B LAWS ly2 S2 W2 m md2 (sg_cid scene_geom_asan_ubsan) (c_fpos cx) HAR2 Hfin2)
as (HF4096 & HFceil & HFapp).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m md2 body (sc_nn scene_geom_asan_ubsan bs) HAR2 Hin2)
as (_ & _ & _ & HBapp & _).
unfold zdisjoint in HSEP. cbn [fst snd] in HSEP.
rewrite EFA, HFB, Hrq in HSEP. rewrite EFA in HF4096. rewrite EFA, HFB in HFceil, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HBapp.
rewrite Hrq in HBapp.
assert (HFd0 : 0 <= sc_F SEGS scene_geom_asan_ubsan cx / 8) by (apply Z.div_pos; lia).
assert (HFd1 : sc_F SEGS scene_geom_asan_ubsan cx / 8 <= 17592184995840).
{ replace 17592184995840 with (140737479966720 / 8) by reflexivity. apply Z.div_le_mono; lia. }
assert (HM8 : (sc_F SEGS scene_geom_asan_ubsan cx + 112) / 8 = sc_F SEGS scene_geom_asan_ubsan cx / 8 + 14).
{ replace (sc_F SEGS scene_geom_asan_ubsan cx + 112) with (sc_F SEGS scene_geom_asan_ubsan cx + 14 * 8) by lia.
apply Z_div_plus. lia. }
assert (DFR : forall x, sc_F SEGS scene_geom_asan_ubsan cx <= x < sc_F SEGS scene_geom_asan_ubsan cx + 16384 ->
0 <= x < 2 ^ 64 /\ ~ (body <= x < body + sc_nn scene_geom_asan_ubsan bs)).
{ intros x Hx. split; [lia|]. lia. }
assert (DSH : forall x, shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) <= x <=
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048 ->
0 <= x < 2 ^ 64 /\ ~ (body <= x < body + sc_nn scene_geom_asan_ubsan bs)).
{ intros x Hx. unfold shadow_addr, SHADOW_OFF in Hx. split; [lia|]. lia. }
assert (DST : forall x, spZ (c_regs cx) - 112 <= x < spZ (c_regs cx) ->
0 <= x < 2 ^ 64 /\ ~ (body <= x < body + sc_nn scene_geom_asan_ubsan bs)).
{ intros x Hx. split; [lia|]. lia. }
assert (DSP : forall x, c_sp1 cx + 16 <= x < c_sp1 cx + 96 ->
0 <= x < 2 ^ 64 /\ ~ (body <= x < body + sc_nn scene_geom_asan_ubsan bs)).
{ intros x Hx. split; [lia|]. lia. }
assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (body <= x < body + sc_nn scene_geom_asan_ubsan bs) ->
aview SEGS (w_H W2) m2 x = aview SEGS (w_H W2) m x)
by (intros x H1 H2; apply AVW; apply MK; assumption).
pose proof HCM2 as (HFRM & HSAV & HSBG & HSH1 & HSH2 & HOPEN & HMAC & _).
split.
- split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  + pose proof HFRM as (HFL & HFP & HFSP). split; [|split].
    * rewrite (RDW (w_H W2) m m2); [exact HFL|].
intros x Hx. rewrite HFB in Hx. apply KEEP; [apply (DFR x); lia | apply (DFR x); lia].
    * intros a Ha. rewrite HFB in Ha. unfold apresent in HFP |- *.
destruct (HFP a ltac:(rewrite HFB; exact Ha)) as (H1 & b & H2).
split; [exact H1|]. exists b. rewrite (MK a ltac:(apply (DFR a); lia) ltac:(apply (DFR a); lia)). exact H2.
    * intros a Ha. rewrite HFB in Ha. change (16384 / 8) with 2048 in Ha.
unfold apresent in HFSP |- *.
destruct (HFSP a ltac:(rewrite HFB; change (16384 / 8) with 2048; exact Ha)) as (H1 & b & H2).
split; [exact H1|]. exists b. rewrite (MK a ltac:(apply (DSH a); lia) ltac:(apply (DSH a); lia)). exact H2.
  + intros j Hj. rewrite (RDW (w_H W2) m m2); [exact (HSAV j Hj)|].
intros x Hx. apply KEEP; [apply (DST x); lia | apply (DST x); lia].
  + apply Forall_forall. intros t Ht.
pose proof (proj1 (Forall_forall _ _) HSBG t Ht) as Ht2.
assert (Htb : 0 <= fst (fst t) /\ snd (fst t) <= 2048)
by (cbn [sg_sh_bg scene_geom_asan_ubsan] in Ht;
destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd]; lia).
intros o Ho. rewrite KEEP; [exact (Ht2 o Ho)
| apply (DSH (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o)); lia
| apply (DSH (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o)); lia].
  + intros o Ho. cbn [sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan_ubsan] in Ho.
rewrite KEEP; [exact (HSH1 o ltac:(cbn [sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan_ubsan]; lia))
| apply (DSH (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o)); lia
| apply (DSH (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o)); lia].
  + intros o Ho. cbn [sg_sh_blk_lo sg_sh_blk_hi scene_geom_asan_ubsan] in Ho.
rewrite KEEP; [exact (HSH2 o ltac:(cbn [sg_sh_blk_lo sg_sh_blk_hi scene_geom_asan_ubsan]; lia))
| apply (DSH (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o)); lia
| apply (DSH (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + o)); lia].
  + unfold sc_open, block_shadow in HOPEN |- *.
cbn [sg_off_mac sg_mac_n scene_geom_asan_ubsan] in HOPEN |- *.
destruct HOPEN as (HO1 & HO2 & HO3). split; [exact HO1|]. split; [exact HO2|].
intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
assert (HXs : shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) <=
shadow_of_addr SHADOW_OFF (sc_F SEGS scene_geom_asan_ubsan cx + 112) + i <=
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048)
by (unfold shadow_of_addr, shadow_addr; rewrite HM8; lia).
rewrite KEEP; [exact (HO3 i Hi) | exact (proj1 (DSH _ HXs)) | exact (proj2 (DSH _ HXs))].
  + unfold garr8 in HMAC |- *. cbn [sg_off_mac scene_geom_asan_ubsan] in HMAC |- *.
intros j Hj. destruct (HMAC j Hj) as (HV & HBv). split; [|exact HBv].
unfold val_mem in HV |- *. intros k Hk. rewrite (AVEQ (w_H W2) m m2); [exact (HV k Hk)|].
apply MK; [apply (DFR (sc_F SEGS scene_geom_asan_ubsan cx + 112 + Z.of_nat j + Z.of_nat k));
cbn [length sc_macb] in Hj; lia
| apply (DFR (sc_F SEGS scene_geom_asan_ubsan cx + 112 + Z.of_nat j + Z.of_nat k));
cbn [length sc_macb] in Hj; lia].
  + exact HROD2.
- pose proof HSP2 as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [|split; [|split; [|split; [|split; [|split]]]]];
(rewrite (RDW (w_H W2) m m2); [first [exact P1|exact P2|exact P3|exact P4|exact P5|exact P6|exact P7]|]);
(intros x Hx; apply KEEP; [apply (DSP x); lia | apply (DSP x); lia]). }
(* ---- the entry state at 0x82c54 ---- *)
pose proof HA as ((HJ1 & Hab1 & Hbb1 & HCM1 & HSP1) & HR1 & R10).
pose proof HJ1 as (HJ & Hfrs1 & Hmle1).
pose proof HR1 as (HR0 & R21 & R22).
pose proof HR0 as (Rsp & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
pose proof HCM1 as (HFRM1 & HSAV1 & HSBG1 & HSHa1 & HSHb1 & HOPEN1 & HMAC1 & HROD1).
assert (EGOT : VAL (A_OBJ 4) = 0x9c6b8) by (vm_compute; reflexivity).
assert (ERLO : pa_relro_lo = 636128) by (vm_compute; reflexivity).
assert (ERHI : pa_relro_hi = 640832) by (vm_compute; reflexivity).
assert (Hnpc : sc_nprime scene_geom_asan_ubsan bs = 0 \/
(1 <= sc_nprime scene_geom_asan_ubsan bs <= 65535 /\
sc_nn scene_geom_asan_ubsan bs = sc_nprime scene_geom_asan_ubsan bs)).
{ destruct (Z.eqb_spec (sc_nprime scene_geom_asan_ubsan bs) 0) as [Hz|Hz]; [left; exact Hz|].
right. assert (Hnn' : sc_nn scene_geom_asan_ubsan bs = sc_nprime scene_geom_asan_ubsan bs)
by (unfold sc_nn; rewrite (proj2 (Z.eqb_neq _ _) Hz); reflexivity).
rewrite Hnn' in Hnnr. split; [exact Hnnr | exact Hnn']. }
assert (Hbodyr : 0 <= body < 2 ^ 64) by lia.
remember (Eimg (Ereg regs' [])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (ER0 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs' r)
by (intros n r Hn Hr; subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E10 : ew E0 10 = Z_to_bv 64 body)
by (rewrite (ER0 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
assert (E24 : ew E0 24 = Z_to_bv 64 (sc_nprime scene_geom_asan_ubsan bs))
by (rewrite (ER0 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
assert (U24 : U E0 (SOff 24 0) = sc_nprime scene_geom_asan_ubsan bs)
by (apply (U_atom E0 24 _ E24); destruct Hnpc as [HZ|(HZ&_)]; lia).
assert (HS : st_ok_pi SEGS VAL E0
(mkSS S1_pcA sr_atoms
[YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0x20e80))]] None
(mkFacts [] [] []))
(restrict (w_H W') (mkst regs' (Z_to_bv 64 (BASE + S1_pcA)) mem' (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E0; apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- constructor; [|constructor]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
assert (EG4 : ew E0 (A_OBJ 4) = Z_to_bv 64 (VAL (A_OBJ 4)))
by (subst E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite EG4, EGOT, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
intros k Hk. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hk |- *.
exists (byte_of_word (sv_denot E0 (SLit 0x20e80)) k). split; [reflexivity|].
pose proof (HROD1 (VAL (A_OBJ 4) + k)
ltac:(right; rewrite HWRLO, HWRHI, ERLO, ERHI, EGOT; lia)
(proj1 (HRO_PLGOT k Hk)) (proj2 (HRO_PLGOT k Hk))) as HAv.
unfold aview in HAv. rewrite (HIMG_PLGOT k Hk) in HAv. cbn [option_map] in HAv.
replace (0x9c6b8 + 0 + k) with (VAL (A_OBJ 4) + k) by (rewrite EGOT; lia).
destruct (mbyte SEGS (mrestrict (w_H W') mem') (VAL (A_OBJ 4) + k)) as [bb|] eqn:Hmbg;
cbn [option_map] in HAv; [|discriminate HAv].
injection HAv as HAv. f_equal. apply bv_eq. rewrite HAv.
cbn [sv_denot]. unfold byte_of_word. rewrite !unsigned_lit_small by lia.
rewrite !Z_to_bv_unsigned. reflexivity.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [exact I | split; [exact I | exact I]]. }
assert (SHOK : sh_ok SEGS s1_Bx (@nil shent) E0 (mrestrict (w_H W') mem')) by (apply Forall_nil).
unfold cfg_at. change (w64 (BASE + S1_pcA)) with (Z_to_bv 64 (BASE + S1_pcA)).
paj_run_to_tok RUNTO HS HJ SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x3b8).
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
pose proof (frame_of_read_only E0
[YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0x20e80))]] _ _
ltac:(vm_compute; reflexivity) HF) as MEQ0.
clear HF HFr HG.
assert (HAE0 : env_agree 32 (Ereg regs' []) E0)
by (rewrite HE0; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (NOTB : alu64 ALU_XOR (ew E0 10) (Z_to_bv 64 (-1)) = w64 (2 ^ 64 - 1 - body)).
{ rewrite E10. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small body) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity. }
assert (LOOP : forall (k : nat) (i : Z) ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
Z.of_nat k = sc_nprime scene_geom_asan_ubsan bs - i -> 0 <= i < sc_nprime scene_geom_asan_ubsan bs ->
s1_jmem cx bs body ly2 S2 W2 mem2 md2 -> s1_regs1 cx bs regs2 ->
getr regs2 7 = w64 body -> getr regs2 12 = w64 (2 ^ 64 - 1 - body) ->
getr regs2 11 = w64 i -> getr regs2 13 = w64 134784 -> getr regs2 14 = w64 1112 ->
SRr SEGS W2 (cfg_at SEGS (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc)) regs2 mem2 md2) POST).
{ clear HS SHOK HJ HEI MEQ0.
assert (HRODE : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
by (rewrite <- HWRLO, <- HWRHI; exact Hrod).
induction k as [|k IH]; intros i ly2 S2 W2 regs2 mem2 md2 Hk Hi HJM HR2 Rb7 Rb12 Rb11 Rb13 Rb14; [lia|].
pose proof HJM as (HJ2 & Hab2 & Hbb2 & HCM2 & HSP2).
pose proof HJ2 as (HJL & Hfrs2 & Hmle2).
pose proof (proj1 HJL) as HAR2.
pose proof HR2 as (HR20 & R221 & R222).
pose proof HR20 as (Rsp2 & Rg3 & Rg4 & Rg8 & Rg9 & Rg18 & Rg19 & Rg20 & Rg23 & Rg24 & Rg25 & Rg26 & Rg27).
assert (Hnpnz : sc_nprime scene_geom_asan_ubsan bs <> 0) by lia.
assert (Hnneq : sc_nn scene_geom_asan_ubsan bs = sc_nprime scene_geom_asan_ubsan bs)
by (unfold sc_nn; rewrite (proj2 (Z.eqb_neq _ _) Hnpnz); reflexivity).
assert (Hnpb : 1 <= sc_nprime scene_geom_asan_ubsan bs <= 65535) by (rewrite <- Hnneq; lia).
assert (Hin2 : In (body, sc_nn scene_geom_asan_ubsan bs) (ablocks B ly2 S2))
by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 body (sc_nn scene_geom_asan_ubsan bs) HAR2 Hin2)
as (_ & _ & _ & HBapp2 & HBpres2 & _).
rewrite Hrq in HBapp2, HBpres2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HBapp2.
pose proof (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 body
(sc_nn scene_geom_asan_ubsan bs) body (sc_nn scene_geom_asan_ubsan bs) HAR2 Hin2
ltac:(lia) ltac:(rewrite Hrq; lia)) as RAB.
pose proof (ro_usable SEGS B LAWS ly2 S2 W2 mem2 md2 134784 8904 HAR2 HZS_PL) as RAPL.
destruct (Z_lt_ge_dec i 8904) as [Hilo | Hihi].
(* ---- i < 8904: the turn reads reac_scene_placeholder[i] ---- *)
+ assert (PLB : exists b : byte, mbyte SEGS (mrestrict (w_H W2) mem2) (134784 + i) = Some b).
{ unfold mbyte.
destruct (mrestrict (w_H W2) mem2 (Z_to_bv 64 (134784 + i))) as [b|] eqn:Hmm; [exists b; reflexivity|].
destruct (seg_rom SEGS (Z_to_bv 64 (134784 + i))) as [b|] eqn:Hss; [exists b; reflexivity|].
exfalso. apply (HIMG_PL i ltac:(lia)). exact Hss. }
destruct PLB as (plb & Hplb).
assert (Hplbr : 0 <= bv_unsigned plb < 256)
by (pose proof (bv_unsigned_in_range 8 plb) as Hpr; change (bv_modulus 8) with 256 in Hpr; lia).
remember (Eimg (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 (bv_unsigned plb)])) as E eqn:HE.
assert (HEIL : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAEL : env_agree 32 (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 (bv_unsigned plb)]) E)
by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn Hr; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (F7 : ew E 7 = Z_to_bv 64 body) by (rewrite (EE 7%nat 7%bv ltac:(lia) eq_refl); exact Rb7).
assert (F11 : ew E 11 = Z_to_bv 64 i) by (rewrite (EE 11%nat 11%bv ltac:(lia) eq_refl); exact Rb11).
assert (F12 : ew E 12 = Z_to_bv 64 (2 ^ 64 - 1 - body))
by (rewrite (EE 12%nat 12%bv ltac:(lia) eq_refl); exact Rb12).
assert (F24 : ew E 24 = Z_to_bv 64 (sc_nprime scene_geom_asan_ubsan bs))
by (rewrite (EE 24%nat 24%bv ltac:(lia) eq_refl); exact Rg24).
assert (F26 : ew E 26 = Z_to_bv 64 SHADOW_OFF)
by (rewrite (EE 26%nat 26%bv ltac:(lia) eq_refl); exact Rg26).
assert (F32 : ew E 32 = Z_to_bv 64 (body + i))
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 (bv_unsigned plb))
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (HBx : U E s1_Bx = SHADOW_OFF)
by (unfold s1_Bx; apply (U_atom E 26 SHADOW_OFF F26); unfold SHADOW_OFF; lia).
assert (U32 : U E (SOff 32 0) = body + i) by (apply (U_atom E 32 _ F32); lia).
assert (U11 : U E (SOff 11 0) = i) by (apply (U_atom E 11 _ F11); lia).
assert (HS : st_ok_pi SEGS VAL E
(mkSS (AF_LLVMFuzzerTestOneInput + 0x3cc)
(sr_set (sr_set sr_atoms 13%bv (SLit 134784)) 14%bv (SLit 1112))
[YP09.mkRegion (Some 11%nat) 134784 134785 0 0 [YP09.mkChunk 134784 (CVal 1 (SOff 33 0))];
YP09.mkRegion (Some 32%nat) 0 1 0 1 []] None
(mkFacts [(11%nat, mkAF 0 8903 0); (12%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1) 0);
(24%nat, mkAF 1 65535 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
(32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 0 255 0)] []
[(SAlu ALU_ADD (SOff 7 0) (SOff 11 0), SOff 32 0)]))
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply (regs_ok_pin E _ regs2 14%bv (SLit 1112));
[apply (regs_ok_pin E _ regs2 13%bv (SLit 134784));
[rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact Rb13]
| intros X; discriminate X | cbn [sv_denot]; exact Rb14].
- vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite F11, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
intros kk Hkk. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hkk |- *.
exists (byte_of_word (sv_denot E (SOff 33 0)) kk). split; [reflexivity|].
replace (i + 134784 + kk) with (134784 + i) by lia.
rewrite Hplb. f_equal.
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (bv_unsigned plb))
by (cbn [sv_denot]; rewrite F33, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
rewrite D33. unfold byte_of_word. rewrite unsigned_lit_small by lia.
replace kk with 0 by lia. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite F32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HBpres2 (body + i + o) ltac:(lia))).
- pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 body (sc_nn scene_geom_asan_ubsan bs) HAR2 Hin2) as HBimg.
unfold off_img in HBimg. rewrite Hrq in HBimg.
cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite F11, F32, !unsigned_lit_small by lia.
destruct HBimg as [Hz|Hz]; [right|left]; lia.
- split; [|split; [exact I | split; [|exact I]]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite F11, F12, F24, F26, F32, F33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
+ apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 7 body F7 ltac:(lia)), U11, U32.
rewrite zcanon_id by (unfold M64; lia). reflexivity. }
assert (SHOK : sh_ok SEGS s1_Bx [mkSHE 11 134784 134785; mkSHE 32 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W2) mem2 E s1_Bx 11 134784 8904 i 134784 134785
RAPL HBx U11 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W2) mem2 E s1_Bx 32 body (sc_nn scene_geom_asan_ubsan bs)
(body + i) 0 1 RAB HBx U32 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at.
change (w64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc)))
with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc))).
paj_run_to_tok RUNTO HS HJL SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x414).
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32%nat (body + i));
[reflexivity | rewrite F32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
replace a with (body + (a - body)) by lia.
apply (Hawrb (ablocks B ly2 S2) ly2 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] (a - body) Hin2).
rewrite Hrq. lia. }
lazymatch type of HF with frame_of _ _ ?mo ?mn =>
assert (MK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mo (Z_to_bv 64 a)) end.
{ intros a Ha Hn. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
rewrite F32, !unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (G7 : ew Ex 7 = Z_to_bv 64 body) by (cbn [ew ewset Nat.eqb]; exact F7);
assert (G11 : ew Ex 11 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact F11);
assert (G12 : ew Ex 12 = Z_to_bv 64 (2 ^ 64 - 1 - body)) by (cbn [ew ewset Nat.eqb]; exact F12);
assert (G24 : ew Ex 24 = Z_to_bv 64 (sc_nprime scene_geom_asan_ubsan bs))
by (cbn [ew ewset Nat.eqb]; exact F24);
assert (G32 : ew Ex 32 = Z_to_bv 64 (body + i)) by (cbn [ew ewset Nat.eqb]; exact F32)
end.
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
* (* the back edge: i + 1 < n' *)
rewrite branch_ne_U, (U_atom _ 24 _ G24 ltac:(lia)),
(U_atom_off _ 11 i 1 G11 ltac:(lia) ltac:(lia)) in Hc.
apply negb_true_iff, Z.eqb_neq in Hc.
paj_run_to_tok RUNTO HS HJL SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x3cc).
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen Ex _ _ _ _ _ _ _ _ _ 32%nat (body + i)) end;
[reflexivity | rewrite G32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
replace a with (body + (a - body)) by lia.
apply (Hawrb (ablocks B ly2 S2) ly2 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] (a - body) Hin2).
rewrite Hrq. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?MD) _ => set (mdw := MD) in * end.
lazymatch type of HF with frame_of _ _ ?mo ?mn =>
assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mo (Z_to_bv 64 a)) end.
{ intros a Ha Hn. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
rewrite G32, !unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of MK2 with forall a, _ -> _ -> ?mn _ = _ =>
assert (MKf : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a))
by (intros a Ha Hn; rewrite (MK2 a Ha Hn); exact (MK1 a Ha Hn));
assert (HRODn0 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mn))
by (eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJL | exact HRODE]);
assert (HRODn : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W2) mn))
by (rewrite HWRLO, HWRHI; exact HRODn0);
pose proof (TRANS W2 mem2 mn ly2 S2 md2 HJM MKf HRODn) as (HCMn & HSPn) end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (HAEx : env_agree 32 (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 (bv_unsigned plb)]) Ex)
by (env_agree_chain HAEL);
pose proof (regs_kept_of_st_ok_pi Ex _ _ regs2
[Z_to_bv 64 (body + i); Z_to_bv 64 (bv_unsigned plb)]
[2;3;4;7;8;9;12;18;19;20;21;22;23;24;25;26;27]%bv HS HAEx ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
prreg HS (11%bv : bv 5) N11. prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ =>
apply (IH (i + 1) ly2 S2 W2 R M MD) end.
** rewrite Nat2Z.inj_succ in Hk. lia.
** lia.
** split; [split; [exact HJL | split; [exact Hfrs2 | exact Hmle2]]|].
split; [exact Hab2 | split; [exact Hbb2 | split; [exact HCMn | exact HSPn]]].
** unfold s1_regs1, s1_regs0. repeat split.
all: lazymatch goal with
| |- spZ _ = _ => unfold spZ in Rsp2 |- *; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Rsp2
| |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto));
first [exact Rg3|exact Rg4|exact Rg8|exact Rg9|exact Rg18|exact Rg19|exact Rg20|exact Rg23|exact Rg24
|exact Rg25|exact Rg26|exact Rg27|exact R221|exact R222]
end.
** rewrite (HK 7%bv ltac:(cbv; tauto)). exact Rb7.
** rewrite (HK 12%bv ltac:(cbv; tauto)). exact Rb12.
** rewrite N11, F11, unsigned_lit_small by lia. reflexivity.
** rewrite N13. reflexivity.
** rewrite N14. reflexivity.
* (* the exit: i + 1 = n' *)
rewrite branch_ne_U, (U_atom _ 24 _ G24 ltac:(lia)),
(U_atom_off _ 11 i 1 G11 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJL SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x434).
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen Ex _ _ _ _ _ _ _ _ _ 32%nat (body + i)) end;
[reflexivity | rewrite G32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
replace a with (body + (a - body)) by lia.
apply (Hawrb (ablocks B ly2 S2) ly2 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] (a - body) Hin2).
rewrite Hrq. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?MD) _ => set (mdw := MD) in * end.
lazymatch type of HF with frame_of _ _ ?mo ?mn =>
assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mo (Z_to_bv 64 a)) end.
{ intros a Ha Hn. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
rewrite G32, !unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of MK2 with forall a, _ -> _ -> ?mn _ = _ =>
assert (MKf : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a))
by (intros a Ha Hn; rewrite (MK2 a Ha Hn); exact (MK1 a Ha Hn));
assert (HRODn0 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mn))
by (eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJL | exact HRODE]);
assert (HRODn : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W2) mn))
by (rewrite HWRLO, HWRHI; exact HRODn0);
pose proof (TRANS W2 mem2 mn ly2 S2 md2 HJM MKf HRODn) as (HCMn & HSPn) end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (HAEx : env_agree 32 (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 (bv_unsigned plb)]) Ex)
by (env_agree_chain HAEL);
pose proof (regs_kept_of_st_ok_pi Ex _ _ regs2
[Z_to_bv 64 (body + i); Z_to_bv 64 (bv_unsigned plb)]
[2;3;4;7;8;9;12;18;19;20;21;22;23;24;25;26;27]%bv HS HAEx ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ => apply (HNEXT ly2 S2 W2 R M MD) end.
split; [|split; [|split]].
** split; [split; [exact HJL | split; [exact Hfrs2 | exact Hmle2]]|].
split; [exact Hab2 | split; [exact Hbb2 | split; [exact HCMn | exact HSPn]]].
** unfold s1_regs1, s1_regs0. repeat split.
all: lazymatch goal with
| |- spZ _ = _ => unfold spZ in Rsp2 |- *; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Rsp2
| |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto));
first [exact Rg3|exact Rg4|exact Rg8|exact Rg9|exact Rg18|exact Rg19|exact Rg20|exact Rg23|exact Rg24
|exact Rg25|exact Rg26|exact Rg27|exact R221|exact R222]
end.
** rewrite (HK 7%bv ltac:(cbv; tauto)). exact Rb7.
** rewrite (HK 12%bv ltac:(cbv; tauto)). exact Rb12.
(* ---- 8904 <= i: the turn stores a zero byte, the placeholder is not read ---- *)
+ remember (Eimg (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 0])) as E eqn:HE.
assert (HEIL : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAEL : env_agree 32 (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 0]) E)
by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn Hr; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (F7 : ew E 7 = Z_to_bv 64 body) by (rewrite (EE 7%nat 7%bv ltac:(lia) eq_refl); exact Rb7).
assert (F11 : ew E 11 = Z_to_bv 64 i) by (rewrite (EE 11%nat 11%bv ltac:(lia) eq_refl); exact Rb11).
assert (F12 : ew E 12 = Z_to_bv 64 (2 ^ 64 - 1 - body))
by (rewrite (EE 12%nat 12%bv ltac:(lia) eq_refl); exact Rb12).
assert (F24 : ew E 24 = Z_to_bv 64 (sc_nprime scene_geom_asan_ubsan bs))
by (rewrite (EE 24%nat 24%bv ltac:(lia) eq_refl); exact Rg24).
assert (F26 : ew E 26 = Z_to_bv 64 SHADOW_OFF)
by (rewrite (EE 26%nat 26%bv ltac:(lia) eq_refl); exact Rg26).
assert (F32 : ew E 32 = Z_to_bv 64 (body + i))
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 0)
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (HBx : U E s1_Bx = SHADOW_OFF)
by (unfold s1_Bx; apply (U_atom E 26 SHADOW_OFF F26); unfold SHADOW_OFF; lia).
assert (U32 : U E (SOff 32 0) = body + i) by (apply (U_atom E 32 _ F32); lia).
assert (U11 : U E (SOff 11 0) = i) by (apply (U_atom E 11 _ F11); lia).
assert (HS : st_ok_pi SEGS VAL E
(mkSS (AF_LLVMFuzzerTestOneInput + 0x3cc)
(sr_set (sr_set sr_atoms 13%bv (SLit 134784)) 14%bv (SLit 1112))
[YP09.mkRegion (Some 32%nat) 0 1 0 1 []] None
(mkFacts [(11%nat, mkAF 8904 65534 0); (12%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 1) 0);
(24%nat, mkAF 1 65535 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
(32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 0 255 0)] []
[(SAlu ALU_ADD (SOff 7 0) (SOff 11 0), SOff 32 0)]))
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply (regs_ok_pin E _ regs2 14%bv (SLit 1112));
[apply (regs_ok_pin E _ regs2 13%bv (SLit 134784));
[rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact Rb13]
| intros X; discriminate X | cbn [sv_denot]; exact Rb14].
- vm_compute; reflexivity.
- constructor; [|constructor]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite F32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HBpres2 (body + i + o) ltac:(lia))).
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | split; [|exact I]]].
+ cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite F11, F12, F24, F26, F32, F33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
+ apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 7 body F7 ltac:(lia)), U11, U32.
rewrite zcanon_id by (unfold M64; lia). reflexivity. }
assert (SHOK : sh_ok SEGS s1_Bx [mkSHE 32 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W2) mem2 E s1_Bx 32 body (sc_nn scene_geom_asan_ubsan bs)
(body + i) 0 1 RAB HBx U32 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at.
change (w64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc)))
with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0x3cc))).
paj_run_to_tok RUNTO HS HJL SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x414).
{ eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32%nat (body + i));
[reflexivity | rewrite F32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
replace a with (body + (a - body)) by lia.
apply (Hawrb (ablocks B ly2 S2) ly2 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] (a - body) Hin2).
rewrite Hrq. lia. }
lazymatch type of HF with frame_of _ _ ?mo ?mn =>
assert (MK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mo (Z_to_bv 64 a)) end.
{ intros a Ha Hn. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
rewrite F32, !unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (G11 : ew Ex 11 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact F11);
assert (G24 : ew Ex 24 = Z_to_bv 64 (sc_nprime scene_geom_asan_ubsan bs))
by (cbn [ew ewset Nat.eqb]; exact F24);
assert (G32 : ew Ex 32 = Z_to_bv 64 (body + i)) by (cbn [ew ewset Nat.eqb]; exact F32)
end.
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
* (* the back edge: i + 1 < n' *)
rewrite branch_ne_U, (U_atom _ 24 _ G24 ltac:(lia)),
(U_atom_off _ 11 i 1 G11 ltac:(lia) ltac:(lia)) in Hc.
apply negb_true_iff, Z.eqb_neq in Hc.
paj_run_to_tok RUNTO HS HJL SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x3cc).
{ lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen Ex _ _ _ _ _ _ _ _ _ 32%nat (body + i)) end;
[reflexivity | rewrite G32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
replace a with (body + (a - body)) by lia.
apply (Hawrb (ablocks B ly2 S2) ly2 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] (a - body) Hin2).
rewrite Hrq. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?MD) _ => set (mdw := MD) in * end.
lazymatch type of HF with frame_of _ _ ?mo ?mn =>
assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mo (Z_to_bv 64 a)) end.
{ intros a Ha Hn. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
rewrite G32, !unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of MK2 with forall a, _ -> _ -> ?mn _ = _ =>
assert (MKf : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a))
by (intros a Ha Hn; rewrite (MK2 a Ha Hn); exact (MK1 a Ha Hn));
assert (HRODn0 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mn))
by (eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJL | exact HRODE]);
assert (HRODn : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W2) mn))
by (rewrite HWRLO, HWRHI; exact HRODn0);
pose proof (TRANS W2 mem2 mn ly2 S2 md2 HJM MKf HRODn) as (HCMn & HSPn) end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (HAEx : env_agree 32 (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 0]) Ex)
by (env_agree_chain HAEL);
pose proof (regs_kept_of_st_ok_pi Ex _ _ regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 0]
[2;3;4;7;8;9;12;18;19;20;21;22;23;24;25;26;27]%bv HS HAEx ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
prreg HS (11%bv : bv 5) N11. prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ =>
apply (IH (i + 1) ly2 S2 W2 R M MD) end.
** rewrite Nat2Z.inj_succ in Hk. lia.
** lia.
** split; [split; [exact HJL | split; [exact Hfrs2 | exact Hmle2]]|].
split; [exact Hab2 | split; [exact Hbb2 | split; [exact HCMn | exact HSPn]]].
** unfold s1_regs1, s1_regs0. repeat split.
all: lazymatch goal with
| |- spZ _ = _ => unfold spZ in Rsp2 |- *; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Rsp2
| |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto));
first [exact Rg3|exact Rg4|exact Rg8|exact Rg9|exact Rg18|exact Rg19|exact Rg20|exact Rg23|exact Rg24
|exact Rg25|exact Rg26|exact Rg27|exact R221|exact R222]
end.
** rewrite (HK 7%bv ltac:(cbv; tauto)). exact Rb7.
** rewrite (HK 12%bv ltac:(cbv; tauto)). exact Rb12.
** rewrite N11, F11, unsigned_lit_small by lia. reflexivity.
** rewrite N13. reflexivity.
** rewrite N14. reflexivity.
* (* the exit: i + 1 = n' *)
rewrite branch_ne_U, (U_atom _ 24 _ G24 ltac:(lia)),
(U_atom_off _ 11 i 1 G11 ltac:(lia) ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJL SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x434).
{ lazymatch goal with |- awr_ok ?Ex _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen Ex _ _ _ _ _ _ _ _ _ 32%nat (body + i)) end;
[reflexivity | rewrite G32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
replace a with (body + (a - body)) by lia.
apply (Hawrb (ablocks B ly2 S2) ly2 [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] (a - body) Hin2).
rewrite Hrq. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?MD) _ => set (mdw := MD) in * end.
lazymatch type of HF with frame_of _ _ ?mo ?mn =>
assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mo (Z_to_bv 64 a)) end.
{ intros a Ha Hn. apply HF. intros (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
rewrite G32, !unsigned_lit_small in Hr by lia. lia. }
clear HF HFr HG.
lazymatch type of MK2 with forall a, _ -> _ -> ?mn _ = _ =>
assert (MKf : forall a, 0 <= a < 2 ^ 64 -> ~ (body <= a < body + sc_nn scene_geom_asan_ubsan bs) ->
mn (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a))
by (intros a Ha Hn; rewrite (MK2 a Ha Hn); exact (MK1 a Ha Hn));
assert (HRODn0 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mn))
by (eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJL | exact HRODE]);
assert (HRODn : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W2) mn))
by (rewrite HWRLO, HWRHI; exact HRODn0);
pose proof (TRANS W2 mem2 mn ly2 S2 md2 HJM MKf HRODn) as (HCMn & HSPn) end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (HAEx : env_agree 32 (Ereg regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 0]) Ex)
by (env_agree_chain HAEL);
pose proof (regs_kept_of_st_ok_pi Ex _ _ regs2 [Z_to_bv 64 (body + i); Z_to_bv 64 0]
[2;3;4;7;8;9;12;18;19;20;21;22;23;24;25;26;27]%bv HS HAEx ltac:(vm_compute; reflexivity)) as HK end.
cbn [ms_regs restrict] in HK.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ => apply (HNEXT ly2 S2 W2 R M MD) end.
split; [|split; [|split]].
** split; [split; [exact HJL | split; [exact Hfrs2 | exact Hmle2]]|].
split; [exact Hab2 | split; [exact Hbb2 | split; [exact HCMn | exact HSPn]]].
** unfold s1_regs1, s1_regs0. repeat split.
all: lazymatch goal with
| |- spZ _ = _ => unfold spZ in Rsp2 |- *; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Rsp2
| |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto));
first [exact Rg3|exact Rg4|exact Rg8|exact Rg9|exact Rg18|exact Rg19|exact Rg20|exact Rg23|exact Rg24
|exact Rg25|exact Rg26|exact Rg27|exact R221|exact R222]
end.
** rewrite (HK 7%bv ltac:(cbv; tauto)). exact Rb7.
** rewrite (HK 12%bv ltac:(cbv; tauto)). exact Rb12. }
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
- (* n' = 0: the fill loop is skipped *)
rewrite branch_eq_U, U24, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x434).
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?MD) _ => set (mdv := MD) in * end.
pose proof (frame_of_read_only E0
[YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0x20e80))]] _ _
ltac:(vm_compute; reflexivity) HF) as MEQ.
rewrite MEQ0 in MEQ. rewrite MEQ in HJ.
pose proof (regs_kept_of_st_ok_pi E0 _ _ regs' [] [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv
HS HAE0 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (7%bv : bv 5) Rt2. prreg HS (12%bv : bv 5) Ra2.
pmkst HS. rewrite MEQ.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ => apply (HNEXT ly' S' W' R M MD) end.
split; [|split; [|split]].
+ split; [split; [exact HJ | split; [exact Hfrs1 | exact Hmle1]]|].
split; [exact Hab1 | split; [exact Hbb1 | split; [exact HCM1 | exact HSP1]]].
+ unfold s1_regs1, s1_regs0. repeat split.
all: lazymatch goal with
| |- spZ _ = _ => unfold spZ in Rsp |- *; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Rsp
| |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto));
first [exact R3|exact R4|exact R8|exact R9|exact R18|exact R19|exact R20|exact R23|exact R24|exact R25
|exact R26|exact R27|exact R21|exact R22]
end.
+ rewrite Rt2, E10. reflexivity.
+ rewrite Ra2. exact NOTB.
- (* n' <> 0: fall into the loop at 0x82c70 *)
rewrite branch_eq_U, U24, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
destruct Hnpc as [HZ | (Hnplo & Hnneq)]; [contradiction|].
paj_run_to_tok RUNTO HS HJ SHOK BAND_SPAN (AF_LLVMFuzzerTestOneInput + 0x3cc).
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?MD) _ => set (mdv := MD) in * end.
pose proof (frame_of_read_only E0
[YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0x20e80))]] _ _
ltac:(vm_compute; reflexivity) HF) as MEQ.
rewrite MEQ0 in MEQ. rewrite MEQ in HJ.
pose proof (regs_kept_of_st_ok_pi E0 _ _ regs' [] [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv
HS HAE0 ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prreg HS (7%bv : bv 5) Rt2. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (13%bv : bv 5) Ra3. prreg HS (14%bv : bv 5) Ra4.
pmkst HS. rewrite MEQ.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ =>
apply (LOOP (Z.to_nat (sc_nprime scene_geom_asan_ubsan bs)) 0 ly' S' W' R M MD) end.
+ rewrite Z2Nat.id by lia. lia.
+ lia.
+ split; [split; [exact HJ | split; [exact Hfrs1 | exact Hmle1]]|].
split; [exact Hab1 | split; [exact Hbb1 | split; [exact HCM1 | exact HSP1]]].
+ unfold s1_regs1, s1_regs0. repeat split.
all: lazymatch goal with
| |- spZ _ = _ => unfold spZ in Rsp |- *; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Rsp
| |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto));
first [exact R3|exact R4|exact R8|exact R9|exact R18|exact R19|exact R20|exact R23|exact R24|exact R25
|exact R26|exact R27|exact R21|exact R22]
end.
+ rewrite Rt2, E10. reflexivity.
+ rewrite Ra2. exact NOTB.
+ rewrite Ra1. reflexivity.
+ rewrite Ra3. reflexivity.
+ rewrite Ra4. reflexivity.
Qed.
Lemma s1_xor_block : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop) (bs : Z -> Z) (body : Z)
ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md',
sc_base SEGS B ameter_triv WK cx ->
s1_stateB cx bs body ly' S' W' regs' mem' md' -> s1_blk cx bs body ->
(forall ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
s1_stateC2 cx bs body ly2 S2 W2 regs2 mem2 md2 ->
SRr SEGS W2 (cfg_at SEGS (BASE + S1_pcC2) regs2 mem2 md2) POST) ->
SRr SEGS W' (cfg_at SEGS (BASE + S1_pcB) regs' mem' md') POST.
Proof.
intros cx POST bs body ly' S' W' regs' mem' md' Hbase HB Hblk HNEXT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct Hbase as (HB0 & Hsp1).
destruct HB0 as (HPRE & Hra & H10 & H11 & Hpn & Hfrs & Hnev & Hlive & Hrod & Hsink & Hfd & Hfs & Hmok).
pose proof HPRE as (HAR0 & Hra1 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & Hstk00 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HB as ((HSJ & Hab & Hbb & HCM & HSP) & HR1 & R7 & R12).
destruct HSJ as (HJ & Hfrs' & Hmole).
destruct HR1 as (HR0 & R21 & R22).
pose proof HR0 as (Rsp & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
destruct Hblk as (Hbok & Hnn & Hb16 & Hb4096 & Hbceil).
pose proof Hbok as (_ & (Hoffb & Hzb) & _ & _ & HAWR & _). unfold off_img in Hoffb.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hfsb : fs_frame_bytes 8 = 16384) by reflexivity.
assert (Hnp : 0 <= sc_nprime scene_geom_asan_ubsan bs <= 65535 /\
  sc_nprime scene_geom_asan_ubsan bs <= sc_nn scene_geom_asan_ubsan bs)
  by (unfold sc_nn in Hnn |- *; destruct (Z.eqb_spec (sc_nprime scene_geom_asan_ubsan bs) 0); lia).
assert (Hrq : req_size (sc_nn scene_geom_asan_ubsan bs) = sc_nn scene_geom_asan_ubsan bs)
  by (unfold req_size; destruct (Z.eqb_spec (sc_nn scene_geom_asan_ubsan bs) 0); lia).
assert (HFeq : frame_addr ly' 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx).
{ unfold sc_F, rt_F, frame_addr. cbn [sg_cid scene_geom_asan_ubsan].
  pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
pose proof HJ as (HAR' & _).
assert (Hin8 : In (8, c_fpos cx) (frames S')) by (rewrite Hfrs'; left; reflexivity).
assert (Hbody : In (body, sc_nn scene_geom_asan_ubsan bs) (ablocks B ly' S'))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly' S' W' mem' md' 8 (c_fpos cx) HAR' Hin8) as (HF4096 & HFceil & _).
pose proof (sep_block_frame SEGS B LAWS ly' S' W' mem' md' body _ 8 (c_fpos cx) HAR' Hbody Hin8) as HdisjF.
unfold zdisjoint in HdisjF. cbn [fst snd] in HdisjF.
rewrite HFeq, Hfsb in HdisjF, HFceil. rewrite HFeq in HF4096.
unfold cfg_at, w64 in HNEXT |- *.
unfold s1F in *.
set (F := sc_F SEGS scene_geom_asan_ubsan cx) in *.
set (rest := sc_rest SEGS cx) in *.
set (cur := sc_cur SEGS cx) in *.
set (np := sc_nprime scene_geom_asan_ubsan bs) in *.
set (nn := sc_nn scene_geom_asan_ubsan bs) in *.
set (sp0 := spZ (c_regs cx)) in *.
pose proof (Z_div_mod_eq_full (sp0 - 224) 32) as Hdm.
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as Hmb.
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8b.
assert (NBF : forall a, F <= a < F + 16384 -> 0 <= a < 2 ^ 64 /\ ~ (body <= a < body + req_size nn))
  by (intros a Ha; rewrite Hrq; lia).
assert (NBS : forall a, SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 2048 ->
  0 <= a < 2 ^ 64 /\ ~ (body <= a < body + req_size nn))
  by (intros a Ha; rewrite Hrq; unfold SHADOW_OFF in Ha; lia).
assert (NBK : forall a, c_sp1 cx <= a < sp0 -> 0 <= a < 2 ^ 64 /\ ~ (body <= a < body + req_size nn))
  by (intros a Ha; rewrite Hrq; lia).
assert (NBI : forall a, 0x10000 <= a < 0x5f9000 -> 0 <= a < 2 ^ 64 /\ ~ (body <= a < body + req_size nn))
  by (intros a Ha; rewrite Hrq; lia).
(* ---- every fact of the cut kept by a memory that differs from mem' only inside the fresh block ---- *)
assert (TRANS : forall mem2 : word -> option byte,
  (forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> mem2 x = mem' x) ->
  s1_cmem cx bs W' mem2 /\ s1_spills cx bs W' mem2).
{ intros mem2 KP.
  assert (AV : forall a, 0 <= a < 2 ^ 64 /\ ~ (body <= a < body + req_size nn) ->
    aview SEGS (w_H W') mem2 a = aview SEGS (w_H W') mem' a).
  { intros a [Ha Hn]. apply aview_eq_of. unfold mrestrict. rewrite KP; [reflexivity|].
    rewrite unsigned_lit_small by lia. exact Hn. }
  assert (AP : forall a, 0 <= a < 2 ^ 64 /\ ~ (body <= a < body + req_size nn) ->
    apresent (w_H W') mem' a -> apresent (w_H W') mem2 a).
  { intros a [Ha Hn] [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite KP; [exact Hb|].
    rewrite unsigned_lit_small by lia. exact Hn. }
  assert (RW : forall a, (forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ ~ (body <= a + k < body + req_size nn)) ->
    rdword (aview SEGS (w_H W') mem2) a = rdword (aview SEGS (w_H W') mem') a).
  { intros a Hk. apply rdword_ext. intros k Hk'. apply AV, Hk, Hk'. }
  assert (SHR : forall lo hi v, 0 <= lo -> hi <= 2048 ->
    sc_shr SEGS scene_geom_asan_ubsan cx W' mem' lo hi v -> sc_shr SEGS scene_geom_asan_ubsan cx W' mem2 lo hi v).
  { intros lo hi v Hlo Hhi H o Ho. rewrite AV; [exact (H o Ho)|]. apply NBS. fold F. unfold shadow_addr. lia. }
  destruct HCM as (CF & CS & CBG & CBI & CBK & COP & CMAC & CRO).
  destruct HSP as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  split.
  - split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + destruct CF as (CF1 & CF2 & CF3). unfold sc_frame. fold F in CF1, CF2, CF3 |- *.
      cbn [sg_cid scene_geom_asan_ubsan] in CF1, CF2, CF3 |- *. rewrite Hfsb in CF1, CF2, CF3 |- *.
      split; [|split].
      * rewrite RW; [exact CF1|]. intros k Hk. apply NBF. lia.
      * intros a Ha. apply AP; [apply NBF; lia | apply CF2; exact Ha].
      * intros a Ha. apply AP; [apply NBS; unfold shadow_addr in Ha; change (16384 / 8) with 2048 in Ha; lia
        | apply CF3; exact Ha].
    + intros j Hj. rewrite RW; [exact (CS j Hj)|]. intros k Hk. apply NBK. fold sp0. lia.
    + unfold sc_shbg in CBG |- *. cbn [sg_sh_bg scene_geom_asan_ubsan] in CBG |- *.
      apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) CBG t Ht) as Ht'.
      cbn [In] in Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Ht' |- *;
      (apply SHR; [lia | lia | exact Ht']).
    + cbn [sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan_ubsan] in CBI |- *. apply SHR; [lia | lia | exact CBI].
    + cbn [sg_sh_blk_lo sg_sh_blk_hi scene_geom_asan_ubsan] in CBK |- *. apply SHR; [lia | lia | exact CBK].
    + unfold sc_open, block_shadow in COP |- *. fold F in COP |- *.
      cbn [sg_off_mac sg_mac_n scene_geom_asan_ubsan] in COP |- *.
      destruct COP as (O1 & O2 & O3). split; [exact O1|]. split; [exact O2|].
      intros i Hi. rewrite AV; [exact (O3 i Hi)|]. apply NBS.
      replace ((6 + 7) / 8) with 1 in Hi by reflexivity.
      pose proof (Z.div_mod (F + 112) 8 ltac:(lia)) as HM. unfold shadow_of_addr. lia.
    + unfold garr8, s1F in CMAC |- *. fold F in CMAC |- *. cbn [sg_off_mac scene_geom_asan_ubsan] in CMAC |- *.
      intros j Hj. destruct (CMAC j Hj) as (V & Hv). split; [|exact Hv].
      apply (val_mem_kept SEGS (w_H W') (w_H W') mem' mem2); [|exact V].
      intros k Hk. apply AV. apply NBF. unfold sc_macb in Hj. cbn [length] in Hj. cbn in Hk. lia.
    + unfold arodata_okS in CRO |- *. intros a Ha Ho Herr. rewrite AV; [exact (CRO a Ha Ho Herr)|]. apply NBI.
      apply pa_img_range. destruct Ha as [(s & Hs & _ & Hlo) | Hr].
      * exists s. split; [exact Hs | exact Hlo].
      * apply pa_relro_img. rewrite <- HWRLO, <- HWRHI. exact Hr.
  - unfold s1_spills. fold F.
    split; [|split; [|split; [|split; [|split; [|split]]]]];
    (rewrite RW; [assumption|]); intros k Hk; apply NBK; lia. }
(* ---- the exit: s1_stateC2 at 0x82d94 for any memory that keeps the cut outside the fresh block ---- *)
assert (EXIT : forall (regs : bvmap 5 word) memc mdc,
  ajournal SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] ly' S' W' memc mdc 1 ->
  (forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> memc x = mem' x) ->
  s1_regs0 cx bs regs -> getr regs 7 = Z_to_bv 64 body ->
  SRr SEGS W' (mkCfg (mkst regs (Z_to_bv 64 (BASE + S1_pcC2)) memc (seg_rom SEGS)) mdc) POST).
{ intros regs memc mdc HJc KP HR G7.
  apply (HNEXT ly' S' W' regs memc mdc).
  destruct (TRANS memc KP) as (TC & TS).
  split; [|split; [exact HR | exact G7]].
  split; [split; [exact HJc | split; [exact Hfrs' | exact Hmole]]|].
  split; [exact Hab|]. split; [exact Hbb|]. split; [exact TC | exact TS]. }
assert (R0T : forall regsA regsB : bvmap 5 word,
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%bv -> getr regsB r = getr regsA r) ->
  s1_regs0 cx bs regsA -> s1_regs0 cx bs regsB).
{ intros regsA regsB HKx (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  unfold s1_regs0, spZ in *.
  rewrite !HKx by (cbv; tauto).
  repeat split; assumption. }
(* ---- the input-derived values of the setup block ---- *)
assert (Hn_rng : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (? & _)]; lia).
assert (Hrest : 0 <= rest < 2 ^ 26) by (subst rest; unfold sc_rest; lia).
assert (Hcu : exists cu, bv_unsigned (getr regs' 22) = cu /\ 0 <= cu /\ cu + rest < 2 ^ 64 /\ (rest = 0 \/ 4096 <= cu)).
{ destruct Hpn as [(Hn0 & _) | (Hn & Hin0)].
  - exists (bv_unsigned (getr regs' 22)). pose proof (bv_unsigned_in_range 64 (getr regs' 22)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr.
    assert (rest = 0) by (subst rest; unfold sc_rest; rewrite Hn0; reflexivity). lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrn].
    exists cur. rewrite R22. unfold w64. rewrite unsigned_lit_small by (subst cur; unfold sc_cur; lia).
    subst cur rest; unfold sc_cur, sc_rest; lia. }
destruct Hcu as (cu & U22' & Hcu0 & Hcu1 & Hcu2).
remember (Eimg (Ereg regs' [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs' []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U21 : bv_unsigned (ew E 21) = rest)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = cu) by (rewrite (EE 22%nat 22%bv eq_refl); exact U22').
assert (U24 : bv_unsigned (ew E 24) = np)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (KEEP : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> mem' x = mem' x)
  by (intros; reflexivity).
(* ---- the xor loop, by fuel induction from its head 0x82d10 ---- *)
assert (LOOP : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) ->
  forall (k : nat) (j : Z) (regs : bvmap 5 word) memc mdc,
  Z.of_nat k = Z.min rest np - j -> 0 <= j < Z.min rest np ->
  ajournal SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(sg_cid scene_geom_asan_ubsan, c_fpos cx)] ly' S' W' memc mdc 1 ->
  (forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> memc x = mem' x) ->
  s1_regs0 cx bs regs -> getr regs 7 = Z_to_bv 64 body -> getr regs 12 = Z_to_bv 64 (2 ^ 64 - 1 - body) ->
  getr regs 22 = Z_to_bv 64 cur -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 (cur + j) -> getr regs 15 = Z_to_bv 64 (cur + j) ->
  getr regs 11 = Z_to_bv 64 (body + j) -> getr regs 16 = Z_to_bv 64 (body + j) ->
  getr regs 14 = Z_to_bv 64 j -> getr regs 21 = Z_to_bv 64 (Z.min rest np - j) ->
  SRr SEGS W' (mkCfg (mkst regs (Z_to_bv 64 (BASE + 1132)) memc (seg_rom SEGS)) mdc) POST).
{ intros Hn0 Hinp k. induction k as [|k IH];
    intros j regs memc mdc Hk Hj HJc KP HRg G7 G12 G22 G13 G10 G15 G11 G16 G14 G21; [lia|].
  clear E HE HEI EE HAE U21 U22 U24 KEEP Hpn Hoffb Hzb HdisjF Hcu2 TRANS.
  pose proof HJc as (HARc & _).
  assert (Hinp' : In (c_p cx, c_n cx) (ablocks B ly' S'))
    by (rewrite Hab; apply in_or_app; left; exact Hinp).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hinp') as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hbody) as (_ & _ & _ & Hbapp & Hbpres & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrn].
  assert (Hcur : cur = c_p cx + Z.min (c_n cx) 11) by reflexivity.
  assert (Hrst : rest = c_n cx - Z.min (c_n cx) 11) by reflexivity.
  destruct (aview SEGS (w_H W') memc (cur + j)) as [vin|] eqn:Hvin;
    [| exfalso; exact (aview_some_of_apresent SEGS _ _ _ (proj1 (Hppres (cur + j) ltac:(lia))) Hvin)].
  destruct (aview SEGS (w_H W') memc (body + j)) as [vb|] eqn:Hvb;
    [| exfalso; exact (aview_some_of_apresent SEGS _ _ _ (proj1 (Hbpres (body + j) ltac:(lia))) Hvb)].
  pose proof (val_mem1_of_aview SEGS _ _ _ _ Hvin) as (VMin & Hvin8).
  pose proof (val_mem1_of_aview SEGS _ _ _ _ Hvb) as (VMb & Hvb8).
  remember (Eimg (Ereg regs [Z_to_bv 64 vin; Z_to_bv 64 vb])) as E1 eqn:HE1.
  assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
  assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
    by (intros n r Hn; subst E1; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 vin; Z_to_bv 64 vb]) E1)
    by (subst E1; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E1 32 = Z_to_bv 64 vin)
    by (subst E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E1 33 = Z_to_bv 64 vb)
    by (subst E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  pose proof HRg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G26 & _).
  assert (U10 : bv_unsigned (ew E1 10) = cur + j)
    by (rewrite (EE1 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
  assert (U15 : bv_unsigned (ew E1 15) = cur + j)
    by (rewrite (EE1 15%nat 15%bv eq_refl), G15; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew E1 11) = body + j)
    by (rewrite (EE1 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
  assert (U16 : bv_unsigned (ew E1 16) = body + j)
    by (rewrite (EE1 16%nat 16%bv eq_refl), G16; apply unsigned_lit_small; lia).
  assert (U14 : bv_unsigned (ew E1 14) = j)
    by (rewrite (EE1 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E1 21) = Z.min rest np - j)
    by (rewrite (EE1 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E1 22) = cur)
    by (rewrite (EE1 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; lia).
  assert (U13 : bv_unsigned (ew E1 13) = 1)
    by (rewrite (EE1 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E1 12) = 2 ^ 64 - 1 - body)
    by (rewrite (EE1 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E1 26) = SHADOW_OFF)
    by (rewrite (EE1 26%nat 26%bv eq_refl), G26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E1 32) = vin) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E1 33) = vb) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E1
    (mkSS 1132 sr_atoms
      [YP09.mkRegion (Some 16%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
       YP09.mkRegion (Some 15%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
      (mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 4096 0x7fffff800000 0);
                (11%nat, mkAF 4096 0x7fffff800000 0); (16%nat, mkAF 4096 0x7fffff800000 0);
                (22%nat, mkAF 4096 0x7fffff800000 0); (13%nat, mkAF 1 1 0);
                (12%nat, mkAF (2 ^ 64 - 1 - 0x7fffff800000) (2 ^ 64 - 1 - 4096) 0);
                (14%nat, mkAF 0 65535 0); (21%nat, mkAF 1 65535 0);
                (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)]
               [mkAC BC_GEU (SOff 10 0) (SOff 22 0); mkAC BC_NE (SAlu ALU_XOR (SOff 13 0) (SLit 0)) (SLit 0)] []))
    (restrict (w_H W') (mkst regs (Z_to_bv 64 (BASE + 1132)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E1; apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U16. split; [lia|]. split; [lia|]. split.
        * intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hbpres (body + j + o) ltac:(lia))).
        * constructor; [|constructor]. apply (chunk_ok_val SEGS E1 _ _ 0 1%N (SOff 33 0) vb).
          -- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
          -- cbn. lia.
          -- cbn. lia.
          -- rewrite Z.add_0_r. exact VMb.
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U15. split; [lia|]. split; [lia|]. split.
        * intros o Ho. lia.
        * constructor; [|constructor]. apply (chunk_ok_val SEGS E1 _ _ 0 1%N (SOff 32 0) vin).
          -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
          -- cbn. lia.
          -- cbn. lia.
          -- rewrite Z.add_0_r. exact VMin.
    - assert (Hdpb : c_p cx + req_size (c_n cx) <= body \/ body + req_size nn <= c_p cx).
      { destruct (al_sep _ _ LAWS _ _ _ _ _ HARc) as [Hsp _]. rewrite Hab in Hsp.
        destruct (in_split _ _ Hinp) as (l1 & l2 & El). rewrite El in Hsp.
        refine (pairwise_In2 zdisjoint _ (c_p cx, req_size (c_n cx)) (body, req_size nn)
          (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
          (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2)
          (map (fun f => (frame_addr ly' (fst f) (snd f), fs_frame_bytes (fst f))) (frames S')) Hsp _).
        rewrite !map_app. cbn [map app]. rewrite <- !app_assoc. reflexivity. }
      cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U15, U16. repeat split; lia.
    - split; [|split; [|exact I]].
      + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U26, U10, U11, U16, U22, U13, U12, U14, U21, U32, U33.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
        repeat split; lia.
      + split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b].
        * rewrite branch_geu_U, !U_SOff, U10, U22, !Z.add_0_r.
          rewrite !zcanon_id by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge. lia.
        * rewrite branch_ne_U, U_SAlu, U_SOff, U_SLit, U13. reflexivity. }
  assert (UBx : U E1 (SOff 26 0) = SHADOW_OFF)
    by (rewrite U_SOff, U26, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  assert (SHOK : sh_ok SEGS (SOff 26 0) [mkSHE 10 0 1; mkSHE 11 0 1; mkSHE 16 0 1] E1 (mrestrict (w_H W') memc)).
  { unfold sh_ok. constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (shent_ok_of_range SEGS (w_H W') memc E1 (SOff 26 0) 10 (c_p cx) (req_size (c_n cx)) (cur + j) 0 1
        (range_addressable_of_block SEGS B LAWS ly' S' W' memc mdc (c_p cx) (c_n cx) (c_p cx) (req_size (c_n cx))
          HARc Hinp' ltac:(lia) ltac:(lia)) UBx);
      [rewrite U_SOff, U10, Z.add_0_r; apply zcanon_id; unfold M64; lia | lia | lia |].
      intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. unfold SHADOW_OFF. lia.
    - apply (shent_ok_of_range SEGS (w_H W') memc E1 (SOff 26 0) 11 body (req_size nn) (body + j) 0 1
        (range_addressable_of_block SEGS B LAWS ly' S' W' memc mdc body nn body (req_size nn)
          HARc Hbody ltac:(lia) ltac:(lia)) UBx);
      [rewrite U_SOff, U11, Z.add_0_r; apply zcanon_id; unfold M64; lia | lia | lia |].
      intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF. lia.
    - apply (shent_ok_of_range SEGS (w_H W') memc E1 (SOff 26 0) 16 body (req_size nn) (body + j) 0 1
        (range_addressable_of_block SEGS B LAWS ly' S' W' memc mdc body nn body (req_size nn)
          HARc Hbody ltac:(lia) ltac:(lia)) UBx);
      [rewrite U_SOff, U16, Z.add_0_r; apply zcanon_id; unfold M64; lia | lia | lia |].
      intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF. lia. }
  clear HE1.
  paj_run_tok RUN HS HJc SHOK BAND_SPAN.
  { cbn [ss_mem].
    eapply (awr_ok_cons_gen E1 _ _ _ _ _ _ _ _ _ 16%nat (body + j));
      [reflexivity | exact U16 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (body + (a - body)) by lia.
    apply HAWR; [exact Hbody | lia]. }
  lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
    assert (KP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
      by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & Hw);
          cbn [ss_mem add_cond In] in Hr; destruct Hr as [<- | [<- | []]];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hw; rewrite ?U16, ?U15 in Hw; lia]);
    clear KPx; rename KP' into KP end.
  clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
  (* 0x82d70 bnez s5: the back edge *)
  psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
  - (* another turn: j + 1 < m *)
    rewrite branch_ne_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U21 in Hc.
    rewrite (zcanon_id (Z.min rest np - j + -1)) in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJc SHOK BAND_SPAN 1132.
    { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc lyx own) end.
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 16%nat (body + j));
        [reflexivity | cbn [ew ewset Nat.eqb]; exact U16 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
      intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (body + (a - body)) by lia.
      apply HAWR; [exact Hbody | lia]. }
    lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
      assert (KP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
        by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & Hw);
            cbn [ss_mem add_cond In] in Hr; destruct Hr as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hw; rewrite ?U16, ?U15 in Hw; lia]);
      clear KPx; rename KP' into KP end.
    clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 7; 8; 9; 12; 13; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv
      HS ltac:(env_agree_chain HAE1) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (10%bv : bv 5) N10. prreg HS (15%bv : bv 5) N15. prreg HS (11%bv : bv 5) N11.
    prreg HS (16%bv : bv 5) N16. prreg HS (14%bv : bv 5) N14. prreg HS (21%bv : bv 5) N21.
    pmkst HS.
    apply (IH (j + 1)); [lia | lia | exact HJc | exact KP | | | | | | | | | | | ].
    + apply (R0T regs); [intros r Hr; apply HK; cbv [In] in Hr |- *; tauto | exact HRg].
    + rewrite HK by (cbv; tauto). exact G7.
    + rewrite HK by (cbv; tauto). exact G12.
    + rewrite HK by (cbv; tauto). exact G22.
    + rewrite HK by (cbv; tauto). exact G13.
    + rewrite N10, U10; f_equal; lia.
    + rewrite N15, U15; f_equal; lia.
    + rewrite N11, U11; f_equal; lia.
    + rewrite N16, U16; f_equal; lia.
    + rewrite N14, U14; f_equal; lia.
    + rewrite N21, U21; f_equal; lia.
  - (* the exit: j + 1 = m *)
    rewrite branch_ne_U, U_SOff, U_SLit in Hc. cbn [ew ewset Nat.eqb] in Hc. rewrite U21 in Hc.
    rewrite (zcanon_id (Z.min rest np - j + -1)) in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJc SHOK BAND_SPAN 1264.
    { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc lyx own) end.
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 16%nat (body + j));
        [reflexivity | cbn [ew ewset Nat.eqb]; exact U16 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
      intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (body + (a - body)) by lia.
      apply HAWR; [exact Hbody | lia]. }
    lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
      assert (KP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
        by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & Hw);
            cbn [ss_mem add_cond In] in Hr; destruct Hr as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hw; rewrite ?U16, ?U15 in Hw; lia]);
      clear KPx; rename KP' into KP end.
    clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 7; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%bv
      HS ltac:(env_agree_chain HAE1) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pmkst HS.
    apply EXIT; [exact HJc | exact KP | | ].
    + apply (R0T regs); [intros r Hr; apply HK; cbv [In] in Hr |- *; tauto | exact HRg].
    + rewrite HK by (cbv; tauto). exact G7. }
(* ---- the setup block 0x82cd8 .. 0x82d0c ---- *)
assert (HS : st_ok_pi SEGS VAL E (mkSS S1_pcB sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 (BASE + S1_pcB)) mem' (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - repeat split. }
assert (HSH : sh_ok SEGS (SOff 26 0) [] E (mrestrict (w_H W') mem')) by apply Forall_nil.
paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
{ apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
  assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
    by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
  clear KPx; rename KEEP' into KEEP end.
clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
(* 0x82cdc bltu a0,s6: the UBSan overflow trap of cur + rest *)
psrr_branch_tok RUN BR HS HSH BAND_SPAN.
{ exfalso. rewrite branch_ltu_U, U_SAlu, !U_SOff, U21, U22 in Hc. cbn [zalu_raw] in Hc.
  rewrite !Z.add_0_r in Hc. rewrite (zcanon_id rest), (zcanon_id cu) in Hc by (unfold M64; lia).
  rewrite (zcanon_id (rest + cu)) in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
{ apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
  assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
    by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
  clear KPx; rename KEEP' into KEEP end.
clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
(* 0x82cec beqz a0: the UBSan null / one-past trap, a0 = snez cur ^ seqz (cur + rest) *)
psrr_branch_tok RUN BR HS HSH BAND_SPAN.
{ exfalso. rewrite branch_eq_U, !U_SAlu, !U_SLit, !U_SOff, U21, U22 in Hc. cbn [zalu_raw] in Hc.
  rewrite !Z.add_0_r in Hc. rewrite (zcanon_id rest), (zcanon_id cu) in Hc by (unfold M64; lia).
  rewrite (zcanon_id (rest + cu)) in Hc by (unfold M64; lia).
  change (zcanon 0) with 0 in Hc. change (zcanon 1) with 1 in Hc.
  revert Hc. destruct (Z.ltb_spec 0 cu); destruct (Z.ltb_spec (rest + cu) 1); intros Hc; try lia;
  vm_compute in Hc; discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
{ apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
  assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
    by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
  clear KPx; rename KEEP' into KEEP end.
clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
(* 0x82cf0 bltu s5,s8: s5 = min (rest, n') *)
psrr_branch_tok RUN BR HS HSH BAND_SPAN.
- (* rest < n': s5 stays rest *)
  rewrite branch_ltu_U, !U_SOff, U21, U24, !Z.add_0_r, (zcanon_id rest), (zcanon_id np) in Hc by (unfold M64; lia).
  apply Z.ltb_lt in Hc. assert (Hm : Z.min rest np = rest) by lia. clear Hc.
  paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
  { apply awr_ok_nil. }
  lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
    assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
      by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
    clear KPx; rename KEEP' into KEEP end.
  clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
  (* 0x82cf8 beqz s5 *)
  psrr_branch_tok RUN BR HS HSH BAND_SPAN.
  + (* m = 0: straight to C2 *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1264.
    { apply awr_ok_nil. }
    lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
      assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
        by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
      clear KPx; rename KEEP' into KEEP end.
    clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' _ [2; 3; 4; 7; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pmkst HS.
    apply EXIT; [exact HJ | exact KEEP | | ].
    * apply (R0T regs'); [intros r Hr; apply HK; cbv [In] in Hr |- *; tauto | exact HR0].
    * rewrite HK by (cbv; tauto). exact R7.
  + (* m = rest > 0: the loop from j = 0 *)
    rewrite branch_eq_U, U_SOff, U_SLit, U21, Z.add_0_r, (zcanon_id rest) in Hc by (unfold M64; lia).
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
    { apply awr_ok_nil. }
    lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
      assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
        by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
      clear KPx; rename KEEP' into KEEP end.
    clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
    destruct Hpn as [(Hn0 & _) | (Hn & Hinp)];
      [exfalso; assert (rest = 0) by (subst rest; unfold sc_rest; rewrite Hn0; reflexivity); lia |].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinp) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrn].
    assert (Hcc : cu = cur).
    { rewrite <- U22', R22. unfold w64. apply unsigned_lit_small. subst cur; unfold sc_cur; lia. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' _ [2; 3; 4; 7; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv
      HS HAE ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (10%bv : bv 5) N10. prreg HS (15%bv : bv 5) N15. prreg HS (11%bv : bv 5) N11.
    prreg HS (16%bv : bv 5) N16. prreg HS (14%bv : bv 5) N14. prreg HS (21%bv : bv 5) N21.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx (13%bv : bv 5) HS) as N13;
      let e := eval vm_compute in (sr_get (ss_regs ssx) (13%bv : bv 5)) in
      change (sr_get (ss_regs ssx) (13%bv : bv 5)) with e in N13; cbn [ms_regs restrict mkst] in N13 end.
    pmkst HS.
    apply (LOOP (proj1 Hn) Hinp (Z.to_nat (Z.min rest np)) 0); [lia | lia | exact HJ | exact KEEP | | | | | | | | | | | ].
    * apply (R0T regs'); [intros r Hr; apply HK; cbv [In] in Hr |- *; tauto | exact HR0].
    * rewrite HK by (cbv; tauto). exact R7.
    * rewrite HK by (cbv; tauto). exact R12.
    * rewrite HK by (cbv; tauto). exact R22.
    * rewrite N13, denot_lit_U, U_SAlu, U_SLit, U_SOff, U22, Z.add_0_r. cbn [zalu_raw].
      change (zcanon 0) with 0. rewrite (zcanon_id cu) by (unfold M64; lia).
      rewrite (proj2 (Z.ltb_lt 0 cu)) by lia. reflexivity.
    * rewrite N10, (EE 22%nat 22%bv eq_refl), R22, Z.add_0_r. reflexivity.
    * rewrite N15, (EE 22%nat 22%bv eq_refl), R22, Z.add_0_r. reflexivity.
    * rewrite N11, (EE 7%nat 7%bv eq_refl), R7, Z.add_0_r. reflexivity.
    * rewrite N16, (EE 7%nat 7%bv eq_refl), R7, Z.add_0_r. reflexivity.
    * rewrite N14. reflexivity.
    * rewrite N21, (EE 21%nat 21%bv eq_refl), R21. unfold w64. f_equal. lia.
- (* n' <= rest: s5 = n' *)
  rewrite branch_ltu_U, !U_SOff, U21, U24, !Z.add_0_r, (zcanon_id rest), (zcanon_id np) in Hc by (unfold M64; lia).
  apply Z.ltb_ge in Hc. assert (Hm : Z.min rest np = np) by lia. clear Hc.
  paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
  { apply awr_ok_nil. }
  lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
    assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
      by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
    clear KPx; rename KEEP' into KEEP end.
  clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
  (* 0x82cf8 beqz s5 *)
  psrr_branch_tok RUN BR HS HSH BAND_SPAN.
  + (* m = 0: straight to C2 *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1264.
    { apply awr_ok_nil. }
    lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
      assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
        by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
      clear KPx; rename KEEP' into KEEP end.
    clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' _ [2; 3; 4; 7; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pmkst HS.
    apply EXIT; [exact HJ | exact KEEP | | ].
    * apply (R0T regs'); [intros r Hr; apply HK; cbv [In] in Hr |- *; tauto | exact HR0].
    * rewrite HK by (cbv; tauto). exact R7.
  + (* m = n' > 0: the loop from j = 0 *)
    rewrite branch_eq_U, U_SOff, U_SLit, U24, Z.add_0_r, (zcanon_id np) in Hc by (unfold M64; lia).
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ HSH BAND_SPAN 1132.
    { apply awr_ok_nil. }
    lazymatch goal with HFx : frame_of _ _ ?m0 ?m1, KPx : forall x : word, _ -> ?m0 x = mem' x |- _ =>
      assert (KEEP' : forall x : word, ~ (body <= bv_unsigned x < body + req_size nn) -> m1 x = mem' x)
        by (intros x Hx; rewrite (HFx x); [exact (KPx x Hx) | intros (r & Hr & _); cbn [ss_mem add_cond In] in Hr; destruct Hr]);
      clear KPx; rename KEEP' into KEEP end.
    clear HF HFr HG. lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => let md := fresh "mdv" in set (md := mdx) in *; clearbody md end.
    destruct Hpn as [(Hn0 & _) | (Hn & Hinp)];
      [exfalso; assert (rest = 0) by (subst rest; unfold sc_rest; rewrite Hn0; reflexivity); lia |].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinp) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrn].
    assert (Hcc : cu = cur).
    { rewrite <- U22', R22. unfold w64. apply unsigned_lit_small. subst cur; unfold sc_cur; lia. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' _ [2; 3; 4; 7; 8; 9; 12; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv
      HS HAE ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (10%bv : bv 5) N10. prreg HS (15%bv : bv 5) N15. prreg HS (11%bv : bv 5) N11.
    prreg HS (16%bv : bv 5) N16. prreg HS (14%bv : bv 5) N14. prreg HS (21%bv : bv 5) N21.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_restrict_reg Hh Ex ssx msx (13%bv : bv 5) HS) as N13;
      let e := eval vm_compute in (sr_get (ss_regs ssx) (13%bv : bv 5)) in
      change (sr_get (ss_regs ssx) (13%bv : bv 5)) with e in N13; cbn [ms_regs restrict mkst] in N13 end.
    pmkst HS.
    apply (LOOP (proj1 Hn) Hinp (Z.to_nat (Z.min rest np)) 0); [lia | lia | exact HJ | exact KEEP | | | | | | | | | | | ].
    * apply (R0T regs'); [intros r Hr; apply HK; cbv [In] in Hr |- *; tauto | exact HR0].
    * rewrite HK by (cbv; tauto). exact R7.
    * rewrite HK by (cbv; tauto). exact R12.
    * rewrite HK by (cbv; tauto). exact R22.
    * rewrite N13, denot_lit_U, U_SAlu, U_SLit, U_SOff, U22, Z.add_0_r. cbn [zalu_raw].
      change (zcanon 0) with 0. rewrite (zcanon_id cu) by (unfold M64; lia).
      rewrite (proj2 (Z.ltb_lt 0 cu)) by lia. reflexivity.
    * rewrite N10, (EE 22%nat 22%bv eq_refl), R22, Z.add_0_r. reflexivity.
    * rewrite N15, (EE 22%nat 22%bv eq_refl), R22, Z.add_0_r. reflexivity.
    * rewrite N11, (EE 7%nat 7%bv eq_refl), R7, Z.add_0_r. reflexivity.
    * rewrite N16, (EE 7%nat 7%bv eq_refl), R7, Z.add_0_r. reflexivity.
    * rewrite N14. reflexivity.
    * rewrite N21, (EE 24%nat 24%bv eq_refl), R24. unfold w64. f_equal. lia.
Qed.

(* C2's body contents are existential: read them off a state where every byte of the block is present (the asan
   twin's s1_bytes / s1_garr8_present, at 7b2b57c5429 lib/A/...S1.v:273-305). *)
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

(* ---- the exit cut: s1_stateC2 at 0x82d94 is cut_C2, so the C2 hypothesis closes the walk.  sc_in (the input
   bytes of the ENTRY state, state-independent) is the one cut_C2 conjunct s1_stateC2 does not carry. ---- *)
Lemma s1_mkC2 : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop) (bs : Z -> Z) (body : Z)
ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md',
sc_base SEGS B ameter_triv WK cx ->
sc_from_C2 SEGS B ameter_triv WK scene_geom_asan_ubsan cx POST ->
sc_in SEGS cx bs ->
s1_stateC2 cx bs body ly' S' W' regs' mem' md' -> s1_blk cx bs body ->
SRr SEGS W' (cfg_at SEGS (BASE + S1_pcC2) regs' mem' md') POST.
Proof.
intros cx POST bs body ly' S' W' regs' mem' md' Hbase HC2 HIN HC Hblk.
destruct HC as ((HSJ & Hab' & Hbb' & HCM & HSP) & HR0 & R7).
pose proof HCM as (CFR & CSV & CBG & CSI & CSK & COP & CMC & CRO).
pose proof HSP as (P10 & P18 & P20 & P28 & P30 & P38 & P58).
pose proof HR0 as (Rsp & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
pose proof Hblk as (Hbok & Hnn & Hb16 & Hb4096 & Hbceil).
pose proof (proj1 (proj1 HSJ)) as HARm.
assert (Ereq : req_size (sc_nn scene_geom_asan_ubsan bs) = sc_nn scene_geom_asan_ubsan bs)
by (unfold req_size; destruct (Z.eqb_spec (sc_nn scene_geom_asan_ubsan bs) 0); lia).
assert (Hin : In (body, sc_nn scene_geom_asan_ubsan bs) (ablocks B ly' S'))
by (rewrite Hab'; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ body (sc_nn scene_geom_asan_ubsan bs) HARm Hin) as (_ & _ & _ & _ & Hpresm & _).
assert (Hnn0 : 0 <= sc_nn scene_geom_asan_ubsan bs) by (unfold s1_blk in Hblk; lia).
destruct (s1_garr8_present (mrestrict (w_H W') mem') body (sc_nn scene_geom_asan_ubsan bs) Hnn0) as (Hlen & Hga).
{ intros j Hj. pose proof (proj1 (Hpresm (body + j) ltac:(rewrite Ereq; lia))) as Hp.
pose proof (aview_some_of_apresent SEGS _ _ _ Hp) as Hv. unfold aview in Hv.
intros Hn. apply Hv. rewrite Hn. reflexivity. }
assert (Epc : BASE + S1_pcC2 = sg_pc_c2 scene_geom_asan_ubsan)
by (cbn [sg_pc_c2 scene_geom_asan_ubsan]; unfold S1_pcC2; lia).
rewrite Epc.
apply (HC2 ly' S' W' regs' mem' md' bs body (s1_bytes (mrestrict (w_H W') mem') body (sc_nn scene_geom_asan_ubsan bs))).
unfold cut_C2.
cbn [vat sg2_sp0 sg2_sp1 sg2_F sg2_Fsp sg2_shF sg2_shbase sg2_blki sg2_blk sg2_expect sg2_mac sg2_shexp sg2_body
sg2_nprime sg2_Fb sg2_nn sg2_flags sg2_step sg2_s7v scene_geom_asan_ubsan].
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s4, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11, RV_t2.
split; [exact HSJ|]. split; [exact Hab'|]. split; [exact Hbb'|]. split; [exact Hbok|].
split; [exact Hlen|]. split; [exact Hga|].
split; [exact CFR|]. split; [exact CSV|]. split; [exact CBG|]. split; [exact CSI|]. split; [exact CSK|].
split; [exact COP|].
split; [unfold sc_img; split; [exact Rsp | split; [exact R3 | split; [exact R4 | exact CRO]]]|].
split; [exact HIN|]. split; [exact Hnn|]. split; [exact CMC|].
split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact P28|]. split; [exact R19|].
split; [exact R26|]. split; [exact R25|]. split; [exact R27|]. split; [exact P30|]. split; [exact P38|].
split; [exact P10|]. split; [exact R7|]. split; [exact R24|]. split; [exact P18|]. split; [exact P20|].
split; [exact P58|]. split; [exact R23|]. exact R20.
Qed.

(* ---- the spine from the malloc return (stateA) to POST: fill, then xor, then the C2 cut ---- *)
Lemma s1_afterA : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop) (bs : Z -> Z) (body : Z)
ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md',
sc_base SEGS B ameter_triv WK cx ->
sc_from_C2 SEGS B ameter_triv WK scene_geom_asan_ubsan cx POST ->
sc_in SEGS cx bs ->
s1_stateA cx bs body ly' S' W' regs' mem' md' -> s1_blk cx bs body ->
SRr SEGS W' (cfg_at SEGS (BASE + S1_pcA) regs' mem' md') POST.
Proof.
intros cx POST bs body ly' S' W' regs' mem' md' Hbase HC2 HIN HA Hblk.
eapply (s1_fill_block cx POST bs body ly' S' W' regs' mem' md' Hbase HA Hblk).
intros ly2 S2 W2 regs2 mem2 md2 HB.
eapply (s1_xor_block cx POST bs body ly2 S2 W2 regs2 mem2 md2 Hbase HB Hblk).
intros ly3x S3x W3x regs3x mem3x md3x HCx.
eapply (s1_mkC2 cx POST bs body ly3x S3x W3x regs3x mem3x md3x Hbase HC2 HIN HCx Hblk).
Qed.

(* ================================================================================================================
   THE WALK, C1 (0x82c28) -> stateA (0x82c54), the shape of the asan twin's scene_seg_S1 (at
   7b2b57c5429 lib/A/P_LLVMFuzzerTestOneInput_S1.v:1032): the entry block and its flag branch (`paj_run_sh` /
   `psrr_branch_pi`), each arm run to the call 0x82c4c and handed to MAIN with a0 = n'' and s8 = n'; MAIN seats a
   fresh state at the call, applies aj_malloc_at04, refutes the NULL abort 0x82c50 from the post's 4096 <= res, and
   hands s1_stateA at 0x82c54 to s1_afterA.  The helpers below are the asan twin's (same names, AU offsets).
   ================================================================================================================ *)
(* `seqz a0,s8 / add a0,s8,a0` (0x82c40-0x82c44): a0 = n' + (n' =? 0) = n''. *)
Lemma s1_nn_val : forall (Ez : env) (v : Z), 0 <= v < 2 ^ 64 -> ew Ez 24 = w64 v ->
sv_denot Ez (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1))) = w64 (if v =? 0 then 1 else v).
Proof.
intros Ez v Hv H24. cbn [sv_denot]. rewrite H24. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. rewrite !zalu64_sound.
unfold zalu64. rewrite !Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id v) by (unfold M64; lia). change (zcanon 1) with 1.
destruct (Z.ltb_spec v 1) as [Hlt | Hge].
- assert (Hv0 : v = 0) by lia. rewrite Hv0. vm_compute. reflexivity.
- destruct (Z.eqb_spec v 0) as [-> | Hne]; [lia|].
change (zcanon (zcanon 0)) with 0. rewrite Z.add_0_r. reflexivity.
Qed.
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
(* `beqz r` on a register atom, as an integer test. *)
Lemma s1_beq0 : forall (Ez : env) (i : nat) (x : Z), ew Ez i = w64 x -> 0 <= x < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot Ez (SOff i 0)) (sv_denot Ez (SLit 0)) = (x =? 0).
Proof.
intros Ez i x H Hx. cbn [branch_taken sv_denot]. rewrite H. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
destruct (Z.eqb_spec x 0) as [-> | Hne]; [apply bv_eqb_eq; reflexivity |].
apply Bool.not_true_is_false. intros Hc. apply bv_eqb_eq in Hc.
apply (f_equal bv_unsigned) in Hc. rewrite !unsigned_lit_small in Hc by lia. lia.
Qed.
(* A run whose state has no region writes nothing. *)
Lemma s1_norun_keep : forall (Ez : env) (W : world SEGS) (m m' : word -> option byte),
frame_of Ez [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros Ez W m m' HFr a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin. cbn in Hin. destruct Hin.
Qed.
(* The three windows of the entry block are exactly the bytes it may write. *)
Lemma s1_win : forall (Ez : env) (c1 c2 c3 : list YP09.chunk) (sp1v : Z),
bv_unsigned (ew Ez 9) = sp1v ->
forall b wlo whi a,
In (b, wlo, whi) (windows [YP09.mkRegion (Some 9%nat) 24 32 24 32 c1;
YP09.mkRegion (Some 9%nat) 32 40 32 40 c2; YP09.mkRegion (Some 9%nat) 88 96 88 96 c3]) ->
base_val Ez b + wlo <= a < base_val Ez b + whi -> s1_prot sp1v a.
Proof.
intros Ez c1 c2 c3 sp1v U9 b wlo whi a Hin Hr.
cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [E1 | [E1 | [E1 | []]]]; injection E1 as <- <- <-;
cbn [base_val] in Hr; rewrite U9 in Hr; unfold s1_prot; lia.
Qed.
(* the register row s1_regs1 survives any step that keeps its fifteen registers, in particular a call *)
Lemma s1_regs1_kept : forall cx bs (regs regs' : bvmap 5 word),
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
s1_regs1 cx bs regs -> s1_regs1 cx bs regs'.
Proof.
intros cx bs regs regs' HK ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27) & R21 & R22).
unfold s1_regs1, s1_regs0. unfold spZ in R2 |- *.
repeat split; rewrite HK by (cbn; tauto); assumption.
Qed.
Lemma s1_regs1_pres : forall cx bs (regs regs' : bvmap 5 word),
aregs_preserved regs regs' -> s1_regs1 cx bs regs -> s1_regs1 cx bs regs'.
Proof.
intros cx bs regs regs' HP. apply s1_regs1_kept.
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- getr _ ?rr = _ => let z := eval vm_compute in (bv_unsigned rr) in
exact (HP z ltac:(unfold acallee_saved; lia)) end |]).
destruct Hr.
Qed.
(* the restricted `frame_of` of the run that produced the goal's machine state, renamed *)
Ltac s1_lastfr K :=
lazymatch goal with |- SRr _ ?W (mkCfg ?m _) _ =>
lazymatch goal with H : frame_of _ _ _ (mrestrict (w_H W) (ms_mem m)) |- _ => rename H into K end end.

Theorem llvmf_S1 : @seg_S1_stmt fx rc SK SEGS B ameter_triv WK scene_geom_asan_ubsan.
Proof.
unfold seg_S1_stmt. intros cx POST Hbase HC2.
unfold sc_from_C1. intros ly3 S3 W3 regs3 mem3 md3 bs HC1.
pose proof (s1_entry cx ly3 S3 W3 regs3 mem3 md3 bs Hbase HC1) as (HS & _ & HAWR).
pose proof Hbase as (HB0 & Hsp1).
pose proof HB0 as (HPRE & Hra & H10 & H11 & Hpn & Hfrs & Hnev & Hlive & Hrod & Hsink & Hfd & Hfs & Hmok).
pose proof HC1 as (HJ0 & Hab & Hbb & HFR & HSV & HSBG & HSHi & HSHk & HOPEN & HIMG & HIN & HMAC &
V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_shb & V_blki & V_blk & V_exp & V_mac & V_shexp & V_flags & V_u16 &
V_rest & V_cur & V_step & V_s7v).
destruct HJ0 as (HJ & Hfrs3 & HMLE).
destruct HIMG as (Hsp & Hgp & Htp & Hrod3).
cbn [vat sg1_sp0 sg1_sp1 sg1_F sg1_Fsp sg1_shF sg1_shbase sg1_blki sg1_blk sg1_expect sg1_mac sg1_shexp
sg1_flags sg1_u16 sg1_rest sg1_cur sg1_step sg1_s7v sg_cid sg_off_blki sg_off_blk sg_off_expect sg_off_mac
scene_geom_asan_ubsan] in V_sp0, V_sp1, V_F, V_Fsp, V_shF, V_shb, V_blki, V_blk, V_exp, V_mac, V_shexp, V_flags,
V_u16, V_rest, V_cur, V_step, V_s7v.
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s4, RV_s5, RV_s6, RV_s7, RV_s8, RV_s9, RV_s10, RV_s11, RV_a6 in
V_sp0, V_sp1, V_F, V_shF, V_shb, V_blki, V_blk, V_flags, V_u16, V_rest, V_cur, V_step, V_s7v.
(* ---- the facts of the entry state the whole walk uses ---- *)
pose proof HPRE as (HAR0 & Hra1 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & Hstk00 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (Has : ASTACK = 16384) by reflexivity.
cbn [sg_cid scene_geom_asan_ubsan] in Hfrs3.
pose proof HJ as (HARc & HlyJ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop : ly_top ly3 = ly_top (c_ly cx))
by (pose proof HlyJ as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT).
assert (Hfin3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HlyJ) as (_ & EFA & _).
assert (EFA3 : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx) by (rewrite EFA; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HARc Hfin3) as (HF4096 & HFceil & HFapp).
rewrite EFA3 in HF4096, HFceil, HFapp.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp.
assert (Hsp1rng : spZ (c_regs cx) - 256 < c_sp1 cx <= spZ (c_regs cx) - 224).
{ rewrite Hsp1. pose proof (Z.div_mod (spZ (c_regs cx) - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 224) 32 ltac:(lia)). lia. }
assert (Hsp1al16 : c_sp1 cx mod 16 = 0).
{ rewrite Hsp1. replace (32 * ((spZ (c_regs cx) - 224) / 32)) with (((spZ (c_regs cx) - 224) / 32 * 2) * 16) by lia.
apply Z_mod_mult. }
assert (Hom : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity).
assert (Hoff : -240 <= c_sp1 cx - spZ (c_regs cx) <= -224)
by (destruct (proj1 (Z.mod_divide (c_sp1 cx - spZ (c_regs cx)) 16 ltac:(lia)) Hom) as [q Hq]; lia).
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs3 [])) 9) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat regs3 [] 9%nat 9%bv eq_refl), V_sp1. apply unsigned_lit_small. lia. }
assert (E16 : ew (Eimg (Ereg regs3 [])) 16 = w64 (sc_flags bs))
by (rewrite (ew_Eimg_Ereg_nat regs3 [] 16%nat 16%bv eq_refl); exact V_flags).
assert (Hb0 : 0 <= bs 0 < 256) by (destruct (HIN 0 ltac:(lia)) as ((Hf1 & Hf2) & _); lia).
assert (Hfl256 : 0 <= sc_flags bs < 256) by (unfold sc_flags; lia).
assert (Hu16 : 0 <= sc_u16 bs <= 65535).
{ unfold sc_u16. destruct (HIN 1 ltac:(lia)) as ((Ha1 & Ha2) & _).
destruct (HIN 2 ltac:(lia)) as ((Hb1 & Hb2) & _). lia. }
assert (Hnpb : 0 <= sc_nprime scene_geom_asan_ubsan bs <= 65535).
{ unfold sc_nprime. cbn [sg_scene_n scene_geom_asan_ubsan]. destruct (Z.land (bs 0) 1 =? 0); lia. }
assert (Hnnb : 1 <= sc_nn scene_geom_asan_ubsan bs <= 65535).
{ unfold sc_nn. destruct (Z.eqb_spec (sc_nprime scene_geom_asan_ubsan bs) 0); lia. }
assert (HAG : env_agree 32 (Ereg regs3 []) (Eimg (Ereg regs3 [])))
by (split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* ---- the rest of the segment, from the call of __wrap_malloc at 0x82c4c ---- *)
assert (MAIN : forall (regsA : bvmap 5 word) (memA : word -> option byte) (mdA : Model),
s1_regs1 cx bs regsA ->
getr regsA 10 = w64 (sc_nn scene_geom_asan_ubsan bs) ->
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly3 S3 W3 memA mdA 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ s1_prot (c_sp1 cx) a ->
aview SEGS (w_H W3) memA a = aview SEGS (w_H W3) mem3 a) ->
rdword (aview SEGS (w_H W3) memA) (c_sp1 cx + 24) = Some (sc_F SEGS scene_geom_asan_ubsan cx) ->
rdword (aview SEGS (w_H W3) memA) (c_sp1 cx + 32) = Some (sc_nn scene_geom_asan_ubsan bs) ->
rdword (aview SEGS (w_H W3) memA) (c_sp1 cx + 88) = Some (sc_flags bs) ->
SRr SEGS W3 (mkCfg (mkst regsA (Z_to_bv 64 (BASE + 0x3a8)) memA (seg_rom SEGS)) mdA) POST).
{ intros regsA memA mdA RK Ra0A HJA KA WF Wnn Wfl.
pose proof RK as ((RA2 & RA3 & RA4 & RA8 & RA9 & RA18 & RA19 & RA20 & RA23 & RA24 & RA25 & RA26 & RA27) & RA21 & RA22).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
assert (HAF : AF_LLVMFuzzerTestOneInput = 0) by reflexivity.
remember (Eimg (Ereg regsA [])) as EA eqn:HEA.
assert (HEIA : img_env VAL A_LIM EA) by (subst EA; apply Eimg_env).
assert (HAGA : env_agree 32 (Ereg regsA []) EA)
by (subst EA; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HSA : st_ok_pi SEGS VAL EA (mkSS 936 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regsA (Z_to_bv 64 (BASE + 936)) memA (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. tauto.
- unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HSA HJA.
{ apply awr_ok_nil. }
pose proof (regs_kept_of_st_ok SEGS EA _ (restrict (w_H W3) ms) regsA []
[2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HSA HAGA eq_refl) as RKA.
cbn [ms_regs restrict] in RKA.
prreg HSA (1%bv : bv 5) Rra.
(* the call run writes nothing *)
assert (KAm : forall a, 0 <= a < 2 ^ 64 -> ~ s1_prot (c_sp1 cx) a ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hna. rewrite <- (KA a Ha Hna).
apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin. cbn in Hin. destruct Hin. }
assert (KAA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) memA a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
intros b wlo whi x Hin. cbn in Hin. destruct Hin. }
assert (Rsp' : spZ (ms_regs ms) = c_sp1 cx).
{ unfold spZ at 1. rewrite (RKA 2%bv ltac:(cbn; tauto)). exact RA2. }
assert (Rs0' : s0Z (ms_regs ms) = spZ (c_regs cx)).
{ unfold s0Z. rewrite (RKA 8%bv ltac:(cbn; tauto)), RA8. unfold w64. apply unsigned_lit_small. lia. }
assert (Rra' : raZ (ms_regs ms) = BASE + 940).
{ unfold raZ. rewrite Rra. apply unsigned_lit_small. lia. }
assert (Hach : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (spZ (c_regs cx)) (rt_ch cx)).
{ apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
apply (s1_chain cx W3 (ms_mem ms) (c_sp1 cx) HPRE); [ | | lia | lia].
+ intros a Ha. rewrite (KAm a ltac:(lia) ltac:(unfold s1_prot; lia)).
apply (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ intros j Hj. rewrite <- (HSV j Hj). apply rdword_ext. intros k Hk.
apply KAm; [lia | unfold s1_prot; lia]. }
pmkst HSA.
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ eapply (aj_malloc_at04 SEGS B LAWS pa_segs_low (pal_env B TL) ML AMALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (sc_nn scene_geom_asan_ubsan bs) (c_sp1 cx - spZ (c_regs cx)) _ (rt_ch cx) HJA).
  - rewrite (RKA 10%bv ltac:(cbn; tauto)). exact Ra0A.
  - unfold MALLOC_MAX. lia.
  - lia.
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
  - apply (HTRACE (pc_malloc_ra0 (as_code B)) (BASE + 940) (ms_regs ms) cx); [exact Hra | exact Rra' |].
    left. split; [reflexivity|]. left. unfold AF_LLVMFuzzerTestOneInput. lia. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres & Eab4 & HK4).
(* ---- what the call leaves: the new block (res, n''), the frame, the stack above sp1 ---- *)
change (0 + 1) with 1 in HJ4.
pose proof HJ4 as (HAR4 & Hly4 & _).
pose proof HK4 as (HK4up & HK4blk & HK4img & HK4frm & HK4pres & HK4win).
cbv beta in HK4blk, HK4frm.
assert (Ereq : req_size (sc_nn scene_geom_asan_ubsan bs) = sc_nn scene_geom_asan_ubsan bs)
by (unfold req_size; destruct (Z.eqb_spec (sc_nn scene_geom_asan_ubsan bs) 0); lia).
rewrite Ereq in HK4blk, HK4frm.
assert (Hin4 : In (res, sc_nn scene_geom_asan_ubsan bs) (ablocks B ly4 S4))
by (rewrite Eab4; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (sc_nn scene_geom_asan_ubsan bs) HAR4 Hin4)
as (Hres16 & Hres4096' & Hresceil & Hresapp & Hrespres & _).
assert (HresA : res + sc_nn scene_geom_asan_ubsan bs <= 2147446784 \/ 17594333495296 <= res).
{ pose proof Hresapp as HA'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HA'. rewrite Ereq in HA'. lia. }
assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 Hly4) as (_ & EFA4 & _).
assert (EFA4' : frame_addr ly4 8 (c_fpos cx) = sc_F SEGS scene_geom_asan_ubsan cx) by (rewrite EFA4; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 res _ 8 (c_fpos cx) HAR4 Hin4 Hfin4) as HsepBF.
unfold zdisjoint in HsepBF. cbn [fst snd] in HsepBF. rewrite EFA4', Ereq in HsepBF.
change (fs_frame_bytes 8) with 16384 in HsepBF.
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HARc Hfin3) as (HF32 & _ & _ & _).
rewrite EFA3 in HF32.
(* lia does not expand `/ 8` here (zify's euclidean-division flag is off), so bound F / 8 once *)
assert (HF8lo : 512 <= sc_F SEGS scene_geom_asan_ubsan cx / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : sc_F SEGS scene_geom_asan_ubsan cx / 8 + 2048 <= 17592184995840).
{ assert (HFc2 : sc_F SEGS scene_geom_asan_ubsan cx + 2048 * 8 <= 0x7fffff800000) by lia.
assert (Hd := Z.div_le_mono (sc_F SEGS scene_geom_asan_ubsan cx + 2048 * 8) 0x7fffff800000 8 ltac:(lia) HFc2).
rewrite Z.div_add in Hd by lia. change (0x7fffff800000 / 8) with 17592184995840 in Hd. lia. }
assert (HF8 : forall k, 0 <= k -> (sc_F SEGS scene_geom_asan_ubsan cx + 8 * k) / 8 = sc_F SEGS scene_geom_asan_ubsan cx / 8 + k).
{ intros k Hk. destruct (proj1 (Z.mod_divide (sc_F SEGS scene_geom_asan_ubsan cx) 32 ltac:(lia)) HF32) as [q Hq].
rewrite Hq. replace (q * 32 + 8 * k) with ((4 * q + k) * 8) by lia. replace (q * 32) with ((4 * q) * 8) by lia.
rewrite !Z.div_mul by lia. reflexivity. }
assert (KST4 : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) memA a).
{ intros a Ha. rewrite <- (KAA a ltac:(lia)). apply HK4up; lia. }
assert (KFR4 : forall a, (sc_F SEGS scene_geom_asan_ubsan cx <= a < sc_F SEGS scene_geom_asan_ubsan cx + 16384 \/
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) <= a < shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048) ->
~ (res <= a < res + sc_nn scene_geom_asan_ubsan bs) ->
aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hna. rewrite (HK4frm 8 (c_fpos cx) a Hfin3).
- apply KAm; unfold shadow_addr, SHADOW_OFF in Ha; [lia | unfold s1_prot; lia].
- unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes 8) with 16384.
change (16384 / 8) with 2048. exact Ha.
- exact Hna. }
assert (Hftok : aftok [] (ablocks B (c_ly cx) (c_S cx)) (res, sc_nn scene_geom_asan_ubsan bs))
by (eapply (aftok_new_block SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia]).
assert (Hfresh : ~ In (res, sc_nn scene_geom_asan_ubsan bs) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. destruct (Hftok Hc 0 ltac:(cbn [snd]; rewrite Ereq; lia)) as (r & [] & _). }
assert (RK4 : s1_regs1 cx bs regs4).
{ apply (s1_regs1_pres cx bs (ms_regs ms) regs4 HP4).
apply (s1_regs1_kept cx bs regsA (ms_regs ms)); [intros r Hr; apply RKA; cbn in Hr |- *; tauto | exact RK]. }
(* ---- s1_stateA at any state of W4 that keeps mem4's view and regs4's registers ---- *)
assert (STA : forall (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly4 S4 W4 mem md 1 ->
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem a = aview SEGS (w_H W4) mem4 a) ->
(forall r, In r [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs r = getr regs4 r) ->
s1_stateA cx bs res ly4 S4 W4 regs mem md).
{ intros regs mem md HJm KM HKr.
pose proof (proj1 HJm) as HARm.
assert (STK : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) memA a).
{ intros a Ha. rewrite (KM a ltac:(lia)). apply KST4. lia. }
assert (STK3 : forall a, c_sp1 cx <= a < 2 ^ 64 -> ~ s1_prot (c_sp1 cx) a ->
aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hp. rewrite (STK a Ha). exact (KA a ltac:(lia) Hp). }
assert (FRM : forall a, (sc_F SEGS scene_geom_asan_ubsan cx <= a < sc_F SEGS scene_geom_asan_ubsan cx + 16384 \/
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) <= a < shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + 2048) ->
aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. assert (Hna : ~ (res <= a < res + sc_nn scene_geom_asan_ubsan bs))
by (unfold shadow_addr, SHADOW_OFF in Ha; lia).
rewrite (KM a ltac:(unfold shadow_addr, SHADOW_OFF in Ha; lia)). exact (KFR4 a Ha Hna). }
destruct (al_frames _ _ LAWS ly4 S4 W4 mem md 8 (c_fpos cx) HARm Hfin4) as (_ & _ & HFpm & HFSpm).
rewrite EFA4' in HFpm, HFSpm. change (fs_frame_bytes 8) with 16384 in HFpm, HFSpm.
unfold s1_stateA, s1_jmem, s1_cmem, s1_spills, s1F.
cbn [sg_cid sg_off_blki sg_off_blk sg_off_expect sg_off_mac sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi
sg_mac_n scene_geom_asan_ubsan].
split; [split; [|split; [|split; [|split]]] | split].
- split; [exact HJm | split; [rewrite Hfrs4, Hfrs3; reflexivity | exact I]].
- rewrite Eab4, Hab. reflexivity.
- rewrite (blocks_bytes_bsum B ly4 S4), Eab4, bsum_app, <- (blocks_bytes_bsum B ly3 S3), Hbb.
change (bsum [(res, sc_nn scene_geom_asan_ubsan bs)]) with (sc_nn scene_geom_asan_ubsan bs + 0). rewrite Ereq. lia.
- split.
{ unfold sc_frame. cbn [sg_cid scene_geom_asan_ubsan]. change (fs_frame_bytes 8) with 16384.
destruct HFR as (HFLAG & _ & _). cbn [sg_cid scene_geom_asan_ubsan] in HFLAG. change (fs_frame_bytes 8) with 16384 in HFLAG.
split; [rewrite <- HFLAG; apply rdword_ext; intros k Hk; apply FRM; left; lia|].
split; [intros a Ha; exact (proj1 (HFpm a Ha))|].
change (16384 / 8) with 2048. intros a Ha.
replace a with (shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + (a - shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx))) by lia.
assert (Ha' : 0 <= a - shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) < 16384 / 8) by (change (16384 / 8) with 2048; lia).
exact (proj1 (HFSpm _ Ha')). }
split.
{ intros j Hj. rewrite <- (HSV j Hj). apply rdword_ext. intros k Hk. apply STK3; [lia | unfold s1_prot; lia]. }
split.
{ unfold sc_shbg in HSBG |- *. cbn [sg_sh_bg scene_geom_asan_ubsan] in HSBG |- *.
rewrite Forall_forall in HSBG |- *. intros t Ht. specialize (HSBG t Ht). cbn [In] in Ht.
destruct Ht as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in HSBG |- *;
unfold sc_shr in HSBG |- *; intros o Ho; rewrite FRM by (right; lia); apply HSBG; exact Ho. }
split.
{ unfold sc_shr in HSHi |- *. intros o Ho. rewrite FRM by (right; lia). apply HSHi. exact Ho. }
split.
{ unfold sc_shr in HSHk |- *. intros o Ho. rewrite FRM by (right; lia). apply HSHk. exact Ho. }
split.
{ unfold sc_open in HOPEN |- *. cbn [sg_mac_n sg_off_mac scene_geom_asan_ubsan] in HOPEN.
destruct HOPEN as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
intros i Hi. rewrite <- (Hc i Hi). change ((6 + 7) / 8) with 1 in Hi.
assert (Ea : shadow_of_addr SHADOW_OFF (sc_F SEGS scene_geom_asan_ubsan cx + 112) + i =
shadow_addr (sc_F SEGS scene_geom_asan_ubsan cx) + (14 + i)).
{ unfold shadow_of_addr, shadow_addr.
replace (sc_F SEGS scene_geom_asan_ubsan cx + 112) with (sc_F SEGS scene_geom_asan_ubsan cx + 8 * 14) by lia.
rewrite HF8 by lia. lia. }
rewrite Ea. apply FRM. right. lia. }
split.
{ intros j Hj. destruct (HMAC j Hj) as (Hv & Hr). split; [|exact Hr].
apply (val_mem_kept SEGS (w_H W3) (w_H W4) mem3 mem); [| exact Hv].
unfold sc_macb in Hj. cbn [length] in Hj. intros k Hk. apply FRM. left. lia. }
{ assert (HRODP : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
by (rewrite <- HWRLO, <- HWRHI; unfold arodata_okP, in_roP; exact Hrod).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm HRODP) as HRODm.
rewrite HWRLO, HWRHI. unfold arodata_okP, in_roP in HRODm. exact HRODm. }
- split; [etransitivity; [| exact V_shexp]; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [etransitivity; [| exact WF]; apply rdword_ext; intros k Hk; apply STK; lia |].
split; [etransitivity; [| exact Wnn]; apply rdword_ext; intros k Hk; apply STK; lia |].
split; [etransitivity; [| exact V_Fsp]; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [etransitivity; [| exact V_exp]; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
split; [etransitivity; [| exact V_mac]; apply rdword_ext; intros k Hk; apply STK3; [lia | unfold s1_prot; lia] |].
etransitivity; [| exact Wfl]; apply rdword_ext; intros k Hk; apply STK; lia.
- apply (s1_regs1_kept cx bs regs4 regs); [intros r Hr; apply HKr; cbn in Hr |- *; tauto | exact RK4].
- rewrite (HKr 10%bv ltac:(cbn; tauto)). exact Ha04. }
(* ---- 0x82c50 `beqz a0`, to the abort block: refuted, the wrapper returned a block at 4096 or above ---- *)
remember (Eimg (Ereg regs4 [])) as E4 eqn:HE4.
assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
assert (HAG4 : env_agree 32 (Ereg regs4 []) E4)
by (subst E4; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs4 r)
by (intros n r Hn; subst E4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS4 : st_ok_pi SEGS VAL E4 (mkSS 940 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 940)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
[subst E4; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | unfold facts_ok; cbn; tauto]. }
paj_run_sh RUNP HS4 HJ4.
{ apply awr_ok_nil. }
s1_lastfr KP1.
assert (E10 : ew E4 10 = w64 res) by (rewrite (EE4 10%nat 10%bv eq_refl); exact Ha04).
assert (Hresb : 0 <= res < 2 ^ 64) by lia.
psrr_branch_pi RUNP BR HS4.
{ exfalso. rewrite (s1_beq0 E4 10 res E10 Hresb) in Hc. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* the not-taken arm sits at the branch with its condition recorded; run it to 0x82c54 (writes nothing) *)
paj_run_to_sh RUNTOP HS4 HJ4 944.
{ apply awr_ok_nil. }
s1_lastfr KP2.
pmkst HS4.
pose proof (regs_kept_of_st_ok SEGS E4 _ _ regs4 [] [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
HS4 HAG4 eq_refl) as HK5.
cbn [ms_regs restrict] in HK5.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) m a = aview SEGS (w_H W4) mem4 a)
by (intros a Ha; rewrite (s1_norun_keep _ _ _ _ KP2 a Ha); exact (s1_norun_keep _ _ _ _ KP1 a Ha));
change (SRr SEGS W4 (cfg_at SEGS (BASE + S1_pcA) r m d) POST) end.
apply (s1_afterA cx POST bs res ly4 S4 W4 _ _ _ Hbase HC2 HIN).
- apply STA; [exact HJ4 | exact KM | exact HK5].
- unfold s1_blk. split.
{ unfold sc_blk_ok. split; [lia|]. split.
{ apply zone2_of_app; [exact Hresapp | exact (blk_off_imgP B ly4 S4 W4 mem4 md4 res _ HAR4 Hin4)]. }
split; [exact Hresceil|]. split; [exact Hres16|]. split; [|exact Hftok].
intros blc lyq ownq i Hb Hi. right; right; left. exists res, (sc_nn scene_geom_asan_ubsan bs).
split; [exact Hb|]. split; [exact Hfresh | lia]. }
split; [exact Hnnb|]. split; [exact Hres16|]. split; [lia | exact Hresceil]. }
(* ---- the entry block 0x82c28-0x82c34 ---- *)
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 []))) by apply Eimg_env.
unfold cfg_at, YG0d.w64. cbn [sg_pc_c1 scene_geom_asan_ubsan].
rewrite <- (Z.add_assoc BASE AF_LLVMFuzzerTestOneInput SEG_C1_off).
change (AF_LLVMFuzzerTestOneInput + SEG_C1_off) with S1_pc1.
paj_run_sh RUNP HS HJ.
{ exact HAWR. }
rename HFr into HFr1. clear HF HG.
psrr_branch_pi RUNP BR HS.
- (* the flag's low bit is 0: n' is the input's u16 (s8 is unchanged) *)
rewrite (s1_cond_and1 _ (sc_flags bs) E16 Hfl256) in Hc. apply Z.eqb_eq in Hc.
assert (Hnp : sc_nprime scene_geom_asan_ubsan bs = sc_u16 bs).
{ unfold sc_nprime. cbn [sg_scene_n scene_geom_asan_ubsan].
rewrite s1_land1 by lia. unfold sc_flags in Hc. rewrite Hc. reflexivity. }
paj_run_to_sh RUNTOP HS HJ 0x3a8.
{ apply (s1_awr _ _ _ _ (spZ (c_regs cx)) (c_sp1 cx)); [exact U9 | lia | lia]. }
assert (E24 : ew (Eimg (Ereg regs3 [])) 24 = w64 (sc_u16 bs))
by (rewrite (ew_Eimg_Ereg_nat regs3 [] 24%nat 24%bv eq_refl); exact V_u16).
pose proof (regs_kept_of_st_ok SEGS (Eimg (Ereg regs3 [])) _ (restrict (w_H W3) ms0) regs3 []
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl) as HK.
cbn [ms_regs restrict] in HK.
pose proof (st_ok_pi_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 9%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 18 0))]) HS eq_refl) as HR0.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 9%nat) 32 40 32 40 [YP09.mkChunk 32 (CVal 8
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1))))]) HS eq_refl) as HR1.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
(YP09.mkRegion (Some 9%nat) 88 96 88 96 [YP09.mkChunk 88 (CVal 8 (SOff 16 0))]) HS eq_refl) as HR2.
destruct HR0 as (_ & _ & _ & HK0). destruct HR1 as (_ & _ & _ & HK1). destruct HR2 as (_ & _ & _ & HK2).
cbn [ms_mem restrict YP09.r_chunks YP09.r_base base_val] in HK0, HK1, HK2.
rewrite U9 in HK0, HK1, HK2.
rewrite Forall_forall in HK0, HK1, HK2.
specialize (HK0 _ (or_introl eq_refl)). specialize (HK1 _ (or_introl eq_refl)).
specialize (HK2 _ (or_introl eq_refl)).
assert (Ra0 : getr (ms_regs ms0) 10%bv = w64 (sc_nn scene_geom_asan_ubsan bs)).
{ refine (eq_trans (st_ok_pi_restrict_reg (w_H W3) (Eimg (Ereg regs3 [])) _ ms0 (10%bv) HS) _).
change (sv_denot (Eimg (Ereg regs3 []))
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1))) = w64 (sc_nn scene_geom_asan_ubsan bs)).
rewrite (s1_nn_val _ (sc_u16 bs) ltac:(lia) E24). unfold sc_nn. rewrite Hnp. reflexivity. }
pmkst HS.
apply (MAIN (ms_regs ms0) (ms_mem ms0)).
+ unfold s1_regs1, s1_regs0, s1F. repeat split.
  * unfold spZ. rewrite (HK 2%bv ltac:(cbn; tauto)). exact Hsp.
  * rewrite (HK 3%bv ltac:(cbn; tauto)). exact Hgp.
  * rewrite (HK 4%bv ltac:(cbn; tauto)). exact Htp.
  * rewrite (HK 8%bv ltac:(cbn; tauto)). exact V_sp0.
  * rewrite (HK 9%bv ltac:(cbn; tauto)). exact V_sp1.
  * rewrite (HK 18%bv ltac:(cbn; tauto)). exact V_F.
  * rewrite (HK 19%bv ltac:(cbn; tauto)). exact V_shF.
  * rewrite (HK 20%bv ltac:(cbn; tauto)). exact V_s7v.
  * rewrite (HK 23%bv ltac:(cbn; tauto)). exact V_step.
  * rewrite (HK 24%bv ltac:(cbn; tauto)), Hnp. exact V_u16.
  * rewrite (HK 25%bv ltac:(cbn; tauto)). exact V_blki.
  * rewrite (HK 26%bv ltac:(cbn; tauto)). exact V_shb.
  * rewrite (HK 27%bv ltac:(cbn; tauto)). exact V_blk.
  * rewrite (HK 21%bv ltac:(cbn; tauto)). exact V_rest.
  * rewrite (HK 22%bv ltac:(cbn; tauto)). exact V_cur.
+ exact Ra0.
+ exact HJ.
+ intros a Ha Hna.
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr1
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 24 (SOff 18 0)); [exact HK0 | | lia].
cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regs3 [] 18%nat 18%bv eq_refl), V_F.
unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 32
(SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLTU (SOff 24 0) (SLit 1)))); [exact HK1 | | lia].
rewrite (s1_nn_val _ (sc_u16 bs) ltac:(lia) E24). unfold sc_nn. rewrite Hnp. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 88 (SOff 16 0)); [exact HK2 | | lia].
cbn [sv_denot]. rewrite E16. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
- (* the flag's low bit is 1: n' is 8904 *)
rewrite (s1_cond_and1 _ (sc_flags bs) E16 Hfl256) in Hc.
assert (Hnp : sc_nprime scene_geom_asan_ubsan bs = 8904).
{ unfold sc_nprime. cbn [sg_scene_n scene_geom_asan_ubsan]. rewrite s1_land1 by lia.
unfold sc_flags in Hc. rewrite Hc. reflexivity. }
assert (Hnn : sc_nn scene_geom_asan_ubsan bs = 8904) by (unfold sc_nn; rewrite Hnp; reflexivity).
paj_run_to_sh RUNTOP HS HJ 0x3a8.
{ apply (s1_awr _ _ _ _ (spZ (c_regs cx)) (c_sp1 cx)); [exact U9 | lia | lia]. }
pose proof (regs_kept_of_st_ok SEGS (Eimg (Ereg regs3 [])) _ (restrict (w_H W3) ms0) regs3 []
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv HS HAG eq_refl) as HK.
cbn [ms_regs restrict] in HK.
pose proof (st_ok_pi_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 9%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 18 0))]) HS eq_refl) as HR0.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 9%nat) 32 40 32 40 [YP09.mkChunk 32 (CVal 8 (SLit 8904))]) HS eq_refl) as HR1.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat
(YP09.mkRegion (Some 9%nat) 88 96 88 96 [YP09.mkChunk 88 (CVal 8 (SOff 16 0))]) HS eq_refl) as HR2.
destruct HR0 as (_ & _ & _ & HK0). destruct HR1 as (_ & _ & _ & HK1). destruct HR2 as (_ & _ & _ & HK2).
cbn [ms_mem restrict YP09.r_chunks YP09.r_base base_val] in HK0, HK1, HK2.
rewrite U9 in HK0, HK1, HK2.
rewrite Forall_forall in HK0, HK1, HK2.
specialize (HK0 _ (or_introl eq_refl)). specialize (HK1 _ (or_introl eq_refl)).
specialize (HK2 _ (or_introl eq_refl)).
assert (Ra0 : getr (ms_regs ms0) 10%bv = w64 (sc_nn scene_geom_asan_ubsan bs)).
{ refine (eq_trans (st_ok_pi_restrict_reg (w_H W3) (Eimg (Ereg regs3 [])) _ ms0 (10%bv) HS) _).
change (sv_denot (Eimg (Ereg regs3 [])) (SLit 8904) = w64 (sc_nn scene_geom_asan_ubsan bs)).
rewrite Hnn. reflexivity. }
assert (R24 : getr (ms_regs ms0) 24%bv = w64 (sc_nprime scene_geom_asan_ubsan bs)).
{ refine (eq_trans (st_ok_pi_restrict_reg (w_H W3) (Eimg (Ereg regs3 [])) _ ms0 (24%bv) HS) _).
change (sv_denot (Eimg (Ereg regs3 [])) (SLit 8904) = w64 (sc_nprime scene_geom_asan_ubsan bs)).
rewrite Hnp. reflexivity. }
pmkst HS.
apply (MAIN (ms_regs ms0) (ms_mem ms0)).
+ unfold s1_regs1, s1_regs0, s1F. repeat split.
  * unfold spZ. rewrite (HK 2%bv ltac:(cbn; tauto)). exact Hsp.
  * rewrite (HK 3%bv ltac:(cbn; tauto)). exact Hgp.
  * rewrite (HK 4%bv ltac:(cbn; tauto)). exact Htp.
  * rewrite (HK 8%bv ltac:(cbn; tauto)). exact V_sp0.
  * rewrite (HK 9%bv ltac:(cbn; tauto)). exact V_sp1.
  * rewrite (HK 18%bv ltac:(cbn; tauto)). exact V_F.
  * rewrite (HK 19%bv ltac:(cbn; tauto)). exact V_shF.
  * rewrite (HK 20%bv ltac:(cbn; tauto)). exact V_s7v.
  * rewrite (HK 23%bv ltac:(cbn; tauto)). exact V_step.
  * exact R24.
  * rewrite (HK 25%bv ltac:(cbn; tauto)). exact V_blki.
  * rewrite (HK 26%bv ltac:(cbn; tauto)). exact V_shb.
  * rewrite (HK 27%bv ltac:(cbn; tauto)). exact V_blk.
  * rewrite (HK 21%bv ltac:(cbn; tauto)). exact V_rest.
  * rewrite (HK 22%bv ltac:(cbn; tauto)). exact V_cur.
+ exact Ra0.
+ exact HJ.
+ intros a Ha Hna.
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
rewrite (kept_of_frame (segs := SEGS) _ _ _ _ _ (s1_prot (c_sp1 cx)) HFr1
(s1_win (Eimg (Ereg regs3 [])) _ _ _ (c_sp1 cx) U9) a Ha Hna).
reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 24 (SOff 18 0)); [exact HK0 | | lia].
cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regs3 [] 18%nat 18%bv eq_refl), V_F.
unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 32 (SLit 8904)); [exact HK1 | | lia].
rewrite Hnn. reflexivity.
+ apply rdword_of_val_mem; [|lia].
apply (s1_chunk_word (Eimg (Ereg regs3 [])) _ (c_sp1 cx) 88 (SOff 16 0)); [exact HK2 | | lia].
cbn [sv_denot]. rewrite E16. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r. reflexivity.
Qed.
End s1.
