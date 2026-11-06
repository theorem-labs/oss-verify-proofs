(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: SEGMENT S5 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput
   (fuzz_scene.asan, sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026).  `scene_seg_S5` proves
   `seg_S5_stmt` of lib/A/P_LLVMFuzzerTestOneInput_seg.v: the cut C5 (0x82eb0) to the cut C6 (0x83020).  (rule 24: no
   function is proved here; the callees are the Section hypotheses below.) *)

(*   THE WALK (the listing dis-LLVMF.asan.txt; pc offsets are from BASE = 0x82878).  After every call the lane kit
   (P_LLVMFuzzerTestOneInput_S5_kit.v, `s5_entry`) rebuilds the symbolic state over the s1-based spill region,
   `paj_run_shc` (A/Prog/YC45.v) runs the block, and each call site goes through its journal rule:
     0x82eb4 malloc                        amalloc04_rule_triv (Reusable/YCbp.v) over AMALLOC
     0x82ee0 __asan_memcpy(before, body, n')   aj_intrin_at OCpy (Reusable/YCbq.v)
     0x82ef4 reac_ctrl_scene_set_mac        cl_callS (A/Prog/YC85.v) over SSM
     r <> 0 arm (n' <> 8904): bcmp 0x82f18, reac_ctrl_scene_build 0x82f2c (returns -1), bcmp 0x82f40, j -> C6
     r =  0 arm (n' =  8904): bcmp 0x82f5c (body + 832 vs mac, 6), 0x82f70 (body vs before, 832),
       0x82f84 (body + 838 vs before + 838, 8066), reac_ctrl_scene_build 0x82f98 (returns 0, body = scene_tag
       with mac at 832), __asan_set_shadow_00 0x82fac (aj_set_shadow_at, lib/A/J_StackSzPf.v), __asan_memset
       0x82fc4 (aj_intrin_at OSet), the three unchecked `sw` 0x82fd4 / 0x82fe4 / 0x82fe8 through a region on
       s6 = expect that is zero from offset 4 (read back with a Theorem Labs lane's scene_chk, P_reac_ctrl_scene_build.v),
       __asan_memcpy 0x82ff8, bcmp(body, expect, 8904) 0x8300c, __asan_set_shadow_f8 0x8301c -> C6.
   Every bcmp goes through the local step BCMP (aj_bcmp_at, YCbq.v); both arms end in the one assertion EXIT, which
   rebuilds cut_C6 from the journal, the bytes S5 keeps (s5_prot, s5_row) and the registers.

   THE ABORT EDGES.  MEASURED: [0x82eb0, 0x83020) holds ten branches to 0x83144 (__asan_handle_no_return; abort at
   0x83148), and no branch to an __asan_report_* stub.  Each is refuted from a callee post, none is elided:
     0x82eb8 beqz a0     malloc's post gives 4096 <= res
     0x82efc bne a0,s2   set_mac's a0 is (if n' = 8904 then 0 else -1) and s2 - 1 is the same (s5_seqz_xor)
     0x82f30, 0x82f9c    bne a0,s6: scene_build's a0 (-1 / 0) equals set_mac's r, which s6 holds
     0x82f1c, 0x82f44, 0x82f60, 0x82f74, 0x82f88, 0x83010   bnez a0: the bcmp returned 0, because its two
                         operands are equal byte for byte (the memcpy copy; set_mac wrote only body + [832, 838)
                         and its stack; scene_build's two posts; `expect` built to scene_tag with mac at 832)

   SECTION HYPOTHESES and their owners.  RO, ML, TL: the glue (a Theorem Labs lane).  AMALLOC: a Theorem Labs lane (AM_*.v).
   AMEMSET, AMEMCPY, ABCMP: a Theorem Labs lane.  ASH00, ASHF8: SetShadowDef, from two Theorem Labs lanes.  SSB, SSM: a Theorem Labs lane
   (P_reac_ctrl_scene_build.v, P_reac_ctrl_scene_set_mac.v).  HEV, HLIVE, HSTK: the entry's budgets (HAND1-PLAN.md
   section 2.4); every callee window of S5 (2 * ESTACK, 32 + ESTACK, 16 + ESTACK) is below ASTACK, so HSTK covers
   them.  HTRACE: a Theorem Labs lane (P_LLVMFuzzerTestOneInput_trace.v).  HWRLO, HWRHI: LANE-LOCAL, in a Theorem Labs lane's verbatim
   text; the 04:04Z ruling made them segment-Section bindings (S3.v:198-199, S4.v:477-480), which the composition discharges by eq_refl.  The sink head SK is a Section variable passed by name to every
   rule that takes one (gate 6h). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YO0c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC4b YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz J_StackSzPf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_seg P_check_step_frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_S5_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The bytes no write of S5 touches, by offset from sp1 / F / shF: everything at or above sp1 (the spills, the 13
   saved words and the callers' frames), the frame outside `expect` ([F, F+224) holds `mac` and the blk objects,
   [F+9128, F+16384) the flag word), and the frame shadow outside the `expect` row. *)
Definition s5_u (sp1 F sF a : Z) : Prop :=
sp1 <= a < 2 ^ 64 \/ F <= a < F + 224 \/ F + 9128 <= a < F + 16384 \/ sF <= a < sF + 28 \/ sF + 1141 <= a < sF + 2048.

Lemma s5_u_out : forall sp1 F sF a lo hi, s5_u sp1 F sF a \/ s5_row sF a -> hi <= sp1 ->
(hi <= F \/ F + 16384 <= lo) -> (hi <= sF \/ sF + 2048 <= lo) -> ~ (lo <= a < hi).
Proof. intros sp1 F sF a lo hi Ha H1 H2 H3. unfold s5_u, s5_row in Ha. lia. Qed.
Lemma s5_u_rng : forall sp1 F sF a, s5_u sp1 F sF a \/ s5_row sF a -> 0 <= sp1 -> 0 <= F -> 0 <= sF -> F + 16384 <= 2 ^ 64 ->
sF + 2048 <= 2 ^ 64 -> 0 <= a < 2 ^ 64.
Proof.
intros sp1 F sF a Ha H0 H1 H2 H3 H4. unfold s5_u, s5_row in Ha.
destruct Ha as [[H|[H|[H|[H|H]]]]|H]; split; lia.
Qed.
Lemma s5_prot_u : forall sp0 sp1 F sF a, sp1 + 224 <= sp0 -> sp0 <= 2 ^ 64 -> s5_prot sp0 sp1 F sF a -> s5_u sp1 F sF a.
Proof. intros sp0 sp1 F sF a H1 H2 Ha. unfold s5_prot in Ha. unfold s5_u. lia. Qed.
Lemma s5_kept_run {rc : YM05.RunCeil} : forall segs E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview segs H mB a = aview segs H mA a.
Proof. intros segs E rs H mA mB a HF Ha Hn. apply (aview_eq_of segs). apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
(* lia without the disjunctive hypotheses of the walk's context: each of them doubles lia's case split. *)
Local Ltac zl := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
Section f.
#[local] Notation PI := PI_scene.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Section h.
Variable B : asyms.
Context {RO : ro_below_ofl (SK := SK) SEGS pa_relro_lo pa_relro_hi}.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib (L := scene_listing) (PI := PI) B.
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Hypothesis ASH00 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
Hypothesis SSB : treac_ctrl_scene_build_spec (SK := SK) (PI := PI) B.
Hypothesis SSM : treac_ctrl_scene_set_mac_spec (SK := SK) (PI := PI) B.
Let errno_low : api_env SEGS B := pal_env B TL.
Variable WK : swalk.
Hypothesis HEV : 6 <= sw_ev WK.
Hypothesis HLIVE : 2 * 65535 <= sw_live WK.
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
Hypothesis HTRACE : rt_trace_in_stmt SEGS (sw_ra WK) (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
(BASE + AF_LLVMFuzzerTestOneInput + 0x328) (BASE + AF_LLVMFuzzerTestOneInput + 0x51c)
(BASE + AF_LLVMFuzzerTestOneInput + 0x640) (BASE + AF_LLVMFuzzerTestOneInput + 0x634)
(BASE + AF_LLVMFuzzerTestOneInput + 0x7b0) (BASE + AF_LLVMFuzzerTestOneInput + 0x7b8) (as_universe B).

#[local] Notation IM := scene_geom_asan.
Let RUNP := SRr_run_pi_AJ (SK := SK) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (SK := SK) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).

Theorem scene_seg_S5 : seg_S5_stmt (SK := SK) SEGS B ameter_triv WK IM.
Proof.
unfold seg_S5_stmt. intros cx POST HBASE HC6.
assert (HSTKC : 240 + REAC_CTRL_SCENE_BUILD_STK <= sw_stk WK).
{ pose proof HSTK as X. unfold REAC_CTRL_SCENE_BUILD_STK. change ESTACK with 4096. change ASTACK with 16384 in X. lia. }
assert (HSTKM : 240 + SET_MAC_STK <= sw_stk WK).
{ pose proof HSTK as X. unfold SET_MAC_STK, SET_MAC_FRAME. change ESTACK with 4096. change ASTACK with 16384 in X. lia. }
unfold sc_from_C5. intros ly3 S3 W3 regs3 mem3 md3 bs body bb ev HCUT.
destruct HBASE as (HB0 & Hsp1eq).
destruct HB0 as (HAFN & Hra0 & Hp0 & Hn0 & Hpn & Hfrs0 & Hev0 & Hlive0 & HROD0 & HSNK0 & HFD0 & HSORT0 & HMOK0).
destruct HCUT as (Hevr & HJ0 & HPerm & HBB & HBLK & Hlenbb & Hbody8 & HFRM & HSAV & HSHBG & HSHBI & HOPBLK & HOPMAC & HIMG & HIN & Hnn1 & HMACB
& V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_expect & V_mac & V_shexp & V_body & V_nn & V_nprime).
destruct HJ0 as (HJ & Hfrs3 & HMLE).
cbn [sg_cid scene_geom_asan] in HJ, Hfrs3.
destruct HIMG as (Hsp3 & Hgp3 & Htp3 & HROD3).
cbn [vat sg5_sp0 sg5_sp1 sg5_F sg5_Fsp sg5_shF sg5_expect sg5_mac sg5_shexp sg5_body sg5_nn sg5_nprime
sg_off_expect sg_off_mac sg_off_blk sg_off_blki sg_cid sg_scene_n sg_blk_n sg_mac_n
RV_s0 RV_s1 RV_s3 RV_s7 RV_s8 scene_geom_asan] in
V_sp0, V_sp1, V_F, V_Fsp, V_shF, V_expect, V_mac, V_shexp, V_body, V_nn, V_nprime.
unfold RV_s0, RV_s1, RV_s3, RV_s7, RV_s8 in
V_sp0, V_sp1, V_F, V_Fsp, V_shF, V_expect, V_mac, V_shexp, V_body, V_nn, V_nprime.
(* ---- the frame, the stack and the two layouts ---- *)
pose proof HAFN as (HAR0 & Hra4' & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & _ & Hnev3 & Hk3 & _).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (sp0 := spZ (c_regs cx)) in *.
set (F := sc_F SEGS IM cx) in *.
assert (Hfin3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; cbn [sg_cid scene_geom_asan]; left; reflexivity).
assert (HcidF : F = frame_addr (c_ly cx) 8 (c_fpos cx)) by reflexivity.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & EFA & EFL).
assert (EFA3 : frame_addr ly3 8 (c_fpos cx) = F) by (rewrite EFA; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hfin3) as (HF32 & HFin_app & HFpres & HFSpres).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hfin3) as HFimg.
rewrite EFA3 in HF4096, HFceil, HFapp, HF32, HFin_app, HFpres, HFSpres, HFimg.
change (fs_frame_bytes 8) with 16384 in *.
(* ---- the entry symbolic state at C5 ---- *)
set (sp1 := c_sp1 cx) in *.
set (sF := shadow_addr F) in *.
set (nn := sc_nn IM bs) in *.
assert (Hsp1rng : sp0 - 256 < sp1 <= sp0 - 224)
by (pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)); pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)); lia).
assert (Hsp1al16 : sp1 mod 16 = 0).
{ replace sp1 with (32 * ((sp0 - 224) / 32)) by (symmetry; exact Hsp1eq).
replace (32 * ((sp0 - 224) / 32)) with (((sp0 - 224) / 32 * 2) * 16) by lia. apply Z_mod_mult. }
assert (Hsp1lo : alloc_ceiling + 16000 <= sp1) by lia.
assert (Hsp1hi : sp1 <= 2 ^ 47) by lia.
assert (Hom : (sp1 - sp0) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity).
assert (Hoff : -240 <= sp1 - sp0 <= -224)
by (destruct (proj1 (Z.mod_divide (sp1 - sp0) 16 ltac:(lia)) Hom) as [q Hq]; lia).
assert (HFlt : 0 <= F < 2 ^ 64) by lia.
assert (HsFlt : 2147450880 + 512 <= sF < 17592186044416 + 2147450880)
by (unfold sF, shadow_addr, SHADOW_OFF;
pose proof (Z.div_le_lower_bound F 8 512 ltac:(lia) ltac:(lia));
pose proof (Z.div_lt_upper_bound F 8 17592186044416 ltac:(lia) ltac:(lia)); lia).
assert (Hnnb : 1 <= nn <= 65535) by exact Hnn1.
assert (Hbody4096 : 4096 <= body) by (destruct HBLK as (H & _); exact H).
assert (Hbodyceil : body + req_size nn <= alloc_ceiling) by (destruct HBLK as (_ & _ & H & _); exact H).
assert (Hreqnn : nn <= req_size nn) by (pose proof (req_size_pos nn ltac:(lia)); lia).
unfold cfg_at, YG0d.w64. cbn [sg_pc_c5 scene_geom_asan].
rewrite <- (Z.add_assoc BASE AF_LLVMFuzzerTestOneInput SEG_C5_off).
remember (Eimg (Ereg regs3 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs3 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nn)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp3).
assert (U9 : bv_unsigned (ew E 9) = sp1)
by (rewrite (EE 9%nat 9%bv eq_refl), V_sp1; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = F)
by (rewrite (EE 23%nat 23%bv eq_refl), V_F; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = sF)
by (rewrite (EE 19%nat 19%bv eq_refl), V_shF; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = body) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = nn) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E
(mkSS (AF_LLVMFuzzerTestOneInput + SEG_C5_off) sr_atoms [s5_spill_region] None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C5_off))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, s5_spill_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold s5_spills. repeat apply Forall_cons; try apply Forall_nil.
+ apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 23 224) (F + 224));
[cbn [sv_denot]; rewrite U23; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V_expect).
+ apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 19 28) (sF + 28));
[cbn [sv_denot]; rewrite U19; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V_shexp).
+ apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 23 0) F);
[cbn [sv_denot]; rewrite U23, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V_Fsp).
+ apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 23 112) (F + 112));
[cbn [sv_denot]; rewrite U23; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V_mac).
+ apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 33 0) nn);
[cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V_nn).
+ apply (chunk_ok_val SEGS E _ sp1 88 8 (SOff 32 0) body);
[cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | zside |].
exact (val_mem_of_rdword SEGS _ _ _ _ V_body).
- cbn. tauto.
- unfold facts_ok; cbn; tauto. }
(* ---- run 1: 0x82eb0 `ld a0,0x38(s1)`, then the call of __wrap_malloc at 0x82eb4 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
(* run 1 has no write window, so it keeps every byte *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrA); [lia | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrA.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
assert (HAGA := HAG).
assert (RKAl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs msA) r = getr regs3 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msA) regs3 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
pmkst HS.
assert (HAF : AF_LLVMFuzzerTestOneInput = 0) by reflexivity.
assert (Ereq : req_size nn = nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia).
pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & HJup & _).
assert (Rsp' : spZ (ms_regs msA) = sp1) by (unfold spZ at 1; rewrite Rsp, (EE 2%nat 2%bv eq_refl); exact Hsp3).
assert (Rs0' : s0Z (ms_regs msA) = sp0)
by (unfold s0Z; rewrite (RKAl 8%bv ltac:(cbn; tauto)), V_sp0; unfold YG0d.w64; apply unsigned_lit_small; lia).
assert (Rra' : raZ (ms_regs msA) = BASE + AF_LLVMFuzzerTestOneInput + 0x640)
by (unfold raZ; rewrite Rra, HAF; apply unsigned_lit_small; lia).
assert (Hsave : forall j, 0 <= j < 13 -> rdword (aview SEGS (w_H W3) (ms_mem msA)) (sp0 - 8 - 8 * j)
= Some (bv_unsigned (getr (c_regs cx) (nth (Z.to_nat j) sc_saved_regs 0%bv)))).
{ intros j Hj. rewrite <- (HSAV j Hj). apply rdword_ext. intros k Hk. apply KA. lia. }
assert (Hach : achain ly3 (aview SEGS (w_H W3) (ms_mem msA)) sp1 sp0 (rt_ch cx)).
{ unfold rt_ch. apply (achain_ly_top (c_ly cx)).
- pose proof Hly3 as LY. destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _). exact LT.
- apply (s5_chain (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ (c_regs cx) sp1 Hch0); [lia | | | | exact Hra4 | lia | | lia].
+ intros a Ha. apply HJup; lia.
+ replace (spZ (c_regs cx) - 8) with (sp0 - 8 - 8 * 0) by (unfold sp0; lia). exact (Hsave 0 ltac:(lia)).
+ replace (spZ (c_regs cx) - 16) with (sp0 - 8 - 8 * 1) by (unfold sp0; lia). exact (Hsave 1 ltac:(lia)).
+ fold sp0. destruct (proj1 (Z.mod_divide sp0 16 ltac:(lia)) Hal16) as [q Hq]. rewrite Hq.
replace (q * 16) with ((2 * q) * 8) by lia. apply Z_mod_mult. }
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ eapply (amalloc04_rule_triv (SK := SK) SEGS B pa_segs_low errno_low LAWS ML AMALLOC W3 (ms_regs msA) (ms_mem msA) (sw_stk WK) sp0 []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 _ ev nn (sp1 - sp0)
(Z_to_bv 64 (BASE + 1600)) (rt_ch cx) HJA).
- rewrite Ra0, E33. reflexivity.
- unfold MALLOC_MAX. lia.
- unfold LIVE_MAX in *. rewrite Ereq in HBB. lia.
- rewrite Rsp'. lia.
- exact Hom.
- lia.
- lia.
- rewrite (RKAl 3%bv ltac:(cbn; tauto)). exact Hgp3.
- rewrite (RKAl 4%bv ltac:(cbn; tauto)). exact Htp3.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold EV_MAX in *. lia.
- apply (achain_chain_pre ly3 _ sp1 sp0 (rt_ch cx) (ms_regs msA) Hach); [rewrite Rsp'; lia | exact Rs0' | rewrite Rra'; lia].
- apply (HTRACE (pc_malloc_ra0 (as_code B)) (BASE + AF_LLVMFuzzerTestOneInput + 0x640) (ms_regs msA) cx Hra0 Rra').
left. split; [reflexivity | right; right; reflexivity].
- exact I. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres & Eab4 & HK4 & _).
set (np := sc_nprime IM bs) in *.
assert (RK3 : s5_rk B sp0 sp1 F sF np regs3).
{ unfold s5_rk. split; [rewrite <- Hsp3; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact Hgp3|]. split; [exact Htp3|]. split; [exact V_sp0|]. split; [exact V_sp1|].
split; [exact V_shF|]. split; [exact V_F | exact V_nprime]. }
assert (RKA : s5_rk B sp0 sp1 F sF np (ms_regs msA))
by (apply (s5_rk_kept B _ _ _ _ _ regs3); [intros r Hr; apply RKAl; cbn in Hr |- *; tauto | exact RK3]).
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP4 RKA) as RK4.
assert (SP3 : s5_spills_at W3 mem3 sp1 F sF body nn)
by (repeat split; assumption).
assert (SPA : s5_spills_at W3 (ms_mem msA) sp1 F sF body nn)
by (apply (s5_spills_kept W3 W3 mem3); [intros a Ha; apply KA; lia | exact SP3]).
pose proof HK4 as (HK4up & HK4blk & HK4img & HK4frm & HK4pres & HK4win).
assert (SP4 : s5_spills_at W4 mem4 sp1 F sF body nn)
by (apply (s5_spills_kept W3 W4 (ms_mem msA)); [intros a Ha; apply HK4up; lia | exact SPA]).
pose proof RK4 as (R4_2 & R4_3 & R4_4 & R4_8 & R4_9 & R4_19 & R4_23 & R4_24).
clear HS HE HEI EE HAG HAGA E32 E33 U2 U9 U23 U19 U32 U33 Ra0 Rra Rsp Rgp Rtp Rs0 E.
(* ---- block B: 0x82eb8 `beqz a0` (refuted), then up to the call of __asan_memcpy at 0x82ee0 ---- *)
pose proof (s5_entry W4 regs4 mem4 1600 sp1 F sF body nn R4_9 R4_23 R4_19 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SP4) as HS.
remember (Eimg (Ereg regs4 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Hin4 : In (res, nn) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_or_app; right; left; reflexivity).
pose proof (proj1 HJ4) as HAR4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res nn HAR4 Hin4) as (Hres16 & Hres4096' & Hresceil & Hresapp & Hrespres & _).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs4 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
(* ---- the cut C6, from what each arm gives back: the journal, the protected bytes, the registers ---- *)
assert (Hftok : aftok [] (ablocks B (c_ly cx) (c_S cx)) (res, nn))
by (eapply (aftok_new_block SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia]).
assert (Hfresh : ~ In (res, nn) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. destruct (Hftok Hc 0 ltac:(cbn [snd]; lia)) as (r & [] & _). }
unfold sc_from_C6 in HC6.
assert (EXIT : forall regs6 mem6 md6,
ajournal (SK := SK) SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 W4 mem6 md6 (ev + 1) ->
(forall a, s5_prot sp0 sp1 F sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a) ->
(forall a, s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a) ->
s5_rk B sp0 sp1 F sF np regs6 -> getr regs6 18 = Z_to_bv 64 body -> getr regs6 20 = Z_to_bv 64 res ->
SRr SEGS W4 (mkCfg (mkst regs6 (Z_to_bv 64 (BASE + 1960)) mem6 (seg_rom SEGS)) md6) POST).
{ intros regs6 mem6 md6 HJ6 KP6 KR6 RK6 R6_18 R6_20.
pose proof RK6 as (R6_2 & R6_3 & R6_4 & R6_8 & R6_9 & R6_19 & R6_23 & R6_24).
pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & Hnev6 & _).
replace (Z_to_bv 64 (BASE + 1960)) with (YG0d.w64 (sg_pc_c6 IM))
by (cbn [sg_pc_c6 scene_geom_asan]; unfold YG0d.w64, SEG_C6_off; rewrite HAF; f_equal).
change (mkCfg (mkst regs6 (YG0d.w64 (sg_pc_c6 IM)) mem6 (seg_rom SEGS)) md6) with (cfg_at SEGS (sg_pc_c6 IM) regs6 mem6 md6).
apply (HC6 ly4 S4 W4 regs6 mem6 md6 bs body res (ev + 1)).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 Hly6) as (_ & EFA6 & _).
assert (Hfin4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs6; left; reflexivity).
destruct (al_frames _ _ LAWS ly4 S4 W4 mem6 md6 8 (c_fpos cx) HAR6 Hfin4) as (_ & _ & HFp6 & HFSp6).
assert (EF6 : frame_addr ly4 8 (c_fpos cx) = F) by (rewrite EFA6; reflexivity).
rewrite EF6 in HFp6, HFSp6. change (fs_frame_bytes 8) with 16384 in HFp6, HFSp6.
change (16384 / 8) with 2048 in HFSp6.
assert (KSH : forall o, 0 <= o < 1176 -> aview SEGS (w_H W4) mem6 (sF + o) = aview SEGS (w_H W3) mem3 (sF + o)).
{ intros o Ho. destruct (Z_lt_dec o 28); [|destruct (Z_lt_dec o 1141)].
- apply KP6. unfold s5_prot. right; right; right; right; left. lia.
- apply KR6. unfold s5_row. lia.
- apply KP6. unfold s5_prot. right; right; right; right; right. lia. }
assert (HF8 : forall k, 0 <= k -> (F + 8 * k) / 8 = F / 8 + k).
{ intros k Hk. destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [q Hq]. rewrite Hq.
replace (q * 32 + 8 * k) with ((4 * q + k) * 8) by lia. replace (q * 32) with ((4 * q) * 8) by lia.
rewrite !Z.div_mul by lia. reflexivity. }
destruct HFRM as (HFLAG & _ & _).
cbn [sg_cid scene_geom_asan] in HFLAG. change (fs_frame_bytes 8) with 16384 in HFLAG.
cbn [sc_open sg_off_blk sg_blk_n sg_off_mac sg_mac_n scene_geom_asan] in HOPBLK, HOPMAC.
unfold cut_C6.
cbn [sg_cid sg_sh_blki_lo sg_sh_blki_hi sg_off_blk sg_blk_n sg_off_mac sg_mac_n sg6_sp0 sg6_sp1 sg6_F sg6_Fsp
sg6_shF sg6_body sg6_before scene_geom_asan vat].
unfold RV_s0, RV_s1, RV_s2, RV_s3, RV_s4, RV_s7.
fold sp0 sp1 F nn. fold sF.
split; [lia|].
split; [split; [exact HJ6|]; split; [rewrite Hfrs6, Hfrs0; reflexivity | exact I]|].
split; [rewrite Eab4; apply Permutation_app_tail; exact HPerm|].
split.
{ rewrite (blocks_bytes_bsum B ly4 S4), Eab4, bsum_app, <- (blocks_bytes_bsum B ly3 S3).
change (bsum [(res, nn)]) with (nn + 0). rewrite Ereq in HBB |- *. lia. }
split; [exact HBLK|].
split.
{ unfold sc_blk_ok. split; [lia|]. split.
{ apply zone2_of_app; [exact Hresapp | exact (blk_off_imgP B ly4 S4 W4 mem4 md4 res nn HAR4 Hin4)]. }
split; [exact Hresceil|]. split; [exact Hres16|]. split; [|exact Hftok].
intros blc lyq ownq i Hb Hi. right; right; left. exists res, nn. split; [exact Hb|]. split; [exact Hfresh | lia]. }
split.
{ unfold sc_frame. cbn [sg_cid scene_geom_asan]. change (fs_frame_bytes 8) with 16384. fold F. fold sF.
split; [rewrite <- HFLAG; apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; right; right; left; lia|].
split; [intros a Ha; exact (proj1 (HFp6 a Ha))|].
change (16384 / 8) with 2048. intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
exact (proj1 (HFSp6 (a - shadow_addr F) ltac:(fold sF; lia))). }
split; [intros j Hj; rewrite <- (HSAV j Hj); apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; right; left; lia|].
split.
{ unfold sc_shbg in *. cbn [sg_sh_bg scene_geom_asan] in *. rewrite Forall_forall in *. intros t Ht.
specialize (HSHBG t Ht). cbn [In] in Ht.
destruct Ht as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in *; unfold sc_shr in *;
intros o Ho; fold F; fold sF; rewrite KSH by lia; apply HSHBG; exact Ho. }
split; [unfold sc_shr in *; intros o Ho; fold F; fold sF; rewrite KSH by lia; apply HSHBI; exact Ho|].
split.
{ unfold sc_open in *. destruct HOPBLK as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
intros i Hi. change ((34 + 7) / 8) with 5 in Hi.
assert (Ea : shadow_of_addr SHADOW_OFF (F + 144) + i = sF + (18 + i))
by (unfold shadow_of_addr, sF, shadow_addr; replace (F + 144) with (F + 8 * 18) by lia; rewrite HF8 by lia; lia).
fold F. rewrite Ea, KSH by lia. rewrite <- Ea. exact (Hc i Hi). }
split.
{ unfold sc_open in *. destruct HOPMAC as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
assert (Ea : shadow_of_addr SHADOW_OFF (F + 112) + i = sF + (14 + i))
by (unfold shadow_of_addr, sF, shadow_addr; replace (F + 112) with (F + 8 * 14) by lia; rewrite HF8 by lia; lia).
fold F. rewrite Ea, KSH by lia. rewrite <- Ea. exact (Hc i Hi). }
split.
{ unfold sc_img. split; [unfold spZ; rewrite R6_2; apply unsigned_lit_small; lia|].
split; [exact R6_3|]. split; [exact R6_4|].
rewrite HWRLO, HWRHI. rewrite HWRLO, HWRHI in HROD0.
assert (HRODP : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
by (unfold arodata_okP, in_roP; exact HROD0).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6 HRODP) as HROD6.
unfold arodata_okP, in_roP in HROD6. exact HROD6. }
split; [exact HIN|]. split; [exact Hnn1|].
split; [exact R6_8|]. split; [exact R6_9|]. split; [exact R6_23|].
split; [rewrite <- V_Fsp; apply rdword_ext; intros k Hk; apply KP6; unfold s5_prot; left; lia|].
split; [exact R6_19|]. split; [exact R6_18 | exact R6_20]. }
(* 0x82eb8 beqz a0 -> abort: malloc returned res >= 4096 *)
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), Ha04 in Hc.
cbn [branch_taken] in Hc. unfold bv_eqb, YG0d.w64 in Hc.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite !unsigned_lit_small in Hc by lia.
apply Z.eqb_eq in Hc. lia. }
paj_run_shc RUNP RUNC HS HJ4.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msB, HJ4 into HJB, HFr into HFrB. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (20%bv : bv 5) Rs4. prreg HS (18%bv : bv 5) Rs2. prreg HS (21%bv : bv 5) Rs5.
assert (HAG4 : env_agree 32 (Ereg regs4 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (RKB : s5_rk B sp0 sp1 F sF np (ms_regs msB)).
{ apply (s5_rk_kept B _ _ _ _ _ regs4); [|exact RK4]. intros x Hx.
exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msB) regs4 (s5_extra body nn) [2; 3; 4; 8; 9; 19; 23; 24]%bv HS HAG4 eq_refl x Hx). }
pose proof RKB as (RB2 & RB3 & RB4 & RB8 & RB9 & RB19 & RB23 & RB24).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msB) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrB); [lia | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. lia. }
clear HFrB.
pmkst HS.
(* ---- facts on n', body and before ---- *)
assert (Enn : nn = if np =? 0 then 1 else np) by reflexivity.
assert (Hnp0 : 0 <= np).
{ unfold np, sc_nprime, sc_u16. cbn [sg_scene_n scene_geom_asan].
destruct (HIN 1 ltac:(lia)) as ((? & ?) & _). destruct (HIN 2 ltac:(lia)) as ((? & ?) & _).
destruct (Z.land (bs 0) 1 =? 0); lia. }
assert (Hnp : 0 <= np <= nn) by (rewrite Enn; destruct (Z.eqb_spec np 0); lia).
assert (Hbody3 : In (body, nn) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | apply in_or_app; right; left; reflexivity]).
assert (Hbody4 : In (body, nn) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_or_app; left; exact Hbody3).
assert (HdisjBR : res + nn <= body \/ body + nn <= res).
{ apply in_split in Hbody3 as (l1 & l2 & E1).
pose proof (sep_blocks_pos SEGS B LAWS ly4 S4 W4 mem4 md4 (body, nn) (res, nn) l1 l2 [] HAR4) as Hd.
rewrite Eab4, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Ereq in Hd. lia. }
pose proof (proj1 HJB) as HARB.
destruct (al_blocks _ _ LAWS _ _ _ _ _ body nn HARB Hbody4) as (_ & _ & Hbceil & _ & HbpresB & _).
(* ---- __asan_memcpy(before, body, n') at 0x82ee0 ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := SK) SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W4 (ms_regs msB) (ms_mem msB)
(sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
res body np (sp1 - sp0) (Z_to_bv 64 (BASE + 1644)) HJB).
- rewrite Ra0, (EE 10%nat 10%bv eq_refl). exact Ha04.
- rewrite Ra1. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs4 _ 0). reflexivity.
- rewrite Ra2, (EE 24%nat 24%bv eq_refl). exact R4_24.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite RB2, unsigned_lit_small by lia. lia.
- exact Hom.
- lia.
- rewrite Hes. lia.
- exact RB3.
- exact RB4.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [| rewrite Hes; lia].
replace a with (res + (a - res)) by lia.
eapply (awr_new_block SEGS B LAWS); [exact HJA | exact HAR4 | exact Eab4 | lia | exact Hin4 | lia].
- eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hin4); lia.
- eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hin4); lia.
- intros Hnz. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hin4); lia.
- cbv iota. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HbpresB a ltac:(lia))) |].
unfold spZ at 1. rewrite RB2, unsigned_lit_small by lia. rewrite Hes. lia. }
split; [lia|]. split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hbody4); lia|].
split; [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hbody4); lia|].
intros Hnz. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HARB Hbody4); lia. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
(* ---- the state at the memcpy return 0x82ee4 (BASE + 1644) ---- *)
pose proof HJ5 as (HAR5 & Hly5 & _ & _ & _ & Hfrs5 & _).
assert (Hfin5 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs5; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR0 Hly5) as (_ & EFA5 & _).
assert (EF4 : frame_addr ly4 8 (c_fpos cx) = F) by (rewrite EFA5; reflexivity).
assert (HbodyZ : body + nn <= 2147446784 \/ 17594333495296 <= body).
{ destruct HBLK as (_ & HZ & _). rewrite Ereq in HZ. exact (zone2_band _ _ HZ). }
assert (HresZ : res + nn <= 2147446784 \/ 17594333495296 <= res).
{ pose proof (zone2_of_app _ _ Hresapp (blk_off_imgP B ly4 S4 W4 mem4 md4 res nn HAR4 Hin4)) as HZ.
rewrite Ereq in HZ. exact (zone2_band _ _ HZ). }
assert (HdFB : body + nn <= F \/ F + 16384 <= body).
{ pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem5 md5 body nn 8 (c_fpos cx) HAR5 Hbody4 Hfin5) as X.
unfold zdisjoint in X. cbn [fst snd] in X. rewrite EF4, Ereq in X. change (fs_frame_bytes 8) with 16384 in X. revert X; zl. }
assert (HdFR : res + nn <= F \/ F + 16384 <= res).
{ pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem5 md5 res nn 8 (c_fpos cx) HAR5 Hin4 Hfin5) as X.
unfold zdisjoint in X. cbn [fst snd] in X. rewrite EF4, Ereq in X. change (fs_frame_bytes 8) with 16384 in X. revert X; zl. }
assert (HF8z : F = 8 * (F / 8)).
{ destruct (proj1 (Z.mod_divide F 32 ltac:(zl)) HF32) as [q Hq]. rewrite Hq.
replace (q * 32) with ((4 * q) * 8) by zl. rewrite Z.div_mul by zl. zl. }
assert (EsF : sF = 2147450880 + F / 8) by (unfold sF, shadow_addr, SHADOW_OFF; reflexivity).
assert (HsFhi : sF + 2048 <= 17594333429760) by zl.
assert (RNG : forall a, s5_u sp1 F sF a \/ s5_row sF a -> 0 <= a < 2 ^ 64)
by (intros a Ha; apply (s5_u_rng sp1 F sF a Ha); zl).
assert (BU : forall a, s5_u sp1 F sF a \/ s5_row sF a -> ~ (body <= a < body + nn))
by (intros a Ha; apply (s5_u_out sp1 F sF a body (body + nn) Ha); [zl | generalize HdFB; zl | generalize HbodyZ; zl]).
assert (RU : forall a, s5_u sp1 F sF a \/ s5_row sF a -> ~ (res <= a < res + nn))
by (intros a Ha; apply (s5_u_out sp1 F sF a res (res + nn) Ha); [zl | generalize HdFR; zl | generalize HresZ; zl]).
assert (SU : forall a lo hi, sp1 - 16384 <= lo -> hi <= sp1 -> s5_u sp1 F sF a \/ s5_row sF a -> ~ (lo <= a < hi))
by (intros a lo hi Hlo Hhi Ha; apply (s5_u_out sp1 F sF a lo hi Ha); zl).
assert (K5 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (RNG a Ha) as Hr.
rewrite (Hfr5 a Hr); [| intros X; apply (RU a Ha); zl | apply (SU a); [zl | zl | exact Ha]].
rewrite (KB a Hr).
destruct (Z_le_gt_dec sp1 a) as [Hup | Hlow].
- rewrite HK4up by zl. apply KA. zl.
- assert (Hfs : F <= a < F + 16384 \/ sF <= a < sF + 2048) by (generalize Ha; unfold s5_u, s5_row; zl).
rewrite (HK4frm 8 (c_fpos cx) a Hfin3); [apply KA; zl | | cbv beta; rewrite Ereq; exact (RU a Ha)].
unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes 8) with 16384.
change (16384 / 8) with 2048. fold sF. exact Hfs. }
assert (SP5 : s5_spills_at W4 mem5 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem5); [intros a Ha; apply K5; left; unfold s5_u; zl | exact SP3]. }
assert (HB5 : forall i, 0 <= i < np -> aview SEGS (w_H W4) mem5 (res + i) = aview SEGS (w_H W4) mem5 (body + i)).
{ intros i Hi. rewrite (Heff5 i Hi). rewrite (Hfr5 (body + i)); [reflexivity | zl | generalize HdisjBR; zl | zl]. }
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP5 RKB) as RK5.
pose proof RK5 as (R5_2 & R5_3 & R5_4 & R5_8 & R5_9 & R5_19 & R5_23 & R5_24).
assert (R5_20 : getr regs5 20 = Z_to_bv 64 res).
{ transitivity (getr (ms_regs msB) 20); [exact (HP5 20 ltac:(unfold acallee_saved; zl))|].
rewrite Rs4, (EE 10%nat 10%bv eq_refl). exact Ha04. }
assert (R5_21 : getr regs5 21 = Z_to_bv 64 body).
{ transitivity (getr (ms_regs msB) 21); [exact (HP5 21 ltac:(unfold acallee_saved; zl))|].
rewrite Rs5. subst E. rewrite Eimg_low by (unfold A_TEXT; zl). exact (ew_Ereg_extra regs4 _ 0). }
assert (R5_18 : bv_unsigned (getr regs5 18) = if np =? 8904 then 1 else 0).
{ assert (X : getr regs5 18 = getr (ms_regs msB) 18) by exact (HP5 18 ltac:(unfold acallee_saved; zl)).
rewrite X, Rs2, s5_seqz_xor, (EE 24%nat 24%bv eq_refl), R4_24. rewrite unsigned_lit_small by zl. reflexivity. }
(* ---- run C: 0x82ee4 .. jal reac_ctrl_scene_set_mac (0x82ef4) ---- *)
clear Hc HS HE HEI EE HAG4 E Ra0 Ra1 Ra2 Rra Rs4 Rs2 Rs5.
pose proof (s5_entry W4 regs5 mem5 1644 sp1 F sF body nn R5_9 R5_23 R5_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP5) as HS.
remember (Eimg (Ereg regs5 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs5 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs5 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
paj_run_shc RUNP RUNC HS HJ5.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. zl. }
rename ms into msC, HJ5 into HJC, HFr into HFrC. clear HF HG.
prreg HS (10%bv : bv 5) RCa0. prreg HS (11%bv : bv 5) RCa1. prreg HS (12%bv : bv 5) RCa2.
prreg HS (1%bv : bv 5) RCra. prreg HS (25%bv : bv 5) RCs9.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msC) a = aview SEGS (w_H W4) mem5 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrC); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrC.
assert (RKCl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24]%bv -> getr (ms_regs msC) r = getr regs5 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msC) regs5 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24]%bv HS HAG eq_refl x Hx). }
pmkst HS.
(* ---- facts the D block needs at every call ---- *)
assert (HF8 : forall k, 0 <= k -> (F + 8 * k) / 8 = F / 8 + k).
{ intros k Hk. rewrite HF8z at 1. replace (8 * (F / 8) + 8 * k) with ((F / 8 + k) * 8) by ring.
rewrite Z.div_mul by zl. reflexivity. }
assert (BSM : forall mem, (forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) mem3 a) ->
block_shadow (aview SEGS (w_H W4) mem) SHADOW_OFF (F + 112) 6).
{ intros mem Hk. unfold sc_open in HOPMAC. cbn [sg_off_mac sg_mac_n scene_geom_asan] in HOPMAC. fold F in HOPMAC.
destruct HOPMAC as (Hm & Hn & Hc). split; [exact Hm|]. split; [exact Hn|].
intros i Hi. change ((6 + 7) / 8) with 1 in Hi.
assert (Ea : shadow_of_addr SHADOW_OFF (F + 112) + i = sF + (14 + i)).
{ unfold shadow_of_addr. rewrite EsF. replace (F + 112) with (F + 8 * 14) by ring. rewrite HF8 by zl. unfold SHADOW_OFF. zl. }
rewrite Ea, Hk by (unfold s5_u; zl). rewrite <- Ea. exact (Hc i Hi). }
pose proof Hly5 as LY5. destruct LY5 as (_ & _ & _ & _ & _ & _ & _ & _ & LT5 & _).
pose proof Hly3 as LY3. destruct LY3 as (_ & _ & _ & _ & _ & _ & _ & _ & LT3 & _).
assert (ACH : forall mem, (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem a = aview SEGS (w_H W3) mem3 a) ->
achain ly4 (aview SEGS (w_H W4) mem) sp1 sp0 (rt_ch cx)).
{ intros mem Hk. apply (achain_ly_top ly3 ly4); [rewrite LT5, LT3; reflexivity|].
apply (achain_kept ly3 (aview SEGS (w_H W3) (ms_mem msA)) _ sp1 sp0 (rt_ch cx) sp1 Hach); [zl | rewrite LT3; zl |].
intros a Ha. rewrite (Hk a Ha), (KA a) by zl. reflexivity. }
assert (HbodyF : ~ In (body, nn) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. destruct HBLK as (_ & _ & _ & _ & _ & Hftb).
destruct (Hftb Hc 0 ltac:(cbn [snd]; rewrite Ereq; zl)) as (r & [] & _). }
assert (Ego : scene_go body np (F + 112) = (np =? 8904)).
{ unfold scene_go, SCENE_BYTES. rewrite (proj2 (Z.eqb_neq body 0)) by zl. rewrite (proj2 (Z.eqb_neq (F + 112) 0)) by zl.
cbn [negb]. rewrite !Bool.andb_true_r. reflexivity. }
assert (Eok : scene_okb body np (F + 112) = (np =? 8904)).
{ unfold scene_okb, SCENE_BYTES. rewrite (proj2 (Z.eqb_neq body 0)) by zl. rewrite (proj2 (Z.eqb_neq (F + 112) 0)) by zl.
cbn [negb]. rewrite !Bool.andb_true_r. reflexivity. }
assert (Hnn89 : np = 8904 -> nn = 8904) by (intros X; rewrite Enn; destruct (Z.eqb_spec np 0); zl).
(* ---- reac_ctrl_scene_set_mac(body, n', mac) at 0x82ef4 (cl_callS over SSM) ---- *)
assert (UC23 : bv_unsigned (ew E 23) = F) by (rewrite (EE 23%nat 23%bv eq_refl), R5_23; apply unsigned_lit_small; zl).
rewrite UC23 in RCa2, RCs9.
assert (EspC : spZ (ms_regs msC) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite (RKCl 2%bv ltac:(cbn; tauto)), R5_2, unsigned_lit_small by zl. ring. }
assert (Es0C : s0Z (ms_regs msC) = sp0).
{ unfold s0Z. rewrite (RKCl 8%bv ltac:(cbn; tauto)), R5_8. apply unsigned_lit_small. zl. }
rewrite pa_sigma_reac_ctrl_scene_set_mac.
eapply SRr_bind.
{ eapply (cl_callS (SK := SK) B LAWS W4 (ms_regs msC) (ms_mem msC) _ (sw_stk WK) sp0 []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
SET_MAC_STK (setmac_fp body np (F + 112)) 0 (sp1 - sp0) (Z_to_bv 64 (BASE + 1664)) (rt_ch cx) _ HJC).
- exact EspC.
- exact Hom.
- zl.
- unfold SET_MAC_STK, SET_MAC_FRAME. zl.
- zl.
- rewrite (RKCl 3%bv ltac:(cbn; tauto)). exact R5_3.
- rewrite (RKCl 4%bv ltac:(cbn; tauto)). exact R5_4.
- exact RCra.
- apply ret_ok_codeptr_v; [zl | reflexivity].
- rewrite unsigned_lit_small by zl. zl.
- replace (sp0 + (sp1 - sp0)) with sp1 by ring. rewrite Es0C. apply ACH.
intros a Ha. rewrite (KC a) by zl. apply K5. left. unfold s5_u. zl.
- intros HPRE. eapply SRr_mono.
+ apply (SSM ly4 S4 W4 (ms_regs msC) (ms_mem msC) _ (rt_ch cx) body np (F + 112) HPRE).
* rewrite RCa0, (EE 21%nat 21%bv eq_refl), R5_21. reflexivity.
* rewrite RCa1, (EE 24%nat 24%bv eq_refl), R5_24. reflexivity.
* exact RCa2.
* zl.
* zl.
* zl.
* intros Hgo. rewrite Ego in Hgo. apply Z.eqb_eq in Hgo. pose proof (Hnn89 Hgo) as Hn8.
unfold MAC_OFF, MAC_LEN.
split; [exists body, nn; split; [exact Hbody4 | rewrite Ereq; zl]|].
split; [right | generalize HdFB; zl].
apply (afobj_of_own SK SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)]
ly4 S4 W4 (ms_mem msC) _ (ev + 1) 8 (c_fpos cx) (F + 112) 6 HJC).
-- left. reflexivity.
-- zl.
-- rewrite EF4. zl.
-- rewrite EF4. change (fs_frame_bytes 8) with 16384. zl.
-- replace (F + 112) with ((F / 8 + 14) * 8) by zl. apply Z_mod_mult.
-- apply (block_shadow_range (aview SEGS (w_H W4) (ms_mem msC)) SHADOW_OFF (F + 112) 6 (F + 112) 6); [| zl | zl].
apply BSM. intros a Ha. rewrite (KC a) by (apply (RNG a); left; exact Ha). apply K5. left. exact Ha.
+ intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ).
exists ly', S', regs', mem', md'. split; [rewrite RCra; reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HQ].
- intros a HFP. right. unfold setmac_fp in HFP. rewrite Ego in HFP.
destruct (Z.eqb_spec np 8904) as [Hq | Hq]; [| destruct HFP as (r & [] & _)].
destruct HFP as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold MAC_OFF, MAC_LEN in Hr. pose proof (Hnn89 Hq) as Hn8.
exists body, nn. split; [exact Hbody4|]. split; [exact HbodyF | rewrite Ereq; zl]. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6c & HP6 & HQ6).
destruct HQ6 as (-> & -> & -> & _ & HD10 & HDmem).
rewrite Ego in HD10, HDmem.
replace (ev + 1 + 0) with (ev + 1) in HJ6 by ring.
assert (RKC : s5_rk B sp0 sp1 F sF np (ms_regs msC))
by (apply (s5_rk_kept B _ _ _ _ _ regs5); [intros r Hr; apply RKCl; cbn in Hr |- *; tauto | exact RK5]).
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP6 RKC) as RK6.
pose proof RK6 as (R6_2 & R6_3 & R6_4 & R6_8 & R6_9 & R6_19 & R6_23 & R6_24).
assert (R6_18 : bv_unsigned (getr regs6 18) = if np =? 8904 then 1 else 0).
{ assert (X : getr regs6 18 = getr (ms_regs msC) 18) by exact (HP6 18 ltac:(unfold acallee_saved; zl)).
rewrite X, (RKCl 18%bv ltac:(cbn; tauto)). exact R5_18. }
assert (R6_20 : getr regs6 20 = Z_to_bv 64 res).
{ assert (X : getr regs6 20 = getr (ms_regs msC) 20) by exact (HP6 20 ltac:(unfold acallee_saved; zl)).
rewrite X, (RKCl 20%bv ltac:(cbn; tauto)). exact R5_20. }
assert (R6_25 : getr regs6 25 = Z_to_bv 64 (F + 112)).
{ assert (X : getr regs6 25 = getr (ms_regs msC) 25) by exact (HP6 25 ltac:(unfold acallee_saved; zl)).
rewrite X. exact RCs9. }
(* what set_mac kept: everything at or above sp1, the frame and its shadow (both arms) *)
assert (K6C : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W4) (ms_mem msC) a).
{ intros a Ha. pose proof (RNG a Ha) as Hr.
destruct (Z.eqb_spec np 8904) as [Hq | Hq].
- destruct HDmem as (_ & HDk). pose proof (Hnn89 Hq) as Hn8. apply HDk; [exact Hr | | rewrite EspC].
+ intros X. apply (BU a Ha). unfold MAC_OFF, MAC_LEN in X. zl.
+ unfold SET_MAC_STK, SET_MAC_FRAME. apply (SU a); [zl | zl | exact Ha].
- apply sm_aview_same_at. apply HDmem. rewrite unsigned_lit_small by zl. rewrite EspC. unfold SET_MAC_FRAME.
apply (SU a); [zl | zl | exact Ha]. }
assert (KU6 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (K6C a Ha), (KC a (RNG a Ha)). exact (K5 a Ha). }
assert (SP6 : s5_spills_at W4 mem6 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem6); [intros a Ha; apply KU6; left; unfold s5_u; zl | exact SP3]. }
(* ---- the call kit of the D block: block and frame operand facts, and one bcmp returning 0 ---- *)
assert (BLKF : forall mem md p m x n, AR SEGS B ly4 S4 W4 mem md -> In (p, m) (ablocks B ly4 S4) -> p <= x ->
x + n <= p + req_size m -> 0 <= n ->
(forall a, x <= a < x + n -> aview SEGS (w_H W4) mem a <> None) /\ amem_range x n /\
range_addressable (aview SEGS (w_H W4) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W4) mem) x n)).
{ intros mem md p m x n HAR Hin H1 H2 Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & _ & _ & Hpres & _).
split; [intros a Ha; apply (aview_some_of_apresent SEGS); apply (proj1 (Hpres a ltac:(zl)))|].
split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); zl|].
split; [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); zl|].
intros Hnz0. eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); zl. }
assert (FRMF : forall mem md x n, AR SEGS B ly4 S4 W4 mem md -> F <= x -> x + n <= F + 16384 -> 0 < n ->
(forall a, x <= a < x + n -> aview SEGS (w_H W4) mem a <> None) /\ amem_range x n /\
shadow_hull_vis (aview SEGS (w_H W4) mem) x n).
{ intros mem md x n HAR H1 H2 Hn.
destruct (al_frames _ _ LAWS ly4 S4 W4 mem md 8 (c_fpos cx) HAR Hfin5) as (_ & _ & Hpres & _).
rewrite EF4 in Hpres. change (fs_frame_bytes 8) with 16384 in Hpres.
split; [intros a Ha; apply (aview_some_of_apresent SEGS); apply (proj1 (Hpres a ltac:(zl)))|].
split; [apply (amem_range_sub_app F 16384); [exact HFapp | zl | zl | zl | zl]|].
apply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 mem md 8 (c_fpos cx)); [exact HAR | exact Hfin5 | rewrite EF4; zl |
rewrite EF4; change (fs_frame_bytes 8) with 16384; zl | exact Hn]. }
assert (BCMP : forall regsT memT mdT x y n retk (Q : world SEGS -> config -> Prop),
ajournal (SK := SK) SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 W4 memT mdT (ev + 1) ->
getr regsT 10 = Z_to_bv 64 x -> getr regsT 11 = Z_to_bv 64 y -> getr regsT 12 = Z_to_bv 64 n ->
getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
s5_rk B sp0 sp1 F sF np regsT ->
0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= alloc_ceiling -> 0 <= y -> y + n <= alloc_ceiling ->
(forall a, x <= a < x + n -> aview SEGS (w_H W4) memT a <> None) ->
(forall a, y <= a < y + n -> aview SEGS (w_H W4) memT a <> None) ->
amem_range x n -> amem_range y n ->
range_addressable (aview SEGS (w_H W4) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W4) memT) x n) ->
range_addressable (aview SEGS (w_H W4) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W4) memT) y n) ->
(forall i, 0 <= i < n -> aview SEGS (w_H W4) memT (x + i) = aview SEGS (w_H W4) memT (y + i)) ->
(forall regs2 mem2 md2,
ajournal (SK := SK) SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 W4 mem2 md2 (ev + 1) ->
aregs_preserved regsT regs2 -> getr regs2 10 = Z_to_bv 64 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) mem2 a = aview SEGS (w_H W4) memT a) ->
SRr SEGS W4 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W4 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT) Q).
{ intros regsT memT mdT x y n retk Q HJT Ha0 Ha1 Ha2 Hra Hrk Hrk2 RKT Hn Hx0 Hxc Hy0 Hyc Hvx Hvy Hmx Hmy Hrx Hhx Hry Hhy Heq Hk.
pose proof RKT as (T2 & T3 & T4 & _).
assert (Usp : spZ regsT = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite T2, unsigned_lit_small by zl; ring).
eapply SRr_bind.
{ apply (aj_bcmp_at (SK := SK) SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W4 regsT memT
(sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 mdT (ev + 1) x y n (sp1 - sp0)
(Z_to_bv 64 (BASE + retk)) HJT Ha0 Ha1 Ha2 Hn Hx0 ltac:(zl) Hy0 ltac:(zl) Usp Hom ltac:(zl) ltac:(rewrite Hes; zl) T3 T4 Hra
(ret_ok_codeptr_v retk Hrk Hrk2)).
- intros a Ha. split; [exact (Hvx a Ha) | rewrite Usp, Hes; zl].
- intros a Ha. split; [exact (Hvy a Ha) | rewrite Usp, Hes; zl].
- intros a Ha. rewrite Hes. zl.
- intros a Ha. rewrite Hes. zl.
- exact Hmx. - exact Hmy. - exact Hrx. - exact Hhx. - exact Hry. - exact Hhy. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2).
apply (Hk regs2 mem2 md2 HJ2 HP2).
- rewrite Hv. apply (proj2 Hcmp). exact Heq.
- intros a Ha Hna. apply Hfr; [exact Ha|]. rewrite Hes. zl. }
(* ---- run D: 0x82ef8 addi s2,s2,-1; 0x82efc bne a0,s2 -> abort ---- *)
clear HS HE HEI EE HAG E RCa0 RCa1 RCa2 RCra RCs9 UC23.
pose proof (s5_entry W4 regs6 mem6 1664 sp1 F sF body nn R6_9 R6_23 R6_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP6) as HS.
remember (Eimg (Ereg regs6 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs6 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs6 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs6 _ 0)).
paj_run_shc RUNP RUNC HS HJ6.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. zl. }
rename ms into msD1, HFr into HFrD1. clear HF HG.
assert (KD1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msD1) a = aview SEGS (w_H W4) mem6 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrD1); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrD1.
(* 0x82efc bne a0,s2 -> abort: a0 = (if n' = 8904 then 0 else -1) = s2 - 1 (set_mac's post and s5_seqz_xor) *)
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), (EE 18%nat 18%bv eq_refl), HD10, R6_18 in Hc.
destruct (np =? 8904); vm_compute in Hc; discriminate Hc. }
clear Hc.
(* 0x82f00 mv s6,a0; 0x82f04 beqz a0 -> 0x82f4c *)
paj_run_shc RUNP RUNC HS HJ6.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msD, HJ6 into HJD, HFr into HFrD. clear HF HG.
assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msD) a = aview SEGS (w_H W4) (ms_mem msD1) a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrD); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrD.
assert (RKDl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv -> getr (ms_regs msD) r = getr regs6 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msD) regs6 (s5_extra body nn)
[2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (22%bv : bv 5) RDs6. prreg HS (18%bv : bv 5) RDs2.
assert (RD22 : getr (ms_regs msD) 22 = w64 (if np =? 8904 then 0 else -1)) by (rewrite RDs6, (EE 10%nat 10%bv eq_refl); exact HD10).
psrr_branch_pi RUNP BR HS.
2: {
(* ======== the r <> 0 arm (n' <> 8904): 0x82f08 .. 0x82f48 -> C6 ======== *)
assert (Hq : np <> 8904).
{ intros Hq. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), HD10 in Hc.
rewrite (proj2 (Z.eqb_eq np 8904) Hq) in Hc. vm_compute in Hc. discriminate Hc. }
rewrite (proj2 (Z.eqb_neq np 8904) Hq) in HD10, HDmem, RD22.
assert (KM6 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) (ms_mem msD) a = aview SEGS (w_H W4) mem5 a).
{ intros a Ha Hn. rewrite (KD a Ha), (KD1 a Ha), <- (KC a Ha). apply sm_aview_same_at. apply HDmem.
rewrite unsigned_lit_small by zl. rewrite EspC. unfold SET_MAC_FRAME. zl. }
assert (KUD : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) (ms_mem msD) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KD a (RNG a Ha)), (KD1 a (RNG a Ha)). exact (KU6 a Ha). }
assert (HBD : forall i, 0 <= i < np -> aview SEGS (w_H W4) (ms_mem msD) (body + i) = aview SEGS (w_H W4) (ms_mem msD) (res + i)).
{ intros i Hi. rewrite !KM6 by zl. symmetry. exact (HB5 i Hi). }
(* run E: 0x82f08 ld s2,0x58(s1) .. jal bcmp (0x82f18) *)
paj_run_shc RUNP RUNC HS HJD.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msE, HJD into HJE, HFr into HFrE. clear HF HG.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msE) a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrE); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrE.
assert (REl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv -> getr (ms_regs msE) r = getr regs6 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msE) regs6 (s5_extra body nn)
[2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) REa0. prreg HS (11%bv : bv 5) REa1. prreg HS (12%bv : bv 5) REa2.
prreg HS (1%bv : bv 5) REra. prreg HS (18%bv : bv 5) REs2. prreg HS (22%bv : bv 5) REs6.
assert (RKE : s5_rk B sp0 sp1 F sF np (ms_regs msE))
by (apply (s5_rk_kept B _ _ _ _ _ regs6); [intros r Hr; apply REl; cbn in Hr |- *; tauto | exact RK6]).
assert (RE18 : getr (ms_regs msE) 18 = Z_to_bv 64 body) by (rewrite REs2; exact E32).
assert (RE20 : getr (ms_regs msE) 20 = Z_to_bv 64 res) by (rewrite (REl 20%bv ltac:(cbn; tauto)); exact R6_20).
assert (RE22 : getr (ms_regs msE) 22 = w64 (-1)) by (rewrite REs6, (EE 10%nat 10%bv eq_refl); exact HD10).
assert (RE25 : getr (ms_regs msE) 25 = Z_to_bv 64 (F + 112)) by (rewrite (REl 25%bv ltac:(cbn; tauto)); exact R6_25).
pmkst HS.
pose proof (proj1 HJE) as HARE.
destruct (BLKF _ _ body nn body np HARE Hbody4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (BV1 & BM1 & BR1 & BH1).
destruct (BLKF _ _ res nn res np HARE Hin4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (BV2 & BM2 & BR2 & BH2).
apply (BCMP (ms_regs msE) (ms_mem msE) _ body res np 1700 _ HJE).
- rewrite REa0. exact E32.
- rewrite REa1, (EE 20%nat 20%bv eq_refl). exact R6_20.
- rewrite REa2, (EE 24%nat 24%bv eq_refl). exact R6_24.
- exact REra.
- zl.
- reflexivity.
- exact RKE.
- zl. - zl. - zl. - zl. - zl.
- exact BV1. - exact BV2. - exact BM1. - exact BM2. - exact BR1. - exact BH1. - exact BR2. - exact BH2.
- intros i Hi. rewrite !(KE _) by zl. exact (HBD i Hi).
- intros regs7 mem7 md7 HJ7 HP7 H7_10 KM7.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP7 RKE) as RK7.
pose proof RK7 as (R7_2 & R7_3 & R7_4 & R7_8 & R7_9 & R7_19 & R7_23 & R7_24).
assert (R7_18 : getr regs7 18 = Z_to_bv 64 body) by (rewrite <- RE18; exact (HP7 18 ltac:(unfold acallee_saved; zl))).
assert (R7_20 : getr regs7 20 = Z_to_bv 64 res) by (rewrite <- RE20; exact (HP7 20 ltac:(unfold acallee_saved; zl))).
assert (R7_22 : getr regs7 22 = w64 (-1)) by (rewrite <- RE22; exact (HP7 22 ltac:(unfold acallee_saved; zl))).
assert (R7_25 : getr regs7 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RE25; exact (HP7 25 ltac:(unfold acallee_saved; zl))).
assert (KM7' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) mem7 a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha Hn. rewrite (KM7 a Ha Hn). exact (KE a Ha). }
assert (KU7 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem7 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KM7' a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). exact (KUD a Ha). }
assert (SP7 : s5_spills_at W4 mem7 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem7); [intros a Ha; apply KU7; left; unfold s5_u; zl | exact SP3]. }
(* 0x82f1c bnez a0 -> abort: bcmp returned 0 *)
clear Hc. clear dependent E.
pose proof (s5_entry W4 regs7 mem7 1700 sp1 F sF body nn R7_9 R7_23 R7_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP7) as HS.
remember (Eimg (Ereg regs7 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs7 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs7 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs7 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), H7_10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run F: 0x82f20 .. jal reac_ctrl_scene_build (0x82f2c) *)
paj_run_shc RUNP RUNC HS HJ7.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msF, HJ7 into HJF, HFr into HFrF. clear HF HG.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W4) mem7 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrF); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrF.
assert (RFl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msF) r = getr regs7 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msF) regs7 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RFa0. prreg HS (11%bv : bv 5) RFa1. prreg HS (12%bv : bv 5) RFa2. prreg HS (1%bv : bv 5) RFra.
assert (RKF : s5_rk B sp0 sp1 F sF np (ms_regs msF))
by (apply (s5_rk_kept B _ _ _ _ _ regs7); [intros r Hr; apply RFl; cbn in Hr |- *; tauto | exact RK7]).
assert (EspF : spZ (ms_regs msF) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite (RFl 2%bv ltac:(cbn; tauto)), R7_2, unsigned_lit_small by zl. ring. }
assert (Es0F : s0Z (ms_regs msF) = sp0).
{ unfold s0Z. rewrite (RFl 8%bv ltac:(cbn; tauto)), R7_8. apply unsigned_lit_small. zl. }
pmkst HS.
rewrite pa_sigma_reac_ctrl_scene_build.
eapply SRr_bind.
{ eapply (cl_callS (SK := SK) B LAWS W4 (ms_regs msF) (ms_mem msF) _ (sw_stk WK) sp0 []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
REAC_CTRL_SCENE_BUILD_STK (scene_fp body np (F + 112)) 0 (sp1 - sp0) (Z_to_bv 64 (BASE + 1720)) (rt_ch cx) _ HJF).
- exact EspF.
- exact Hom.
- zl.
- unfold REAC_CTRL_SCENE_BUILD_STK. zl.
- zl.
- rewrite (RFl 3%bv ltac:(cbn; tauto)). exact R7_3.
- rewrite (RFl 4%bv ltac:(cbn; tauto)). exact R7_4.
- exact RFra.
- apply ret_ok_codeptr_v; [zl | reflexivity].
- rewrite unsigned_lit_small by zl. zl.
- replace (sp0 + (sp1 - sp0)) with sp1 by ring. rewrite Es0F. apply ACH.
intros a Ha. rewrite (KF a) by zl. apply KU7. left. unfold s5_u. zl.
- intros HPRE. eapply SRr_mono.
+ apply (SSB ly4 S4 W4 (ms_regs msF) (ms_mem msF) _ (rt_ch cx) body np (F + 112) HPRE).
* rewrite RFa0, (EE 18%nat 18%bv eq_refl). exact R7_18.
* rewrite RFa1, (EE 24%nat 24%bv eq_refl). exact R7_24.
* rewrite RFa2, (EE 25%nat 25%bv eq_refl). exact R7_25.
* zl.
* zl.
* zl.
* intros Hok. rewrite Eok in Hok. apply Z.eqb_eq in Hok. contradiction.
+ intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ).
exists ly', S', regs', mem', md'. split; [rewrite RFra; reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HQ].
- intros a HFP. unfold scene_fp in HFP. rewrite Eok, (proj2 (Z.eqb_neq np 8904) Hq) in HFP. destruct HFP as (r & [] & _). }
cbv beta. intros W8 c8 _ (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HJ8c & HP8 & HQ8).
destruct HQ8 as (-> & -> & -> & HSB). rewrite Eok, (proj2 (Z.eqb_neq np 8904) Hq) in HSB. destruct HSB as (H8_10 & KM8).
replace (ev + 1 + 0) with (ev + 1) in HJ8 by ring.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP8 RKF) as RK8.
pose proof RK8 as (R8_2 & R8_3 & R8_4 & R8_8 & R8_9 & R8_19 & R8_23 & R8_24).
assert (RF18 : getr (ms_regs msF) 18 = Z_to_bv 64 body) by (rewrite (RFl 18%bv ltac:(cbn; tauto)); exact R7_18).
assert (RF20 : getr (ms_regs msF) 20 = Z_to_bv 64 res) by (rewrite (RFl 20%bv ltac:(cbn; tauto)); exact R7_20).
assert (RF22 : getr (ms_regs msF) 22 = w64 (-1)) by (rewrite (RFl 22%bv ltac:(cbn; tauto)); exact R7_22).
assert (RF25 : getr (ms_regs msF) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RFl 25%bv ltac:(cbn; tauto)); exact R7_25).
assert (R8_18 : getr regs8 18 = Z_to_bv 64 body) by (rewrite <- RF18; exact (HP8 18 ltac:(unfold acallee_saved; zl))).
assert (R8_20 : getr regs8 20 = Z_to_bv 64 res) by (rewrite <- RF20; exact (HP8 20 ltac:(unfold acallee_saved; zl))).
assert (R8_22 : getr regs8 22 = w64 (-1)) by (rewrite <- RF22; exact (HP8 22 ltac:(unfold acallee_saved; zl))).
assert (R8_25 : getr regs8 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RF25; exact (HP8 25 ltac:(unfold acallee_saved; zl))).
assert (KM8' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) mem8 a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha Hn. rewrite (KM8 a Ha) by (rewrite EspF; zl). rewrite (KF a Ha). exact (KM7' a Ha Hn). }
assert (KU8 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem8 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KM8' a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). exact (KUD a Ha). }
assert (SP8 : s5_spills_at W4 mem8 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem8); [intros a Ha; apply KU8; left; unfold s5_u; zl | exact SP3]. }
(* 0x82f30 bne a0,s6 -> abort: scene_build returned -1 = set_mac's r *)
clear dependent E.
pose proof (s5_entry W4 regs8 mem8 1720 sp1 F sF body nn R8_9 R8_23 R8_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP8) as HS.
remember (Eimg (Ereg regs8 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs8 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs8 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs8 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), (EE 22%nat 22%bv eq_refl), H8_10, R8_22 in Hc.
vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run G: 0x82f34 .. jal bcmp (0x82f40) *)
paj_run_shc RUNP RUNC HS HJ8.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msG, HJ8 into HJG, HFr into HFrG. clear HF HG.
assert (KG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msG) a = aview SEGS (w_H W4) mem8 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrG); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrG.
assert (RGl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msG) r = getr regs8 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msG) regs8 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RGa0. prreg HS (11%bv : bv 5) RGa1. prreg HS (12%bv : bv 5) RGa2. prreg HS (1%bv : bv 5) RGra.
assert (RKG : s5_rk B sp0 sp1 F sF np (ms_regs msG))
by (apply (s5_rk_kept B _ _ _ _ _ regs8); [intros r Hr; apply RGl; cbn in Hr |- *; tauto | exact RK8]).
pmkst HS.
pose proof (proj1 HJG) as HARG.
destruct (BLKF _ _ body nn body np HARG Hbody4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (GV1 & GM1 & GR1 & GH1).
destruct (BLKF _ _ res nn res np HARG Hin4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (GV2 & GM2 & GR2 & GH2).
apply (BCMP (ms_regs msG) (ms_mem msG) _ body res np 1740 _ HJG).
+ rewrite RGa0, (EE 18%nat 18%bv eq_refl). exact R8_18.
+ rewrite RGa1, (EE 20%nat 20%bv eq_refl). exact R8_20.
+ rewrite RGa2, (EE 24%nat 24%bv eq_refl). exact R8_24.
+ exact RGra.
+ zl.
+ reflexivity.
+ exact RKG.
+ zl. + zl. + zl. + zl. + zl.
+ exact GV1. + exact GV2. + exact GM1. + exact GM2. + exact GR1. + exact GH1. + exact GR2. + exact GH2.
+ intros i Hi. rewrite !(KG _) by zl. rewrite !KM8' by zl. exact (HBD i Hi).
+ intros regs9 mem9 md9 HJ9 HP9 H9_10 KM9.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP9 RKG) as RK9.
pose proof RK9 as (R9_2 & R9_3 & R9_4 & R9_8 & R9_9 & R9_19 & R9_23 & R9_24).
assert (RG18 : getr (ms_regs msG) 18 = Z_to_bv 64 body) by (rewrite (RGl 18%bv ltac:(cbn; tauto)); exact R8_18).
assert (RG20 : getr (ms_regs msG) 20 = Z_to_bv 64 res) by (rewrite (RGl 20%bv ltac:(cbn; tauto)); exact R8_20).
assert (R9_18 : getr regs9 18 = Z_to_bv 64 body) by (rewrite <- RG18; exact (HP9 18 ltac:(unfold acallee_saved; zl))).
assert (R9_20 : getr regs9 20 = Z_to_bv 64 res) by (rewrite <- RG20; exact (HP9 20 ltac:(unfold acallee_saved; zl))).
assert (KU9 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem9 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KM9 a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). rewrite (KG a (RNG a Ha)). exact (KU8 a Ha). }
assert (SP9 : s5_spills_at W4 mem9 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem9); [intros a Ha; apply KU9; left; unfold s5_u; zl | exact SP3]. }
(* 0x82f44 bnez a0 -> abort: bcmp returned 0; then j 0x82f48 -> C6 0x83020 *)
clear dependent E.
pose proof (s5_entry W4 regs9 mem9 1740 sp1 F sF body nn R9_9 R9_23 R9_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP9) as HS.
remember (Eimg (Ereg regs9 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs9 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs9 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs9 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), H9_10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_to_shc RUNTOP HS HJ9 1960.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msH, HJ9 into HJH, HFr into HFrH. clear HF HG.
assert (KH : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msH) a = aview SEGS (w_H W4) mem9 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrH); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrH.
assert (RHl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msH) r = getr regs9 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msH) regs9 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
pmkst HS.
apply EXIT.
* exact HJH.
* intros a Ha. pose proof (s5_prot_u sp0 sp1 F sF a ltac:(zl) ltac:(zl) Ha) as Hu.
rewrite (KH a (RNG a (or_introl Hu))). exact (KU9 a (or_introl Hu)).
* intros a Ha. rewrite (KH a (RNG a (or_intror Ha))). exact (KU9 a (or_intror Ha)).
* apply (s5_rk_kept B _ _ _ _ _ regs9); [intros r Hr; apply RHl; cbn in Hr |- *; tauto | exact RK9].
* rewrite (RHl 18%bv ltac:(cbn; tauto)). exact R9_18.
* rewrite (RHl 20%bv ltac:(cbn; tauto)). exact R9_20. }
(* ======== the r = 0 arm (n' = 8904): 0x82f4c .. 0x8301c -> C6 ======== *)
assert (Hq : np = 8904).
{ destruct (Z.eqb_spec np 8904) as [X|X]; [exact X|]. exfalso. cbn [sv_denot] in Hc.
rewrite (EE 10%nat 10%bv eq_refl), HD10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
pose proof (Hnn89 Hq) as Hn8.
rewrite (proj2 (Z.eqb_eq np 8904) Hq) in HD10, HDmem, RD22.
destruct HDmem as (HDmac & HDk). unfold MAC_LEN, MAC_OFF in HDmac, HDk.
assert (KMD : forall a, 0 <= a < 2 ^ 64 -> ~ (body + 832 <= a < body + 838) -> ~ (sp1 - 8192 <= a < sp1) ->
aview SEGS (w_H W4) (ms_mem msD) a = aview SEGS (w_H W4) mem5 a).
{ intros a Ha H1 H2. rewrite (KD a Ha), (KD1 a Ha), <- (KC a Ha).
apply HDk; [exact Ha | zl | rewrite EspC; unfold SET_MAC_STK, SET_MAC_FRAME; zl]. }
assert (KUD : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) (ms_mem msD) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KD a (RNG a Ha)), (KD1 a (RNG a Ha)). exact (KU6 a Ha). }
assert (BD2 : forall i, 0 <= i < 6 -> aview SEGS (w_H W4) (ms_mem msD) (body + 832 + i) = aview SEGS (w_H W4) mem5 (F + 112 + i)).
{ intros i Hi. rewrite (KD _) by zl. rewrite (KD1 _) by zl. rewrite (HDmac i Hi). apply KC. zl. }
assert (MAC5 : forall i, 0 <= i < 6 -> aview SEGS (w_H W4) (ms_mem msD) (F + 112 + i) = aview SEGS (w_H W4) mem5 (F + 112 + i)).
{ intros i Hi. rewrite (KUD _) by (left; unfold s5_u; zl). symmetry. apply K5. left. unfold s5_u. zl. }
(* run I: 0x82f4c ld s2,0x58(s1) .. jal bcmp (0x82f5c): bcmp(body + 0x340, mac, 6) *)
paj_run_shc RUNP RUNC HS HJD.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msI, HJD into HJI, HFr into HFrI. clear HF HG.
assert (KI : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msI) a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrI); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrI.
assert (RIl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv -> getr (ms_regs msI) r = getr regs6 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msI) regs6 (s5_extra body nn)
[2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RIa0. prreg HS (11%bv : bv 5) RIa1. prreg HS (12%bv : bv 5) RIa2.
prreg HS (1%bv : bv 5) RIra. prreg HS (18%bv : bv 5) RIs2. prreg HS (22%bv : bv 5) RIs6.
assert (RKI : s5_rk B sp0 sp1 F sF np (ms_regs msI))
by (apply (s5_rk_kept B _ _ _ _ _ regs6); [intros r Hr; apply RIl; cbn in Hr |- *; tauto | exact RK6]).
assert (RI18 : getr (ms_regs msI) 18 = Z_to_bv 64 body) by (rewrite RIs2; exact E32).
assert (RI20 : getr (ms_regs msI) 20 = Z_to_bv 64 res) by (rewrite (RIl 20%bv ltac:(cbn; tauto)); exact R6_20).
assert (RI22 : getr (ms_regs msI) 22 = w64 0) by (rewrite RIs6, (EE 10%nat 10%bv eq_refl); exact HD10).
assert (RI25 : getr (ms_regs msI) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RIl 25%bv ltac:(cbn; tauto)); exact R6_25).
pmkst HS.
pose proof (proj1 HJI) as HARI.
destruct (BLKF _ _ body nn (body + 832) 6 HARI Hbody4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (IV1 & IM1 & IR1 & IH1).
destruct (FRMF _ _ (F + 112) 6 HARI ltac:(zl) ltac:(zl) ltac:(zl)) as (IV2 & IM2 & IH2).
apply (BCMP (ms_regs msI) (ms_mem msI) _ (body + 832) (F + 112) 6 1768 _ HJI).
{ rewrite RIa0, E32, unsigned_lit_small by zl. reflexivity. }
{ rewrite RIa1, (EE 25%nat 25%bv eq_refl). exact R6_25. }
{ rewrite RIa2. reflexivity. }
{ exact RIra. }
{ zl. }
{ reflexivity. }
{ exact RKI. }
{ zl. } { zl. } { zl. } { zl. } { zl. }
{ exact IV1. } { exact IV2. } { exact IM1. } { exact IM2. } { exact IR1. } { exact IH1. }
{ apply (block_shadow_range _ _ (F + 112) 6 (F + 112) 6); [| zl | zl]. apply BSM.
intros a Ha. rewrite (KI a) by (apply (RNG a); left; exact Ha). apply KUD. left. exact Ha. }
{ intros _. exact IH2. }
{ intros i Hi. rewrite !(KI _) by zl. rewrite (BD2 i Hi). symmetry. exact (MAC5 i Hi). }
intros regs10 mem10 md10 HJ10 HP10 H10_10 KM10.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP10 RKI) as RK10.
pose proof RK10 as (R10_2 & R10_3 & R10_4 & R10_8 & R10_9 & R10_19 & R10_23 & R10_24).
assert (R10_18 : getr regs10 18 = Z_to_bv 64 body) by (rewrite <- RI18; exact (HP10 18 ltac:(unfold acallee_saved; zl))).
assert (R10_20 : getr regs10 20 = Z_to_bv 64 res) by (rewrite <- RI20; exact (HP10 20 ltac:(unfold acallee_saved; zl))).
assert (R10_22 : getr regs10 22 = w64 0) by (rewrite <- RI22; exact (HP10 22 ltac:(unfold acallee_saved; zl))).
assert (R10_25 : getr regs10 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RI25; exact (HP10 25 ltac:(unfold acallee_saved; zl))).
assert (KM10' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) mem10 a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha Hn. rewrite (KM10 a Ha Hn). exact (KI a Ha). }
assert (KU10 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem10 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KM10' a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). exact (KUD a Ha). }
assert (SP10 : s5_spills_at W4 mem10 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem10); [intros a Ha; apply KU10; left; unfold s5_u; zl | exact SP3]. }
(* 0x82f60 bnez a0 -> abort: bcmp(body + 832, mac, 6) = 0 (set_mac's ok post) *)
clear dependent E.
pose proof (s5_entry W4 regs10 mem10 1768 sp1 F sF body nn R10_9 R10_23 R10_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP10) as HS.
remember (Eimg (Ereg regs10 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs10 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs10 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs10 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), H10_10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run J: 0x82f64 .. jal bcmp (0x82f70): bcmp(body, before, 0x340) *)
paj_run_shc RUNP RUNC HS HJ10.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msJ, HJ10 into HJJ, HFr into HFrJ. clear HF HG.
assert (KJ : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msJ) a = aview SEGS (w_H W4) mem10 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrJ); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrJ.
assert (RJl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msJ) r = getr regs10 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msJ) regs10 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RJa0. prreg HS (11%bv : bv 5) RJa1. prreg HS (12%bv : bv 5) RJa2. prreg HS (1%bv : bv 5) RJra.
assert (RKJ : s5_rk B sp0 sp1 F sF np (ms_regs msJ))
by (apply (s5_rk_kept B _ _ _ _ _ regs10); [intros r Hr; apply RJl; cbn in Hr |- *; tauto | exact RK10]).
assert (RJ18 : getr (ms_regs msJ) 18 = Z_to_bv 64 body) by (rewrite (RJl 18%bv ltac:(cbn; tauto)); exact R10_18).
assert (RJ20 : getr (ms_regs msJ) 20 = Z_to_bv 64 res) by (rewrite (RJl 20%bv ltac:(cbn; tauto)); exact R10_20).
assert (RJ22 : getr (ms_regs msJ) 22 = w64 0) by (rewrite (RJl 22%bv ltac:(cbn; tauto)); exact R10_22).
assert (RJ25 : getr (ms_regs msJ) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RJl 25%bv ltac:(cbn; tauto)); exact R10_25).
pmkst HS.
pose proof (proj1 HJJ) as HARJ.
destruct (BLKF _ _ body nn body 832 HARJ Hbody4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (JV1 & JM1 & JR1 & JH1).
destruct (BLKF _ _ res nn res 832 HARJ Hin4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (JV2 & JM2 & JR2 & JH2).
apply (BCMP (ms_regs msJ) (ms_mem msJ) _ body res 832 1788 _ HJJ).
{ rewrite RJa0, (EE 18%nat 18%bv eq_refl). exact R10_18. }
{ rewrite RJa1, (EE 20%nat 20%bv eq_refl). exact R10_20. }
{ rewrite RJa2. reflexivity. }
{ exact RJra. }
{ zl. }
{ reflexivity. }
{ exact RKJ. }
{ zl. } { zl. } { zl. } { zl. } { zl. }
{ exact JV1. } { exact JV2. } { exact JM1. } { exact JM2. } { exact JR1. } { exact JH1. } { exact JR2. } { exact JH2. }
{ intros i Hi. rewrite !(KJ _) by zl. rewrite !KM10' by zl.
rewrite (KMD (body + i)) by zl. rewrite (KMD (res + i)) by (generalize HdisjBR; zl).
symmetry. apply HB5. zl. }
intros regs11 mem11 md11 HJ11 HP11 H11_10 KM11.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP11 RKJ) as RK11.
pose proof RK11 as (R11_2 & R11_3 & R11_4 & R11_8 & R11_9 & R11_19 & R11_23 & R11_24).
assert (R11_18 : getr regs11 18 = Z_to_bv 64 body) by (rewrite <- RJ18; exact (HP11 18 ltac:(unfold acallee_saved; zl))).
assert (R11_20 : getr regs11 20 = Z_to_bv 64 res) by (rewrite <- RJ20; exact (HP11 20 ltac:(unfold acallee_saved; zl))).
assert (R11_22 : getr regs11 22 = w64 0) by (rewrite <- RJ22; exact (HP11 22 ltac:(unfold acallee_saved; zl))).
assert (R11_25 : getr regs11 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RJ25; exact (HP11 25 ltac:(unfold acallee_saved; zl))).
assert (KM11' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) mem11 a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha Hn. rewrite (KM11 a Ha Hn). rewrite (KJ a Ha). exact (KM10' a Ha Hn). }
assert (KU11 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem11 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KM11' a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). exact (KUD a Ha). }
assert (SP11 : s5_spills_at W4 mem11 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem11); [intros a Ha; apply KU11; left; unfold s5_u; zl | exact SP3]. }
(* 0x82f74 bnez a0 -> abort: bcmp(body, before, 832) = 0 *)
clear dependent E.
pose proof (s5_entry W4 regs11 mem11 1788 sp1 F sF body nn R11_9 R11_23 R11_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP11) as HS.
remember (Eimg (Ereg regs11 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs11 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs11 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs11 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), H11_10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run K: 0x82f78 .. jal bcmp (0x82f84): bcmp(body + 0x346, before + 0x346, n' - 0x346) *)
paj_run_shc RUNP RUNC HS HJ11.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msK, HJ11 into HJK, HFr into HFrK. clear HF HG.
assert (KK : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msK) a = aview SEGS (w_H W4) mem11 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrK); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrK.
assert (RKl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msK) r = getr regs11 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msK) regs11 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RKa0. prreg HS (11%bv : bv 5) RKa1. prreg HS (12%bv : bv 5) RKa2. prreg HS (1%bv : bv 5) RKra.
assert (RKK : s5_rk B sp0 sp1 F sF np (ms_regs msK))
by (apply (s5_rk_kept B _ _ _ _ _ regs11); [intros r Hr; apply RKl; cbn in Hr |- *; tauto | exact RK11]).
assert (RK18 : getr (ms_regs msK) 18 = Z_to_bv 64 body) by (rewrite (RKl 18%bv ltac:(cbn; tauto)); exact R11_18).
assert (RK20 : getr (ms_regs msK) 20 = Z_to_bv 64 res) by (rewrite (RKl 20%bv ltac:(cbn; tauto)); exact R11_20).
assert (RK22 : getr (ms_regs msK) 22 = w64 0) by (rewrite (RKl 22%bv ltac:(cbn; tauto)); exact R11_22).
assert (RK25 : getr (ms_regs msK) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RKl 25%bv ltac:(cbn; tauto)); exact R11_25).
pmkst HS.
pose proof (proj1 HJK) as HARK.
destruct (BLKF _ _ body nn (body + 838) 8066 HARK Hbody4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (KV1 & KM1 & KR1 & KH1).
destruct (BLKF _ _ res nn (res + 838) 8066 HARK Hin4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (KV2 & KM2 & KR2 & KH2).
apply (BCMP (ms_regs msK) (ms_mem msK) _ (body + 838) (res + 838) 8066 1808 _ HJK).
{ rewrite RKa0, (EE 18%nat 18%bv eq_refl), R11_18, unsigned_lit_small by zl. reflexivity. }
{ rewrite RKa1, (EE 20%nat 20%bv eq_refl), R11_20, unsigned_lit_small by zl. reflexivity. }
{ rewrite RKa2, (EE 24%nat 24%bv eq_refl), R11_24, unsigned_lit_small by zl. rewrite Hq. reflexivity. }
{ exact RKra. }
{ zl. }
{ reflexivity. }
{ exact RKK. }
{ zl. } { zl. } { zl. } { zl. } { zl. }
{ exact KV1. } { exact KV2. } { exact KM1. } { exact KM2. } { exact KR1. } { exact KH1. } { exact KR2. } { exact KH2. }
{ intros i Hi. rewrite !(KK _) by zl. rewrite !KM11' by zl.
rewrite (KMD (body + 838 + i)) by zl. rewrite (KMD (res + 838 + i)) by (generalize HdisjBR; zl).
replace (body + 838 + i) with (body + (838 + i)) by ring. replace (res + 838 + i) with (res + (838 + i)) by ring.
symmetry. apply HB5. zl. }
intros regs12 mem12 md12 HJ12 HP12 H12_10 KM12.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP12 RKK) as RK12.
pose proof RK12 as (R12_2 & R12_3 & R12_4 & R12_8 & R12_9 & R12_19 & R12_23 & R12_24).
assert (R12_18 : getr regs12 18 = Z_to_bv 64 body) by (rewrite <- RK18; exact (HP12 18 ltac:(unfold acallee_saved; zl))).
assert (R12_20 : getr regs12 20 = Z_to_bv 64 res) by (rewrite <- RK20; exact (HP12 20 ltac:(unfold acallee_saved; zl))).
assert (R12_22 : getr regs12 22 = w64 0) by (rewrite <- RK22; exact (HP12 22 ltac:(unfold acallee_saved; zl))).
assert (R12_25 : getr regs12 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RK25; exact (HP12 25 ltac:(unfold acallee_saved; zl))).
assert (KM12' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) mem12 a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha Hn. rewrite (KM12 a Ha Hn). rewrite (KK a Ha). exact (KM11' a Ha Hn). }
assert (KU12 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem12 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KM12' a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). exact (KUD a Ha). }
assert (SP12 : s5_spills_at W4 mem12 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem12); [intros a Ha; apply KU12; left; unfold s5_u; zl | exact SP3]. }
(* 0x82f88 bnez a0 -> abort: bcmp(body + 838, before + 838, 8066) = 0 *)
clear dependent E.
pose proof (s5_entry W4 regs12 mem12 1808 sp1 F sF body nn R12_9 R12_23 R12_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP12) as HS.
remember (Eimg (Ereg regs12 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs12 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs12 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs12 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), H12_10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run L: 0x82f8c .. jal reac_ctrl_scene_build (0x82f98) *)
paj_run_shc RUNP RUNC HS HJ12.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msL, HJ12 into HJL, HFr into HFrL. clear HF HG.
assert (KL : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msL) a = aview SEGS (w_H W4) mem12 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrL); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrL.
assert (RLl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msL) r = getr regs12 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msL) regs12 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RLa0. prreg HS (11%bv : bv 5) RLa1. prreg HS (12%bv : bv 5) RLa2. prreg HS (1%bv : bv 5) RLra.
assert (RKL : s5_rk B sp0 sp1 F sF np (ms_regs msL))
by (apply (s5_rk_kept B _ _ _ _ _ regs12); [intros r Hr; apply RLl; cbn in Hr |- *; tauto | exact RK12]).
assert (RL18 : getr (ms_regs msL) 18 = Z_to_bv 64 body) by (rewrite (RLl 18%bv ltac:(cbn; tauto)); exact R12_18).
assert (RL20 : getr (ms_regs msL) 20 = Z_to_bv 64 res) by (rewrite (RLl 20%bv ltac:(cbn; tauto)); exact R12_20).
assert (RL22 : getr (ms_regs msL) 22 = w64 0) by (rewrite (RLl 22%bv ltac:(cbn; tauto)); exact R12_22).
assert (RL25 : getr (ms_regs msL) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RLl 25%bv ltac:(cbn; tauto)); exact R12_25).
assert (EspL : spZ (ms_regs msL) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite (RLl 2%bv ltac:(cbn; tauto)), R12_2, unsigned_lit_small by zl. ring. }
assert (Es0L : s0Z (ms_regs msL) = sp0).
{ unfold s0Z. rewrite (RLl 8%bv ltac:(cbn; tauto)), R12_8. apply unsigned_lit_small. zl. }
assert (KLD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 8192 <= a < sp1) -> aview SEGS (w_H W4) (ms_mem msL) a = aview SEGS (w_H W4) (ms_mem msD) a).
{ intros a Ha Hn. rewrite (KL a Ha). exact (KM12' a Ha Hn). }
pmkst HS.
rewrite pa_sigma_reac_ctrl_scene_build.
eapply SRr_bind.
{ eapply (cl_callS (SK := SK) B LAWS W4 (ms_regs msL) (ms_mem msL) _ (sw_stk WK) sp0 []
(c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
REAC_CTRL_SCENE_BUILD_STK (scene_fp body np (F + 112)) 0 (sp1 - sp0) (Z_to_bv 64 (BASE + 1828)) (rt_ch cx) _ HJL).
- exact EspL.
- exact Hom.
- zl.
- unfold REAC_CTRL_SCENE_BUILD_STK. zl.
- zl.
- rewrite (RLl 3%bv ltac:(cbn; tauto)). exact R12_3.
- rewrite (RLl 4%bv ltac:(cbn; tauto)). exact R12_4.
- exact RLra.
- apply ret_ok_codeptr_v; [zl | reflexivity].
- rewrite unsigned_lit_small by zl. zl.
- replace (sp0 + (sp1 - sp0)) with sp1 by ring. rewrite Es0L. apply ACH.
intros a Ha. rewrite (KL a) by zl. apply KU12. left. unfold s5_u. zl.
- intros HPRE. eapply SRr_mono.
+ apply (SSB ly4 S4 W4 (ms_regs msL) (ms_mem msL) _ (rt_ch cx) body np (F + 112) HPRE).
* rewrite RLa0, (EE 18%nat 18%bv eq_refl). exact R12_18.
* rewrite RLa1, (EE 24%nat 24%bv eq_refl). exact R12_24.
* rewrite RLa2, (EE 25%nat 25%bv eq_refl). exact R12_25.
* zl.
* zl.
* zl.
* intros _. split; [assert (X : In (body, 8904) (ablocks B ly4 S4)) by (rewrite <- Hn8; exact Hbody4); exact X|]. unfold SCENE_MAC_LEN.
apply (afobj_of_own SK SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)]
ly4 S4 W4 (ms_mem msL) _ (ev + 1) 8 (c_fpos cx) (F + 112) 6 HJL).
-- left. reflexivity.
-- zl.
-- rewrite EF4. zl.
-- rewrite EF4. change (fs_frame_bytes 8) with 16384. zl.
-- replace (F + 112) with ((F / 8 + 14) * 8) by zl. apply Z_mod_mult.
-- apply (block_shadow_range (aview SEGS (w_H W4) (ms_mem msL)) SHADOW_OFF (F + 112) 6 (F + 112) 6); [| zl | zl].
apply BSM. intros a Ha. rewrite (KL a) by (apply (RNG a); left; exact Ha). apply KU12. left. exact Ha.
+ intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ).
exists ly', S', regs', mem', md'. split; [rewrite RLra; reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HQ].
- intros a HFP. unfold scene_fp in HFP. rewrite Eok, (proj2 (Z.eqb_eq np 8904) Hq) in HFP.
destruct HFP as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold P_reac_ctrl_scene_build.SCENE_BYTES in Hr.
right. exists body, nn. split; [exact Hbody4|]. split; [exact HbodyF | rewrite Ereq; zl]. }
cbv beta. intros W13 c13 _ (ly13 & S13 & regs13 & mem13 & md13 & -> & HJ13 & HJ13c & HP13 & HQ13).
destruct HQ13 as (-> & -> & -> & HSB). rewrite Eok, (proj2 (Z.eqb_eq np 8904) Hq) in HSB. destruct HSB as (H13_10 & HBODY13).
replace (ev + 1 + 0) with (ev + 1) in HJ13 by ring.
pose proof HJ13c as (_ & _ & _ & _ & _ & _ & _ & _ & J13up & _ & _ & J13fr & _).
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP13 RKL) as RK13.
pose proof RK13 as (R13_2 & R13_3 & R13_4 & R13_8 & R13_9 & R13_19 & R13_23 & R13_24).
assert (R13_18 : getr regs13 18 = Z_to_bv 64 body) by (rewrite <- RL18; exact (HP13 18 ltac:(unfold acallee_saved; zl))).
assert (R13_20 : getr regs13 20 = Z_to_bv 64 res) by (rewrite <- RL20; exact (HP13 20 ltac:(unfold acallee_saved; zl))).
assert (R13_22 : getr regs13 22 = w64 0) by (rewrite <- RL22; exact (HP13 22 ltac:(unfold acallee_saved; zl))).
assert (R13_25 : getr regs13 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RL25; exact (HP13 25 ltac:(unfold acallee_saved; zl))).
assert (KX13 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem13 a = aview SEGS (w_H W4) (ms_mem msL) a).
{ intros a Ha. pose proof (RNG a Ha) as Hr.
destruct (Z_le_gt_dec sp1 a) as [Hup | Hlow].
- apply J13up; [zl | unfold REAC_CTRL_SCENE_BUILD_STK; rewrite Hes; zl].
- assert (Hfs : F <= a < F + 16384 \/ sF <= a < sF + 2048) by (generalize Ha; unfold s5_u, s5_row; zl).
apply (J13fr 8 (c_fpos cx) a Hfin5).
+ unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF4. change (fs_frame_bytes 8) with 16384. change (16384 / 8) with 2048.
fold sF. exact Hfs.
+ intros HFP. unfold scene_fp in HFP. rewrite Eok, (proj2 (Z.eqb_eq np 8904) Hq) in HFP.
destruct HFP as (r & [<- | []] & Hr0). cbn [fst snd] in Hr0. apply (BU a Ha). unfold P_reac_ctrl_scene_build.SCENE_BYTES in Hr0. zl. }
assert (KU13 : forall a, s5_u sp1 F sF a \/ s5_row sF a -> aview SEGS (w_H W4) mem13 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KX13 a Ha), (KLD a (RNG a Ha)) by (apply (SU a); [zl | zl | exact Ha]). exact (KUD a Ha). }
assert (SP13 : s5_spills_at W4 mem13 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem13); [intros a Ha; apply KU13; left; unfold s5_u; zl | exact SP3]. }
assert (BODY13 : forall i, 0 <= i < 8904 -> ~ (832 <= i < 838) -> aview SEGS (w_H W4) mem13 (body + i) = Some (scene_tag i)).
{ intros i Hi Hm. rewrite (HBODY13 i) by (unfold P_reac_ctrl_scene_build.SCENE_BYTES; zl).
unfold SCENE_MAC_OFF, SCENE_MAC_LEN. destruct (Z.leb_spec 832 i); destruct (Z.ltb_spec i (832 + 6)); cbn [andb];
first [reflexivity | exfalso; zl]. }
assert (BMAC13 : forall j, 0 <= j < 6 -> aview SEGS (w_H W4) mem13 (body + (832 + j)) = aview SEGS (w_H W4) mem5 (F + 112 + j)).
{ intros j Hj. rewrite (HBODY13 (832 + j)) by (unfold P_reac_ctrl_scene_build.SCENE_BYTES; zl).
unfold SCENE_MAC_OFF, SCENE_MAC_LEN. replace ((832 <=? 832 + j) && (832 + j <? 832 + 6)) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; zl).
replace (F + 112 + (832 + j - 832)) with (F + 112 + j) by ring. rewrite (KLD _) by zl. exact (MAC5 j Hj). }
assert (HFz : F + 16384 <= 2147450880 \/ 17594333495296 <= F)
by (generalize HFapp; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; zl).
assert (ZRA : forall mem, (forall i, 0 <= i < 1113 -> aview SEGS (w_H W4) mem (sF + 28 + i) = Some 0) ->
range_addressable (aview SEGS (w_H W4) mem) SHADOW_OFF (F + 224) 8904).
{ intros mem Hz. apply zero_shadow_range; [replace (F + 224) with ((F / 8 + 28) * 8) by zl; apply Z_mod_mult | reflexivity |].
intros i Hi. change (8904 / 8) with 1113 in Hi. unfold shadow_of_addr. replace (F + 224) with (F + 8 * 28) by ring.
rewrite HF8 by zl. replace (SHADOW_OFF + (F / 8 + 28) + i) with (sF + 28 + i) by (rewrite EsF; unfold SHADOW_OFF; ring).
exact (Hz i Hi). }
(* 0x82f9c bne a0,s6 -> abort: scene_build returned 0 = set_mac's r *)
clear dependent E.
pose proof (s5_entry W4 regs13 mem13 1828 sp1 F sF body nn R13_9 R13_23 R13_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP13) as HS.
remember (Eimg (Ereg regs13 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs13 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs13 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs13 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), (EE 22%nat 22%bv eq_refl), H13_10, R13_22 in Hc.
vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run M: 0x82fa0 .. jal __asan_set_shadow_00 (0x82fac): the `expect` row shF + [0x1c, 0x475) *)
paj_run_shc RUNP RUNC HS HJ13.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msM, HJ13 into HJM, HFr into HFrM. clear HF HG.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msM) a = aview SEGS (w_H W4) mem13 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrM); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrM.
assert (RMl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25]%bv -> getr (ms_regs msM) r = getr regs13 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msM) regs13 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RMa0. prreg HS (11%bv : bv 5) RMa1. prreg HS (1%bv : bv 5) RMra. prreg HS (21%bv : bv 5) RMs5.
assert (RKM : s5_rk B sp0 sp1 F sF np (ms_regs msM))
by (apply (s5_rk_kept B _ _ _ _ _ regs13); [intros r Hr; apply RMl; cbn in Hr |- *; tauto | exact RK13]).
assert (USF : bv_unsigned (ew E 19) = sF) by (rewrite (EE 19%nat 19%bv eq_refl), R13_19; apply unsigned_lit_small; zl).
assert (RM21 : getr (ms_regs msM) 21 = Z_to_bv 64 (sF + 28)) by (rewrite RMs5, USF; reflexivity).
assert (RM18 : getr (ms_regs msM) 18 = Z_to_bv 64 body) by (rewrite (RMl 18%bv ltac:(cbn; tauto)); exact R13_18).
assert (RM20 : getr (ms_regs msM) 20 = Z_to_bv 64 res) by (rewrite (RMl 20%bv ltac:(cbn; tauto)); exact R13_20).
assert (RM25 : getr (ms_regs msM) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RMl 25%bv ltac:(cbn; tauto)); exact R13_25).
pose proof RKM as (M2 & M3 & M4 & _).
assert (EspM : spZ (ms_regs msM) = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite M2, unsigned_lit_small by zl; ring).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_set_shadow_at (SK := SK) SEGS B LAWS pa_segs_low (SIGMA SS___asan_set_shadow_00) 0 ASH00 W4 (ms_regs msM) (ms_mem msM)
(sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1) 8 (c_fpos cx) (sF + 28) 1113
(sp1 - sp0) (Z_to_bv 64 (BASE + 1848)) HJM).
- left. reflexivity.
- rewrite RMa0, USF. reflexivity.
- rewrite RMa1. reflexivity.
- zl.
- rewrite EF4. fold sF. zl.
- rewrite EF4. fold sF. change (fs_frame_bytes 8 / 8) with 2048. zl.
- exact EspM.
- exact Hom.
- zl.
- zl.
- exact M3.
- exact M4.
- exact RMra.
- apply ret_ok_codeptr_v; [zl | reflexivity]. }
cbv beta. intros W14 c14 _ (-> & regs14 & mem14 & md14 & -> & HJ14 & HP14 & HSH14 & KSH14 & _).
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP14 RKM) as RK14.
pose proof RK14 as (R14_2 & R14_3 & R14_4 & R14_8 & R14_9 & R14_19 & R14_23 & R14_24).
assert (R14_18 : getr regs14 18 = Z_to_bv 64 body) by (rewrite <- RM18; exact (HP14 18 ltac:(unfold acallee_saved; zl))).
assert (R14_20 : getr regs14 20 = Z_to_bv 64 res) by (rewrite <- RM20; exact (HP14 20 ltac:(unfold acallee_saved; zl))).
assert (R14_21 : getr regs14 21 = Z_to_bv 64 (sF + 28)) by (rewrite <- RM21; exact (HP14 21 ltac:(unfold acallee_saved; zl))).
assert (R14_25 : getr regs14 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RM25; exact (HP14 25 ltac:(unfold acallee_saved; zl))).
assert (SP14 : s5_spills_at W4 mem14 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem14); [intros a Ha | exact SP3].
rewrite (KSH14 a) by zl. rewrite (KM a) by zl. apply KU13. left. unfold s5_u. zl. }
(* run N: 0x82fb0 ld s6,0x18(s1) .. jal __asan_memset (0x82fc4) *)
clear dependent E.
pose proof (s5_entry W4 regs14 mem14 1848 sp1 F sF body nn R14_9 R14_23 R14_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP14) as HS.
remember (Eimg (Ereg regs14 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs14 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs14 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs14 _ 0)).
paj_run_shc RUNP RUNC HS HJ14.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msN, HJ14 into HJN, HFr into HFrN. clear HF HG.
assert (KN : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msN) a = aview SEGS (w_H W4) mem14 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrN); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrN.
assert (RNl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv -> getr (ms_regs msN) r = getr regs14 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msN) regs14 (s5_extra body nn)
[2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RNa0. prreg HS (11%bv : bv 5) RNa1. prreg HS (12%bv : bv 5) RNa2. prreg HS (1%bv : bv 5) RNra.
prreg HS (18%bv : bv 5) RNs2. prreg HS (22%bv : bv 5) RNs6.
assert (UF : bv_unsigned (ew E 23) = F) by (rewrite (EE 23%nat 23%bv eq_refl), R14_23; apply unsigned_lit_small; zl).
assert (RKN : s5_rk B sp0 sp1 F sF np (ms_regs msN))
by (apply (s5_rk_kept B _ _ _ _ _ regs14); [intros r Hr; apply RNl; cbn in Hr |- *; tauto | exact RK14]).
assert (RN22 : getr (ms_regs msN) 22 = Z_to_bv 64 (F + 224)) by (rewrite RNs6, UF; reflexivity).
assert (RN20 : getr (ms_regs msN) 20 = Z_to_bv 64 res) by (rewrite (RNl 20%bv ltac:(cbn; tauto)); exact R14_20).
assert (RN21 : getr (ms_regs msN) 21 = Z_to_bv 64 (sF + 28)) by (rewrite (RNl 21%bv ltac:(cbn; tauto)); exact R14_21).
assert (RN25 : getr (ms_regs msN) 25 = Z_to_bv 64 (F + 112)) by (rewrite (RNl 25%bv ltac:(cbn; tauto)); exact R14_25).
pose proof RKN as (N2 & N3 & N4 & _).
assert (EspN : spZ (ms_regs msN) = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite N2, unsigned_lit_small by zl; ring).
assert (ZN : forall i, 0 <= i < 1113 -> aview SEGS (w_H W4) (ms_mem msN) (sF + 28 + i) = Some 0).
{ intros i Hi. rewrite (KN _) by zl. exact (HSH14 i Hi). }
assert (NOROW : forall a, s5_u sp1 F sF a -> ~ (sF + 28 <= a < sF + 28 + 1113))
by (intros a Ha; generalize Ha HFz; unfold s5_u; zl).
assert (KU14 : forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) mem14 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KSH14 a (RNG a (or_introl Ha)) (NOROW a Ha)). rewrite (KM a (RNG a (or_introl Ha))). exact (KU13 a (or_introl Ha)). }
pmkst HS.
pose proof (proj1 HJN) as HARN.
destruct (FRMF _ _ (F + 228) 8900 HARN ltac:(zl) ltac:(zl) ltac:(zl)) as (NV & NM & NH).
(* __asan_memset(expect + 4, 0, 8900) at 0x82fc4 *)
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := SK) SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) AMEMSET W4 (ms_regs msN) (ms_mem msN)
(sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
(F + 228) 0 8900 (sp1 - sp0) (Z_to_bv 64 (BASE + 1872)) HJN).
- rewrite RNa0, UF. reflexivity.
- exact RNa1.
- exact RNa2.
- zl.
- zl.
- zl.
- exact EspN.
- exact Hom.
- zl.
- rewrite Hes. zl.
- exact N3.
- exact N4.
- exact RNra.
- apply ret_ok_codeptr_v; [zl | reflexivity].
- intros a Ha. split; [| rewrite Hes; zl].
right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF4. change (fs_frame_bytes 8) with 16384. zl.
- exact NM.
- apply (range_addressable_sub _ _ (F + 224) 8904); [apply ZRA; exact ZN | zl | zl].
- intros _. exact NH.
- exact I. }
cbv beta. intros W15 c15 _ (-> & regs15 & mem15 & md15 & -> & HJ15 & HP15 & H15_10 & HSET15 & KFR15 & _).
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP15 RKN) as RK15.
pose proof RK15 as (R15_2 & R15_3 & R15_4 & R15_8 & R15_9 & R15_19 & R15_23 & R15_24).
assert (R15_18 : getr regs15 18 = Z_to_bv 64 8192) by (rewrite <- RNs2; exact (HP15 18 ltac:(unfold acallee_saved; zl))).
assert (R15_20 : getr regs15 20 = Z_to_bv 64 res) by (rewrite <- RN20; exact (HP15 20 ltac:(unfold acallee_saved; zl))).
assert (R15_21 : getr regs15 21 = Z_to_bv 64 (sF + 28)) by (rewrite <- RN21; exact (HP15 21 ltac:(unfold acallee_saved; zl))).
assert (R15_22 : getr regs15 22 = Z_to_bv 64 (F + 224)) by (rewrite <- RN22; exact (HP15 22 ltac:(unfold acallee_saved; zl))).
assert (R15_25 : getr regs15 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RN25; exact (HP15 25 ltac:(unfold acallee_saved; zl))).
assert (KU15 : forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) mem15 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (RNG a (or_introl Ha)) as Hr.
rewrite (KFR15 a Hr); [| generalize Ha HFz; unfold s5_u; zl | apply (SU a); [zl | zl | left; exact Ha]].
rewrite (KN a Hr). exact (KU14 a Ha). }
assert (ZM15 : forall i, 0 <= i < 1113 -> aview SEGS (w_H W4) mem15 (sF + 28 + i) = Some 0).
{ intros i Hi. rewrite (KFR15 _) by (generalize HFz; zl). exact (ZN i Hi). }
(* run O: 0x82fc8 .. jal __asan_memcpy (0x82ff8): the three unchecked `sw` tags into `expect`, through a region
   based on s6 = expect covering its 8904 bytes, zero from offset 4 on (the memset) *)
clear dependent E.
remember (Eimg (Ereg regs15 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs15 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs15 []) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (U22 : bv_unsigned (ew E 22) = F + 224) by (rewrite (EE 22%nat 22%bv eq_refl), R15_22; apply unsigned_lit_small; zl).
pose proof (proj1 HJ15) as HAR15.
destruct (al_frames _ _ LAWS ly4 S4 W4 mem15 md15 8 (c_fpos cx) HAR15 Hfin5) as (_ & _ & HF15 & _).
rewrite EF4 in HF15. change (fs_frame_bytes 8) with 16384 in HF15.
assert (HS : st_ok_pi SEGS VAL E (mkSS 1872 sr_atoms [YP09.mkRegion (Some 22%nat) 0 8904 0 8904 [YP09.mkChunk 4 (CZero 8900)]]
None (mkFacts [] [] [])) (restrict (w_H W4) (mkst regs15 (Z_to_bv 64 (BASE + 1872)) mem15 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
rewrite U22. split; [zl|]. split; [zl|]. split.
+ intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HF15 (F + 224 + o) ltac:(zl))).
+ apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_val YP09.c_off] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|].
replace (F + 224 + 4 + i) with (F + 228 + i) by ring.
apply (scb_mbyte_of_aview SEGS (w_H W4) mem15 (F + 228 + i) 0). rewrite (HSET15 i Hi). reflexivity.
- cbn. tauto.
- unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJ15.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF4. change (fs_frame_bytes 8) with 16384. zl. }
rename ms into msO, HJ15 into HJO, HFr into HFrO. clear HF HG.
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 224 <= a < F + 9128) -> aview SEGS (w_H W4) (ms_mem msO) a = aview SEGS (w_H W4) mem15 a).
{ intros a Ha Hn. apply (s5_kept_run SEGS _ _ _ _ _ a HFrO Ha).
intros (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. rewrite U22 in Hrb. zl. }
clear HFrO.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRO. cbn [ms_mem restrict] in HRO.
unfold region_ok in HRO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRO.
destruct HRO as (_ & _ & _ & HCK). rewrite U22 in HCK.
lazymatch type of HCK with Forall _ ?cs => assert (HCHK : scene_chk cs = true) by (vm_compute; reflexivity) end.
assert (EXO : forall i, 0 <= i < 8904 -> ~ (832 <= i < 838) -> aview SEGS (w_H W4) (ms_mem msO) (F + 224 + i) = Some (scene_tag i)).
{ intros i Hi Hm.
pose proof (scene_chk_ok _ HCHK i ltac:(unfold P_reac_ctrl_scene_build.SCENE_BYTES; zl) ltac:(unfold SCENE_MAC_OFF, SCENE_MAC_LEN; zl)) as Hcz.
pose proof (cz_val_mbyte SEGS E _ (F + 224) _ i (scene_tag i) HCK Hcz) as Hb.
unfold aview. cbv beta. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (scene_tag_range i).
change (bv_modulus 8) with 256. zl. }
clear HCK HCHK.
prreg HS (10%bv : bv 5) ROa0. prreg HS (11%bv : bv 5) ROa1. prreg HS (12%bv : bv 5) ROa2. prreg HS (1%bv : bv 5) ROra.
assert (ROl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msO) r = getr regs15 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msO) regs15 []
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
assert (RKO : s5_rk B sp0 sp1 F sF np (ms_regs msO))
by (apply (s5_rk_kept B _ _ _ _ _ regs15); [intros r Hr; apply ROl; cbn in Hr |- *; tauto | exact RK15]).
assert (RO18 : getr (ms_regs msO) 18 = Z_to_bv 64 8192) by (rewrite (ROl 18%bv ltac:(cbn; tauto)); exact R15_18).
assert (RO20 : getr (ms_regs msO) 20 = Z_to_bv 64 res) by (rewrite (ROl 20%bv ltac:(cbn; tauto)); exact R15_20).
assert (RO21 : getr (ms_regs msO) 21 = Z_to_bv 64 (sF + 28)) by (rewrite (ROl 21%bv ltac:(cbn; tauto)); exact R15_21).
assert (RO22 : getr (ms_regs msO) 22 = Z_to_bv 64 (F + 224)) by (rewrite (ROl 22%bv ltac:(cbn; tauto)); exact R15_22).
assert (RO25 : getr (ms_regs msO) 25 = Z_to_bv 64 (F + 112)) by (rewrite (ROl 25%bv ltac:(cbn; tauto)); exact R15_25).
pose proof RKO as (O2 & O3 & O4 & _).
assert (EspO : spZ (ms_regs msO) = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite O2, unsigned_lit_small by zl; ring).
assert (KUO : forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) (ms_mem msO) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KO a (RNG a (or_introl Ha))) by (generalize Ha HFz; unfold s5_u; zl). exact (KU15 a Ha). }
assert (MACO : forall j, 0 <= j < 6 -> aview SEGS (w_H W4) (ms_mem msO) (F + 112 + j) = aview SEGS (w_H W4) mem5 (F + 112 + j)).
{ intros j Hj. rewrite (KUO _) by (unfold s5_u; zl). symmetry. apply K5. left. unfold s5_u. zl. }
assert (ZMO : forall i, 0 <= i < 1113 -> aview SEGS (w_H W4) (ms_mem msO) (sF + 28 + i) = Some 0).
{ intros i Hi. rewrite (KO _) by (generalize HFz; zl). exact (ZM15 i Hi). }
pmkst HS.
pose proof (proj1 HJO) as HARO.
destruct (FRMF _ _ (F + 1056) 6 HARO ltac:(zl) ltac:(zl) ltac:(zl)) as (OV1 & OM1 & OH1).
destruct (FRMF _ _ (F + 112) 6 HARO ltac:(zl) ltac:(zl) ltac:(zl)) as (OV2 & OM2 & OH2).
(* __asan_memcpy(expect + 0x340, mac, 6) at 0x82ff8 *)
eapply SRr_bind.
{ eapply (aj_intrin_at (SK := SK) SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W4 (ms_regs msO) (ms_mem msO)
(sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1)
(F + 1056) (F + 112) 6 (sp1 - sp0) (Z_to_bv 64 (BASE + 1924)) HJO).
- rewrite ROa0, U22. replace (F + 224 + 832) with (F + 1056) by ring. reflexivity.
- rewrite ROa1, (EE 25%nat 25%bv eq_refl). exact R15_25.
- exact ROa2.
- zl.
- zl.
- zl.
- exact EspO.
- exact Hom.
- zl.
- rewrite Hes. zl.
- exact O3.
- exact O4.
- exact ROra.
- apply ret_ok_codeptr_v; [zl | reflexivity].
- intros a Ha. split; [| rewrite Hes; zl].
right; right; right. exists 8, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF4. change (fs_frame_bytes 8) with 16384. zl.
- exact OM1.
- apply (range_addressable_sub _ _ (F + 224) 8904); [apply ZRA; exact ZMO | zl | zl].
- intros _. exact OH1.
- cbv iota. split; [zl|]. split; [zl|]. split.
{ intros a Ha. split; [exact (OV2 a Ha) | rewrite EspO, Hes; zl]. }
split; [zl|]. split; [exact OM2|]. split.
{ apply (block_shadow_range _ _ (F + 112) 6 (F + 112) 6); [| zl | zl]. apply BSM. intros a Ha. exact (KUO a Ha). }
intros _. exact OH2. }
cbv beta. intros W16 c16 _ (-> & regs16 & mem16 & md16 & -> & HJ16 & HP16 & H16_10 & HCPY16 & KFR16 & _).
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP16 RKO) as RK16.
pose proof RK16 as (R16_2 & R16_3 & R16_4 & R16_8 & R16_9 & R16_19 & R16_23 & R16_24).
assert (R16_18 : getr regs16 18 = Z_to_bv 64 8192) by (rewrite <- RO18; exact (HP16 18 ltac:(unfold acallee_saved; zl))).
assert (R16_20 : getr regs16 20 = Z_to_bv 64 res) by (rewrite <- RO20; exact (HP16 20 ltac:(unfold acallee_saved; zl))).
assert (R16_21 : getr regs16 21 = Z_to_bv 64 (sF + 28)) by (rewrite <- RO21; exact (HP16 21 ltac:(unfold acallee_saved; zl))).
assert (R16_22 : getr regs16 22 = Z_to_bv 64 (F + 224)) by (rewrite <- RO22; exact (HP16 22 ltac:(unfold acallee_saved; zl))).
assert (R16_25 : getr regs16 25 = Z_to_bv 64 (F + 112)) by (rewrite <- RO25; exact (HP16 25 ltac:(unfold acallee_saved; zl))).
assert (KU16 : forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) mem16 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (RNG a (or_introl Ha)) as Hr.
rewrite (KFR16 a Hr); [| generalize Ha HFz; unfold s5_u; zl | apply (SU a); [zl | zl | left; exact Ha]].
exact (KUO a Ha). }
assert (ZM16 : forall i, 0 <= i < 1113 -> aview SEGS (w_H W4) mem16 (sF + 28 + i) = Some 0).
{ intros i Hi. rewrite (KFR16 _) by (generalize HFz; zl). exact (ZMO i Hi). }
assert (SP16 : s5_spills_at W4 mem16 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem16); [intros a Ha; apply KU16; unfold s5_u; zl | exact SP3]. }
(* run P: 0x82ffc addiw a2,s2,0x2c8; ld s2,0x58(s1) .. jal bcmp (0x8300c): bcmp(body, expect, 8904) *)
clear dependent E.
pose proof (s5_entry W4 regs16 mem16 1924 sp1 F sF body nn R16_9 R16_23 R16_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP16) as HS.
remember (Eimg (Ereg regs16 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs16 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs16 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs16 _ 0)).
paj_run_shc RUNP RUNC HS HJ16.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msP, HJ16 into HJP, HFr into HFrP. clear HF HG.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msP) a = aview SEGS (w_H W4) mem16 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrP); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrP.
assert (RPl : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msP) r = getr regs16 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msP) regs16 (s5_extra body nn)
[2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RPa0. prreg HS (11%bv : bv 5) RPa1. prreg HS (12%bv : bv 5) RPa2. prreg HS (1%bv : bv 5) RPra.
prreg HS (18%bv : bv 5) RPs2.
assert (RKP : s5_rk B sp0 sp1 F sF np (ms_regs msP))
by (apply (s5_rk_kept B _ _ _ _ _ regs16); [intros r Hr; apply RPl; cbn in Hr |- *; tauto | exact RK16]).
assert (RP18 : getr (ms_regs msP) 18 = Z_to_bv 64 body) by (rewrite RPs2; exact E32).
assert (RP20 : getr (ms_regs msP) 20 = Z_to_bv 64 res) by (rewrite (RPl 20%bv ltac:(cbn; tauto)); exact R16_20).
assert (RP21 : getr (ms_regs msP) 21 = Z_to_bv 64 (sF + 28)) by (rewrite (RPl 21%bv ltac:(cbn; tauto)); exact R16_21).
assert (ZMP : forall i, 0 <= i < 1113 -> aview SEGS (w_H W4) (ms_mem msP) (sF + 28 + i) = Some 0).
{ intros i Hi. rewrite (KP _) by zl. exact (ZM16 i Hi). }
assert (CHB : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 16384) -> ~ (sF <= a < sF + 2048) -> ~ (sp1 - 8192 <= a < sp1) ->
aview SEGS (w_H W4) (ms_mem msP) a = aview SEGS (w_H W4) mem13 a).
{ intros a Ha H1 H2 H3. rewrite (KP a Ha). rewrite (KFR16 a Ha) by zl. rewrite (KO a Ha) by zl.
rewrite (KFR15 a Ha) by zl. rewrite (KN a Ha). rewrite (KSH14 a Ha) by zl. exact (KM a Ha). }
pmkst HS.
pose proof (proj1 HJP) as HARP.
destruct (BLKF _ _ body nn body 8904 HARP Hbody4 ltac:(zl) ltac:(rewrite Ereq; zl) ltac:(zl)) as (PV1 & PM1 & PR1 & PH1).
destruct (FRMF _ _ (F + 224) 8904 HARP ltac:(zl) ltac:(zl) ltac:(zl)) as (PV2 & PM2 & PH2).
apply (BCMP (ms_regs msP) (ms_mem msP) _ body (F + 224) 8904 1944 _ HJP).
{ rewrite RPa0. exact E32. }
{ rewrite RPa1, (EE 22%nat 22%bv eq_refl). exact R16_22. }
{ rewrite RPa2, (EE 18%nat 18%bv eq_refl), R16_18. vm_compute. reflexivity. }
{ exact RPra. }
{ zl. }
{ reflexivity. }
{ exact RKP. }
{ zl. } { zl. } { zl. } { zl. } { zl. }
{ exact PV1. } { exact PV2. } { exact PM1. } { exact PM2. } { exact PR1. } { exact PH1. }
{ apply ZRA. exact ZMP. }
{ intros _. exact PH2. }
{ intros i Hi. rewrite (CHB (body + i)) by (generalize HdFB HbodyZ; zl). rewrite (KP (F + 224 + i)) by zl.
destruct (Z_lt_dec i 832) as [Hlt | Hge]; [| destruct (Z_lt_dec i 838) as [Hlt2 | Hge2]].
- rewrite (BODY13 i) by zl. rewrite (KFR16 (F + 224 + i)) by zl. rewrite (EXO i) by zl. reflexivity.
- replace i with (832 + (i - 832)) by ring. rewrite (BMAC13 (i - 832)) by zl.
replace (F + 224 + (832 + (i - 832))) with (F + 1056 + (i - 832)) by ring.
rewrite (HCPY16 (i - 832)) by zl. rewrite (MACO (i - 832)) by zl. reflexivity.
- rewrite (BODY13 i) by zl. rewrite (KFR16 (F + 224 + i)) by zl. rewrite (EXO i) by zl. reflexivity. }
intros regs17 mem17 md17 HJ17 HP17 H17_10 KM17.
pose proof (s5_rk_pres B _ _ _ _ _ _ _ HP17 RKP) as RK17.
pose proof RK17 as (R17_2 & R17_3 & R17_4 & R17_8 & R17_9 & R17_19 & R17_23 & R17_24).
assert (R17_18 : getr regs17 18 = Z_to_bv 64 body) by (rewrite <- RP18; exact (HP17 18 ltac:(unfold acallee_saved; zl))).
assert (R17_20 : getr regs17 20 = Z_to_bv 64 res) by (rewrite <- RP20; exact (HP17 20 ltac:(unfold acallee_saved; zl))).
assert (R17_21 : getr regs17 21 = Z_to_bv 64 (sF + 28)) by (rewrite <- RP21; exact (HP17 21 ltac:(unfold acallee_saved; zl))).
assert (KU17 : forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) mem17 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. pose proof (RNG a (or_introl Ha)) as Hr.
rewrite (KM17 a Hr) by (apply (SU a); [zl | zl | left; exact Ha]). rewrite (KP a Hr). exact (KU16 a Ha). }
assert (SP17 : s5_spills_at W4 mem17 sp1 F sF body nn).
{ apply (s5_spills_kept W3 W4 mem3 mem17); [intros a Ha; apply KU17; unfold s5_u; zl | exact SP3]. }
(* 0x83010 bnez a0 -> abort: bcmp(body, expect, 8904) = 0 *)
clear dependent E.
pose proof (s5_entry W4 regs17 mem17 1944 sp1 F sF body nn R17_9 R17_23 R17_19 ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl)
ltac:(zl) ltac:(zl) ltac:(zl) ltac:(zl) SP17) as HS.
remember (Eimg (Ereg regs17 (s5_extra body nn))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs17 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs17 (s5_extra body nn)) E)
by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; zl | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 body)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; zl); exact (ew_Ereg_extra regs17 _ 0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. cbn [sv_denot] in Hc. rewrite (EE 10%nat 10%bv eq_refl), H17_10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* run Q: 0x83014 .. jal __asan_set_shadow_f8 (0x8301c), returning to C6 0x83020 *)
paj_run_shc RUNP RUNC HS HJ17.
{ intros a (r & Hin & Ha).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. zl. }
rename ms into msQ, HJ17 into HJQ, HFr into HFrQ. clear HF HG.
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msQ) a = aview SEGS (w_H W4) mem17 a).
{ intros a Ha. eapply (aview_kept_frame _ _ _ _ _ 0 HFrQ); [zl | | exact Ha].
intros b Hb (r & Hin & Hrb).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin. destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. zl. }
clear HFrQ.
assert (RQl : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr (ms_regs msQ) r = getr regs17 r).
{ intros x Hx. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W4) msQ) regs17 (s5_extra body nn)
[2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HS HAG eq_refl x Hx). }
prreg HS (10%bv : bv 5) RQa0. prreg HS (11%bv : bv 5) RQa1. prreg HS (1%bv : bv 5) RQra.
assert (RKQ : s5_rk B sp0 sp1 F sF np (ms_regs msQ))
by (apply (s5_rk_kept B _ _ _ _ _ regs17); [intros r Hr; apply RQl; cbn in Hr |- *; tauto | exact RK17]).
assert (RQ18 : getr (ms_regs msQ) 18 = Z_to_bv 64 body) by (rewrite (RQl 18%bv ltac:(cbn; tauto)); exact R17_18).
assert (RQ20 : getr (ms_regs msQ) 20 = Z_to_bv 64 res) by (rewrite (RQl 20%bv ltac:(cbn; tauto)); exact R17_20).
assert (KUQ : forall a, s5_u sp1 F sF a -> aview SEGS (w_H W4) (ms_mem msQ) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (KQ a (RNG a (or_introl Ha))). exact (KU17 a Ha). }
pose proof RKQ as (Q2 & Q3 & Q4 & _).
assert (EspQ : spZ (ms_regs msQ) = sp0 + (sp1 - sp0)) by (unfold spZ; rewrite Q2, unsigned_lit_small by zl; ring).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_set_shadow_at (SK := SK) SEGS B LAWS pa_segs_low (SIGMA SS___asan_set_shadow_f8) 0xf8 ASHF8 W4 (ms_regs msQ) (ms_mem msQ)
(sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly4 S4 _ (ev + 1) 8 (c_fpos cx) (sF + 28) 1113
(sp1 - sp0) (Z_to_bv 64 (BASE + 1960)) HJQ).
- left. reflexivity.
- rewrite RQa0, (EE 21%nat 21%bv eq_refl). exact R17_21.
- exact RQa1.
- zl.
- rewrite EF4. fold sF. zl.
- rewrite EF4. fold sF. change (fs_frame_bytes 8 / 8) with 2048. zl.
- exact EspQ.
- exact Hom.
- zl.
- zl.
- exact Q3.
- exact Q4.
- exact RQra.
- apply ret_ok_codeptr_v; [zl | reflexivity]. }
cbv beta. intros W18 c18 _ (-> & regs18 & mem18 & md18 & -> & HJ18 & HP18 & HSH18 & KSH18 & _).
assert (ROW3 : forall o, 28 <= o < 1141 -> aview SEGS (w_H W3) mem3 (sF + o) = Some 248).
{ intros o Ho. unfold sc_shbg in HSHBG. cbn [sg_sh_bg scene_geom_asan] in HSHBG.
rewrite Forall_forall in HSHBG.
specialize (HSHBG ((28, 1141), 248) ltac:(cbn; repeat (first [left; reflexivity | right]))).
unfold sc_shr in HSHBG. cbn [fst snd] in HSHBG. fold F in HSHBG. fold sF in HSHBG. exact (HSHBG o Ho). }
apply EXIT.
- exact HJ18.
- intros a Ha. pose proof (s5_prot_u sp0 sp1 F sF a ltac:(zl) ltac:(zl) Ha) as Hu.
rewrite (KSH18 a (RNG a (or_introl Hu)) (NOROW a Hu)). exact (KUQ a Hu).
- intros a Ha. unfold s5_row in Ha. replace a with (sF + 28 + (a - (sF + 28))) by ring.
rewrite (HSH18 (a - (sF + 28))) by zl. replace (sF + 28 + (a - (sF + 28))) with (sF + (a - sF)) by ring.
symmetry. apply ROW3. zl.
- exact (s5_rk_pres B _ _ _ _ _ _ _ HP18 RKQ).
- rewrite <- RQ18. exact (HP18 18 ltac:(unfold acallee_saved; zl)).
- rewrite <- RQ20. exact (HP18 20 ltac:(unfold acallee_saved; zl)).
Qed.

End h.
End f.
End d.
Print Assumptions scene_seg_S5.
