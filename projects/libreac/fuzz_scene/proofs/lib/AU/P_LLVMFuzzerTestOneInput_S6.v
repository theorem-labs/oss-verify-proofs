(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* SEGMENT S6 of the asan-ubsan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput.  Proves
   `seg_S6_stmt SEGS B ameter_triv WK scene_geom_asan_ubsan` (lib/AU/P_LLVMFuzzerTestOneInput_seg.v): from cut C6
   (0x83158) to the `ret` (0x831fc), the walk realizes the entry contract's post, `sc_ret`.

   This is the port of the asan proof, lib/A/P_LLVMFuzzerTestOneInput_S6.v (a Theorem Labs lane, at
   916e1f35ef3), onto the asan-ubsan cut, with the asan-ubsan kit (lib.AU.Prog; YCbq, YC5d, YE01, YCbp and
   StackFreeJournal from lib.AU, gate 6o).  The proof has the same four runs and the same closing.

   Image: fuzz_scene.asan-ubsan, sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f.  The four
   runs (listing dis-LLVMF.asan-ubsan.txt, lines 559-600):
     run 1  0x83158-0x8315c  `mv a0,s6` and `jal __wrap_free`; F2 frees `before` through aj_free_at (YCbq.v:992)
                             with AFREE, the trace of the site 0x83160 from HTRACE, and `aftok [] ... (before, nn)`
                             of the cut for the "not the caller's block" premise.
     run 2  0x83160-0x83164  `mv a0,s4` and `jal __wrap_free`; F3 frees `body`, same rule, site 0x83168.
     run 3  0x83168-0x831a8  the release block: the six `sb a0,{0xe,0x12..0x16}(s3)` re-poison stores of mac and
                             blk, the reloads `ld s2,0x18(s1)` and `ld s4,0x28(s1)` of F from its two spill slots,
                             the `[F] = 0x45e0360e` release magic at 0x83194, the `beqz s4` of 0x83198 -- DECIDED NOT
                             TAKEN from the atom fact 4096 <= F (the frame of the live fake stack), so the real-stack
                             arm 0x831b0-0x831b8 (`__asan_set_shadow_00`) is dead and is not walked -- and
                             `__asan_stack_free_8(F, 9408)` at 0x831a8 through lib/AU/StackFreeJournal.v
                             aj_stack_free_at with ASF8 (StackFreeDef's astack_free_realizes at class 8).
     run 4  0x831ac-0x831fc  `j` over the dead arm, `a0 = 0`, `addi sp,s0,-0xe0`, the 13 epilogue loads of the
                             caller's saved words and `ret`, closed with paj_ret_at (AU/Prog/ScenePaLib.v:59).
   What differs from asan: the registers at C6 (before in s6, body in s4, F only in the spill slots [s1+0x18] and
   [s1+0x28]), so run 3 takes F as an extra atom (32) of its environment, and the two spill slots as chunks of one
   read-only region at s1; the pcs and the trace sites.  No UBSan guard lies in this range (a Theorem Labs lane's TWINMAP.md 4.2),
   `beqz s4` 0x83198 is the ONLY conditional branch in the segment, and no `__asan_report_*` call site is in it
   (the range holds exactly three calls: two `__wrap_free` and `__asan_stack_free_8`).

   The post's clauses come from: the journal of the last state (ajournal_materialize, YCbq.v:665); k = ev + 2 <= 6
   <= EV_LIB; aregs_preserved from the 13 reloaded words (sc_saves of the cut, kept by every call because the save
   area lies above sp1); a0 = 0 from the run; the block permutation by cancelling `before` and `body` from the
   cut's permutation (Permutation_app_inv); the fds and fs clauses from the journal's `aos_step []` (closed sink,
   aos_step_closed); the sink's cells from `sink_img_laws` (lib/AU/G_Sink.v) and the journal's image clause; the
   meter from ameter_triv; and the input bytes from the journal's block clause at (p, n).

   Owners of the hypotheses: a Theorem Labs lane (ML, TL, AIL), a Theorem Labs lane (AFREE, HTRACE), a Theorem Labs lane (ASF8), and the
   budget side conditions HEV / HSTK, which are LLVMF_EV <= EV_LIB and LLVMF_SPDROP + ASTACK <= LLVMF_STK of
   lib/AU/P_LLVMFuzzerTestOneInput.v (HEV, HSTK) at LLVMF_EV = 6 and LLVMF_SPDROP = 240.  AR_laws is the theorem
   AR_laws_ok (Reusable/YG0q.v:803), not a hypothesis; the walk needs no frame_flag_lawP.
   Gate 6h: the sink head is the Section variable SK, passed explicitly to seg_S6_stmt (`@seg_S6_stmt fx rc SK`),
   never resolved by instance search; `llvmf_S6_scene` at the end is that theorem at scene's own head, musl's
   ofl_head 0x5f7190 of this image (the value of lib/AU/P_LLVMFuzzerTestOneInput.v's scene_sink_head). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
(* gate 6o: the image-differing modules from lib.AU, everything the trunk's lib/Reusable holds from lib.Reusable *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import StackFreeJournal.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1g YC1h YC45 YC4b.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg G_Sink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* a callee-saved register kept across a call, as the bv literal the walk's facts use *)
Ltac s6pres H z r name :=
pose proof (H z ltac:(unfold acallee_saved; lia)) as name;
replace (Z_to_bv 5 z) with r in name by (apply bv_eq; vm_compute; reflexivity).
(* the 13 callee-saved words of the caller, as the epilogue reloads them: [sp0 - 8 - 8 j] = atom 32 + j *)
Definition s6_stack_chunk (j : nat) : YP09.chunk := YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)).
Definition s6_save_region : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 (map s6_stack_chunk (seq 0 13)).
Definition s6_extra (regs : bvmap 5 word) : list word := map (fun r => getr regs r) sc_saved_regs.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h: the head's type is written fully qualified, so no other unit's YI16 twin can capture the short name *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
Section f.
(* PI_scene, not an abstract PAImg: lib/AU/P_LLVMFuzzerTestOneInput_seg.v's scene_geom_asan_ubsan is stated at
   PI_scene. *)
#[local] Notation PI := (@PI_scene rc).
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* the donor's A/ACf5.v:172-186 rt_chain, at scene's own chain shape (rt_ch of the ctx file) *)
Lemma s6_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) ->
4096 <= raZ regs -> alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs)
(if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- apply (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk);
  [exact H8 | exact H16 | exact Hra | exact Hceil | exact Hal | lia | exact Hsp'].
- left. split; [right; left; lia | reflexivity].
Qed.
(* A Theorem Labs lane's P_check_step_S3.v:131 s3_kept_run *)
Lemma s6_kept_run : forall E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H mB a = aview SEGS H mA a.
Proof. intros E rs H mA mB a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Section h.
Variable B : asyms.
Variable WK : swalk.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis ASF8 : StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) 8.
Hypothesis AIL : sink_img_laws SEGS B (sw_sink WK).
Hypothesis HEV : 6 <= sw_ev WK.
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
(* the six allocator sites of this image: malloc ra +0x3ac / +0x5cc / +0x708, free ra +0x6fc / +0x8bc / +0x8c4
   (lib/AU/P_LLVMFuzzerTestOneInput.v RT_*_off) *)
Hypothesis HTRACE : rt_trace_in_stmt SEGS (sw_ra WK) (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
(BASE + AF_LLVMFuzzerTestOneInput + 0x3ac) (BASE + AF_LLVMFuzzerTestOneInput + 0x5cc)
(BASE + AF_LLVMFuzzerTestOneInput + 0x708) (BASE + AF_LLVMFuzzerTestOneInput + 0x6fc)
(BASE + AF_LLVMFuzzerTestOneInput + 0x8bc) (BASE + AF_LLVMFuzzerTestOneInput + 0x8c4) (as_universe B).

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* A fresh symbolic state at a cut or a call return: every register an atom, no region, no fact. *)
Lemma s6_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- unfold facts_ok. cbn. tauto.
Qed.
Theorem llvmf_S6 : @seg_S6_stmt fx rc SK SEGS B ameter_triv WK scene_geom_asan_ubsan.
Proof.
unfold seg_S6_stmt, sc_from_C6.
intros cx Hbase ly3 S3 W3 regs3 mem3 md3 bs body before ev HC6.
destruct cx as [ly S W regs mem md p n fpos sp1 E0 T].
unfold sc_base, sc_base0 in Hbase.
unfold cut_C6, sc_j, sc_frame, sc_saves, sc_shbg, sc_shr, sc_open, sc_blk_ok, sc_img, sc_F, rt_F, vat in HC6.
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T
     sg_cid sg_frame sg_off_blki sg_off_mac sg_off_blk sg_off_expect sg_blk_n sg_mac_n sg_scene_n
     sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi sg_sh_bg
     sg6_F sg6_shF sg6_sp1 sg6_sp0 sg6_before sg6_body sg6_Fsp scene_geom_asan_ubsan] in Hbase, HC6.
destruct Hbase as ((HPRE & Hra & Ha0 & Ha1 & Hpn & Hfrs0 & Hev0 & Hlive0 & HROD & HSNK0 & HFD0 & HSORT0 & _) & Esp1).
destruct HC6 as (Hevr & (HJ & Hfrs3 & HMLE) & HPerm & Hbytes & HBLKb & HBLKf & (Hflagw & HFpres & HFSpres)
 & Hsaved & HSHBG & HSHblki & HOPNblk & HOPNmac & (Esp3 & Egp3 & Etp3 & HROD3) & Hinp & Hnn
 & R6sp0 & R6sp1 & R6F & R6Fsp & R6shF & R6body & R6before).
unfold RV_s0, RV_s1, RV_s3, RV_s4, RV_s6 in R6sp0, R6sp1, R6shF, R6body, R6before.
(* ---- names and the facts every step uses ---- *)
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & _ & Hnev3 & Hk3 & G1 & G2 & G3 & G4 & Hgone3 & Hpres3 & Hstatic3 & G5 & HQT3).
set (sp0 := spZ regs) in *.
set (F := frame_addr ly 8 fpos) in *.
set (nn := sc_nn scene_geom_asan_ubsan bs) in *.
assert (Hfin3 : In (8, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EFA : frame_addr ly3 8 fpos = F)
  by (unfold F, frame_addr; destruct Hly3 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (EFL : flag_addr ly3 8 fpos = flag_addr ly 8 fpos)
  by (unfold flag_addr; destruct Hly3 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
rewrite EFA in HF4096, HFceil, HFapp.
change (fs_frame_bytes 8) with 16384 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
cbn [rt_FL c_ly c_fpos] in Hflagw. fold F in Hflagw.
set (FL := flag_addr ly 8 fpos) in *.
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _); exact ET).
assert (Hsp064 : 0 <= sp0 < 2 ^ 64) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr;
change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
assert (Hal8 : sp0 mod 8 = 0).
{ pose proof Hal16 as Hc. apply Z.mod_divide in Hc; [|lia]. destruct Hc as (t & Ht).
  rewrite Ht. replace (t * 16) with ((t * 2) * 8) by lia. apply Z_mod_mult. }
assert (HSV8 : rdword (aview SEGS (w_H W3) mem3) (sp0 - 8) = Some (raZ regs)).
{ pose proof (Hsaved 0 ltac:(lia)) as H0. replace (sp0 - 8 - 8 * 0) with (sp0 - 8) in H0 by lia.
  cbn [Z.to_nat nth sc_saved_regs] in H0. exact H0. }
assert (HSV16 : rdword (aview SEGS (w_H W3) mem3) (sp0 - 16) = Some (s0Z regs)).
{ pose proof (Hsaved 1 ltac:(lia)) as H1. replace (sp0 - 8 - 8 * 1) with (sp0 - 16) in H1 by lia.
  cbn [Z.to_nat nth sc_saved_regs] in H1. exact H1. }
(* ---- the caller chain at any later state: the donor's rt_chain at scene's saved area ---- *)
assert (HCH : forall (rd' : reader) sp',
(forall a, sp0 <= a < 2 ^ 64 -> rd' a = aview SEGS (w_H W) mem a) ->
rdword rd' (sp0 - 8) = Some (raZ regs) -> rdword rd' (sp0 - 16) = Some (s0Z regs) ->
sp' + 16 <= sp0 ->
achain ly3 rd' sp' sp0 (if sp0 + 16 <? ly_top ly3 then [(sp0, raZ regs, s0Z regs)] else [])).
{ intros rd' sp' Hk H8 H16 Hsp'.
  apply (s6_chain ly3 (aview SEGS (w_H W) mem) rd' regs sp');
  [ apply (achain_ly_top ly ly3); [exact Etop3 | exact Hch0]
  | rewrite Etop3; lia | exact Hk | exact H8 | exact H16 | exact Hra4 | lia | exact Hal8 | lia ]. }
(* ---- the realigned stack pointer: sp0 - 240 <= sp1 <= sp0 - 224, 32-aligned ---- *)
assert (Hq : exists q, sp1 = 32 * q) by (exists ((sp0 - 224) / 32); exact Esp1).
destruct Hq as (q & Hq).
assert (Hsp1 : sp0 - 240 <= sp1 <= sp0 - 224).
{ pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as M.
  pose proof Hal16 as Hal16c. apply Z.mod_divide in Hal16c; [|lia]. destruct Hal16c as (t & Ht).
  assert (Hm : exists m, (sp0 - 224) mod 32 = 16 * m) by (exists (t - 14 - 2 * ((sp0 - 224) / 32)); lia).
  destruct Hm as (m & Hm). rewrite Esp1. lia. }
assert (Hsp1m16 : (sp1 - sp0) mod 16 = 0).
{ rewrite Zminus_mod, Hal16, Hq. replace (32 * q) with ((2 * q) * 16) by lia. rewrite Z_mod_mult. reflexivity. }
assert (Hnev3' : st_nev S3 < EV_MAX) by lia.
(* ---- run 1: C6 0x83158 (offset 2228) .. jal __wrap_free at 0x8315c ---- *)
assert (Epc6 : sg_pc_c6 scene_geom_asan_ubsan = BASE + 2228).
{ unfold scene_geom_asan_ubsan. cbn [sg_pc_c6]. unfold SEG_C6_off, AF_LLVMFuzzerTestOneInput. rewrite Z.add_0_r. reflexivity. }
unfold cfg_at. rewrite Epc6. unfold w64 at 1.
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HS : st_ok_pi SEGS VAL E (mkSS 2228 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 2228)) mem3 (seg_rom SEGS))))
by (subst E; apply s6_entry).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. rewrite (EE 22%nat 22%bv eq_refl), R6before in Ra0.
prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) R2A. rewrite (EE 2%nat 2%bv eq_refl) in R2A.
prreg HS (3%bv : bv 5) R3A. rewrite (EE 3%nat 3%bv eq_refl), Egp3 in R3A.
prreg HS (4%bv : bv 5) R4A. rewrite (EE 4%nat 4%bv eq_refl), Etp3 in R4A.
prreg HS (8%bv : bv 5) R8A. rewrite (EE 8%nat 8%bv eq_refl), R6sp0 in R8A.
prreg HS (9%bv : bv 5) R9A. rewrite (EE 9%nat 9%bv eq_refl), R6sp1 in R9A.
prreg HS (19%bv : bv 5) R19A. rewrite (EE 19%nat 19%bv eq_refl), R6shF in R19A.
prreg HS (20%bv : bv 5) R20A. rewrite (EE 20%nat 20%bv eq_refl), R6body in R20A.
assert (EspA : spZ (ms_regs msA) = sp1)
by (unfold spZ; rewrite R2A; unfold spZ in Esp3; rewrite Esp3; reflexivity).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) mem3 a)
by (intros a Ha; eapply s6_kept_run; [exact HFrA | exact Ha | intros (r & Hr & _); destruct Hr]).
pmkst HS.
rewrite (pal_free B TL).
assert (Hs0A : s0Z (ms_regs msA) = sp0)
by (unfold s0Z; rewrite R8A; unfold w64; apply unsigned_lit_small; lia).
assert (HraA : raZ (ms_regs msA) = BASE + 2236)
by (unfold raZ; rewrite Rra; apply unsigned_lit_small; pose proof pa_base_lo; pose proof pa_B_ok as (_ & HB2 & _); lia).
assert (KRD : forall a, sp0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite KA by lia; apply G1; lia).
(* ---- F2: __wrap_free (before) at 0x8315c, ra 0x83160 ---- *)
eapply SRr_bind.
{ eapply (aj_free_at SEGS B LAWS pa_segs_low (pal_env B TL) ML AFREE W3 (ms_regs msA) (ms_mem msA)
  (sw_stk WK) sp0 [] ly S W mem md [(8, fpos)] ly3 S3 _ ev before nn (sp1 - sp0)
  (Z_to_bv 64 (BASE + 2236))
  (if sp0 + 16 <? ly_top ly then [(sp0, raZ regs, s0Z regs)] else []) HJA).
  - eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. left. reflexivity.
  - exact Ra0.
  - rewrite EspA. lia.
  - exact Hsp1m16.
  - lia.
  - lia.
  - exact R3A.
  - exact R4A.
  - exact Rra.
  - apply ret_ok_codeptr_v; [pose proof pa_base_lo; lia | reflexivity].
  - exact Hnev3'.
  - (* chain_pre at the call *)
    eapply (achain_chain_pre ly3 _ sp1 sp0 _ (ms_regs msA));
    [| rewrite EspA; lia | exact Hs0A | rewrite HraA; pose proof pa_base_lo; lia].
    rewrite <- Etop3.
    apply (HCH (aview SEGS (w_H W3) (ms_mem msA)) sp1 KRD);
    [ rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp0 - 8) ltac:(intros k Hk; apply KA; lia)); exact HSV8
    | rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp0 - 16) ltac:(intros k Hk; apply KA; lia)); exact HSV16
    | lia ].
  - (* the trace of this free site *)
    unfold rt_trace_in_stmt in HTRACE.
    apply (HTRACE (pc_free_ra0 (as_code B)) (BASE + 2236) (ms_regs msA)
      (mkRTCX SEGS ly S W regs mem md p n fpos sp1 E0 T)); [exact Hra | exact HraA |].
    right. split; [reflexivity|]. right. left. unfold AF_LLVMFuzzerTestOneInput. lia.
  - cbn [fst snd] in HBLKf. exact (proj2 (proj2 (proj2 (proj2 (proj2 HBLKf))))). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJB & HPB & (l1 & l2 & EabB1 & EabB2) & Hfrs4 & HK4).
clear HS Ra0 Rra EspA KRD Hs0A HraA HE HEI EE HFrA E.
(* ---- what the first free kept ---- *)
assert (Hsp1c : alloc_ceiling + ASTACK <= sp1) by lia.
assert (KB : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem msA) a)
by (intros a Ha; apply (proj1 HK4); lia).
assert (HPermB : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(body, nn)])).
{ rewrite EabB2.
  pose proof (Permutation_app_inv l1 l2 (ablocks B ly S ++ [(body, nn)]) [] (before, nn)) as Hinv.
  rewrite app_nil_r in Hinv. apply Hinv. rewrite <- EabB1. exact HPerm. }
assert (HinB : In (body, nn) (ablocks B ly4 S4))
by (eapply Permutation_in; [apply Permutation_sym; exact HPermB | apply in_or_app; right; left; reflexivity]).
assert (Hfin4 : In (8, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hnev4' : st_nev S4 < EV_MAX)
by (pose proof HJB as (_ & _ & _ & _ & _ & _ & HnevB & _); lia).
s6pres HPB 2 ((2%bv) : bv 5) P2B.
s6pres HPB 3 ((3%bv) : bv 5) P3B.
s6pres HPB 4 ((4%bv) : bv 5) P4B.
s6pres HPB 8 ((8%bv) : bv 5) P8B.
s6pres HPB 9 ((9%bv) : bv 5) P9B.
s6pres HPB 19 ((19%bv) : bv 5) P19B.
s6pres HPB 20 ((20%bv) : bv 5) P20B.
(* ---- run 2: 0x83160 .. jal __wrap_free at 0x83164 ---- *)
remember (Eimg (Ereg regs4 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs4 r)
by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HS : st_ok_pi SEGS VAL E (mkSS 2236 sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 2236)) mem4 (seg_rom SEGS))))
by (subst E; apply s6_entry).
paj_run_shc RUNP RUNC HS HJB.
{ apply awr_ok_nil. }
rename ms into msB, HJB into HJB2, HFr into HFrB. clear HF HG.
prreg HS (10%bv : bv 5) Rb0. rewrite (EE 20%nat 20%bv eq_refl), P20B, R20A in Rb0.
prreg HS (1%bv : bv 5) Rrb.
prreg HS (2%bv : bv 5) R2B. rewrite (EE 2%nat 2%bv eq_refl), P2B, R2A in R2B.
prreg HS (3%bv : bv 5) R3B. rewrite (EE 3%nat 3%bv eq_refl), P3B, R3A in R3B.
prreg HS (4%bv : bv 5) R4B. rewrite (EE 4%nat 4%bv eq_refl), P4B, R4A in R4B.
prreg HS (8%bv : bv 5) R8B. rewrite (EE 8%nat 8%bv eq_refl), P8B, R8A in R8B.
prreg HS (9%bv : bv 5) R9B. rewrite (EE 9%nat 9%bv eq_refl), P9B, R9A in R9B.
prreg HS (19%bv : bv 5) R19B. rewrite (EE 19%nat 19%bv eq_refl), P19B, R19A in R19B.
assert (EspB : spZ (ms_regs msB) = sp1)
by (unfold spZ; rewrite R2B; unfold spZ in Esp3; rewrite Esp3; reflexivity).
assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msB) a = aview SEGS (w_H W4) mem4 a)
by (intros a Ha; eapply s6_kept_run; [exact HFrB | exact Ha | intros (r & Hr & _); destruct Hr]).
assert (Hs0B : s0Z (ms_regs msB) = sp0)
by (unfold s0Z; rewrite R8B; unfold w64; apply unsigned_lit_small; lia).
assert (HraB : raZ (ms_regs msB) = BASE + 2244)
by (unfold raZ; rewrite Rrb; apply unsigned_lit_small; pose proof pa_base_lo; pose proof pa_B_ok as (_ & HB2 & _); lia).
assert (KRD2 : forall a, sp0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msB) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite KB2 by lia; rewrite KB by lia; rewrite KA by lia; apply G1; lia).
pmkst HS.
rewrite (pal_free B TL).
(* ---- F3: __wrap_free (body) at 0x83164, ra 0x83168 ---- *)
eapply SRr_bind.
{ eapply (aj_free_at SEGS B LAWS pa_segs_low (pal_env B TL) ML AFREE W4 (ms_regs msB) (ms_mem msB)
  (sw_stk WK) sp0 [] ly S W mem md [(8, fpos)] ly4 S4 _ (ev + 1) body nn (sp1 - sp0)
  (Z_to_bv 64 (BASE + 2244))
  (if sp0 + 16 <? ly_top ly then [(sp0, raZ regs, s0Z regs)] else []) HJB2).
  - exact HinB.
  - exact Rb0.
  - rewrite EspB. lia.
  - exact Hsp1m16.
  - lia.
  - lia.
  - exact R3B.
  - exact R4B.
  - exact Rrb.
  - apply ret_ok_codeptr_v; [pose proof pa_base_lo; lia | reflexivity].
  - exact Hnev4'.
  - eapply (achain_chain_pre ly4 _ sp1 sp0 _ (ms_regs msB));
    [| rewrite EspB; lia | exact Hs0B | rewrite HraB; pose proof pa_base_lo; lia].
    assert (Etop4 : ly_top ly4 = ly_top ly3).
    { rewrite Etop3. pose proof HJB2 as (_ & HlyB & _).
      destruct HlyB as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _). exact ET. }
    apply (achain_ly_top ly3 ly4 _ _ _ _ Etop4).
    rewrite <- Etop3.
    apply (HCH (aview SEGS (w_H W4) (ms_mem msB)) sp1 KRD2);
    [ rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp0 - 8) ltac:(intros k Hk; rewrite KB2 by lia; rewrite KB by lia; apply KA; lia)); exact HSV8
    | rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp0 - 16) ltac:(intros k Hk; rewrite KB2 by lia; rewrite KB by lia; apply KA; lia)); exact HSV16
    | lia ].
  - unfold rt_trace_in_stmt in HTRACE.
    apply (HTRACE (pc_free_ra0 (as_code B)) (BASE + 2244) (ms_regs msB)
      (mkRTCX SEGS ly S W regs mem md p n fpos sp1 E0 T)); [exact Hra | exact HraB |].
    right. split; [reflexivity|]. right. right. unfold AF_LLVMFuzzerTestOneInput. lia.
  - cbn [fst snd] in HBLKb. exact (proj2 (proj2 (proj2 (proj2 (proj2 HBLKb))))). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJC & HPC & (m1 & m2 & EabC1 & EabC2) & Hfrs5 & HK5).
clear HS Rb0 Rrb EspB KRD2 Hs0B HraB HE HEI EE HFrB E.
(* ---- what the second free kept ---- *)
assert (HPermC : Permutation (ablocks B ly5 S5) (ablocks B ly S)).
{ rewrite EabC2.
  pose proof (Permutation_app_inv m1 m2 (ablocks B ly S) [] (body, nn)) as Hinv.
  rewrite app_nil_r in Hinv. apply Hinv. rewrite <- EabC1. exact HPermB. }
assert (Hfin5 : In (8, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
pose proof HJC as (HAR5 & Hly5 & _ & Hwle5' & Hio5 & Hfrs5' & Hnev5 & _ & J1 & J2 & J3 & J4 & Hgone5 & Hpres5 & _ & J5 & HQT5).
assert (EFA5 : frame_addr ly5 8 fpos = F)
by (unfold F, frame_addr; destruct Hly5 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (EFL5 : flag_addr ly5 8 fpos = FL)
by (unfold FL, flag_addr; destruct Hly5 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
destruct (al_frames _ _ LAWS ly5 S5 W5 mem5 md5 8 fpos HAR5 Hfin5) as (HF32 & _ & HFpres5 & HFSpres5).
rewrite EFA5 in HFpres5, HFSpres5. change (fs_frame_bytes 8) with 16384 in HFpres5, HFSpres5.
change (16384 / 8) with 2048 in HFSpres5.
pose proof (shadow_addr_bounds F ltac:(lia)) as Hshb1.
pose proof (shadow_addr_bounds (F + 16384) ltac:(lia)) as Hshb2.
pose proof (shadow_range_end F 16384 ltac:(lia)) as Hshe.
assert (HFsh8 : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
(* every heap block of this walk is apart from the frame's shadow (zone2) *)
assert (DISJsh : forall b m a, zone2 b m -> kLowMemEnd <= a < kHighShadowEnd -> ~ (b <= a < b + m))
by (intros b m a (_ & Hz) Ha Hr; rewrite C5 in Ha; rewrite C2 in Ha; lia).
(* the frame and its shadow are apart: the frame is in the application range, the shadow between the two *)
assert (DSH : shadow_addr F + 2048 <= F \/ F + 16384 <= shadow_addr F).
{ rewrite C5, C2 in Hshb1. rewrite C5, C2 in Hshb2. change (16384 / 8) with 2048 in Hshe.
  destruct HFapp as (_ & [Hlow | (Hhigh & _)]); [right | left]; lia. }
s6pres HPC 2 ((2%bv) : bv 5) P2C. s6pres HPC 3 ((3%bv) : bv 5) P3C. s6pres HPC 4 ((4%bv) : bv 5) P4C.
s6pres HPC 8 ((8%bv) : bv 5) P8C. s6pres HPC 9 ((9%bv) : bv 5) P9C. s6pres HPC 19 ((19%bv) : bv 5) P19C.
rewrite R2B in P2C. rewrite R3B in P3C. rewrite R4B in P4C.
rewrite R8B in P8C. rewrite R9B in P9C. rewrite R19B in P19C.
assert (EFA4 : frame_addr ly4 8 fpos = F)
by (pose proof HJB2 as (_ & HlyB & _); unfold F, frame_addr;
    destruct HlyB as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (Hshrng : forall a, shadow_addr F <= a < shadow_addr F + 2048 -> kLowMemEnd <= a < kHighShadowEnd)
by (intros a Ha; rewrite C5, C2 in Hshb1, Hshb2; rewrite C5, C2; change (16384 / 8) with 2048 in Hshe; lia).
(* the frame and its shadow, kept across the two frees and the two runs *)
assert (KFRAME : forall a, (F <= a < F + 16384 \/ shadow_addr F <= a < shadow_addr F + 2048) ->
aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha.
  assert (HnE5 : ~ (body <= a < body + req_size nn)).
  { destruct Ha as [Ha | Ha].
    - pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 (ms_mem msB) _ body nn 8 fpos
        (proj1 HJB2) HinB Hfin4) as Hd.
      rewrite EFA4 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      change (fs_frame_bytes 8) with 16384 in Hd. lia.
    - apply (DISJsh body (req_size nn) a (proj1 (proj2 HBLKb))). apply Hshrng. exact Ha. }
  assert (HnE4 : ~ (before <= a < before + req_size nn)).
  { destruct Ha as [Ha | Ha].
    - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem msA) _ before nn 8 fpos
        (proj1 HJA)
        ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_or_app; right; left; reflexivity)
        Hfin3) as Hd.
      rewrite EFA in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      change (fs_frame_bytes 8) with 16384 in Hd. lia.
    - apply (DISJsh before (req_size nn) a (proj1 (proj2 HBLKf))). apply Hshrng. exact Ha. }
  rewrite ((proj1 (proj2 (proj2 (proj2 HK5)))) 8 fpos a Hfin4
    ltac:(rewrite EFA4; destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd];
          change (fs_frame_bytes 8) with 16384; change (16384 / 8) with 2048; lia) HnE5).
  rewrite KB2 by (unfold kLowMemEnd, kHighShadowEnd in *; destruct Ha as [Ha|Ha]; lia).
  rewrite ((proj1 (proj2 (proj2 (proj2 HK4)))) 8 fpos a Hfin3
    ltac:(rewrite EFA; destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd];
          change (fs_frame_bytes 8) with 16384; change (16384 / 8) with 2048; lia) HnE4).
  apply KA. rewrite C5, C2 in Hshb1, Hshb2. destruct Ha as [Ha|Ha]; lia. }
assert (KSTK : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (proj1 HK5 a ltac:(lia) ltac:(lia)). rewrite KB2 by lia.
  rewrite (proj1 HK4 a ltac:(lia) ltac:(lia)). apply KA. lia. }
(* F in its two spill slots [s1+0x18] and [s1+0x28] *)
assert (HFa5 : rdword (aview SEGS (w_H W5) mem5) (sp1 + 24) = Some F)
by (rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp1 + 24) ltac:(intros k Hk; apply KSTK; lia)); exact R6F).
assert (HFb5 : rdword (aview SEGS (w_H W5) mem5) (sp1 + 40) = Some F)
by (rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp1 + 40) ltac:(intros k Hk; apply KSTK; lia)); exact R6Fsp).
(* ---- run 3: the release block 0x83168 .. jal __asan_stack_free_8 at 0x831a8.  F is held in no register here, so
   the environment carries it as the extra atom 32: the two spill slots are chunks of a read-only region at s1
   that hold atom 32, and the magic store goes to a region based at atom 32. ---- *)
remember (Eimg (Ereg regs5 [Z_to_bv 64 F])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs5 r)
by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 F).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs5 [Z_to_bv 64 F] 0). }
assert (U9 : bv_unsigned (ew E 9) = sp1)
by (rewrite (EE 9%nat 9%bv eq_refl), P9C; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr F)
by (rewrite (EE 19%nat 19%bv eq_refl), P19C; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = F)
by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E
(mkSS 2244 sr_atoms
 [YP09.mkRegion (Some 19%nat) 14 24 14 24 [];
  YP09.mkRegion (Some 9%nat) 24 48 48 24 [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 32%nat) 0 8 0 8 []]
 None (mkFacts [(32%nat, mkAF 4096 (2 ^ 47) 0)] [] []))
(restrict (w_H W5) (mkst regs5 (Z_to_bv 64 (BASE + 2244)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    + rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres5 o ltac:(lia))).
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 32 0) F).
        -- cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        -- change (8 * Z.of_N 8) with 64. lia.
        -- change (Z.of_N 8) with 8. lia.
        -- exact (val_mem_of_rdword SEGS (w_H W5) mem5 _ _ HFa5).
      * apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 32 0) F).
        -- cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        -- change (8 * Z.of_N 8) with 64. lia.
        -- change (Z.of_N 8) with 8. lia.
        -- exact (val_mem_of_rdword SEGS (w_H W5) mem5 _ _ HFb5).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres5 (F + o) ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite C5, C2 in Hshb1. repeat split; (destruct DSH as [DSHa | DSHb]; lia).
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32, Z.pow_0_r, Z.mod_1_r. lia. }
paj_run_shc RUNP RUNC HS HJC.
{ intros a (r & Hin & Hr). cbn [ss_mem] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - right; right; right. exists 8, fpos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA5. rewrite U19 in Hr.
    change (fs_frame_bytes 8 / 8) with 2048. lia.
  - exfalso. rewrite U9 in Hr. lia.
  - right; right; right. exists 8, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFA5. rewrite U32 in Hr.
    change (fs_frame_bytes 8) with 16384. lia. }
rename ms into msC, HJC into HJC2, HFr into HFrC. clear HF HG.
prreg HS (10%bv : bv 5) Rc0. rewrite E32 in Rc0.
prreg HS (11%bv : bv 5) Rc1.
prreg HS (1%bv : bv 5) Rrc.
prreg HS (2%bv : bv 5) R2C. rewrite (EE 2%nat 2%bv eq_refl), P2C in R2C.
prreg HS (3%bv : bv 5) R3C. rewrite (EE 3%nat 3%bv eq_refl), P3C in R3C.
prreg HS (4%bv : bv 5) R4C. rewrite (EE 4%nat 4%bv eq_refl), P4C in R4C.
prreg HS (8%bv : bv 5) R8C. rewrite (EE 8%nat 8%bv eq_refl), P8C in R8C.
assert (EspC : spZ (ms_regs msC) = sp1)
by (unfold spZ; rewrite R2C; unfold spZ in Esp3; rewrite Esp3; reflexivity).
assert (KC : forall a, 0 <= a < 2 ^ 64 ->
~ (shadow_addr F + 14 <= a < shadow_addr F + 24) -> ~ (F <= a < F + 8) ->
aview SEGS (w_H W5) (ms_mem msC) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha Hn1 Hn2. eapply s6_kept_run; [exact HFrC | exact Ha |].
  intros (r & Hin & Hr). cbn [ss_mem] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - rewrite U19 in Hr. lia.
  - rewrite U9 in Hr. lia.
  - rewrite U32 in Hr. lia. }
assert (Hflag5 : rdword (aview SEGS (w_H W5) (ms_mem msC)) (F + 16384 - 8) = Some FL).
{ rewrite (rdword_ext (aview SEGS (w_H W5) mem5) _ (F + 16384 - 8)
    ltac:(intros k Hk; apply KC; [lia | rewrite C5, C2 in Hshb1, Hshb2; change (16384 / 8) with 2048 in Hshe; lia | lia])).
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (F + 16384 - 8) ltac:(intros k Hk; apply KFRAME; left; lia)).
  exact Hflagw. }
pmkst HS.
(* ---- __asan_stack_free_8 (F, 9408) at 0x831a8, ra 0x831ac ---- *)
eapply SRr_bind.
{ eapply (aj_stack_free_at SEGS B LAWS pa_segs_low ML (SIGMA SS___asan_stack_free_8) 8 ASF8 ltac:(lia)
  W5 (ms_regs msC) (ms_mem msC) (sw_stk WK) sp0 [] ly S W mem md [] ly5 S5 _ (ev + 1 + 1) fpos 9408 (sp1 - sp0)
  (Z_to_bv 64 (BASE + 2312)) HJC2).
  - rewrite EFA5. exact Rc0.
  - exact Rc1.
  - change (fs_frame_bytes 8) with 16384. lia.
  - reflexivity.
  - rewrite EFA5, EFL5. change (fs_frame_bytes 8) with 16384. exact Hflag5.
  - rewrite EspC. lia.
  - exact Hsp1m16.
  - lia.
  - rewrite Hes. lia.
  - exact R3C.
  - exact R4C.
  - exact Rrc.
  - apply ret_ok_codeptr_v; [pose proof pa_base_lo; lia | reflexivity]. }
cbv beta. intros W6 c6 Hwle6 (-> & regs6 & mem6 & md6 & -> & HJD & HPD & HSHf & HKf & HPRf).
(* ---- what the release left: the caller's save area is untouched ---- *)
destruct (al_flag _ _ LAWS ly5 S5 W5 mem5 md5 8 fpos HAR5 Hfin5) as (_ & _ & HFLapp & _).
rewrite EFL5 in HFLapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (Hsf : sf_span 8 9408 = 1176) by reflexivity.
assert (HSHbelow : shadow_addr F + 2048 < sp1) by (rewrite C5, C2 in Hshb1; lia).
assert (HFLbelow : FL < sp1) by lia.
assert (HFbelow : F + 16384 < sp1) by lia.
assert (KSAVE : forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W5) mem6 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha.
  rewrite (HKf a ltac:(lia) ltac:(rewrite EFA5, Hsf; lia) ltac:(rewrite EFL5; lia) ltac:(lia)).
  rewrite KC by lia.
  rewrite (proj1 HK5 a ltac:(lia) ltac:(lia)). rewrite KB2 by lia.
  rewrite (proj1 HK4 a ltac:(lia) ltac:(lia)). apply KA. lia. }
assert (Hsaved6 : forall j, 0 <= j < 13 ->
rdword (aview SEGS (w_H W5) mem6) (sp0 - 8 - 8 * j) =
Some (bv_unsigned (getr regs (nth (Z.to_nat j) sc_saved_regs 0%bv)))).
{ intros j Hj.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) _ (sp0 - 8 - 8 * j) ltac:(intros k Hk; apply KSAVE; lia)).
  exact (Hsaved j Hj). }
s6pres HPD 8 ((8%bv) : bv 5) P8D. rewrite R8C in P8D.
s6pres HPD 3 ((3%bv) : bv 5) P3D. rewrite R3C in P3D.
s6pres HPD 4 ((4%bv) : bv 5) P4D. rewrite R4C in P4D.
(* ---- run 4: the epilogue 0x831ac .. ret 0x831fc ---- *)
remember (Eimg (Ereg regs6 (s6_extra regs))) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = getr regs6 r)
by (intros k r Hk; subst E2; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 13)%nat -> ew E2 (32 + j) = getr regs (nth j sc_saved_regs 0%bv)).
{ intros j Hj. subst E2. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  unfold s6_extra. do 13 (destruct j as [|j]; [reflexivity|]). lia. }
assert (X0 : ew E2 32 = getr regs (1%bv : bv 5)) by (exact (EX 0%nat ltac:(lia))).
assert (X1 : ew E2 33 = getr regs (8%bv : bv 5)) by (exact (EX 1%nat ltac:(lia))).
assert (X2 : ew E2 34 = getr regs (9%bv : bv 5)) by (exact (EX 2%nat ltac:(lia))).
assert (X3 : ew E2 35 = getr regs (18%bv : bv 5)) by (exact (EX 3%nat ltac:(lia))).
assert (X4 : ew E2 36 = getr regs (19%bv : bv 5)) by (exact (EX 4%nat ltac:(lia))).
assert (X5 : ew E2 37 = getr regs (20%bv : bv 5)) by (exact (EX 5%nat ltac:(lia))).
assert (X6 : ew E2 38 = getr regs (21%bv : bv 5)) by (exact (EX 6%nat ltac:(lia))).
assert (X7 : ew E2 39 = getr regs (22%bv : bv 5)) by (exact (EX 7%nat ltac:(lia))).
assert (X8 : ew E2 40 = getr regs (23%bv : bv 5)) by (exact (EX 8%nat ltac:(lia))).
assert (X9 : ew E2 41 = getr regs (24%bv : bv 5)) by (exact (EX 9%nat ltac:(lia))).
assert (X10 : ew E2 42 = getr regs (25%bv : bv 5)) by (exact (EX 10%nat ltac:(lia))).
assert (X11 : ew E2 43 = getr regs (26%bv : bv 5)) by (exact (EX 11%nat ltac:(lia))).
assert (X12 : ew E2 44 = getr regs (27%bv : bv 5)) by (exact (EX 12%nat ltac:(lia))).
assert (U8D : bv_unsigned (ew E2 8) = sp0)
by (rewrite (EE2 8%nat 8%bv eq_refl), P8D; unfold w64; apply unsigned_lit_small; lia).
assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 2312 sr_atoms [s6_save_region] None (mkFacts [] [] []))
(restrict (w_H W5) (mkst regs6 (Z_to_bv 64 (BASE + 2312)) mem6 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, s6_save_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    rewrite U8D. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    unfold s6_stack_chunk.
    apply (chunk_ok_val SEGS E2 _ sp0 (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
      (bv_unsigned (getr regs (nth j sc_saved_regs 0%bv)))).
    + cbn [sv_denot]. rewrite (EX j ltac:(lia)), Z.add_0_r. reflexivity.
    + pose proof (bv_unsigned_in_range 64 (getr regs (nth j sc_saved_regs 0%bv))) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. change (8 * Z.of_N 8) with 64. lia.
    + change (Z.of_N 8) with 8. lia.
    + replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
      apply (val_mem_of_rdword SEGS (w_H W5) mem6).
      rewrite (Hsaved6 (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
  - cbn. tauto.
  - unfold facts_ok. cbn. tauto. }
paj_run_shc RUNP RUNC HS2 HJD.
{ intros a (r & Hin & Hr). cbn [ss_mem] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val s6_save_region] in Hr. exfalso. rewrite U8D in Hr. lia. }
rename ms into msD, HJD into HJD2, HFr into HFrD. clear HF HG.
(* ---- the ret at 0x831fc ---- *)
eapply (paj_ret_at (PL := PL_scene) (PI := PI) W5 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
intros matF.
unfold sc_ret. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T].
lazymatch goal with |- exists ly' S' regs' mem' md' ev', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists ly5, (stack_free_state 8 fpos S5), rg, mm, mdx, (ev + 1 + 1) end.
pose proof (ajournal_materialize SEGS B LAWS pa_segs_low (sw_stk WK) sp0 [] ly S W mem md []
  ly5 (stack_free_state 8 fpos S5) W5 (ms_mem msD) _ (ev + 1 + 1) matF HJD2) as HJF.
pose proof HJF as (HARF & HlyF & _ & HwleF & HIOF & _ & HnevF & _ & N1 & N2 & N3 & N4 & _).
pose proof (aos_step_closed [] _ _ sink_closed_nil HIOF) as (Efd & Efsys & _ & _).
prreg HS2 (1%bv : bv 5) Rra2. prreg HS2 (2%bv : bv 5) Rsp2. prreg HS2 (3%bv : bv 5) Rgp2.
prreg HS2 (4%bv : bv 5) Rtp2. prreg HS2 (10%bv : bv 5) Ra02.
split.
{ unfold cfg_at. f_equal. f_equal.
  rewrite Rra2, X0.
  unfold w64. unfold raZ in Hra. rewrite <- Hra, Z_to_bv_bv_unsigned. exact Hraok. }
unfold scene_tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
split; [exact HJF|].
split; [lia|].
split.
{ apply aregs_preserved_eqs.
  - rewrite Rsp2, (EE2 8%nat 8%bv eq_refl), P8D. unfold w64, spZ. apply Z_to_bv_bv_unsigned.
  - rewrite Rgp2, (EE2 3%nat 3%bv eq_refl), P3D. exact (eq_sym Hgp0).
  - rewrite Rtp2, (EE2 4%nat 4%bv eq_refl), P4D. exact (eq_sym Htp0).
  - prreg HS2 (8%bv : bv 5) Rr8. rewrite Rr8, X1. reflexivity.
  - prreg HS2 (9%bv : bv 5) Rr9. rewrite Rr9, X2. reflexivity.
  - prreg HS2 (18%bv : bv 5) Rr18. rewrite Rr18, X3. reflexivity.
  - prreg HS2 (19%bv : bv 5) Rr19. rewrite Rr19, X4. reflexivity.
  - prreg HS2 (20%bv : bv 5) Rr20. rewrite Rr20, X5. reflexivity.
  - prreg HS2 (21%bv : bv 5) Rr21. rewrite Rr21, X6. reflexivity.
  - prreg HS2 (22%bv : bv 5) Rr22. rewrite Rr22, X7. reflexivity.
  - prreg HS2 (23%bv : bv 5) Rr23. rewrite Rr23, X8. reflexivity.
  - prreg HS2 (24%bv : bv 5) Rr24. rewrite Rr24, X9. reflexivity.
  - prreg HS2 (25%bv : bv 5) Rr25. rewrite Rr25, X10. reflexivity.
  - prreg HS2 (26%bv : bv 5) Rr26. rewrite Rr26, X11. reflexivity.
  - prreg HS2 (27%bv : bv 5) Rr27. rewrite Rr27, X12. reflexivity. }
split; [exact Ra02|].
split.
{ unfold ablocks. rewrite blocks_stack_free_state. exact HPermC. }
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [unfold m_fs; rewrite Efsys; reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact HSORT0|].
split.
{ destruct HSNK0 as (HSNKv & HSNKp). split.
  - apply Forall_forall. intros (a0, w0) Hin0.
    pose proof (proj1 (Forall_forall _ _) HSNKv (a0, w0) Hin0) as Hv. cbn [fst snd] in Hv |- *.
    intros k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview SEGS).
    destruct (AIL (a0 + Z.of_nat k)
      ltac:(apply Exists_exists; exists (a0, w0); split; [exact Hin0 | unfold in_zr; cbn [fst snd]; lia]))
      as (Himg & Hns & Herr).
    exact (N3 (a0 + Z.of_nat k) Himg Hns Herr (fp_spares_closed [] _ sink_closed_nil)).
  - unfold m_fds. rewrite Efd. exact HSNKp. }
split; [exact I|].
intros i Hi.
destruct Hpn as [(Hn0 & _) | (Hnpos & Hpin)]; [exfalso; lia|].
apply (N2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym|].
  + unfold ablocks; rewrite blocks_stack_free_state; exact HPermC.
  + exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0 | Hne0]; [exfalso; lia | exact Hi].
- apply inFP_nil.
Qed.
End h.
End f.
End d.

(* ---- gate 6h: the theorem at scene's own sink head, musl's ofl_head 0x5f7190 of fuzz_scene.asan-ubsan (the
   value of lib/AU/P_LLVMFuzzerTestOneInput.v's scene_sink_head), passed by name, never by instance search. ---- *)
Definition s6_scene_sink_head : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head :=
{| OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sk_ofl_head := 0x5f7190 |}.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition llvmf_S6_scene := @llvmf_S6 fx rc s6_scene_sink_head.
End s.

Print Assumptions llvmf_S6.
Print Assumptions llvmf_S6_scene.
