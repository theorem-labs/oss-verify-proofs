(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx form of FMgxaSeamReady.v (readiness of the three interceptors at musl vfprintf's
   call, READY's clauses and seam_ready_holds), over the engine's allocator relation ARx with its laws
   YCbqG.AR_laws_x, the two side laws LAY / BANDP (FMgxaSeamARX.v proves both at reply's ARX) and the world field
   w_H8 as the Section hypothesis W_H8. The three ready predicates are reply's own (RT_gxa_calls_mem's copy_ready /
   set_ready, RT_gxa_calls' strn_ready), as in FMgxaSeamReady.v. FMgxaSeamReady.v is not edited.

   FMgxaSeamReady.v's AR-free lemmas are used from it (module RD), each under its own name by an Abbreviation, so that
   Section CX and this file's importers (RT_pf_snp_pcom / RT_pf_snp_srr, as SRy.<name>) read them unchanged: items 1-4
   of its header, FMgxaSeamReady.v :153-556 (sview, al8_shad_hull, hull_lo_le_hi, hull_sub, hull_prefix,
   qc_words_of_hull_m, chk_ok_of_pf_rng_loc, chk_ok_of_pf_rng_hull_m, aview_sview, qc_words_of_hull,
   chk_ok_of_pf_rng_hull, hull_in_shadow, hull_kept, pf_rng_app, hull_kept_v, copy_ready_intro_loc,
   set_ready_intro_loc, strn_ready_intro_loc, loc_of_view, copy_ready_intro_cjnormv, set_ready_intro_cjnormv,
   strn_ready_intro_cjnormv, bz_mrd_mbyte, le_byte1, nth_le_bytes, le8_nth, c8_of_val_mem, c1_of_val_mem,
   wview_of_mrd, rw_range, rw_of_ro, cells_cons, cells_cons8), and four AR-free lemmas of its Section C, :947-972
   (dest_tail_of_amem8, seam_dest_rng) and :1045-1058 (band_word, shadow_band). Until FMgxaSeamReady.v built (it reads
   the world field w_H8, which reply's world record now has), this file carried byte-identical copies of those 37
   lemmas (a working branch 1afa6c01fcd). W_H8 stays a Section hypothesis, so no consumer changes; the field
   discharges it by `fun W a H => w_H8 W a H`.

   Section CX is the conversion of FMgxaSeamReady.v Section C done by fuzz_preset (PSnpSeamReady.v :529-1155 and
   PSnpSeamReadyAR.v :140-216 at a working branch dad42dbecbc4) of a Theorem Labs lane's FMgxaSeamReady.v Section
   C (3242941dc964 :557-1264):
   - Section hypotheses (fm :557-560 `LAWS : AR_laws`, TB; preset :529-547): ARx, hl, `LAWS : YCbqG.AR_laws_x
     tfibsegs B ARx hl` (its fields alx_zshadow, alx_zshadow_byte, alx_const_cells are the ones read), LAY (preset's
     alx_layout_ok), BANDP (preset's alx_band_pres, PSnpSeamReady.v:542-543, verbatim), TB and W_H8 (preset
     :545-546, in the world field's form). preset's stk_bounds_x hypothesis is FMgxaSeamNormX.stk_bounds_x at LAY.
   - every `ecall_preU tfibsegs B ly S U W regs mem md` -> `FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md`,
     `ARU tfibsegs B ly S U W mem md` -> `ARx ly S Hp W mem md`, binder U -> Hp; destructs `((HAR & ..) & HUOK & HUP)`
     -> `(HAR & ..)` (ecall_pre_x is one flat conjunction); FMupoison.stk_kHighMemBeg (ARm's am_layout) ->
     stk_bounds_x.
   - the runtime cells (fm :564-667, preset :549-653): owned_agree (the image's owned writable bytes, held through
     YG0q.const_cells_owned, which is ARm-internal) -> data_agree (every byte of the image's writable data
     [0x9d000, 0x5fb000), reply's read-only top and GLOBALS_TOP = 0x5fb000, NM.globals_top_A), and the destination
     is kept off that range by the added premise DIMG `D + dn <= 65536 \/ GLOBALS_TOP <= D` (GXA's own requirement
     on the destination) in place of dest_ok's ~ aowned; AF0x.tfib_const_lookup (ARm's am_const) -> const_lookup_x
     from the law alx_const_cells (preset's PSnpRodata.const_lookup_lx, lib/A/PSnpRodata.v:53-58); owned_agree_seam
     -> data_agree_seam (no ARU_mem_low: ARx is over mem itself). DIMG is threaded through seam_cells, every clause
     and seam_ready_holds (its last premise), as in preset.
   - the stack (fm :669-747, preset ReadyAR :148-196): stack_view0 from the law alx_zshadow_byte (in place of
     am_zshadow at the stack range, ARU_view_out, ARU_shadow_out_block, ARU_stack_not_block); stack_hull /
     stack_rng from LAY (in place of am_layout); stack_rng_v unchanged but for ARx.
   - the prefix (fm :749-775, preset ReadyAR :198-216): prefix_hull from the law alx_zshadow (no in_ush /
     ARU_poisoned split).
   - word_vis (fm :1064-1113, preset :953-1001): the image env tfib_img_env by vm_compute (in place of AR's
     al_img_env); the layout from LAY; the client / non-client split and ahs_pres become the one law BANDP for a
     byte not in_vis0; the in_vis0 case (NM.vis0_word_pres_cjnormv) is unchanged but over mem; w_H8 -> W_H8.
   - the clauses (fm :777-1039, :1115-1263; preset :672-940, :1003-1153): the substitutions above only.
   Added, with no fm / preset counterpart: munch_win_dest and seam_ready_holds_at, READY at a store derived from the
   per-call store cjnormv ly R by a munch over the footprint that keeps the shadow (the seam's assembly needs it).
   Not carried from preset: its Section R stand-ins for the three ready predicates (copy_ready_def / set_ready_def
   / strn_ready_def, PSnpSeamReady.v:266-292; reply has the predicates themselves), and nothing of preset's memnorm
   keep or arodata_okP layers (no Section C lemma of either file names them). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YG0q YI04 YA0n YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
AB1v AF0m AF0x FMupoison RT_IImgA FMgxaSeamBase FMgxaSeamShadow.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Common.PropExec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.Shadow.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memcpyw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memsetw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Spec.StrFun.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNormG.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNormX.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamGuard.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamReady.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module GAF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Module GCC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Module BSh := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.Shadow.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module BK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Module BMW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNorm.
Module NG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNormG.
Module NMX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNormX.
(* this file does not Import RStep, where the image's symbol map `sym` lives *)
Module RSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module FMM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Module RSN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module SG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamGuard.
Module BSF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Spec.StrFun.
Module MN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module GXI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GCA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GV := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Module BzPE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Common.PropExec.
Module BzI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
(* the AR form, whose AR-free lemmas this file uses *)
Module RD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamReady.
(* strn_ready counts with the Bz tree's strnlen_res (RT_gxa_strnlen.v:100) *)
#[local] Abbreviation strnlen_res := BSF.strnlen_res.

#[local] Existing Instance A_img.

(* ===================================================================================== *)
(* 1. FMgxaSeamReady.v's AR-free lemmas, used from it                                    *)
(* ===================================================================================== *)

(* items 1-4 of FMgxaSeamReady.v's header (its :153-556) and four AR-free lemmas of its Section C (:947-972,
   :1045-1058), under their own names: Section CX below and this file's importers read them unchanged *)
Abbreviation sview := RD.sview.
Abbreviation al8_shad_hull := RD.al8_shad_hull.
Abbreviation hull_lo_le_hi := RD.hull_lo_le_hi.
Abbreviation hull_sub := RD.hull_sub.
Abbreviation hull_prefix := RD.hull_prefix.
Abbreviation qc_words_of_hull_m := RD.qc_words_of_hull_m.
Abbreviation chk_ok_of_pf_rng_loc := RD.chk_ok_of_pf_rng_loc.
Abbreviation chk_ok_of_pf_rng_hull_m := RD.chk_ok_of_pf_rng_hull_m.
Abbreviation aview_sview := RD.aview_sview.
Abbreviation qc_words_of_hull := RD.qc_words_of_hull.
Abbreviation chk_ok_of_pf_rng_hull := RD.chk_ok_of_pf_rng_hull.
Abbreviation hull_in_shadow := RD.hull_in_shadow.
Abbreviation hull_kept := RD.hull_kept.
Abbreviation pf_rng_app := RD.pf_rng_app.
Abbreviation hull_kept_v := RD.hull_kept_v.
Abbreviation copy_ready_intro_loc := RD.copy_ready_intro_loc.
Abbreviation set_ready_intro_loc := RD.set_ready_intro_loc.
Abbreviation strn_ready_intro_loc := RD.strn_ready_intro_loc.
Abbreviation loc_of_view := RD.loc_of_view.
Abbreviation copy_ready_intro_cjnormv := RD.copy_ready_intro_cjnormv.
Abbreviation set_ready_intro_cjnormv := RD.set_ready_intro_cjnormv.
Abbreviation strn_ready_intro_cjnormv := RD.strn_ready_intro_cjnormv.
Abbreviation bz_mrd_mbyte := RD.bz_mrd_mbyte.
Abbreviation le_byte1 := RD.le_byte1.
Abbreviation nth_le_bytes := RD.nth_le_bytes.
Abbreviation le8_nth := RD.le8_nth.
Abbreviation c8_of_val_mem := RD.c8_of_val_mem.
Abbreviation c1_of_val_mem := RD.c1_of_val_mem.
Abbreviation wview_of_mrd := RD.wview_of_mrd.
Abbreviation rw_range := RD.rw_range.
Abbreviation rw_of_ro := RD.rw_of_ro.
Abbreviation cells_cons := RD.cells_cons.
Abbreviation cells_cons8 := RD.cells_cons8.
Abbreviation dest_tail_of_amem8 := RD.dest_tail_of_amem8.
Abbreviation seam_dest_rng := RD.seam_dest_rng.
Abbreviation band_word := RD.band_word.
Abbreviation shadow_band := RD.shadow_band.

Section CX. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable hl : Z.
(* the engine's laws (top_x's ARX_laws at reply's instance); the fields read are alx_zshadow, alx_zshadow_byte and
   alx_const_cells *)
Hypothesis LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl.
(* the layout is layout_ok (preset's AR_laws_x field alx_layout_ok; FMgxaSeamARX.ARX_LAY at reply's instance) *)
Hypothesis LAY : forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly.
(* the shadow band's presence (preset's alx_band_pres, verbatim; FMgxaSeamARX.ARX_BANDP at reply's instance) *)
Hypothesis BANDP : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None.
Hypothesis TB : TfibSyms B.
(* the world's w_H8 field in its field form (a Theorem Labs lane's YA0n.v:27; reply's world record gains it on
   a working branch): a Section hypothesis until that branch lands, discharged then by
   `fun W a H => w_H8 W a H` *)
Hypothesis W_H8 : forall (W : world tfibsegs) a, in_band_rw a -> w_H W (Z_to_bv 64 a) = w_H W (Z_to_bv 64 (a - a mod 8)).

(* ---- the runtime cells ---- *)

(* the image's constant table holds in the harness's restricted store (the law alx_const_cells; preset's
   PSnpRodata.const_lookup_lx) *)
Lemma const_lookup_x : forall ly S Hp (W : world tfibsegs) mem md a (w : nat) v,
  ARx ly S Hp W mem md ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S Hp W mem md a w v HAR E.
apply (cell_holds_val_mem B ly (w_H W) mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly))
         (YCbqG.alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.

(* a store that agrees with the harness's restricted store on the image's writable data [0x9d000, 0x5fb000)
   (GLOBALS_TOP = 0x5fb000, NM.globals_top_A) holds the runtime's cells.  fm's form took only the owned bytes
   (YG0q.const_cells_owned, ARm-internal); here the destination is kept off that range by READY's premise
   D + dn <= 65536 \/ GLOBALS_TOP <= D instead *)
Definition data_agree (m0 m' : word -> option byte) : Prop :=
  forall x : word, 0x9d000 <= bv_unsigned x < 0x5fb000 -> m' x = m0 x.

Lemma val_mem_const_at : forall ly S Hp (W : world tfibsegs) mem md (m' : word -> option byte) a (w : nat) v,
  ARx ly S Hp W mem md -> data_agree (mrestrict (w_H W) mem) m' ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  0x9d000 <= a -> a + Z.of_nat w <= 0x5fb000 ->
  val_mem tfibsegs m' a w v.
Proof.
intros ly S Hp W mem md m' a w v HAR AG E Ha Haw.
pose proof (const_lookup_x ly S Hp W mem md a w v HAR E) as V.
intros k Hk.
assert (Hx : bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)) = a + Z.of_nat k) by (apply wz; lia).
specialize (V k Hk). unfold mbyte in V |- *.
rewrite (AG (Z_to_bv 64 (a + Z.of_nat k))); [exact V | rewrite Hx; lia].
Qed.

Lemma ro_c8_at : forall ly S Hp (W : world tfibsegs) mem md (m' : word -> option byte) a v,
  ARx ly S Hp W mem md -> data_agree (mrestrict (w_H W) mem) m' ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
  0x9d000 <= a -> a + 8 <= 0x5fb000 -> 0 <= v < 2 ^ 64 ->
  BzSt.ro_cells BzI.asegs m' a [BzCl.C8 (Z_to_bv 64 v)].
Proof.
intros ly S Hp W mem md m' a v M AG E H1 H2 Hv. apply c8_of_val_mem; [lia | lia | exact Hv |].
exact (val_mem_const_at ly S Hp W mem md m' a 8 v M AG E H1 ltac:(lia)).
Qed.

Lemma ro_c1_at : forall ly S Hp (W : world tfibsegs) mem md (m' : word -> option byte) a v,
  ARx ly S Hp W mem md -> data_agree (mrestrict (w_H W) mem) m' ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
  0x9d000 <= a -> a + 1 <= 0x5fb000 -> 0 <= v < 256 ->
  BzSt.ro_cells BzI.asegs m' a [BzCl.C1 (Z_to_bv 8 v)].
Proof.
intros ly S Hp W mem md m' a v M AG E H1 H2 Hv. apply c1_of_val_mem; [lia | lia | exact Hv |].
exact (val_mem_const_at ly S Hp W mem md m' a 1 v M AG E H1 ltac:(lia)).
Qed.

Local Ltac c8 M AG := eapply (ro_c8_at _ _ _ _ _ _ _ _ _ M AG); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M AG := eapply (ro_c1_at _ _ _ _ _ _ _ _ _ M AG); [vm_compute; reflexivity | lia | lia | lia].

(* the six cell predicates the three ready predicates carry *)
Lemma cells_of_agree : forall ly S Hp (W : world tfibsegs) mem md (m' : word -> option byte),
  ARx ly S Hp W mem md -> data_agree (mrestrict (w_H W) mem) m' ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros ly S Hp W mem md m' M AG.
split; [|split; [|split; [|split; [|split]]]].
- unfold BR.m2s_cells, BSh.SHB, BR.kHighMemEnd.
  split; [|split]; (apply rw_of_ro; [|vm_compute; reflexivity]).
  + apply cells_cons8; [c8 M AG|]. apply cells_cons8; [c8 M AG|]. apply cells_cons8; [c8 M AG|]. c8 M AG.
  + c8 M AG.
  + apply cells_cons8; [c8 M AG|]. apply cells_cons8; [c8 M AG|]. c8 M AG.
- unfold BMW.icells. split; [c8 M AG|]. split; [c8 M AG|]. split; [c8 M AG|]. split; [c8 M AG | c1 M AG].
- unfold BSW.icells_ms. split; [c8 M AG|]. split; [c8 M AG|]. split; [c8 M AG|]. split; [c8 M AG | c1 M AG].
- unfold BNW.icells_sn. split; [c8 M AG|]. split; [c8 M AG|]. split; [c8 M AG|].
  split; [apply rw_of_ro; [c1 M AG | vm_compute; reflexivity] | c1 M AG].
- unfold BCW.icells_mc. split; [c8 M AG|]. split; [c8 M AG|].
  split; [c8 M AG | apply rw_of_ro; [c1 M AG | vm_compute; reflexivity]].
- unfold BNW.icells_sns. c8 M AG.
Qed.

(* READY's store: a munch of cjnormv over the footprint keeps every byte of the image's writable data (the stack
   window, the FILE and the cookie are high; the destination is off the image's data, DIMG).  Those bytes are
   application memory, where cjnormv drops exactly what cjnorm drops (NM.seam_drop_app) *)
Lemma data_agree_seam : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo -> lo <= spZ regs ->
  spZ regs <= Fp -> Fp + 232 <= CK ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  data_agree (mrestrict (w_H W) mem) m'.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo Hq HFp HCK DIMG MU x Hx.
pose proof HPRE as (HAR & _).
pose proof (NMX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as SK.
rewrite NM.globals_top_A in DIMG.
rewrite (MU x).
- unfold NM.cjnormv, NG.gdrop_normalize.
  rewrite (NM.seam_drop_app ly R x ltac:(unfold GAF.app_mem, GAF.LOWMEM_END; lia)).
  rewrite (NM.keep_of_writable x (NM.ro_addr_off x ltac:(lia)) ltac:(unfold TASK_SIZE; lia)).
  unfold cjstore, mrestrict. destruct (w_H W x); reflexivity.
- unfold GV.vf_snf_fp. cbn [CJF.outside]. unfold kHighMemBeg in SK.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma seam_cells : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo -> lo <= spZ regs ->
  spZ regs <= Fp -> Fp + 232 <= CK ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo Hq HFp HCK DIMG MU.
pose proof HPRE as (HAR & _).
exact (cells_of_agree ly S Hp W mem md m' HAR
         (data_agree_seam ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo Hq HFp HCK DIMG MU)).
Qed.

(* ---- the stack: the law alx_zshadow_byte over [ly_stk_lo, ly_stk_hi), both ends page-aligned (layout_ok's
   lo_top) ---- *)
Lemma stack_view0 : forall ly S Hp (W : world tfibsegs) mem md a, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= a < ly_stk_hi ly -> aview tfibsegs (w_H W) mem (shadow_addr a) = Some 0.
Proof.
intros ly S Hp W mem md a HAR Ha.
replace (shadow_addr a) with (SHADOW_OFF + a / 8) by (unfold shadow_addr; reflexivity).
exact (YCbqG.alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md a HAR Ha).
Qed.

(* the hull of a stack range is visible: every byte of it is a shadow byte of the stack *)
Lemma stack_hull : forall ly S Hp (W : world tfibsegs) mem md x n, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= x -> 0 < n -> x + n <= ly_stk_hi ly ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros ly S Hp W mem md x n HAR Hx Hn Hxn.
pose proof (LAY ly S Hp W mem md HAR) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold page_aligned in T5, T6.
intros s Hs.
assert (Ea : shadow_addr (8 * (s - SHADOW_OFF)) = s)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
assert (Ha : ly_stk_lo ly <= 8 * (s - SHADOW_OFF) < ly_stk_hi ly).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF. clear - Hs Hx Hn Hxn T5 T6.
  Z.div_mod_to_equations. lia. }
rewrite <- Ea, (stack_view0 ly S Hp W mem md _ HAR Ha). discriminate.
Qed.

(* a stack range is addressable for GXA and its hull is visible *)
Lemma stack_rng : forall ly S Hp (W : world tfibsegs) mem md x n, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= x -> 0 <= n -> x + n + 9 <= ly_stk_hi ly ->
  GAF.pf_rng (cjstore (w_H W) mem) x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros ly S Hp W mem md x n HAR Hx Hn Hxn.
pose proof (LAY ly S Hp W mem md HAR) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_stk_ceil ly LO) as SC. pose proof ASAN_CEIL_range as [CR _].
unfold page_aligned in T5, T6.
split.
- apply pf_rng_of_view.
  + unfold kHighMemBeg in T7. lia.
  + exact Hn.
  + unfold kHighMemEnd in T4. lia.
  + right. split; lia.
  + intros y Hy. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF y) with (shadow_addr y) by (unfold shadow_of_addr, shadow_addr; lia).
    apply (stack_view0 ly S Hp W mem md y HAR). lia.
- intros Hn0. exact (stack_hull ly S Hp W mem md x n HAR Hx Hn0 ltac:(lia)).
Qed.

(* the same at the per-call store, for a stack range inside the window R carves out: its shadow
   bytes and its hull are kept, so pf_rng and the hull cross to cjnormv *)
Lemma stack_rng_v : forall ly R S Hp (W : world tfibsegs) mem md (lo q : Z) x n,
  ARx ly S Hp W mem md -> NM.sd_hull_kept ly R lo (q - lo) ->
  ly_stk_lo ly <= lo -> lo <= x -> 0 <= n -> x + n <= q -> x + n + 9 <= ly_stk_hi ly ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) x n /\
  (0 < n -> NM.sd_hull_kept ly R x n) /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros ly R S Hp W mem md lo q x n HU KW Hlo Hx Hn Hxn Hq.
destruct (stack_rng ly S Hp W mem md x n HU ltac:(lia) Hn ltac:(lia)) as [PF HV].
assert (KH : 0 < n -> NM.sd_hull_kept ly R x n)
  by (intros Hn0; exact (NM.sd_hull_kept_sub ly R lo (q - lo) x n KW ltac:(lia) ltac:(lia) ltac:(lia))).
split; [|split; [exact KH | exact HV]].
apply (NM.pf_rng_cjnormv ly R (w_H W) mem x n); [|exact PF].
intros i Hi. exact (NM.sh_kept_of_hull ly R x n (KH ltac:(lia)) i Hi).
Qed.

(* the musl prefix's hull: the nine bytes at sym 0x1029e = 0x10b54 have their hull in the shadow of the image's
   first zero-shadow range [0x10000, 0x20eb0), which the law alx_zshadow fills with 0 *)
Lemma prefix_hull : forall ly S Hp (W : world tfibsegs) mem md,
  TfibSyms B -> ARx ly S Hp W mem md ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) (@RSt.sym A_img 0x1029e) 9.
Proof.
intros ly S Hp W mem md HTB HAR.
pose proof (YCbqG.alx_zshadow _ _ _ LAWS ly S Hp W mem md (0x10000, 0x20eb0 - 0x10000) HAR
              ltac:(unfold zero_shadow_ranges; right; exact (zsh_rodata_of_tfib B HTB))) as HZ0.
cbn [fst snd] in HZ0. unfold zero_shadow in HZ0.
rewrite sym_musl_prefix. intros s Hs.
assert (Hr : 0x10000 <= 8 * (s - SHADOW_OFF) < 0x20eb0).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF. clear - Hs. Z.div_mod_to_equations. lia. }
assert (E : shadow_of_addr SHADOW_OFF 0x10000 + (s - SHADOW_OFF - 0x10000 / 8) = s)
  by (unfold shadow_of_addr; clear - Hr; Z.div_mod_to_equations; lia).
assert (Hv : aview tfibsegs (w_H W) mem s = Some 0)
  by (rewrite <- E; apply HZ0; clear - Hr; Z.div_mod_to_equations; lia).
rewrite Hv. discriminate.
Qed.

(* ---- the clauses.  Premises: READY's (FMgxaSeam.v:318-327) and DIMG, only those each clause uses ---- *)

(* memcpy from ranges whose pf_rng and hull are known: the whole of copy_ready but the two ranges *)
Lemma seam_copy_of_rng : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 -> 0 <= N ->
    (N = 0 \/ Dst + N <= sp - 64 - GCC.COPY_DEPTH \/ sp - 64 <= Dst) ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) Dst N -> (0 < N -> NM.sd_hull_kept ly R Dst N) ->
    (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) Dst N) ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> (0 < N -> NM.sd_hull_kept ly R P N) ->
    (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG MU MK
  sp Dst P N H1 H2 HN SEP PD KD VD PP KP VP.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by exact (NMX.stk_bounds_x ARx LAY ly S Hp W mem md HAR).
destruct (seam_cells ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo ltac:(unfold GCA.OUT_DEPTH in HGEO; lia)
            HFp HCK DIMG MU) as (C1 & C2 & _).
apply (copy_ready_intro_loc m' (sp - 64) Dst P N N N).
- unfold BR.kHighShadowEnd, GCC.COPY_DEPTH. unfold GCA.OUT_DEPTH in H1. unfold kHighMemBeg in SK. lia.
- unfold kHighMemEnd in SK. lia.
- exact HN.
- unfold GCC.COPY_DEPTH in SEP |- *. lia.
- exact (GAF.pf_rng_kept _ _ Dst N PD MK).
- exact (GAF.pf_rng_kept _ _ P N PP MK).
- lia.
- lia.
- intros Hn0. exact (hull_kept_v ly R (w_H W) mem m' Dst N MK (KD Hn0) Hn0 (pf_rng_app _ Dst N PD) (VD Hn0)).
- intros Hn0. exact (hull_kept_v ly R (w_H W) mem m' P N MK (KP Hn0) Hn0 (pf_rng_app _ P N PP) (VP Hn0)).
- exact C1.
- exact C2.
Qed.

(* CLOSES: memcpy into vfprintf's buffer from that buffer or from printf_core's stack (both inside
   the stack window [lo, spZ regs), which R carves out) *)
Lemma seam_ready_copy_stack : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 ->
    spZ regs - 352 <= Dst /\ Dst + N <= spZ regs - 352 + GXI.SNF_CAP -> 0 <= N ->
    (P = spZ regs - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= spZ regs - 368) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG KW MU MK
  sp Dst P N H1 H2 [HD1 HD2] HN HP.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
pose proof HAR as HU.
assert (G1 : lo + 4640 <= sp) by exact H1.
assert (G2 : lo + 4640 <= spZ regs - 368) by exact HGEO.
assert (G3 : Dst + N <= spZ regs - 352 + 80) by exact HD2.
destruct (stack_rng_v ly R S Hp W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia) ltac:(lia))
  as (PD & KD & VD).
assert (PS : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N /\ (0 < N -> NM.sd_hull_kept ly R P N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N)).
{ change GXI.SNF_CAP with 80 in HP.
  destruct HP as [[-> HP]|[HP1 HP2]];
    apply (stack_rng_v ly R S Hp W mem md lo (spZ regs) _ N HU KW Hlo); lia. }
destruct PS as (PP & KP & VP).
exact (seam_copy_of_rng ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG MU MK
         sp Dst P N H1 H2 HN ltac:(right; right; lia) PD KD VD PP KP VP).
Qed.

(* CLOSES: memset on printf_core's stack *)
Lemma seam_ready_set : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst N, lo + GSC.SET_DEPTH <= sp -> sp <= Dst -> Dst + N + 8 <= spZ regs - 368 ->
    FMM.set_ready m' sp Dst N.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG KW MU MK sp Dst N H1 H2 H3.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
pose proof HAR as HU.
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by exact (NMX.stk_bounds_x ARx LAY ly S Hp W mem md HAR).
unfold GCA.OUT_DEPTH, GSC.SET_DEPTH in *.
destruct (seam_cells ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo ltac:(lia) HFp HCK DIMG MU)
  as (C1 & _ & C3 & _).
destruct (Z_le_gt_dec 0 N) as [HN|HN]; [|intros HN'; lia].
destruct (stack_rng_v ly R S Hp W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia) ltac:(lia))
  as (PD & KD & VD).
apply (set_ready_intro_cjnormv ly R (w_H W) mem m' sp Dst N N MK).
- unfold BR.kHighShadowEnd, GSC.SET_DEPTH. unfold kHighMemBeg in SK. lia.
- unfold kHighMemEnd in SK. lia.
- exact HN.
- right; right. exact H2.
- exact (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem Dst N PD)).
- exact (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem Dst N PD)).
- lia.
- exact KD.
- exact VD.
- exact C1.
- exact C3.
Qed.

(* the copy clause in full, given what READY does not carry: the hull of every range addressable in
   the per-call store (the source a guard clause names by pf_rng only) *)
Lemma seam_ready_copy_hull : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) -> (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) -> NM.sd_hull_kept ly R D (Z.of_nat dn) ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) D (Z.of_nat dn) ->
  (0 < Z.of_nat dn -> shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn)) ->
  (forall P N, GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> 0 < N ->
     shadow_hull_vis (aview tfibsegs (w_H W) mem) P N) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 ->
    (D <= Dst /\ Dst + N <= D + Z.of_nat dn \/ spZ regs - 352 <= Dst /\ Dst + N <= spZ regs - 352 + GXI.SNF_CAP) ->
    0 <= N ->
    (P = spZ regs - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= spZ regs - 368 \/
     GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG HSEP KW KDD PDD VDD HULL MU MK
  sp Dst P N H1 H2 HDst HN HP.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
pose proof HAR as HU.
assert (DR : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) Dst N /\ (0 < N -> NM.sd_hull_kept ly R Dst N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) Dst N) /\
             (N = 0 \/ Dst + N <= sp - 64 - GCC.COPY_DEPTH \/ sp - 64 <= Dst)).
{ destruct HDst as [[HD1 HD2]|[HD1 HD2]].
  - split; [|split; [|split]].
    + replace Dst with (D + (Dst - D)) by lia.
      exact (GAF.pf_rng_sub _ D (Z.of_nat dn) (Dst - D) N PDD ltac:(lia) HN ltac:(lia)).
    + intros Hn0. exact (NM.sd_hull_kept_sub ly R D (Z.of_nat dn) Dst N KDD HD1 Hn0 ltac:(lia)).
    + intros Hn0. exact (hull_sub _ D (Z.of_nat dn) Dst N (VDD ltac:(lia)) HD1 Hn0 HD2).
    + unfold GCA.OUT_DEPTH, GCC.COPY_DEPTH in *. lia.
  - unfold GXI.SNF_CAP, GCA.OUT_DEPTH in *.
    destruct (stack_rng_v ly R S Hp W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia)
                ltac:(lia)) as (PD & KD & VD).
    split; [exact PD|]. split; [exact KD|]. split; [exact VD | lia]. }
destruct DR as (PD & KD & VD & SEP).
assert (PR : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N /\ (0 < N -> NM.sd_hull_kept ly R P N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N)).
{ destruct HP as [[-> HP]|[[HP1 HP2]|HP]].
  - unfold GXI.SNF_CAP, GCA.OUT_DEPTH in *.
    exact (stack_rng_v ly R S Hp W mem md lo (spZ regs) (spZ regs - 352) N HU KW Hlo ltac:(lia) HN
             ltac:(lia) ltac:(lia)).
  - unfold GCA.OUT_DEPTH in *.
    exact (stack_rng_v ly R S Hp W mem md lo (spZ regs) P N HU KW Hlo ltac:(lia) HN ltac:(lia)
             ltac:(lia)).
  - split; [exact HP|]. split; [|exact (HULL P N HP)].
    intros Hn0.
    exact (NM.hull_of_sh_kept ly R P N (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP))
             Hn0 (pf_rng_app _ P N (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP)))). }
destruct PR as (PP & KP & VP).
exact (seam_copy_of_rng ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG MU MK
         sp Dst P N H1 H2 HN SEP PD KD VD PP KP VP).
Qed.

(* the memcpy clause from READY's premises, through seam_ready_copy_hull: the destination's facts that
   lemma takes come from READY (seam_dest_rng, the hull, and R's carve-out); the hull of a source
   named only by pf_rng (HULL) is still seam_ready_copy_hull's own premise *)
Lemma seam_ready_dest : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) -> NM.sd_hull_kept ly R D (Z.of_nat dn) ->
  amem_range D (Z.of_nat dn) -> amem_range D (Z.of_nat dn + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D (Z.of_nat dn) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn) -> 0 <= D -> Z.of_nat dn <= 2 ^ 40 ->
  (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
  (forall P N, GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> 0 < N ->
     shadow_hull_vis (aview tfibsegs (w_H W) mem) P N) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 ->
    (D <= Dst /\ Dst + N <= D + Z.of_nat dn \/ spZ regs - 352 <= Dst /\ Dst + N <= spZ regs - 352 + GXI.SNF_CAP) ->
    0 <= N ->
    (P = spZ regs - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= spZ regs - 368 \/
     GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG KW KDD HAM HAM8 HRA HV HD0 HDN
  HSEP HULL MU MK.
apply (seam_ready_copy_hull ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG HSEP KW KDD
         (NM.pf_rng_cjnormv ly R (w_H W) mem D (Z.of_nat dn) (NM.sh_kept_of_hull ly R D (Z.of_nat dn) KDD)
            (seam_dest_rng (w_H W) mem D dn HD0 HDN HAM HAM8 HRA))
         (fun _ => HV) HULL MU MK).
Qed.

(* the strnlen clause, given what it does not carry: the hull of the bytes strnlen checks *)
Lemma seam_ready_strn_hull : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp S0 N L buf, lo + GNC.STRN_DEPTH <= sp -> sp <= spZ regs - 368 ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) S0 L -> Z.min (strnlen_res N buf + 1) N <= L ->
    (0 < Z.min (strnlen_res N buf + 1) N ->
       shadow_hull_vis (aview tfibsegs (w_H W) mem) S0 (Z.min (strnlen_res N buf + 1) N)) ->
    RSN.strn_ready m' sp S0 N buf.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG MU MK sp S0 N L buf H1 H2 PR HL VS.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by exact (NMX.stk_bounds_x ARx LAY ly S Hp W mem md HAR).
destruct (seam_cells ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo ltac:(unfold GCA.OUT_DEPTH in HGEO; lia)
            HFp HCK DIMG MU) as (C1 & _ & _ & C4 & C5 & C6).
destruct (NM.pf_rng_cjnormv_back ly R (w_H W) mem S0 L PR) as [PR0 KS].
apply (strn_ready_intro_loc m' sp S0 N L buf); try assumption.
- unfold BR.kHighShadowEnd. unfold GNC.STRN_DEPTH in *. unfold kHighMemBeg in SK. lia.
- unfold kHighMemEnd in SK. lia.
- exact (GAF.pf_rng_kept _ _ S0 L PR MK).
- intros Hk.
  apply (hull_kept_v ly R (w_H W) mem m' S0 _ MK
           (NM.sd_hull_kept_sub ly R S0 L S0 (Z.min (strnlen_res N buf + 1) N)
              (NM.hull_of_sh_kept ly R S0 L KS ltac:(lia) (pf_rng_app _ S0 L PR0))
              ltac:(lia) ltac:(lia) ltac:(lia))
           Hk); [|exact (VS Hk)].
  exact (GAF.app_ivl_sub S0 (S0 + L) S0 (S0 + Z.min (strnlen_res N buf + 1) N)
           (pf_rng_app _ S0 L PR0) ltac:(lia) ltac:(lia)).
Qed.

(* ===================================================================================== *)
(* 6. the hull of a range named only by pf_rng (W_H8, BANDP) and READY                    *)
(* ===================================================================================== *)

(* the image's segments lie in [4096, kImgEnd) (the image env aview_band and aview_band_hidden need; fm took it from
   AR's ledger, al_img_env; here it is a fact about tfibsegs, by vm_compute) *)
Lemma tfib_img_env : forall sg, In sg tfibsegs ->
  4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd.
Proof.
assert (E : forallb (fun sg => (4096 <=? Z.of_N (seg_base sg)) && (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? kImgEnd))
              tfibsegs = true) by (vm_compute; reflexivity).
intros sg Hin. rewrite forallb_forall in E. specialize (E sg Hin).
apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.

(* a byte of the 8-aligned shadow word of a byte s0 the per-call store holds is readable.  The presence ARx's laws
   do not carry (a visible in_vis0 band byte, which ahs_pres, YG0n.v:442-444, and so BANDP leave out) is exactly
   what cjnormv's own drop gives back: it drops such a byte unless a hull of R carves it out, so s0 present in
   cjnormv puts s in a visible hull of R (FMgxaSeamNorm.vis0_word_pres_cjnormv) *)
Lemma word_vis : forall ly R S Hp (W : world tfibsegs) mem md s0 s,
  ARx ly S Hp W mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  in_band_rw s0 -> s / 8 = s0 / 8 ->
  NM.cjnormv ly R (w_H W) mem (Z_to_bv 64 s0) <> None ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
intros ly R S Hp W mem md s0 s HAR HVR Hb0 E P0v.
pose proof tfib_img_env as IMG.
pose proof (LAY ly S Hp W mem md HAR) as LO.
pose proof (band_word s0 s Hb0 E) as Hb.
(* s0 is readable in the harness's store: cjnormv holds it, so the restricted store does *)
assert (R0 : aview tfibsegs (w_H W) mem s0 <> None).
{ pose proof (NM.cjnormv_store ly R (w_H W) mem (Z_to_bv 64 s0) P0v) as X.
  unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 s0)) as [b|] eqn:Em;
    [cbn; discriminate | exfalso; exact (X Em)]. }
(* s0 is visible and present, so by W_H8 s is visible *)
assert (Hh0 : w_H W (Z_to_bv 64 s0) = false).
{ destruct (w_H W (Z_to_bv 64 s0)) eqn:Eh; [|reflexivity]. exfalso.
  exact (R0 (aview_band_hidden tfibsegs (w_H W) mem s0 IMG Hb0 Eh)). }
assert (Hh : w_H W (Z_to_bv 64 s) = false).
{ assert (E8 : s - s mod 8 = s0 - s0 mod 8) by (rewrite (Z.mod_eq s 8), (Z.mod_eq s0 8) by lia; lia).
  rewrite (W_H8 W s Hb), E8, <- (W_H8 W s0 Hb0). exact Hh0. }
assert (NNEM : forall P : Prop, ~ ~ (P \/ ~ P))
  by (intros P k; apply k; right; intros p; apply k; left; exact p).
intros Hn. apply (NNEM (in_vis0 ly s)). intros [V|NV].
- (* in_vis0: cjnormv keeps s, because it kept s0 and the hulls of R are visible *)
  apply (proj2 (aview_band tfibsegs (w_H W) mem s IMG Hb Hh)); [|exact Hn].
  intros Em.
  apply (NM.vis0_word_pres_cjnormv ly R (w_H W) mem LO HVR s s0 Hb V E Hh P0v).
  unfold NM.cjnormv, NG.gdrop_normalize. cbv beta.
  destruct (NM.seam_drop ly R (Z_to_bv 64 s)); [reflexivity|].
  unfold cjstore, mrestrict. rewrite Hh. exact Em.
- (* not in_vis0: the shadow band's presence (BANDP) *)
  exact (BANDP ly S Hp W mem md s HAR Hb Hh NV Hn).
Qed.

(* the hull of a range named only by pf_rng at the per-call store *)
Lemma hull_of_pf_rng_H8 : forall ly R S Hp (W : world tfibsegs) mem md P N,
  ARx ly S Hp W mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> 0 < N ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) P N.
Proof.
intros ly R S Hp W mem md P N HU HVR PF HN s Hs.
destruct (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N PF) as [PF0 _].
destruct PF0 as (_ & (_ & _ & _ & AD) & _ & _).
(* each byte of the range has its shadow byte in the band and held by cjnormv *)
assert (RB : forall i, 0 <= i < N ->
             in_band_rw (shadow_addr (P + i)) /\
             NM.cjnormv ly R (w_H W) mem (Z_to_bv 64 (shadow_addr (P + i))) <> None).
{ intros i Hi. destruct (AD i Hi) as (APP & _).
  split; [exact (shadow_band _ APP) | exact (NM.cjnormv_present_of_pf_rng ly R (w_H W) mem P N i PF Hi)]. }
destruct (Z_lt_le_dec s (shadow_addr P)) as [L1|L1].
- (* the aligned word of the first byte's shadow byte *)
  destruct (RB 0 ltac:(lia)) as [B0 R0]. rewrite Z.add_0_r in B0, R0.
  apply (word_vis ly R S Hp W mem md (shadow_addr P) s HU HVR B0); [|exact R0].
  clear - Hs L1. Z.div_mod_to_equations. lia.
- destruct (Z_le_gt_dec s (shadow_addr (P + N - 1))) as [L2|L2].
  + (* the shadow byte of a byte of the range *)
    assert (Hx : exists i, 0 <= i < N /\ shadow_addr (P + i) = s).
    { clear - L1 L2 HN. unfold shadow_addr, SHADOW_OFF in *.
      destruct (Z_le_gt_dec (8 * (s - 2147450880)) P) as [K|K].
      - exists 0. rewrite Z.add_0_r. split; [lia|]. Z.div_mod_to_equations. lia.
      - exists (8 * (s - 2147450880) - P). split; [Z.div_mod_to_equations; lia|].
        replace (P + (8 * (s - 2147450880) - P)) with ((s - 2147450880) * 8) by lia.
        rewrite Z.div_mul by lia. lia. }
    destruct Hx as (i & Hi & Es). destruct (RB i Hi) as [Bi Ri]. rewrite Es in Bi, Ri.
    exact (word_vis ly R S Hp W mem md s s HU HVR Bi eq_refl Ri).
  + (* the aligned word of the last byte's shadow byte *)
    destruct (RB (N - 1) ltac:(lia)) as [B1 R1].
    replace (P + (N - 1)) with (P + N - 1) in B1, R1 by lia.
    apply (word_vis ly R S Hp W mem md (shadow_addr (P + N - 1)) s HU HVR B1); [|exact R1].
    clear - Hs L2. Z.div_mod_to_equations. lia.
Qed.

(* the quick check's two aligned shadow words at any store that keeps the per-call store's shadow *)
Lemma qc_words_of_pf_rng_H8 : forall ly R S Hp (W : world tfibsegs) mem md (m' : word -> option byte) P N,
  ARx ly S Hp W mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> BQ.qc_words m' P N.
Proof.
intros ly R S Hp W mem md m' P N HU HVR MK PF.
destruct (Z_lt_le_dec 0 N) as [HN|HN]; [|intros [Hn _]; lia].
pose proof PF as (_ & (Hp0 & _ & Hpn & _) & _). unfold GAF.APPMEM_END in Hpn.
destruct (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N PF) as [PF0 KS].
apply (qc_words_of_hull_m m' P N Hp0 HN ltac:(lia)).
apply (hull_kept_v ly R (w_H W) mem m' P N MK
         (NM.hull_of_sh_kept ly R P N KS HN (pf_rng_app _ P N PF0)) HN (pf_rng_app _ P N PF0)).
exact (hull_of_pf_rng_H8 ly R S Hp W mem md P N HU HVR PF HN).
Qed.

(* the memcpy clause with the source hull from W_H8: seam_ready_dest without its HULL premise *)
Lemma seam_ready_copy : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) -> NM.sd_hull_kept ly R D (Z.of_nat dn) ->
  amem_range D (Z.of_nat dn) -> amem_range D (Z.of_nat dn + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D (Z.of_nat dn) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn) -> 0 <= D -> Z.of_nat dn <= 2 ^ 40 ->
  (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 ->
    (D <= Dst /\ Dst + N <= D + Z.of_nat dn \/ spZ regs - 352 <= Dst /\ Dst + N <= spZ regs - 352 + GXI.SNF_CAP) ->
    0 <= N ->
    (P = spZ regs - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= spZ regs - 368 \/
     GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD DIMG KW KDD HAM HAM8 HRA HV HD0 HDN
  HSEP MU MK.
pose proof HPRE as (HAR & _).
pose proof HAR as HU.
exact (seam_ready_dest ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG KW KDD HAM HAM8 HRA
         HV HD0 HDN HSEP (fun P N PF HN => hull_of_pf_rng_H8 ly R S Hp W mem md P N HU HVR PF HN) MU MK).
Qed.

(* the strnlen clause with the hull from W_H8: seam_ready_strn_hull without its hull premise *)
Lemma seam_ready_strn : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp S0 N L buf, lo + GNC.STRN_DEPTH <= sp -> sp <= spZ regs - 368 ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) S0 L -> Z.min (strnlen_res N buf + 1) N <= L ->
    RSN.strn_ready m' sp S0 N buf.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD DIMG MU MK sp S0 N L buf H1 H2 PR HL.
pose proof HPRE as (HAR & _).
pose proof HAR as HU.
apply (seam_ready_strn_hull ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG MU MK
         sp S0 N L buf H1 H2 PR HL).
intros Hk.
apply (hull_prefix _ S0 L _ (hull_of_pf_rng_H8 ly R S Hp W mem md S0 L HU HVR PR ltac:(lia))). lia.
Qed.

(* READY (FMgxaSeam.v) at reply's three predicates, for any carve-out list R that holds the destination and the
   stack window and whose hulls the harness sees; its last premise DIMG keeps the destination off the image's data *)
Theorem seam_ready_holds : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md ->
  In (D, Z.of_nat dn) R -> In (lo, spZ regs - lo) R ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 ->
  (forall a, lo <= a < spZ regs -> apresent (w_H W) mem a) ->
  spZ regs <= Fp -> Fp + 232 <= CK -> CK + 16 <= GAF.APPMEM_END ->
  dest_ok tfibsegs B ly S W regs mem Fp 232 -> dest_ok tfibsegs B ly S W regs mem CK 16 ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  amem_range D (Z.of_nat dn) -> amem_range D (Z.of_nat dn + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D (Z.of_nat dn) ->
  0 <= D -> Z.of_nat dn <= 2 ^ 40 ->
  (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  SG.seam_calls_ready FMM.copy_ready FMM.set_ready RSN.strn_ready
    (NM.cjnormv ly R (w_H W) mem) (spZ regs) lo Fp CK D dn.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn HPRE InD InW HVR Hlo HGEO _ HFp HCK _ _ _ DD HAM HAM8 HRA
  HD0 HDN HSEP DIMG.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by exact (NMX.stk_bounds_x ARx LAY ly S Hp W mem md HAR).
assert (HV : shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn))
  by exact (proj1 (Forall_forall _ _) HVR (D, Z.of_nat dn) InD).
assert (KDD : NM.sd_hull_kept ly R D (Z.of_nat dn)).
{ apply (NM.hull_kept_carved ly R (D, Z.of_nat dn) InD); cbn [fst snd]; [lia|].
  exact (NM.amem_app D (Z.of_nat dn) HD0 HAM). }
assert (KW : NM.sd_hull_kept ly R lo (spZ regs - lo)).
{ apply (NM.hull_kept_carved ly R (lo, spZ regs - lo) InW); cbn [fst snd].
  - unfold kHighMemBeg in SK. lia.
  - unfold GAF.APPMEM_END. unfold kHighMemEnd in SK. lia. }
unfold SG.seam_calls_ready. intros m' MU _ MK.
split; [|split].
- exact (seam_ready_copy ly R S Hp W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD DIMG KW KDD
           HAM HAM8 HRA HV HD0 HDN HSEP MU MK).
- exact (seam_ready_set ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG KW MU MK).
- intros sp S0 N L buf H1 H2 PR HL.
  exact (seam_ready_strn ly R S Hp W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD DIMG MU MK
           sp S0 N L buf H1 H2 PR HL).
Qed.

(* ---- READY at a store derived from the per-call store ---- *)

(* a munch over the stack window and the destination is a munch over vfprintf's whole footprint *)
Lemma munch_win_dest : forall lo q Fp CK D (dn : nat) (m0 m1 : word -> option byte),
  CJF.munch [(lo, q); (D, D + Z.of_nat dn)] m0 m1 -> CJF.munch (GV.vf_snf_fp lo q Fp CK D dn) m0 m1.
Proof.
intros lo q Fp CK D dn m0 m1 MU x Hx. apply MU.
unfold GV.vf_snf_fp in Hx. cbn [CJF.outside] in Hx |- *. tauto.
Qed.

(* READY at any store m1 that a munch over the footprint reaches from the per-call store cjnormv ly R and that keeps
   its shadow (a store the assembly reaches after earlier writes to the stack window or the destination; for a munch
   over [(lo, q); (D, D + dn)] only, munch_win_dest).  seam_calls_ready at m1 quantifies over the stores m' a further
   munch reaches from m1; m' is a munch of cjnormv ly R itself (CJF.munch_trans), with its shadow (meta_kept_trans),
   and a range addressable in m1 is addressable in cjnormv ly R (pf_rng_kept, the shadow being the same).  No wmono
   from cjnormv ly R to m1 is asked: no clause reads it. *)
Theorem seam_ready_holds_at : forall ly R S Hp (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m1 : word -> option byte),
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md ->
  In (D, Z.of_nat dn) R -> In (lo, spZ regs - lo) R ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 ->
  (forall a, lo <= a < spZ regs -> apresent (w_H W) mem a) ->
  spZ regs <= Fp -> Fp + 232 <= CK -> CK + 16 <= GAF.APPMEM_END ->
  dest_ok tfibsegs B ly S W regs mem Fp 232 -> dest_ok tfibsegs B ly S W regs mem CK 16 ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  amem_range D (Z.of_nat dn) -> amem_range D (Z.of_nat dn + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D (Z.of_nat dn) ->
  0 <= D -> Z.of_nat dn <= 2 ^ 40 ->
  (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP A_img <= D) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m1 ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m1 ->
  SG.seam_calls_ready FMM.copy_ready FMM.set_ready RSN.strn_ready m1 (spZ regs) lo Fp CK D dn.
Proof.
intros ly R S Hp W regs mem md lo Fp CK D dn m1 HPRE InD InW HVR Hlo HGEO _ HFp HCK _ _ _ DD HAM HAM8 HRA
  HD0 HDN HSEP DIMG MU1 MK1.
pose proof HPRE as (HAR & _ & _ & _ & HSPhi & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by exact (NMX.stk_bounds_x ARx LAY ly S Hp W mem md HAR).
assert (HV : shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn))
  by exact (proj1 (Forall_forall _ _) HVR (D, Z.of_nat dn) InD).
assert (KDD : NM.sd_hull_kept ly R D (Z.of_nat dn)).
{ apply (NM.hull_kept_carved ly R (D, Z.of_nat dn) InD); cbn [fst snd]; [lia|].
  exact (NM.amem_app D (Z.of_nat dn) HD0 HAM). }
assert (KW : NM.sd_hull_kept ly R lo (spZ regs - lo)).
{ apply (NM.hull_kept_carved ly R (lo, spZ regs - lo) InW); cbn [fst snd].
  - unfold kHighMemBeg in SK. lia.
  - unfold GAF.APPMEM_END. unfold kHighMemEnd in SK. lia. }
assert (MK10 : GAF.meta_kept m1 (NM.cjnormv ly R (w_H W) mem)) by (intros a Ha; symmetry; exact (MK1 a Ha)).
unfold SG.seam_calls_ready. intros m' MU _ MK.
pose proof (CJF.munch_trans _ _ _ _ MU1 MU) as MU0.
pose proof (GAF.meta_kept_trans _ _ _ MK1 MK) as MK0.
split; [|split].
- intros sp Dst P N H1 H2 HDst HN HP.
  apply (seam_ready_copy ly R S Hp W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD DIMG KW KDD
           HAM HAM8 HRA HV HD0 HDN HSEP MU0 MK0 sp Dst P N H1 H2 HDst HN).
  destruct HP as [HP|[HP|HP]]; [left; exact HP | right; left; exact HP |].
  right; right. exact (GAF.pf_rng_kept _ _ P N HP MK10).
- exact (seam_ready_set ly R S Hp W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD DIMG KW MU0 MK0).
- intros sp S0 N L buf H1 H2 PR HL.
  exact (seam_ready_strn ly R S Hp W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD DIMG MU0 MK0
           sp S0 N L buf H1 H2 (GAF.pf_rng_kept _ _ S0 L PR MK10) HL).
Qed.

End CX.
