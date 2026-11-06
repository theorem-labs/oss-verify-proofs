(* The NORMALIZATION layer of the GXA seam at musl vfprintf.

   GXA's statement (lib/CJ/RL/GXA/VfprintfCall.v:22 vfprintf_guarded_stmt) asks `mem_inv img_segs m`
   (VfprintfCall.v:37) of the store it runs on.  For the harness's store m = cjstore (w_H W) mem that
   is not derivable (FMgxaSeamInv.v).  So the seam runs GXA on the NORMALIZED store
     cjnorm H mem := MemNorm.normalize_cj tfibsegs (cjstore H mem)        (lib/MemNorm.v:534)
   which drops every stored byte at a read-only address and every stored byte above TASK_SIZE outside
   the image (MemNorm.cj_drop, :527).  mem_inv holds of it by construction (mem_inv_cjnorm).  This file
   moves the run and every fact between the two stores:
   1. read agreement (MemNorm.ro_agree, :41) from the contract's own consts_view
      (FMsnprintfShared.v:115), when the constant list cr covers the image's read-only bytes
      (ro_agree_of_consts; fm's instance ro_covered_fm);
   2. the normalized store and its invariant (cjnorm, mem_inv_cjnorm);
   3. each store premise of GXA's statement and of its guard vf_ready_a, from m to cjnorm H mem.
      Two generic facts carry them: a read agrees at every address below TASK_SIZE under ro_agree
      (mrd_cjnorm) and at every kept address without it (mrd_cjnorm_keep); a write view agrees at
      every kept address (wview_cjnorm).  A not-read-only address below TASK_SIZE is kept
      (keep_of_writable).  The extra conditions each premise needs are in its statement;
   4. the run: GXA's evt from cjnorm H mem gives an evt from the harness's store, ending in a state
      related to GXA's (MemNorm.ms_rel_cj) that keeps the dropped bytes (MemNorm.cj_same), in the
      shape FMgxa_bridge.srr_of_gxa_evt consumes (evt_from_norm, srr_of_norm_evt);
   5. GXA's post read at the harness's final state (post_from_norm), and the harness's view there
      (view_from_norm);
   6. the VIS0-aware store cjnormv ly R H mem := FMgxaSeamNormG.gdrop_normalize (seam_drop ly R)
      (cjstore H mem): cjnorm's drops plus every shadow byte whose 8-aligned word meets ly_vis0,
      except the aligned shadow hulls of the carve-out list R; its invariant, the premise
      transfers, the run and the post, each the cjnorm form at seam_drop ly R (the *_cjnormv and
      *_v lemmas);
   7. what seam_drop keeps (seam_drop_keeps): at the seam's R (seam_R: the destination, the format,
      the stack window, the musl prefix, each %s string) the hull of every range whose shadow the
      walk reads, and every application byte cjnorm keeps; and the way back from cjnormv to the
      harness's store (pf_rng_cjnormv_back, cjnormv_present_of_pf_rng, hull_cjnormv);
   8. the presence AR does not carry, at cjnormv (vis0_word_pres_cjnormv), from layout_ok and the
      hulls of R visible; FMgxaSeamReady.word_vis is its consumer.

   The guard's readiness hypothesis PSnpSeamGuard.seam_calls_ready is not transferred: its
   consumers state it at the normalized store (vf_ready_cjnorm takes it at cjnorm H mem,
   vf_ready_cjnormv at cjnormv ly R H mem). *)
(* Modified by Theorem Labs, 2026-10: copied to omx-clap-core/fuzz_preset as lib/AU/PSnpSeamNorm.v (image B) from port-fm's lib/A/FMgxaSeamNorm.v (origin/cold/port-fm-rtprintf-param 3e35620c52e) under SEAM-SPLIT R1-R7: module paths fuzz_manifest -> fuzz_preset; RT_IImgA / A_img -> lib/CJ/RL/I/IImgB / N_img_asan; FMgxa_bridge / FMgxaSeamBase / FMgxaSeamCall / FMgxaSeamGuard -> lib/AU/PSnpGxaBridge / PSnpSeamBase / PSnpSeamCall / PSnpSeamGuard; FMsnprintfShared / FMgxaSeamPf / FMgxaSeamNormG -> lib/Reusable/PSnpShared / PSnpSeamPf / PSnpSeamNormG (the family constructors fmt_at / pf_arg_asan / pf_args_asan from lib/Reusable/PSnpPfFam.v, as PSnpSeamDef takes them); FMupoison dropped. Its one AR fact, layout_of_preU, is over ARx: FCiface.ecall_pre_x and the Section hypothesis alx_layout_ok (YCbqG.ARx_layout_ok_law). Numerals relocated to this image (R7): the read-only segments' top 0x99000 -> 0xa1000 (the r-x segment's end, page-rounded: A 0xa04b0, B 0xa0d4c), the segments' top 0x677000 -> 0x600000 (last segment's end page-rounded: A 0x5ff1b0, B 0x5ffa70), GLOBALS_TOP = sym 0x35000 = 0x600000, got_ssp = sym 0x22e18 = 0xa2ff8, ssp_guard = sym 0x34288 = 0x5fe1d0, musl's prefix sym 0x1029e = 0x10b7c, each checked by vm_compute; 0x22e18 / 0x1029e / 0x35000 themselves are GXA's sym keys; and SnpxDefs's one cross-group change (parent 15:2xZ): GXA's argument list is PSnpSeamPf.pt_pargs ps args, so args_kept_of_asan and seam_drop_keeps take any pa with Forall2 GPF.pt_parg_rel args pa (PA_u, the %04x arm, is a non-string arm). This file walks no machine step and reads no runtime-option cell (relocation rule 15:22Z). *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpSeamNorm.v.reloc.tsv. Comment numerals are as written. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YP02 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm CJBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require
PropExec MState Mem Exec Frame Cells Step FP Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require
Printf_model G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require
AsanFacts G_printf_core_common G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpGxaBridge PSnpSeamBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require PSnpShared.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PSnpSeamCall PSnpSeamGuard.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require FMsnprintfPf PSnpSeamPf PSnpSeamNormG PSnpPfFam.
(* Required, not Imported: ecall_pre_x and the layout law, by qualified name (SEAM-SPLIT R4-R5) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require FCiface YCbqG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* lib/Lib and lib/CJ/Lib have modules of the same short names; every one is named by its full path *)
Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.MemNorm.
Module LE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Module CJP := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.PropExec.
Module CJMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.MState.
Module CJM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.
Module CJE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Exec.
Module CJF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Frame.
Module CJC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Cells.
Module CJS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.
Module CJFP := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.FP.
Module CJA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Arr.
Module PR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.Prelim.
Module GPAD := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_pad.
Module GPOP := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_pop_arg.
Module GFP := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.
Module PM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.Printf_model.
Module GXI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVX := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_vfprintf_snf.
Module AF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.AsanFacts.
Module GC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_snfsink.
Module GV := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_vfprintf_snf.
Module NG := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.PSnpSeamNormG.
Module SPF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.FMsnprintfPf.
Module SSH := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.PSnpShared.
(* the family constructors fmt_at / pf_arg_asan / pf_args_asan (fm's FMsnprintfShared.v:42-69) live in PSnpPfFam.v *)
Module SFF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.PSnpPfFam.
Module GPF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.PSnpSeamPf.

#[local] Existing Instance N_img_asan.

(* ===================================================================================== *)
(* 0. fm.asan's segments                                                                   *)
(* ===================================================================================== *)

(* MemNorm's W^X side condition: no writable executable segment overlaps a read-only one *)
Lemma wx_apart_tfib : MN.wx_apart tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* every read-only segment lies in [0x10000, 0xa1000) (AE3h.v:1353 tfib_rom_low gives the top) *)
Lemma tfib_ro_range : forall x : word, CJM.ro_addr tfibsegs x = true -> 0x10000 <= bv_unsigned x < 0xa2000.
Proof.
assert (F : forallb (fun seg => seg_writable seg ||
                                ((0x10000 <=? Z.of_N (seg_base seg)) &&
                                 (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 0xa2000)))%bool tfibsegs = true)
  by (vm_compute; reflexivity).
intros x Hx. unfold CJM.ro_addr in Hx.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:Hf; [|discriminate Hx].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & H1 & H2).
pose proof (proj1 (forallb_forall _ _) F seg Hin) as Hs. cbv beta in Hs.
apply negb_true_iff in Hx. rewrite Hx in Hs. cbn [orb] in Hs.
apply andb_prop in Hs as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
Qed.

Lemma ro_addr_off : forall x : word,
  bv_unsigned x < 0x10000 \/ 0xa2000 <= bv_unsigned x -> CJM.ro_addr tfibsegs x = false.
Proof.
intros x Hx. destruct (CJM.ro_addr tfibsegs x) eqn:E; [|reflexivity].
pose proof (tfib_ro_range x E). lia.
Qed.

(* GXA's GLOBALS_TOP on N_img_asan (RT_IImgA.v:73) *)
Lemma globals_top_A : @GXI.GLOBALS_TOP N_img_asan = 0x601000.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================================== *)
(* 1. read agreement from the contract's consts_view                                      *)
(* ===================================================================================== *)

(* the static side condition on the contract's constant list: it covers every read-only byte *)
Definition ro_covered (cr : list (Z * Z)) : Prop :=
  forall a : word, CJM.ro_addr tfibsegs a = true -> Exists (in_zr (bv_unsigned a)) cr.

(* fm's instance: the one range [0x10000, 0xa1000) *)
Lemma ro_covered_fm : ro_covered [(0x10000, 0xa2000 - 0x10000)].
Proof.
intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
pose proof (tfib_ro_range a Ha). lia.
Qed.

Section RA. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ro_agree_of_consts : forall (W : world tfibsegs) mem cr,
  PSnpShared.consts_view tfibsegs W mem cr -> ro_covered cr ->
  MN.ro_agree tfibsegs (cjstore (w_H W) mem).
Proof.
intros W mem cr HC Hcov a Hro.
pose proof (HC (bv_unsigned a) (Hcov a Hro)) as E.
rewrite aview_mrd in E.
assert (Ha : CJM.wa (bv_unsigned a) = a) by (unfold CJM.wa; apply Z_to_bv_bv_unsigned).
rewrite Ha, Z_to_bv_bv_unsigned in E.
change (CJM.mrd tfibsegs (cjstore (w_H W) mem) a = YK11.seg_rom tfibsegs a).
revert E.
destruct (CJM.mrd tfibsegs (cjstore (w_H W) mem) a) as [b|], (YK11.seg_rom tfibsegs a) as [c|];
  cbn [option_map]; intros E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

End RA.

(* ===================================================================================== *)
(* 2. the normalized store and its invariant                                               *)
(* ===================================================================================== *)

Definition cjnorm (H : word -> bool) (mem : word -> option byte) : word -> option byte :=
  MN.normalize_cj tfibsegs (cjstore H mem).

Lemma mem_inv_cjnorm : forall H mem, CJM.mem_inv tfibsegs (cjnorm H mem).
Proof.
intros H mem. apply CJM.mem_inv_intro. intros a b E.
exact (MN.mem_inv_cj_normalize tfibsegs (cjstore H mem) a b E).
Qed.

Lemma mem_rel_cjnorm : forall H mem, MN.ro_agree tfibsegs (cjstore H mem) ->
  MN.mem_rel_cj tfibsegs (cjstore H mem) (cjnorm H mem).
Proof. intros H mem Hro. exact (MN.mem_rel_cj_normalize tfibsegs (cjstore H mem) Hro). Qed.

(* ===================================================================================== *)
(* 3. premise transfers m -> cjnorm H mem                                                  *)
(* ===================================================================================== *)

(* ---- the two generic facts ---- *)
Lemma mrd_cjnorm_keep : forall H mem (a : word), MN.cj_drop tfibsegs a = false ->
  CJM.mrd tfibsegs (cjnorm H mem) a = CJM.mrd tfibsegs (cjstore H mem) a.
Proof. intros H mem a E. unfold CJM.mrd, cjnorm, MN.normalize_cj. cbv beta. rewrite E. reflexivity. Qed.

(* a read below TASK_SIZE (or inside the image) agrees; MemNorm.mrd_normalize_cj over lib/Lib *)
Lemma mrd_cjnorm : forall H mem (a : word), MN.ro_agree tfibsegs (cjstore H mem) ->
  find_segment tfibsegs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE ->
  CJM.mrd tfibsegs (cjnorm H mem) a = CJM.mrd tfibsegs (cjstore H mem) a.
Proof. intros H mem a Hro Ha. exact (MN.mrd_normalize_cj tfibsegs (cjstore H mem) a Hro (or_intror Ha)). Qed.

(* a write view agrees at every address the normalization keeps *)
Lemma wview_cjnorm : forall H mem (a : word), MN.cj_drop tfibsegs a = false ->
  wview tfibsegs (cjnorm H mem) a = wview tfibsegs (cjstore H mem) a.
Proof. intros H mem a E. unfold wview, cjnorm, MN.normalize_cj. cbv beta. rewrite E. reflexivity. Qed.

(* a writable (not read-only) address below TASK_SIZE is never dropped *)
Lemma keep_of_writable : forall a : word, CJM.ro_addr tfibsegs a = false -> bv_unsigned a < TASK_SIZE ->
  MN.cj_drop tfibsegs a = false.
Proof. intros a H1 H2. exact (MN.cj_drop_false_intro tfibsegs a H1 (or_intror H2)). Qed.

(* ---- kept ranges ---- *)
Definition cj_kept (lo hi : Z) : Prop := forall x, lo <= x < hi -> MN.cj_drop tfibsegs (CJM.wa x) = false.

Lemma cj_kept_sub : forall lo hi lo' hi', cj_kept lo hi -> lo <= lo' -> hi' <= hi -> cj_kept lo' hi'.
Proof. intros lo hi lo' hi' K H1 H2 x Hx. apply K. lia. Qed.

(* a range below TASK_SIZE that misses the read-only part of the image is kept *)
Lemma cj_kept_off_ro : forall lo hi, 0 <= lo -> hi <= TASK_SIZE -> (hi <= 0x10000 \/ 0xa2000 <= lo) ->
  cj_kept lo hi.
Proof.
intros lo hi H0 H1 H2 x Hx.
assert (Hu : bv_unsigned (CJM.wa x) = x) by (apply CJM.wa_unsigned; unfold TASK_SIZE in H1; lia).
apply keep_of_writable; [apply ro_addr_off|]; rewrite Hu; lia.
Qed.

(* GXA's windows: the stack, the FILE and the cookie lie at or above GLOBALS_TOP *)
Lemma cj_kept_high : forall lo hi, @GXI.GLOBALS_TOP N_img_asan <= lo -> hi <= TASK_SIZE -> cj_kept lo hi.
Proof. intros lo hi H1 H2. rewrite globals_top_A in H1. apply cj_kept_off_ro; lia. Qed.

(* GXA's destination: below the image or at or above GLOBALS_TOP (VfprintfCall.v:42) *)
Lemma cj_kept_dest : forall D n, 0 <= D -> D + n <= TASK_SIZE ->
  (D + n <= 65536 \/ @GXI.GLOBALS_TOP N_img_asan <= D) -> cj_kept D (D + n).
Proof. intros D n H0 H1 H2. rewrite globals_top_A in H2. apply cj_kept_off_ro; lia. Qed.

Lemma cj_kept_check : forall lo n,
  forallb (fun i => negb (MN.cj_drop tfibsegs (CJM.wa (lo + Z.of_nat i)))) (seq 0 n) = true ->
  cj_kept lo (lo + Z.of_nat n).
Proof.
intros lo n F x Hx. rewrite forallb_forall in F.
assert (Hin : In (Z.to_nat (x - lo)) (seq 0 n)) by (apply in_seq; lia).
specialize (F _ Hin). rewrite Z2Nat.id in F by lia. replace (lo + (x - lo)) with x in F by lia.
apply negb_true_iff in F. exact F.
Qed.

(* ---- bytes, writability, cells, stack ---- *)
Lemma bytes_at_cjnorm : forall H mem a bs, MN.ro_agree tfibsegs (cjstore H mem) ->
  a + Z.of_nat (length bs) <= TASK_SIZE ->
  CJM.bytes_at tfibsegs (cjstore H mem) a bs -> CJM.bytes_at tfibsegs (cjnorm H mem) a bs.
Proof. intros H mem a bs Hro Hl Hb. exact (MN.bytes_at_normalize_cj_low tfibsegs (cjstore H mem) a bs Hro Hl Hb). Qed.

Lemma bytes_at_cjnorm_kept : forall H mem a bs, cj_kept a (a + Z.of_nat (length bs)) ->
  CJM.bytes_at tfibsegs (cjstore H mem) a bs -> CJM.bytes_at tfibsegs (cjnorm H mem) a bs.
Proof.
intros H mem a bs K (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
rewrite mrd_cjnorm_keep by (apply K; lia). exact (H3 i Hi).
Qed.

Lemma wr_at_cjnorm : forall H mem a n, cj_kept a (a + n) ->
  CJM.wr_at tfibsegs (cjstore H mem) a n -> CJM.wr_at tfibsegs (cjnorm H mem) a n.
Proof.
intros H mem a n K (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
rewrite wview_cjnorm by (apply K; lia). exact (H3 i Hi).
Qed.

Lemma rw_cells_cjnorm : forall H mem A cs, cj_kept A (A + Z.of_nat (CJC.cells_size cs)) ->
  CJS.rw_cells tfibsegs (cjstore H mem) A cs -> CJS.rw_cells tfibsegs (cjnorm H mem) A cs.
Proof.
intros H mem A cs K ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
- apply bytes_at_cjnorm_kept; [|exact Hb]. rewrite CJC.cells_bytes_length by exact Hwf. exact K.
- exact (wr_at_cjnorm H mem A _ K Hw).
Qed.

Lemma stk_cjnorm : forall H mem lo hi, cj_kept lo hi ->
  CJF.stk tfibsegs (cjstore H mem) lo hi -> CJF.stk tfibsegs (cjnorm H mem) lo hi.
Proof.
intros H mem lo hi K (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
rewrite wview_cjnorm, mrd_cjnorm_keep by exact (K a Ha). exact (H3 a Ha).
Qed.

(* ---- GXA's premises, one by one (VfprintfCall.v:29-38) ---- *)
Lemma snf_file_size : forall bufp CK, CJC.cells_size (@GVX.snf_file N_img_asan bufp CK) = 232%nat.
Proof. reflexivity. Qed.

(* rw_cells img_segs m Fp (snf_file bufp CK) *)
Lemma file_cjnorm : forall H mem Fp bufp CK, @GXI.GLOBALS_TOP N_img_asan <= Fp -> Fp + 232 <= TASK_SIZE ->
  CJS.rw_cells tfibsegs (cjstore H mem) Fp (GVX.snf_file bufp CK) ->
  CJS.rw_cells tfibsegs (cjnorm H mem) Fp (GVX.snf_file bufp CK).
Proof.
intros H mem Fp bufp CK H1 H2 R. apply rw_cells_cjnorm; [|exact R].
rewrite snf_file_size. exact (cj_kept_high Fp (Fp + 232) H1 H2).
Qed.

(* rw_cells img_segs m CK [C8 D; C8 N] *)
Lemma cookie_cjnorm : forall H mem CK v1 v2, @GXI.GLOBALS_TOP N_img_asan <= CK -> CK + 16 <= TASK_SIZE ->
  CJS.rw_cells tfibsegs (cjstore H mem) CK [CJC.C8 v1; CJC.C8 v2] ->
  CJS.rw_cells tfibsegs (cjnorm H mem) CK [CJC.C8 v1; CJC.C8 v2].
Proof. intros H mem CK v1 v2 H1 H2 R. apply rw_cells_cjnorm; [exact (cj_kept_high CK (CK + 16) H1 H2) | exact R]. Qed.

(* rw_cells img_segs m D [CB dn bs] *)
Lemma dest_cjnorm : forall H mem D dn bs, 0 <= D -> D + Z.of_nat dn <= TASK_SIZE ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP N_img_asan <= D) ->
  CJS.rw_cells tfibsegs (cjstore H mem) D [CJC.CB dn bs] ->
  CJS.rw_cells tfibsegs (cjnorm H mem) D [CJC.CB dn bs].
Proof.
intros H mem D dn bs H0 H1 H2 R. apply rw_cells_cjnorm; [|exact R].
cbn [CJC.cells_size CJC.csize]. rewrite Nat.add_0_r. exact (cj_kept_dest D (Z.of_nat dn) H0 H1 H2).
Qed.

(* bytes_at img_segs m A (zb fmt), the format in the image: GXA's own A + |fmt| <= GLOBALS_TOP bounds it *)
Lemma fmt_cjnorm : forall H mem A (fmt : list Z), MN.ro_agree tfibsegs (cjstore H mem) ->
  A + PR.zlength fmt <= @GXI.GLOBALS_TOP N_img_asan ->
  CJM.bytes_at tfibsegs (cjstore H mem) A (GFP.zb fmt) -> CJM.bytes_at tfibsegs (cjnorm H mem) A (GFP.zb fmt).
Proof.
intros H mem A fmt Hro Hl Hb. apply bytes_at_cjnorm; [exact Hro| |exact Hb].
rewrite globals_top_A in Hl. unfold GFP.zb. rewrite length_map. unfold PR.zlength in Hl. unfold TASK_SIZE. lia.
Qed.

(* va_area m VA slots *)
Lemma va_area_cjnorm : forall H mem VA slots, MN.ro_agree tfibsegs (cjstore H mem) ->
  VA + 8 * PR.zlength slots <= TASK_SIZE ->
  GPOP.va_area (cjstore H mem) VA slots -> GPOP.va_area (cjnorm H mem) VA slots.
Proof.
intros H mem VA slots Hro Hl Hv. unfold GPOP.va_area in *.
apply bytes_at_cjnorm; [exact Hro| |exact Hv].
rewrite CJA.u64s_length. unfold PR.zlength in Hl. lia.
Qed.

(* stk img_segs m lo q *)
Lemma stk_window_cjnorm : forall H mem lo q, @GXI.GLOBALS_TOP N_img_asan <= lo -> q <= TASK_SIZE ->
  CJF.stk tfibsegs (cjstore H mem) lo q -> CJF.stk tfibsegs (cjnorm H mem) lo q.
Proof. intros H mem lo q H1 H2 S. exact (stk_cjnorm H mem lo q (cj_kept_high lo q H1 H2) S). Qed.

(* ssp_cells m canary: both cells are in writable image segments, so no condition *)
Lemma ssp_kept : cj_kept (@GPAD.got_ssp N_img_asan) (@GPAD.got_ssp N_img_asan + 8) /\
                 cj_kept (@GPAD.ssp_guard N_img_asan) (@GPAD.ssp_guard N_img_asan + 8).
Proof.
split.
- apply (cj_kept_check (@GPAD.got_ssp N_img_asan) 8). vm_compute. reflexivity.
- apply (cj_kept_check (@GPAD.ssp_guard N_img_asan) 8). vm_compute. reflexivity.
Qed.

Lemma ssp_cells_cjnorm : forall H mem canary,
  GPAD.ssp_cells (cjstore H mem) canary -> GPAD.ssp_cells (cjnorm H mem) canary.
Proof.
intros H mem canary [S1 S2]. destruct ssp_kept as [K1 K2].
split; [apply rw_cells_cjnorm; [exact K1 | exact S1] | apply rw_cells_cjnorm; [exact K2 | exact S2]].
Qed.

(* ---- the ASan shadow: every shadow byte is kept, so no condition ---- *)
Lemma shadow_kept : forall a, AF.in_shadow a -> MN.cj_drop tfibsegs (CJM.wa a) = false.
Proof.
intros a Ha.
assert (Hr : 0xa2000 <= a /\ a + 1 <= TASK_SIZE)
  by (unfold AF.in_shadow, AF.LOWMEM_END, AF.LOWSHADOW_END, AF.HIGHSHADOW_BEG, AF.HIGHMEM_BEG in Ha;
      unfold TASK_SIZE; lia).
apply (cj_kept_off_ro a (a + 1)); lia.
Qed.

Lemma meta_kept_cjnorm : forall H mem, AF.meta_kept (cjstore H mem) (cjnorm H mem).
Proof. intros H mem a Ha. exact (mrd_cjnorm_keep H mem _ (shadow_kept a Ha)). Qed.

Lemma addressable_cjnorm : forall H mem p n,
  AF.addressable (cjstore H mem) p n -> AF.addressable (cjnorm H mem) p n.
Proof. intros H mem p n Hp. exact (AF.addressable_kept _ _ p n Hp (meta_kept_cjnorm H mem)). Qed.

(* pf_rng m A |fmt| (the guard) *)
Lemma pf_rng_cjnorm : forall H mem p n, AF.pf_rng (cjstore H mem) p n -> AF.pf_rng (cjnorm H mem) p n.
Proof. intros H mem p n Hp. exact (AF.pf_rng_kept _ _ p n Hp (meta_kept_cjnorm H mem)). Qed.

(* musl_prefix_addressable m (the guard) *)
Lemma musl_prefix_cjnorm : forall H mem,
  AF.musl_prefix_addressable (cjstore H mem) -> AF.musl_prefix_addressable (cjnorm H mem).
Proof. intros H mem Hp. exact (pf_rng_cjnorm H mem _ _ Hp). Qed.

(* args_pf m slots args (the guard) *)
Lemma args_pf_cjnorm : forall H mem slots args,
  GV.args_pf (cjstore H mem) slots args -> GV.args_pf (cjnorm H mem) slots args.
Proof. intros H mem slots args Hp. exact (PSnpSeamGuard.args_pf_kept _ _ slots args (meta_kept_cjnorm H mem) Hp). Qed.

(* ---- GX's args_ok: each %s string ends below TASK_SIZE (args_pf gives it) ---- *)
Fixpoint args_task (slots : list word) (args : list PM.parg) {struct args} : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => True
                  | w :: slots' => match a with
                                   | PM.PA_s s => bv_unsigned w + PR.zlength s + 1 <= TASK_SIZE
                                   | _ => True
                                   end /\ args_task slots' args'
                  end
  end.

Lemma args_task_of_pf : forall m slots args, GV.args_pf m slots args -> args_task slots args.
Proof.
intros m slots args. revert slots. induction args as [|a args IH]; intros slots Hp; [exact I|].
destruct slots as [|w slots]; [exact I|]. destruct Hp as [H1 H2]. split; [|exact (IH slots H2)].
destruct a; try exact I. destruct H1 as (_ & (_ & _ & Hle & _) & _).
unfold AF.APPMEM_END in Hle. unfold TASK_SIZE. lia.
Qed.

Lemma bytes_at_app_l : forall (segs : list Segment) m a bs1 bs2,
  CJM.bytes_at segs m a (bs1 ++ bs2) -> CJM.bytes_at segs m a bs1.
Proof. intros segs m a bs1 bs2 Hb. exact (proj1 (proj1 (CJM.bytes_at_app segs m a bs1 bs2) Hb)). Qed.

(* the string's bytes are read up to the 8-byte boundary past its NUL and no further: the slack
   arg_ok quantifies is cut to that length, which ends below TASK_SIZE (a multiple of 8) *)
Lemma arg_ok_cjnorm : forall H mem (Fp B BS RC RCS RE RES lo sp ap : Z) (w : word) (a : PM.parg),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  match a with PM.PA_s s => bv_unsigned w + PR.zlength s + 1 <= TASK_SIZE | _ => True end ->
  GXI.arg_ok Fp B BS RC RCS RE RES (cjstore H mem) lo sp ap w a ->
  GXI.arg_ok Fp B BS RC RCS RE RES (cjnorm H mem) lo sp ap w a.
Proof.
intros H mem Fp B BS RC RCS RE RES lo sp ap w a Hro Hl HA.
destruct a as [s|i|u|d|l]; try exact HA.
cbn [GXI.arg_ok] in HA |- *.
destruct HA as (slack & BY & HS & PAD & NZ & D1 & D2 & D3 & D4 & D5 & D6).
pose proof (Z.mod_pos_bound (- (bv_unsigned w + PR.zlength s + 1)) 8 ltac:(lia)) as Hk.
remember ((- (bv_unsigned w + PR.zlength s + 1)) mod 8) as k eqn:Ek.
assert (Hend : bv_unsigned w + PR.zlength s + 1 + k <= TASK_SIZE).
{ subst k. unfold TASK_SIZE in *. Z.div_mod_to_equations. lia. }
assert (Hlen : PR.zlength (firstn (Z.to_nat k) slack) = k).
{ unfold PR.zlength in *. rewrite firstn_length_le by lia. lia. }
exists (firstn (Z.to_nat k) slack). rewrite Hlen.
split.
- apply bytes_at_cjnorm; [exact Hro| |].
  + rewrite length_app. cbn [length]. unfold GFP.zb. rewrite length_map.
    unfold PR.zlength in Hend, Hlen. lia.
  + rewrite <- (firstn_skipn (Z.to_nat k) slack) in BY.
    rewrite app_comm_cons, app_assoc in BY. exact (bytes_at_app_l _ _ _ _ _ BY).
- split; [exact HS|]. split; [lia|]. split; [exact NZ|].
  repeat (split; [lia|]). lia.
Qed.

Lemma args_ok_cjnorm : forall H mem (Fp B BS RC RCS RE RES lo sp ap : Z) slots args,
  MN.ro_agree tfibsegs (cjstore H mem) -> args_task slots args ->
  GXI.args_ok Fp B BS RC RCS RE RES (cjstore H mem) lo sp ap slots args ->
  GXI.args_ok Fp B BS RC RCS RE RES (cjnorm H mem) lo sp ap slots args.
Proof.
intros H mem Fp B BS RC RCS RE RES lo sp ap slots args Hro. revert slots.
induction args as [|a args IH]; intros slots Hl HA; [destruct slots; exact I|].
destruct slots as [|w slots]; [destruct HA|].
destruct Hl as [Hl1 Hl2]. destruct HA as [HA1 HA2].
split; [exact (arg_ok_cjnorm H mem Fp B BS RC RCS RE RES lo sp ap w a Hro Hl1 HA1) | exact (IH slots Hl2 HA2)].
Qed.

(* ---- the guard vf_ready_a at the normalized store (G_vfprintf_snf.v:219) ---- *)
Lemma vf_ready_cjnorm : forall copy_ready set_ready strn_ready H mem (q lo Fp CK D : Z) (dn : nat)
    (N bufp A VA : Z) (fmt : list Z) (slots : list word) (args : list PM.parg),
  A + PR.zlength fmt <= sym 0x22e18 ->
  AF.pf_rng (cjstore H mem) A (PR.zlength fmt) -> AF.musl_prefix_addressable (cjstore H mem) ->
  GV.args_pf (cjstore H mem) slots args ->
  AF.app_ivl lo q -> AF.app_ivl Fp (Fp + 232) -> AF.app_ivl CK (CK + 16) -> AF.app_ivl D (D + Z.of_nat dn) ->
  lo + GC.OUT_DEPTH <= q - 368 ->
  PSnpSeamGuard.seam_calls_ready copy_ready set_ready strn_ready (cjnorm H mem) q lo Fp CK D dn ->
  GV.vf_ready_a (GS.snf_out_ready copy_ready) set_ready strn_ready copy_ready PSnpSeamCall.SEAM_INV
    (cjnorm H mem) q lo Fp CK D dn N bufp A VA fmt slots args.
Proof.
intros copy_ready set_ready strn_ready H mem q lo Fp CK D dn N bufp A VA fmt slots args
  HA PF PRE APF ALO AFP ACK AD GEO READY.
apply PSnpSeamGuard.vf_ready_a_holds;
  [exact HA | exact (pf_rng_cjnorm _ _ _ _ PF) | exact (musl_prefix_cjnorm _ _ PRE)
  | exact (args_pf_cjnorm _ _ _ _ APF) | exact ALO | exact AFP | exact ACK | exact AD | exact GEO | exact READY].
Qed.

(* ===================================================================================== *)
(* 4. the run                                                                              *)
(* ===================================================================================== *)

(* the converse of CJBridge.msteps_bridge: the two mstep relations are the same relation *)
Lemma msteps_lib_cj : forall segs ms ms', LE.msteps segs ms ms' -> CJE.msteps segs ms ms'.
Proof.
intros segs ms ms' H. induction H as [ms|ms ms1 ms2 H1 _ IH].
- apply CJE.msteps_refl.
- eapply CJE.msteps_cons; [exact H1 | exact IH].
Qed.

Lemma evt_lib_cj : forall segs (Q : machine_state -> Prop) ms, LE.evt segs Q ms -> CJE.evt segs Q ms.
Proof. intros segs Q ms (ms' & H & HQ). exists ms'. split; [exact (msteps_lib_cj segs ms ms' H) | exact HQ]. Qed.

(* CJ evt on the normalized store -> CJ evt on the harness's store, through lib/Lib *)
Theorem evt_from_norm_MS : forall H mem R F pc fc rv ro (Q : machine_state -> Prop),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  CJE.evt tfibsegs Q (CJMS.MS R F pc fc rv (cjnorm H mem) ro) ->
  CJE.evt tfibsegs
    (fun s => exists s0, Q s0 /\ MN.ms_rel_cj tfibsegs s s0 /\ MN.cj_same tfibsegs (cjstore H mem) (ms_mem s))
    (CJMS.MS R F pc fc rv (cjstore H mem) ro).
Proof.
intros H mem R F pc fc rv ro Q Hro Hev. apply evt_lib_cj.
exact (MN.evt_normalize_cj tfibsegs Q R F pc fc rv (cjstore H mem) ro wx_apart_tfib Hro
         (CJBridge.evt_bridge tfibsegs Q Q _ (fun _ h => h) Hev)).
Qed.

Section Run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the premise in the shape GXA delivers (VfprintfCall.v:44, with the ambient FP state), the
   conclusion in the shape FMgxa_bridge.srr_of_gxa_evt consumes *)
Theorem evt_from_norm : forall (W : world tfibsegs) (pc : Z) regs mem (Q : machine_state -> Prop),
  MN.ro_agree tfibsegs (cjstore (w_H W) mem) ->
  CJE.evt (@img_segs N_img_asan) Q
    (CJMS.MS regs (@fp_regs fx) (w64 pc) (@fp_csr fx) None (cjnorm (w_H W) mem) (CJP.seg_rom (@img_segs N_img_asan))) ->
  CJE.evt (@img_segs N_img_asan)
    (fun s => exists s0, Q s0 /\ MN.ms_rel_cj tfibsegs s s0 /\ MN.cj_same tfibsegs (cjstore (w_H W) mem) (ms_mem s))
    (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom tfibsegs))).
Proof.
intros W pc regs mem Q Hro Hev.
exact (evt_from_norm_MS (w_H W) mem regs (@fp_regs fx) (w64 pc) (@fp_csr fx) None (CJP.seg_rom tfibsegs) Q Hro Hev).
Qed.

(* the same chained through the bridge: a GXA walk on the normalized store is the harness's SRr *)
Theorem srr_of_norm_evt : forall (Hwx : wx_segs_nowrap tfibsegs) (W : world tfibsegs) (pc : Z) regs mem md
  (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  MN.ro_agree tfibsegs (cjstore (w_H W) mem) ->
  CJE.evt (@img_segs N_img_asan) Q
    (CJMS.MS regs (@fp_regs fx) (w64 pc) (@fp_csr fx) None (cjnorm (w_H W) mem) (CJP.seg_rom (@img_segs N_img_asan))) ->
  (forall ms' s0 model', Q s0 -> MN.ms_rel_cj tfibsegs ms' s0 ->
     MN.cj_same tfibsegs (cjstore (w_H W) mem) (ms_mem ms') ->
     same_but_materialized md model' -> hclean (w_H W) ms' ->
     POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
intros Hwx W pc regs mem md Q POST Hro Hev HK.
apply (srr_of_gxa_evt Hwx W pc regs mem md _ POST (evt_from_norm W pc regs mem Q Hro Hev)).
intros ms' model' (s0 & HQ & Hrel & Hsame) Hsm Hcl. exact (HK ms' s0 model' HQ Hrel Hsame Hsm Hcl).
Qed.

End Run.

(* ===================================================================================== *)
(* 5. post transfers s0 -> s                                                               *)
(* ===================================================================================== *)

(* ---- the final stores: m0' (GXA's, from cjnorm) and m' (the harness's, from cjstore) ---- *)
Lemma bytes_at_from_rel : forall m' m0' a bs, MN.mem_rel_cj tfibsegs m' m0' ->
  CJM.bytes_at tfibsegs m0' a bs -> CJM.bytes_at tfibsegs m' a bs.
Proof. intros m' m0' a bs R Hb. exact (MN.bytes_at_rel_cj tfibsegs m' m0' a bs R Hb). Qed.

Lemma rw_cells_from_rel : forall m' m0' A cs, MN.mem_rel_cj tfibsegs m' m0' ->
  CJS.rw_cells tfibsegs m0' A cs -> CJS.rw_cells tfibsegs m' A cs.
Proof.
intros m' m0' A cs R ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
- exact (MN.bytes_at_rel_cj tfibsegs m' m0' A _ R Hb).
- exact (MN.wr_at_rel_cj tfibsegs m' m0' A _ R Hw).
Qed.

Lemma stk_from_rel : forall m' m0' lo hi, MN.mem_rel_cj tfibsegs m' m0' ->
  CJF.stk tfibsegs m0' lo hi -> CJF.stk tfibsegs m' lo hi.
Proof.
intros m' m0' lo hi R (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
destruct (H3 a Ha) as [Hw [b Hb]].
pose proof (MN.keep_of_wview_cj tfibsegs m' m0' _ R Hw) as K.
split.
- rewrite <- (MN.wview_rel_cj tfibsegs m' m0' _ R K). exact Hw.
- exists b. exact (MN.mrd_rel_cj tfibsegs m' m0' _ b R Hb).
Qed.

Lemma ssp_cells_from_rel : forall m' m0' canary, MN.mem_rel_cj tfibsegs m' m0' ->
  GPAD.ssp_cells m0' canary -> GPAD.ssp_cells m' canary.
Proof.
intros m' m0' canary R [S1 S2].
split; [exact (rw_cells_from_rel m' m0' _ _ R S1) | exact (rw_cells_from_rel m' m0' _ _ R S2)].
Qed.

Lemma munch_from_norm : forall H mem m' m0' (Wn : list (Z * Z)), MN.ro_agree tfibsegs (cjstore H mem) ->
  MN.mem_rel_cj tfibsegs m' m0' -> MN.cj_same tfibsegs (cjstore H mem) m' ->
  CJF.munch Wn (cjnorm H mem) m0' -> CJF.munch Wn (cjstore H mem) m'.
Proof.
intros H mem m' m0' Wn Hro R S MU.
exact (MN.munch_rel_cj tfibsegs Wn (cjstore H mem) (cjnorm H mem) m' m0' (mem_rel_cjnorm H mem Hro) R S MU).
Qed.

Lemma wmono_from_norm : forall H mem m' m0', MN.ro_agree tfibsegs (cjstore H mem) ->
  MN.mem_rel_cj tfibsegs m' m0' -> MN.cj_same tfibsegs (cjstore H mem) m' ->
  CJF.wmono tfibsegs (cjnorm H mem) m0' -> CJF.wmono tfibsegs (cjstore H mem) m'.
Proof.
intros H mem m' m0' Hro R S WM.
exact (MN.wmono_rel_cj tfibsegs (cjstore H mem) (cjnorm H mem) m' m0' (mem_rel_cjnorm H mem Hro) R S WM).
Qed.

(* every read below TASK_SIZE (or in the image) agrees between the two final stores *)
Lemma mrd_from_norm : forall m m' m0' (x : word), MN.ro_agree tfibsegs m ->
  MN.mem_rel_cj tfibsegs m' m0' -> MN.cj_same tfibsegs m m' ->
  find_segment tfibsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE ->
  CJM.mrd tfibsegs m' x = CJM.mrd tfibsegs m0' x.
Proof.
intros m m' m0' x Hro R S Hx. destruct (MN.cj_drop tfibsegs x) eqn:E.
- destruct (MN.cj_drop_true tfibsegs x E) as [Er | [Ef Et]].
  + unfold CJM.mrd. rewrite (MN.mem_rel_cj_drop tfibsegs m' m0' x R E), (S x E).
    exact (Hro x Er).
  + exfalso. destruct Hx as [Hx|Hx]; [exact (Hx Ef) | lia].
- unfold CJM.mrd. rewrite (MN.mem_rel_cj_keep tfibsegs m' m0' x R E). reflexivity.
Qed.

(* the harness's invariant comes back only where it held: the dropped bytes are the old ones *)
Lemma mem_inv_from_norm : forall m m', CJM.mem_inv tfibsegs m -> MN.cj_same tfibsegs m m' ->
  CJM.mem_inv tfibsegs m'.
Proof.
intros m m' Hi S. apply CJM.mem_inv_intro. intros a b E. destruct (MN.cj_drop tfibsegs a) eqn:D.
- rewrite (S a D) in E. exact (CJM.mem_inv_elim tfibsegs m a b Hi E).
- exact (MN.cj_drop_false tfibsegs a D).
Qed.

(* the machine state: s is s0 with the harness's store *)
Lemma ms_from_norm : forall s s0 R F pc fc rv m0' ro, MN.ms_rel_cj tfibsegs s s0 ->
  s0 = CJMS.MS R F pc fc rv m0' ro -> s = CJMS.MS R F pc fc rv (ms_mem s) ro.
Proof.
intros s s0 R F pc fc rv m0' ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _) ->.
destruct s as [r f p sv v c m ro']. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
Qed.

Section View. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the harness's view of the two final stores, below TASK_SIZE *)
Lemma view_from_norm : forall H mem m' m0' a, MN.ro_agree tfibsegs (cjstore H mem) ->
  MN.mem_rel_cj tfibsegs m' m0' -> MN.cj_same tfibsegs (cjstore H mem) m' ->
  0 <= a < TASK_SIZE ->
  aview tfibsegs H (munrestrict H mem m') a = aview tfibsegs H (munrestrict H mem m0') a.
Proof.
intros H mem m' m0' a Hro R S Ha. rewrite !aview_mrd.
assert (Hu : bv_unsigned (CJM.wa a) = a) by (apply CJM.wa_unsigned; unfold TASK_SIZE in Ha; lia).
unfold cjstore, mrestrict, munrestrict, CJM.mrd. cbv beta.
destruct (H (CJM.wa a)) eqn:Eh; [reflexivity|].
f_equal.
change (CJM.mrd tfibsegs m' (CJM.wa a) = CJM.mrd tfibsegs m0' (CJM.wa a)).
apply (mrd_from_norm (cjstore H mem)); [exact Hro | exact R | exact S | right; rewrite Hu; lia].
Qed.

End View.

(* ---- GXA's post at the harness's final state ---- *)
(* the post GXA's guarded statement delivers (VfprintfCall.v:43, GX's vfprintf_snf_post at
   lib/CJ/RL/GX/G_vfprintf_snf.v:203), at the store m the harness's run started from, without
   mem_inv: mem_inv comes back only if m had it (mem_inv_from_norm) *)
Definition vf_post_store (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (fjunk : list byte) (m' : word -> option byte),
    ms' = CJMS.MS (CJF.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                           s10 s11 t3 t4 t5 t6)
                  Ft (CJMS.ret_pc ra) fc' None m' (CJP.seg_rom tfibsegs)
    /\ CJF.munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m'
    /\ CJF.wmono tfibsegs m m'
    /\ CJFP.frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ CJF.stk tfibsegs m' lo (bv_unsigned sp)
    /\ GPAD.ssp_cells m' canary
    /\ CJS.rw_cells tfibsegs m' D
         [CJC.CB dn (GFP.zb (firstn (Z.to_nat N) o) ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (Z.min (PR.zlength o) N))) junkd)]
    /\ CJS.rw_cells tfibsegs m' CK
         [CJC.C8 (Z_to_bv 64 (D + Z.min (PR.zlength o) N)); CJC.C8 (Z_to_bv 64 (N - Z.min (PR.zlength o) N))]
    /\ CJS.rw_cells tfibsegs m' Fp [CJC.CB 232 fjunk].

Theorem post_from_norm : forall H mem
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word)
    (s st0 : machine_state),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  MN.ms_rel_cj tfibsegs s st0 -> MN.cj_same tfibsegs (cjstore H mem) (ms_mem s) ->
  GVX.vfprintf_snf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjnorm H mem) st0 ->
  vf_post_store ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjstore H mem) s.
Proof.
intros H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary s st0
  Hro Hrel Hsame HP.
destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & fjunk & m0' &
                E & MU & WM & _ & FRM & FOK & ST & SSP & DC & CKC & FC).
assert (R : MN.mem_rel_cj tfibsegs (ms_mem s) m0').
{ destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & R). subst st0. exact R. }
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', fjunk, (ms_mem s).
split; [exact (ms_from_norm s st0 _ _ _ _ _ m0' _ Hrel E)|].
split; [exact (munch_from_norm H mem _ m0' _ Hro R Hsame MU)|].
split; [exact (wmono_from_norm H mem _ m0' Hro R Hsame WM)|].
split; [exact FRM|]. split; [exact FOK|].
split; [exact (stk_from_rel _ m0' _ _ R ST)|].
split; [exact (ssp_cells_from_rel _ m0' _ R SSP)|].
split; [exact (rw_cells_from_rel _ m0' _ _ R DC)|].
split; [exact (rw_cells_from_rel _ m0' _ _ R CKC)|].
exact (rw_cells_from_rel _ m0' _ _ R FC).
Qed.

(* the same from GXA's own post form (G_vfprintf_snf.v:60), whatever its INV *)
Theorem post_from_norm_a : forall (INV : (word -> option byte) -> Prop) H mem
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word)
    (s st0 : machine_state),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  MN.ms_rel_cj tfibsegs s st0 -> MN.cj_same tfibsegs (cjstore H mem) (ms_mem s) ->
  GV.vfprintf_snf_a_post INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjnorm H mem) st0 ->
  vf_post_store ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjstore H mem) s.
Proof.
intros INV H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary s st0
  Hro Hrel Hsame HP.
exact (post_from_norm H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
         s st0 Hro Hrel Hsame (GV.vfprintf_snf_a_post_plain INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
                                 Fp CK D N dn junkd r o lo canary (cjnorm H mem) st0 HP)).
Qed.

(* ===================================================================================== *)
(* 6. the VIS0-aware normalization cjnormv                                                 *)
(* ===================================================================================== *)

(* cjnormv ly R H mem drops what cjnorm drops and, in addition, every shadow byte whose 8-aligned word
   meets a range of ly_vis0 (the visible-zero shadow of the runtime's own zones), except the aligned
   shadow hull of each range in the carve-out list R.  The seam takes R = the destination, the
   format, the stack window, the musl prefix and each %s string (seam_R): the contract or AR gives
   each of them its shadow_hull_vis, and nothing in the contract keeps a string, the format or (in a
   general layout, where ly_vis0 may meet the image's or the stack's shadow words) the window or the
   prefix off ly_vis0.
   The word test is guarded (shb): it drops only bytes in [LOWMEM_END, HIGHMEM_BEG), so never an
   application byte and never a segment byte, for every ly.  The run moves by FMgxaSeamNormG's
   simulation at the drop set seam_drop ly R, whose one premise seam_drop_ok holds for every ly and R.
   What the drop buys (vis0_word_pres_cjnormv): a visible in_vis0 band byte that shares its 8-aligned
   word with a present byte of cjnormv is present.  The test is by word, so the present byte's word
   is dropped unless carved; carved hulls are whole words; the hull is visible.  The premises are
   layout_ok (every in_vis0 byte is in the guard) and the hulls of R visible. *)

Section V. Context {rc : YM05.RunCeil}.

(* a is in the shadow region between the application's two halves *)
Definition shb (a : Z) : bool := andb (AF.LOWMEM_END <=? a) (a <? AF.HIGHMEM_BEG).

(* the 8-aligned word of a meets the range v *)
Definition word_meets (a : Z) (v : Z * Z) : bool := andb (fst v <? a / 8 * 8 + 8) (a / 8 * 8 <? fst v + snd v).

(* a is in the aligned shadow hull of the range r (the span of shadow_hull_vis, YG0d.v:310-311) *)
Definition hullb (a : Z) (r : Z * Z) : bool :=
  andb (shadow_addr (fst r) / 8 * 8 <=? a) (a <? shadow_addr (fst r + snd r - 1) / 8 * 8 + 8).

Definition dz_shadow (ly : alayout) (a : Z) : bool := andb (shb a) (existsb (word_meets a) (ly_vis0 ly)).

Definition in_hulls (R : list (Z * Z)) (a : Z) : bool := existsb (hullb a) R.

Definition seam_drop (ly : alayout) (R : list (Z * Z)) (a : word) : bool :=
  orb (MN.cj_drop tfibsegs a) (andb (dz_shadow ly (bv_unsigned a)) (negb (in_hulls R (bv_unsigned a)))).

Definition cjnormv (ly : alayout) (R : list (Z * Z)) (H : word -> bool) (mem : word -> option byte)
  : word -> option byte := NG.gdrop_normalize (seam_drop ly R) (cjstore H mem).

(* ---- the drop set is an instance of FMgxaSeamNormG's: it keeps every writable segment byte ---- *)
Lemma tfib_seg_top : forall x : word, find_segment tfibsegs (bv_unsigned x) 1 <> None -> bv_unsigned x < 0x601000.
Proof.
assert (F : forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 0x601000) tfibsegs = true)
  by (vm_compute; reflexivity).
intros x Hx. destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:Hf; [|exfalso; exact (Hx eq_refl)].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & H1 & H2).
pose proof (proj1 (forallb_forall _ _) F seg Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs. lia.
Qed.

(* the word test drops only bytes between the application's two halves *)
Lemma dz_shadow_range : forall ly a, dz_shadow ly a = true -> AF.LOWMEM_END <= a < AF.HIGHMEM_BEG.
Proof.
intros ly a H. unfold dz_shadow, shb in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma dz_app : forall ly a, AF.app_mem a -> dz_shadow ly a = false.
Proof.
intros ly a Ha. destruct (dz_shadow ly a) eqn:D; [|reflexivity]. exfalso.
pose proof (dz_shadow_range ly a D). unfold AF.app_mem, AF.LOWMEM_END, AF.HIGHMEM_BEG in *. lia.
Qed.

Lemma dz_low : forall ly a, a < AF.LOWMEM_END -> dz_shadow ly a = false.
Proof.
intros ly a Ha. destruct (dz_shadow ly a) eqn:D; [|reflexivity]. exfalso.
pose proof (dz_shadow_range ly a D). lia.
Qed.

Lemma seam_drop_ok : forall ly R a, seam_drop ly R a = true ->
  CJM.ro_addr tfibsegs a = true \/ find_segment tfibsegs (bv_unsigned a) 1 = None.
Proof.
intros ly R a H. unfold seam_drop in H. apply orb_true_iff in H as [H|H].
- destruct (MN.cj_drop_true tfibsegs a H) as [E | [E _]]; [left; exact E | right; exact E].
- right. apply andb_prop in H as [H _]. pose proof (dz_shadow_range ly _ H) as [H1 _].
  destruct (find_segment tfibsegs (bv_unsigned a) 1) eqn:Ef; [|reflexivity].
  exfalso. pose proof (tfib_seg_top a ltac:(rewrite Ef; discriminate)). unfold AF.LOWMEM_END in H1. lia.
Qed.

Lemma cj_sub_seam : forall ly R a, MN.cj_drop tfibsegs a = true -> seam_drop ly R a = true.
Proof. intros ly R a H. unfold seam_drop. rewrite H. reflexivity. Qed.

Lemma seam_drop_cj : forall ly R a, seam_drop ly R a = false -> MN.cj_drop tfibsegs a = false.
Proof. intros ly R a H. unfold seam_drop in H. apply orb_false_iff in H. exact (proj1 H). Qed.

(* an application byte is dropped exactly when cjnorm drops it *)
Lemma seam_drop_app : forall ly R (a : word), AF.app_mem (bv_unsigned a) -> seam_drop ly R a = MN.cj_drop tfibsegs a.
Proof. intros ly R a Ha. unfold seam_drop. rewrite (dz_app ly _ Ha). cbn [andb]. apply orb_false_r. Qed.

(* ---- the normalized store and its invariant ---- *)
Lemma mem_inv_cjnormv : forall ly R H mem, CJM.mem_inv tfibsegs (cjnormv ly R H mem).
Proof.
intros ly R H mem. apply CJM.mem_inv_intro. intros a b E.
exact (NG.gmem_inv_cj_normalize tfibsegs (seam_drop ly R) (cj_sub_seam ly R) (cjstore H mem) a b E).
Qed.

Lemma mem_rel_cjnormv : forall ly R H mem, MN.ro_agree tfibsegs (cjstore H mem) ->
  NG.gmem_rel tfibsegs (seam_drop ly R) (cjstore H mem) (cjnormv ly R H mem).
Proof.
intros ly R H mem Hro. exact (NG.gmem_rel_normalize tfibsegs (seam_drop ly R) (seam_drop_ok ly R) (cjstore H mem) Hro).
Qed.

(* ---- the generic facts ---- *)
Lemma mrd_cjnormv_keep : forall ly R H mem (a : word), seam_drop ly R a = false ->
  CJM.mrd tfibsegs (cjnormv ly R H mem) a = CJM.mrd tfibsegs (cjstore H mem) a.
Proof. intros ly R H mem a E. unfold CJM.mrd, cjnormv, NG.gdrop_normalize. cbv beta. rewrite E. reflexivity. Qed.

Lemma wview_cjnormv : forall ly R H mem (a : word), seam_drop ly R a = false ->
  wview tfibsegs (cjnormv ly R H mem) a = wview tfibsegs (cjstore H mem) a.
Proof. intros ly R H mem a E. unfold wview, cjnormv, NG.gdrop_normalize. cbv beta. rewrite E. reflexivity. Qed.

(* a read below TASK_SIZE (or inside the image) that the zone test does not drop agrees *)
Lemma mrd_cjnormv : forall ly R H mem (a : word), MN.ro_agree tfibsegs (cjstore H mem) ->
  find_segment tfibsegs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE ->
  dz_shadow ly (bv_unsigned a) = false ->
  CJM.mrd tfibsegs (cjnormv ly R H mem) a = CJM.mrd tfibsegs (cjstore H mem) a.
Proof.
intros ly R H mem a Hro Ha D. apply (NG.gmrd_normalize tfibsegs (seam_drop ly R) (cjstore H mem) a Hro).
intros E Er. exfalso. unfold seam_drop in E. rewrite D, andb_false_l, orb_false_r in E.
destruct (MN.cj_drop_true tfibsegs a E) as [E1 | [E1 E2]]; [congruence|].
destruct Ha as [Ha|Ha]; [exact (Ha E1) | lia].
Qed.

(* every in_shadow byte below TASK_SIZE is kept by cj_drop *)
Lemma cj_keep_shadow_rng : forall s : Z, 0xa2000 <= s -> s + 1 <= TASK_SIZE -> MN.cj_drop tfibsegs (CJM.wa s) = false.
Proof. intros s H1 H2. exact (cj_kept_off_ro s (s + 1) ltac:(lia) H2 ltac:(right; lia) s ltac:(lia)). Qed.

(* ---- kept data ranges ---- *)
Definition sd_kept (ly : alayout) (R : list (Z * Z)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> seam_drop ly R (CJM.wa x) = false.

(* a range cjnorm keeps that is application memory is kept *)
Lemma sd_kept_app : forall ly R lo hi, cj_kept lo hi -> AF.app_ivl lo hi -> sd_kept ly R lo hi.
Proof.
intros ly R lo hi K A x Hx. pose proof (A x Hx) as Ax.
assert (Hu : bv_unsigned (CJM.wa x) = x)
  by (apply CJM.wa_unsigned; unfold AF.app_mem, AF.LOWMEM_END, AF.HIGHMEM_BEG, AF.APPMEM_END in Ax; lia).
rewrite seam_drop_app by (rewrite Hu; exact Ax). exact (K x Hx).
Qed.

Lemma bytes_at_cjnormv_kept : forall ly R H mem a bs, sd_kept ly R a (a + Z.of_nat (length bs)) ->
  CJM.bytes_at tfibsegs (cjstore H mem) a bs -> CJM.bytes_at tfibsegs (cjnormv ly R H mem) a bs.
Proof.
intros ly R H mem a bs K (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
rewrite mrd_cjnormv_keep by (apply K; lia). exact (H3 i Hi).
Qed.

(* bytes the zone test does not drop, below TASK_SIZE, under the read agreement *)
Lemma bytes_at_cjnormv : forall ly R H mem a bs, MN.ro_agree tfibsegs (cjstore H mem) ->
  a + Z.of_nat (length bs) <= TASK_SIZE ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> dz_shadow ly x = false) ->
  CJM.bytes_at tfibsegs (cjstore H mem) a bs -> CJM.bytes_at tfibsegs (cjnormv ly R H mem) a bs.
Proof.
intros ly R H mem a bs Hro Hl D (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
assert (Hu : bv_unsigned (CJM.wa (a + Z.of_nat i)) = a + Z.of_nat i) by (apply CJM.wa_unsigned; lia).
rewrite mrd_cjnormv; [exact (H3 i Hi) | exact Hro | right; rewrite Hu; lia | rewrite Hu; apply D; lia].
Qed.

Lemma wr_at_cjnormv : forall ly R H mem a n, sd_kept ly R a (a + n) ->
  CJM.wr_at tfibsegs (cjstore H mem) a n -> CJM.wr_at tfibsegs (cjnormv ly R H mem) a n.
Proof.
intros ly R H mem a n K (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
rewrite wview_cjnormv by (apply K; lia). exact (H3 i Hi).
Qed.

Lemma rw_cells_cjnormv : forall ly R H mem A cs, sd_kept ly R A (A + Z.of_nat (CJC.cells_size cs)) ->
  CJS.rw_cells tfibsegs (cjstore H mem) A cs -> CJS.rw_cells tfibsegs (cjnormv ly R H mem) A cs.
Proof.
intros ly R H mem A cs K ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
- apply bytes_at_cjnormv_kept; [|exact Hb]. rewrite CJC.cells_bytes_length by exact Hwf. exact K.
- exact (wr_at_cjnormv ly R H mem A _ K Hw).
Qed.

Lemma stk_cjnormv : forall ly R H mem lo hi, sd_kept ly R lo hi ->
  CJF.stk tfibsegs (cjstore H mem) lo hi -> CJF.stk tfibsegs (cjnormv ly R H mem) lo hi.
Proof.
intros ly R H mem lo hi K (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
rewrite wview_cjnormv, mrd_cjnormv_keep by exact (K a Ha). exact (H3 a Ha).
Qed.

(* ---- GXA's premises (VfprintfCall.v:29-38): cjnorm's statements, the data ranges in app memory ---- *)
Lemma file_cjnormv : forall ly R H mem Fp bufp CK, @GXI.GLOBALS_TOP N_img_asan <= Fp -> Fp + 232 <= TASK_SIZE ->
  AF.app_ivl Fp (Fp + 232) ->
  CJS.rw_cells tfibsegs (cjstore H mem) Fp (GVX.snf_file bufp CK) ->
  CJS.rw_cells tfibsegs (cjnormv ly R H mem) Fp (GVX.snf_file bufp CK).
Proof.
intros ly R H mem Fp bufp CK H1 H2 A Rc. apply rw_cells_cjnormv; [|exact Rc].
rewrite snf_file_size. exact (sd_kept_app ly R Fp (Fp + 232) (cj_kept_high Fp (Fp + 232) H1 H2) A).
Qed.

Lemma cookie_cjnormv : forall ly R H mem CK v1 v2, @GXI.GLOBALS_TOP N_img_asan <= CK -> CK + 16 <= TASK_SIZE ->
  AF.app_ivl CK (CK + 16) ->
  CJS.rw_cells tfibsegs (cjstore H mem) CK [CJC.C8 v1; CJC.C8 v2] ->
  CJS.rw_cells tfibsegs (cjnormv ly R H mem) CK [CJC.C8 v1; CJC.C8 v2].
Proof.
intros ly R H mem CK v1 v2 H1 H2 A Rc. apply rw_cells_cjnormv; [|exact Rc].
exact (sd_kept_app ly R CK (CK + 16) (cj_kept_high CK (CK + 16) H1 H2) A).
Qed.

Lemma dest_cjnormv : forall ly R H mem D dn bs, 0 <= D -> D + Z.of_nat dn <= TASK_SIZE ->
  (D + Z.of_nat dn <= 65536 \/ @GXI.GLOBALS_TOP N_img_asan <= D) -> AF.app_ivl D (D + Z.of_nat dn) ->
  CJS.rw_cells tfibsegs (cjstore H mem) D [CJC.CB dn bs] ->
  CJS.rw_cells tfibsegs (cjnormv ly R H mem) D [CJC.CB dn bs].
Proof.
intros ly R H mem D dn bs H0 H1 H2 A Rc. apply rw_cells_cjnormv; [|exact Rc].
cbn [CJC.cells_size CJC.csize]. rewrite Nat.add_0_r.
exact (sd_kept_app ly R D (D + Z.of_nat dn) (cj_kept_dest D (Z.of_nat dn) H0 H1 H2) A).
Qed.

(* the format: below GLOBALS_TOP, so below LOWMEM_END, where the zone test drops nothing *)
Lemma fmt_cjnormv : forall ly R H mem A (fmt : list Z), MN.ro_agree tfibsegs (cjstore H mem) ->
  A + PR.zlength fmt <= @GXI.GLOBALS_TOP N_img_asan ->
  CJM.bytes_at tfibsegs (cjstore H mem) A (GFP.zb fmt) -> CJM.bytes_at tfibsegs (cjnormv ly R H mem) A (GFP.zb fmt).
Proof.
intros ly R H mem A fmt Hro Hl Hb. rewrite globals_top_A in Hl.
assert (Lz : Z.of_nat (length (GFP.zb fmt)) = PR.zlength fmt) by (unfold GFP.zb, PR.zlength; rewrite length_map; reflexivity).
apply bytes_at_cjnormv; [exact Hro | rewrite Lz; unfold TASK_SIZE; lia | | exact Hb].
intros x Hx. apply dz_low. unfold AF.LOWMEM_END. rewrite Lz in Hx. lia.
Qed.

Lemma va_area_cjnormv : forall ly R H mem VA slots, MN.ro_agree tfibsegs (cjstore H mem) ->
  VA + 8 * PR.zlength slots <= TASK_SIZE -> AF.app_ivl VA (VA + 8 * PR.zlength slots) ->
  GPOP.va_area (cjstore H mem) VA slots -> GPOP.va_area (cjnormv ly R H mem) VA slots.
Proof.
intros ly R H mem VA slots Hro Hl A Hv. unfold GPOP.va_area in *.
assert (Lz : Z.of_nat (length (CJA.u64s slots)) = 8 * PR.zlength slots) by (rewrite CJA.u64s_length; unfold PR.zlength; lia).
apply bytes_at_cjnormv; [exact Hro | rewrite Lz; exact Hl | | exact Hv].
intros x Hx. apply dz_app. apply A. rewrite Lz in Hx. exact Hx.
Qed.

Lemma stk_window_cjnormv : forall ly R H mem lo q, @GXI.GLOBALS_TOP N_img_asan <= lo -> q <= TASK_SIZE ->
  AF.app_ivl lo q ->
  CJF.stk tfibsegs (cjstore H mem) lo q -> CJF.stk tfibsegs (cjnormv ly R H mem) lo q.
Proof. intros ly R H mem lo q H1 H2 A S. exact (stk_cjnormv ly R H mem lo q (sd_kept_app ly R lo q (cj_kept_high lo q H1 H2) A) S). Qed.

(* the stack-protector cells: below LOWMEM_END in writable image segments, so no condition *)
Lemma ssp_cells_cjnormv : forall ly R H mem canary,
  GPAD.ssp_cells (cjstore H mem) canary -> GPAD.ssp_cells (cjnormv ly R H mem) canary.
Proof.
intros ly R H mem canary [S1 S2]. destruct ssp_kept as [K1 K2].
assert (G1 : @GPAD.got_ssp N_img_asan = 0xa34d8) by (vm_compute; reflexivity).
assert (G2 : @GPAD.ssp_guard N_img_asan = 0x5fe770) by (vm_compute; reflexivity).
assert (A1 : AF.app_ivl (@GPAD.got_ssp N_img_asan) (@GPAD.got_ssp N_img_asan + 8))
  by (intros a Ha; left; unfold AF.LOWMEM_END; lia).
assert (A2 : AF.app_ivl (@GPAD.ssp_guard N_img_asan) (@GPAD.ssp_guard N_img_asan + 8))
  by (intros a Ha; left; unfold AF.LOWMEM_END; lia).
split; apply rw_cells_cjnormv; [exact (sd_kept_app ly R _ _ K1 A1) | exact S1 | exact (sd_kept_app ly R _ _ K2 A2)
                               | exact S2].
Qed.

(* ---- the ASan shadow: a range whose shadow bytes are not dropped ---- *)
Definition sh_kept (ly : alayout) (R : list (Z * Z)) (p n : Z) : Prop :=
  forall i, 0 <= i < n -> seam_drop ly R (CJM.wa (AF.shadow_addr (p + i))) = false.

Lemma pf_rng_cjnormv : forall ly R H mem p n, sh_kept ly R p n ->
  AF.pf_rng (cjstore H mem) p n -> AF.pf_rng (cjnormv ly R H mem) p n.
Proof.
intros ly R H mem p n K (HN & (A1 & A2 & A3 & AD) & EN & SV).
split; [exact HN|]. split; [|split; [exact EN | exact SV]].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
intros i Hi. destruct (AD i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
exact (eq_trans (mrd_cjnormv_keep ly R H mem _ (K i Hi)) Hb).
Qed.

Lemma musl_prefix_cjnormv : forall ly R H mem, sh_kept ly R (@sym N_img_asan 0x1029e) 9 ->
  AF.musl_prefix_addressable (cjstore H mem) -> AF.musl_prefix_addressable (cjnormv ly R H mem).
Proof. intros ly R H mem K Hp. exact (pf_rng_cjnormv ly R H mem _ _ K Hp). Qed.

(* the shadow bytes args_pf reads: each %s string's (G_vfprintf_snf.v:90-98) *)
Fixpoint args_kept (ly : alayout) (R : list (Z * Z)) (slots : list word) (args : list PM.parg) {struct args} : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => True
                  | w :: slots' => match a with
                                   | PM.PA_s s => sh_kept ly R (bv_unsigned w) (PR.zlength s + 1)
                                   | _ => True
                                   end /\ args_kept ly R slots' args'
                  end
  end.

Lemma args_pf_cjnormv : forall ly R H mem slots args, args_kept ly R slots args ->
  GV.args_pf (cjstore H mem) slots args -> GV.args_pf (cjnormv ly R H mem) slots args.
Proof.
intros ly R H mem slots args. revert slots.
induction args as [|a args IH]; intros slots K P; destruct slots as [|w slots]; try exact I.
destruct K as [K1 K2]. destruct P as [P1 P2]. split; [|exact (IH slots K2 P2)].
destruct a; try exact I. exact (pf_rng_cjnormv ly R H mem _ _ K1 P1).
Qed.

(* ---- GX's args_ok: each %s string and its slack word are application memory (args_pf gives it) ---- *)
Fixpoint args_app (slots : list word) (args : list PM.parg) {struct args} : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => True
                  | w :: slots' => match a with
                                   | PM.PA_s s => AF.app_ivl (bv_unsigned w) (bv_unsigned w + PR.zlength s + 8)
                                   | _ => True
                                   end /\ args_app slots' args'
                  end
  end.

Lemma args_app_of_pf : forall m slots args, GV.args_pf m slots args -> args_app slots args.
Proof.
intros m slots args. revert slots. induction args as [|a args IH]; intros slots Hp; [exact I|].
destruct slots as [|w slots]; [exact I|]. destruct Hp as [H1 H2]. split; [|exact (IH slots H2)].
destruct a; try exact I. destruct H1 as (_ & AD & _ & SV).
pose proof (AF.addressable_app _ _ _ AD) as A. assert (Hz : 0 <= PR.zlength s) by (unfold PR.zlength; lia).
pose proof (A (bv_unsigned w + PR.zlength s) ltac:(lia)) as A1.
pose proof (SV (PR.zlength s) ltac:(lia)) as A2.
intros x Hx. destruct (Z_lt_le_dec x (bv_unsigned w + (PR.zlength s + 1))) as [L|L]; [apply A; lia|].
unfold AF.app_mem, AF.LOWMEM_END, AF.HIGHMEM_BEG, AF.APPMEM_END in *. lia.
Qed.

Lemma arg_ok_cjnormv : forall ly R H mem (Fp B BS RC RCS RE RES lo sp ap : Z) (w : word) (a : PM.parg),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  match a with
  | PM.PA_s s => bv_unsigned w + PR.zlength s + 1 <= TASK_SIZE /\
                 AF.app_ivl (bv_unsigned w) (bv_unsigned w + PR.zlength s + 8)
  | _ => True
  end ->
  GXI.arg_ok Fp B BS RC RCS RE RES (cjstore H mem) lo sp ap w a ->
  GXI.arg_ok Fp B BS RC RCS RE RES (cjnormv ly R H mem) lo sp ap w a.
Proof.
intros ly R H mem Fp B BS RC RCS RE RES lo sp ap w a Hro Hl HA.
destruct a as [s|i|u|d|l]; try exact HA.
cbn [GXI.arg_ok] in HA |- *. destruct Hl as [Hl Happ].
destruct HA as (slack & BY & HS & PAD & NZ & D1 & D2 & D3 & D4 & D5 & D6).
pose proof (Z.mod_pos_bound (- (bv_unsigned w + PR.zlength s + 1)) 8 ltac:(lia)) as Hk.
remember ((- (bv_unsigned w + PR.zlength s + 1)) mod 8) as k eqn:Ek.
assert (Hend : bv_unsigned w + PR.zlength s + 1 + k <= TASK_SIZE).
{ subst k. unfold TASK_SIZE in *. Z.div_mod_to_equations. lia. }
assert (Hlen : PR.zlength (firstn (Z.to_nat k) slack) = k).
{ unfold PR.zlength in *. rewrite firstn_length_le by lia. lia. }
exists (firstn (Z.to_nat k) slack). rewrite Hlen.
split.
- apply bytes_at_cjnormv; [exact Hro| | |].
  + rewrite length_app. cbn [length]. unfold GFP.zb. rewrite length_map.
    unfold PR.zlength in Hend, Hlen. lia.
  + intros x Hx. apply dz_app. apply Happ. rewrite length_app in Hx. cbn [length] in Hx.
    unfold GFP.zb in Hx. rewrite length_map in Hx. unfold PR.zlength in Hlen |- *. lia.
  + rewrite <- (firstn_skipn (Z.to_nat k) slack) in BY.
    rewrite app_comm_cons, app_assoc in BY. exact (bytes_at_app_l _ _ _ _ _ BY).
- split; [exact HS|]. split; [lia|]. split; [exact NZ|].
  repeat (split; [lia|]). lia.
Qed.

Lemma args_ok_cjnormv : forall ly R H mem (Fp B BS RC RCS RE RES lo sp ap : Z) slots args,
  MN.ro_agree tfibsegs (cjstore H mem) -> args_task slots args -> args_app slots args ->
  GXI.args_ok Fp B BS RC RCS RE RES (cjstore H mem) lo sp ap slots args ->
  GXI.args_ok Fp B BS RC RCS RE RES (cjnormv ly R H mem) lo sp ap slots args.
Proof.
intros ly R H mem Fp B BS RC RCS RE RES lo sp ap slots args Hro. revert slots.
induction args as [|a args IH]; intros slots Hl Ha HA; [destruct slots; exact I|].
destruct slots as [|w slots]; [destruct HA|].
destruct Hl as [Hl1 Hl2]. destruct Ha as [Ha1 Ha2]. destruct HA as [HA1 HA2].
split; [|exact (IH slots Hl2 Ha2 HA2)].
apply (arg_ok_cjnormv ly R H mem Fp B BS RC RCS RE RES lo sp ap w a Hro); [|exact HA1].
destruct a; try exact I. exact (conj Hl1 Ha1).
Qed.

(* ---- the guard vf_ready_a at the VIS0-aware store (G_vfprintf_snf.v:219) ---- *)
Lemma vf_ready_cjnormv : forall copy_ready set_ready strn_ready ly R H mem (q lo Fp CK D : Z) (dn : nat)
    (N bufp A VA : Z) (fmt : list Z) (slots : list word) (args : list PM.parg),
  A + PR.zlength fmt <= sym 0x22e18 ->
  AF.pf_rng (cjstore H mem) A (PR.zlength fmt) -> sh_kept ly R A (PR.zlength fmt) ->
  AF.musl_prefix_addressable (cjstore H mem) -> sh_kept ly R (@sym N_img_asan 0x1029e) 9 ->
  GV.args_pf (cjstore H mem) slots args -> args_kept ly R slots args ->
  AF.app_ivl lo q -> AF.app_ivl Fp (Fp + 232) -> AF.app_ivl CK (CK + 16) -> AF.app_ivl D (D + Z.of_nat dn) ->
  lo + GC.OUT_DEPTH <= q - 368 ->
  PSnpSeamGuard.seam_calls_ready copy_ready set_ready strn_ready (cjnormv ly R H mem) q lo Fp CK D dn ->
  GV.vf_ready_a (GS.snf_out_ready copy_ready) set_ready strn_ready copy_ready PSnpSeamCall.SEAM_INV
    (cjnormv ly R H mem) q lo Fp CK D dn N bufp A VA fmt slots args.
Proof.
intros copy_ready set_ready strn_ready ly R H mem q lo Fp CK D dn N bufp A VA fmt slots args
  HA PF KF PRE KP APF KA ALO AFP ACK AD GEO READY.
apply PSnpSeamGuard.vf_ready_a_holds;
  [exact HA | exact (pf_rng_cjnormv _ _ _ _ _ _ KF PF) | exact (musl_prefix_cjnormv _ _ _ _ KP PRE)
  | exact (args_pf_cjnormv _ _ _ _ _ _ KA APF) | exact ALO | exact AFP | exact ACK | exact AD | exact GEO | exact READY].
Qed.

(* ---- the run ---- *)
Theorem evt_from_norm_MS_v : forall ly R H mem Rg F pc fc rv ro (Q : machine_state -> Prop),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  CJE.evt tfibsegs Q (CJMS.MS Rg F pc fc rv (cjnormv ly R H mem) ro) ->
  CJE.evt tfibsegs
    (fun s => exists s0, Q s0 /\ NG.gms_rel tfibsegs (seam_drop ly R) s s0 /\
                         NG.gcj_same (seam_drop ly R) (cjstore H mem) (ms_mem s))
    (CJMS.MS Rg F pc fc rv (cjstore H mem) ro).
Proof.
intros ly R H mem Rg F pc fc rv ro Q Hro Hev. apply evt_lib_cj.
exact (NG.gevt_normalize tfibsegs (seam_drop ly R) (seam_drop_ok ly R) Q Rg F pc fc rv (cjstore H mem) ro
         wx_apart_tfib Hro (CJBridge.evt_bridge tfibsegs Q Q _ (fun _ h => h) Hev)).
Qed.

Section RunV. Context {fx : YK11.FPState}.

Theorem evt_from_norm_v : forall ly R (W : world tfibsegs) (pc : Z) regs mem (Q : machine_state -> Prop),
  MN.ro_agree tfibsegs (cjstore (w_H W) mem) ->
  CJE.evt (@img_segs N_img_asan) Q
    (CJMS.MS regs (@fp_regs fx) (w64 pc) (@fp_csr fx) None (cjnormv ly R (w_H W) mem) (CJP.seg_rom (@img_segs N_img_asan))) ->
  CJE.evt (@img_segs N_img_asan)
    (fun s => exists s0, Q s0 /\ NG.gms_rel tfibsegs (seam_drop ly R) s s0 /\
                         NG.gcj_same (seam_drop ly R) (cjstore (w_H W) mem) (ms_mem s))
    (restrict (w_H W) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom tfibsegs))).
Proof.
intros ly R W pc regs mem Q Hro Hev.
exact (evt_from_norm_MS_v ly R (w_H W) mem regs (@fp_regs fx) (w64 pc) (@fp_csr fx) None (CJP.seg_rom tfibsegs) Q
         Hro Hev).
Qed.

End RunV.

(* ---- the post: GXA's final store m0' (from cjnormv) read at the harness's m' (from cjstore) ---- *)
Lemma rw_cells_from_rel_v : forall ly R m' m0' A cs, NG.gmem_rel tfibsegs (seam_drop ly R) m' m0' ->
  CJS.rw_cells tfibsegs m0' A cs -> CJS.rw_cells tfibsegs m' A cs.
Proof.
intros ly R m' m0' A cs Rl ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
- exact (NG.gbytes_at_rel tfibsegs (seam_drop ly R) m' m0' A _ Rl Hb).
- exact (NG.gwr_at_rel tfibsegs (seam_drop ly R) (seam_drop_ok ly R) m' m0' A _ Rl Hw).
Qed.

Lemma stk_from_rel_v : forall ly R m' m0' lo hi, NG.gmem_rel tfibsegs (seam_drop ly R) m' m0' ->
  CJF.stk tfibsegs m0' lo hi -> CJF.stk tfibsegs m' lo hi.
Proof.
intros ly R m' m0' lo hi Rl (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros a Ha.
destruct (H3 a Ha) as [Hw [b Hb]].
pose proof (NG.gkeep_of_wview tfibsegs (seam_drop ly R) (seam_drop_ok ly R) m' m0' _ Rl Hw) as K.
split.
- rewrite <- (NG.gwview_rel tfibsegs (seam_drop ly R) m' m0' _ Rl K). exact Hw.
- exists b. exact (NG.gmrd_rel tfibsegs (seam_drop ly R) m' m0' _ b Rl Hb).
Qed.

Lemma ssp_cells_from_rel_v : forall ly R m' m0' canary, NG.gmem_rel tfibsegs (seam_drop ly R) m' m0' ->
  GPAD.ssp_cells m0' canary -> GPAD.ssp_cells m' canary.
Proof.
intros ly R m' m0' canary Rl [S1 S2].
split; [exact (rw_cells_from_rel_v ly R m' m0' _ _ Rl S1) | exact (rw_cells_from_rel_v ly R m' m0' _ _ Rl S2)].
Qed.

Lemma munch_from_norm_v : forall ly R H mem m' m0' (Wn : list (Z * Z)), MN.ro_agree tfibsegs (cjstore H mem) ->
  NG.gmem_rel tfibsegs (seam_drop ly R) m' m0' -> NG.gcj_same (seam_drop ly R) (cjstore H mem) m' ->
  CJF.munch Wn (cjnormv ly R H mem) m0' -> CJF.munch Wn (cjstore H mem) m'.
Proof.
intros ly R H mem m' m0' Wn Hro Rl S MU.
exact (NG.gmunch_rel tfibsegs (seam_drop ly R) Wn (cjstore H mem) (cjnormv ly R H mem) m' m0'
         (mem_rel_cjnormv ly R H mem Hro) Rl S MU).
Qed.

Lemma wmono_from_norm_v : forall ly R H mem m' m0', MN.ro_agree tfibsegs (cjstore H mem) ->
  NG.gmem_rel tfibsegs (seam_drop ly R) m' m0' -> NG.gcj_same (seam_drop ly R) (cjstore H mem) m' ->
  CJF.wmono tfibsegs (cjnormv ly R H mem) m0' -> CJF.wmono tfibsegs (cjstore H mem) m'.
Proof.
intros ly R H mem m' m0' Hro Rl S WM.
exact (NG.gwmono_rel tfibsegs (seam_drop ly R) (cjstore H mem) (cjnormv ly R H mem) m' m0'
         (mem_rel_cjnormv ly R H mem Hro) Rl S WM).
Qed.

(* the harness's invariant comes back only where it held: the dropped bytes are the old ones *)
Lemma mem_inv_from_norm_v : forall ly R m m', CJM.mem_inv tfibsegs m -> NG.gcj_same (seam_drop ly R) m m' ->
  CJM.mem_inv tfibsegs m'.
Proof.
intros ly R m m' Hi S. apply CJM.mem_inv_intro. intros a b E. destruct (seam_drop ly R a) eqn:D.
- rewrite (S a D) in E. exact (CJM.mem_inv_elim tfibsegs m a b Hi E).
- exact (MN.cj_drop_false tfibsegs a (seam_drop_cj ly R a D)).
Qed.

Lemma ms_from_norm_v : forall ly R s s0 Rg F pc fc rv m0' ro, NG.gms_rel tfibsegs (seam_drop ly R) s s0 ->
  s0 = CJMS.MS Rg F pc fc rv m0' ro -> s = CJMS.MS Rg F pc fc rv (ms_mem s) ro.
Proof.
intros ly R s s0 Rg F pc fc rv m0' ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _) ->.
destruct s as [r f p sv v c m ro']. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
Qed.

Theorem post_from_norm_v : forall ly R H mem
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word)
    (s st0 : machine_state),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  NG.gms_rel tfibsegs (seam_drop ly R) s st0 -> NG.gcj_same (seam_drop ly R) (cjstore H mem) (ms_mem s) ->
  GVX.vfprintf_snf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjnormv ly R H mem) st0 ->
  vf_post_store ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjstore H mem) s.
Proof.
intros ly R H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary s st0
  Hro Hrel Hsame HP.
destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & fjunk & m0' &
                E & MU & WM & _ & FRM & FOK & ST & SSP & DC & CKC & FC).
assert (Rl : NG.gmem_rel tfibsegs (seam_drop ly R) (ms_mem s) m0').
{ destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & Rl). subst st0. exact Rl. }
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', fjunk, (ms_mem s).
split; [exact (ms_from_norm_v ly R s st0 _ _ _ _ _ m0' _ Hrel E)|].
split; [exact (munch_from_norm_v ly R H mem _ m0' _ Hro Rl Hsame MU)|].
split; [exact (wmono_from_norm_v ly R H mem _ m0' Hro Rl Hsame WM)|].
split; [exact FRM|]. split; [exact FOK|].
split; [exact (stk_from_rel_v ly R _ m0' _ _ Rl ST)|].
split; [exact (ssp_cells_from_rel_v ly R _ m0' _ Rl SSP)|].
split; [exact (rw_cells_from_rel_v ly R _ m0' _ _ Rl DC)|].
split; [exact (rw_cells_from_rel_v ly R _ m0' _ _ Rl CKC)|].
exact (rw_cells_from_rel_v ly R _ m0' _ _ Rl FC).
Qed.

Theorem post_from_norm_a_v : forall (INV : (word -> option byte) -> Prop) ly R H mem
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D N : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word)
    (s st0 : machine_state),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  NG.gms_rel tfibsegs (seam_drop ly R) s st0 -> NG.gcj_same (seam_drop ly R) (cjstore H mem) (ms_mem s) ->
  GV.vfprintf_snf_a_post INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjnormv ly R H mem) st0 ->
  vf_post_store ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
    (cjstore H mem) s.
Proof.
intros INV ly R H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary s st0
  Hro Hrel Hsame HP.
exact (post_from_norm_v ly R H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D N dn junkd r o lo canary
         s st0 Hro Hrel Hsame (GV.vfprintf_snf_a_post_plain INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
                                 Fp CK D N dn junkd r o lo canary (cjnormv ly R H mem) st0 HP)).
Qed.

(* ===================================================================================== *)
(* 7. what seam_drop keeps: the hulls the walk reads                                        *)
(* ===================================================================================== *)

(* every byte of the aligned shadow hull of [x, x + n) is kept *)
Definition sd_hull_kept (ly : alayout) (R : list (Z * Z)) (x n : Z) : Prop :=
  forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> seam_drop ly R (CJM.wa s) = false.

(* the shadow byte of each byte of a range lies in the range's hull *)
Lemma sh_kept_of_hull : forall ly R x n, sd_hull_kept ly R x n -> sh_kept ly R x n.
Proof.
intros ly R x n K i Hi. apply K.
unfold AF.shadow_addr, AF.ASAN_K, shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* the hull of a range of application memory lies in [SHADOW_OFF, TASK_SIZE) *)
Lemma hull_rng : forall x n s, 0 <= x -> x + n <= AF.APPMEM_END ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0xa2000 <= s /\ s + 1 <= TASK_SIZE.
Proof.
intros x n s H0 H1 Hs. unfold shadow_addr, SHADOW_OFF, AF.APPMEM_END, TASK_SIZE in *.
Z.div_mod_to_equations. lia.
Qed.

Lemma hull_wa : forall x n s, 0 <= x -> x + n <= AF.APPMEM_END ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> bv_unsigned (CJM.wa s) = s.
Proof.
intros x n s H0 H1 Hs. destruct (hull_rng x n s H0 H1 Hs) as [L1 L2].
apply CJM.wa_unsigned. unfold TASK_SIZE in L2. lia.
Qed.

(* a carved range: its hull is kept by construction *)
Lemma hull_kept_carved : forall ly R r, In r R -> 0 <= fst r -> fst r + snd r <= AF.APPMEM_END ->
  sd_hull_kept ly R (fst r) (snd r).
Proof.
intros ly R r Hin H0 H1 s Hs. destruct (hull_rng _ _ s H0 H1 Hs) as [L1 L2].
unfold seam_drop. rewrite (cj_keep_shadow_rng s L1 L2), (hull_wa _ _ s H0 H1 Hs).
assert (Hh : in_hulls R s = true).
{ unfold in_hulls. apply existsb_exists. exists r. split; [exact Hin|].
  unfold hullb. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite Hh. cbn [negb orb]. apply andb_false_r.
Qed.

(* ---- the seam's carve-out list: the destination, the format, the stack window, the musl prefix
   and each %s string ---- *)
Fixpoint str_rngs (ws : list Z) (args : list SPF.pf_arg) {struct args} : list (Z * Z) :=
  match args with
  | [] => []
  | a :: args' => match ws with
                  | [] => []
                  | w :: ws' => match a with
                                | SPF.APtr s => (w, Z.of_nat (length s) + 1) :: str_rngs ws' args'
                                | _ => str_rngs ws' args'
                                end
                  end
  end.

Definition seam_R (s0 dn f : Z) (fmt : list Z) (lo K : Z) (ws : list Z) (args : list SPF.pf_arg) : list (Z * Z) :=
  (s0, dn) :: (f, Z.of_nat (length fmt) + 1) :: (lo, K) :: (@sym N_img_asan 0x1029e, 9) :: str_rngs ws args.

Lemma amem_app : forall p n, 0 <= p -> amem_range p n -> p + n <= AF.APPMEM_END.
Proof. intros p n H0 H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, AF.APPMEM_END in *. lia. Qed.

(* each %s string's shadow, as GXA's args_pf reads it, is kept when the string's range is carved *)
Lemma args_kept_of_asan : forall ly R rd rs ws args (pa : list PM.parg),
  (forall r, In r (str_rngs ws args) -> In r R) -> SFF.pf_args_asan rd rs ws args ->
  Forall2 GPF.pt_parg_rel args pa ->
  args_kept ly R (map w64 ws) pa.
Proof.
intros ly R rd rs ws args pa Hin Hp HF. revert ws Hin Hp.
induction HF as [|a p args pa Hap HF IH]; intros ws Hin Hp; [exact I|].
destruct ws as [|w ws]; [destruct Hp|]. destruct Hp as [H1 H2]. cbn [map args_kept]. split.
- destruct Hap as [-> | (v & -> & ->)]; [|exact I].
  destruct a as [v|u|s]; cbn [GPF.pt_parg]; try exact I.
  cbv beta iota delta [SFF.pf_arg_asan] in H1. destruct H1 as (_ & Hw & _ & _ & _ & _ & HAM & _).
  pose proof (amem_app w _ ltac:(lia) HAM) as Hl.
  assert (Hu : bv_unsigned (w64 w) = w)
    by (apply CJM.wa_unsigned; unfold AF.APPMEM_END in Hl; lia).
  assert (Hz : PR.zlength s = Z.of_nat (length s)) by reflexivity.
  rewrite Hu, Hz. apply sh_kept_of_hull.
  exact (hull_kept_carved ly R (w, Z.of_nat (length s) + 1) (Hin _ (or_introl eq_refl)) ltac:(cbn; lia) Hl).
- apply IH; [|exact H2]. intros r Hr. apply Hin. destruct a; cbn [str_rngs]; [exact Hr | exact Hr | right; exact Hr].
Qed.

(* (ii) under the contract's premises (sh_avfprintf_icpt_realizesUx, FMsnprintfSx.v:210-247),
   seam_drop at the seam's R keeps the shadow hull of every named range whose shadow the walk reads
   (the destination, the format, the stack window [lo, lo + K), the musl prefix, each %s string: all
   carved), for every ly; and it never drops an application byte cjnorm keeps (the data bytes of the
   FILE, the cookie, the window, the destination, the format, the slots and the strings).  The FILE
   and the cookie need no hull: no interceptor check names them and vf_ready_a asks them app_ivl
   only.  The contract gives the window's bounds: lo = spZ - K >= ly_stk_lo >= 0 and spZ <= 2^47
   (GXA (2) and (4)). *)
Theorem seam_drop_keeps : forall ly (lo K s0 dn f : Z) (fmt ws : list Z) (args : list SPF.pf_arg) rd rs,
  0 <= lo -> 0 <= K -> lo + K <= 2 ^ 47 ->
  0 < s0 -> amem_range s0 dn ->
  0 < f -> amem_range f (Z.of_nat (length fmt) + 1) ->
  SFF.pf_args_asan rd rs ws args ->
  sd_hull_kept ly (seam_R s0 dn f fmt lo K ws args) s0 dn /\
  sd_hull_kept ly (seam_R s0 dn f fmt lo K ws args) f (Z.of_nat (length fmt) + 1) /\
  sd_hull_kept ly (seam_R s0 dn f fmt lo K ws args) lo K /\
  sd_hull_kept ly (seam_R s0 dn f fmt lo K ws args) (@sym N_img_asan 0x1029e) 9 /\
  (forall pa, Forall2 GPF.pt_parg_rel args pa -> args_kept ly (seam_R s0 dn f fmt lo K ws args) (map w64 ws) pa) /\
  (forall a : word, AF.app_mem (bv_unsigned a) -> seam_drop ly (seam_R s0 dn f fmt lo K ws args) a = MN.cj_drop tfibsegs a).
Proof.
intros ly lo K s0 dn f fmt ws args rd rs Hlo HK HlK Hs0 AMS Hf AMF HPA.
assert (Sm : @sym N_img_asan 0x1029e = 0x10b7c) by (vm_compute; reflexivity).
set (R := seam_R s0 dn f fmt lo K ws args).
split; [exact (hull_kept_carved ly R (s0, dn) (or_introl eq_refl) ltac:(cbn; lia) (amem_app s0 dn ltac:(lia) AMS))|].
split; [exact (hull_kept_carved ly R (f, Z.of_nat (length fmt) + 1) (or_intror (or_introl eq_refl)) ltac:(cbn; lia)
                 (amem_app f _ ltac:(lia) AMF))|].
split; [exact (hull_kept_carved ly R (lo, K) (or_intror (or_intror (or_introl eq_refl))) ltac:(cbn; lia)
                 ltac:(cbn; unfold AF.APPMEM_END; lia))|].
split; [exact (hull_kept_carved ly R (@sym N_img_asan 0x1029e, 9) (or_intror (or_intror (or_intror (or_introl eq_refl))))
                 ltac:(cbn [fst snd]; rewrite Sm; lia) ltac:(cbn [fst snd]; rewrite Sm; unfold AF.APPMEM_END; lia))|].
split; [intros pa Hpa; apply (args_kept_of_asan ly R rd rs ws args pa); [intros r Hr; right; right; right; right; exact Hr | exact HPA | exact Hpa]|].
intros a Ha. exact (seam_drop_app ly R a Ha).
Qed.

(* the contract's ecall_pre_x carries layout_ok (alx_layout_ok) (Step 3's first premise) *)
Section KP. Context {fx : YK11.FPState}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis alx_layout_ok : YCbqG.ARx_layout_ok_law tfibsegs ARx.

Lemma layout_of_preU : forall ly S Hp (W : world tfibsegs) regs mem md,
  FCiface.ecall_pre_x tfibsegs B ARx ly S Hp W regs mem md -> layout_ok ly.
Proof. intros ly S Hp W regs mem md (HAR & _). exact (alx_layout_ok ly S Hp W mem md HAR). Qed.

End KP.

(* the hulls of the seam's R are visible when the contract's (the destination's shadow_hull_vis,
   fmt_at's, pf_arg_asan's) and AR's (the window's stack shadow, the prefix's zero rodata shadow) are:
   Step 3's last premise at the seam's R *)
Lemma seam_R_hulls : forall (rd : Z -> option Z) rs s0 dn f fmt lo K ws args,
  shadow_hull_vis rd s0 dn -> SFF.fmt_at rd rs f fmt -> shadow_hull_vis rd lo K ->
  shadow_hull_vis rd (@sym N_img_asan 0x1029e) 9 -> SFF.pf_args_asan rd rs ws args ->
  Forall (fun r => shadow_hull_vis rd (fst r) (snd r)) (seam_R s0 dn f fmt lo K ws args).
Proof.
intros rd rs s0 dn f fmt lo K ws args HD HF HW HM HA. constructor; [exact HD|].
constructor; [destruct HF as (_ & _ & _ & _ & _ & HV); exact HV|].
constructor; [exact HW|]. constructor; [exact HM|].
revert ws HA. induction args as [|a args IH]; intros ws HA; [constructor|].
destruct ws as [|w ws]; [destruct HA|]. destruct HA as [H1 H2].
destruct a as [v|u|s]; cbn [str_rngs]; [exact (IH ws H2) | exact (IH ws H2)|].
constructor; [|exact (IH ws H2)]. cbv beta iota delta [SFF.pf_arg_asan] in H1.
destruct H1 as (_ & _ & _ & _ & _ & _ & _ & _ & HV). exact HV.
Qed.

(* ---- the drop is word-uniform on the shadow, so a range whose shadow bytes are kept has its
   whole hull kept ---- *)
Lemma word8_leb : forall l s s0, s / 8 = s0 / 8 -> (l * 8 <=? s) = (l * 8 <=? s0).
Proof.
intros l s s0 E. destruct (Z.leb_spec (l * 8) s), (Z.leb_spec (l * 8) s0); try reflexivity;
exfalso; Z.div_mod_to_equations; lia.
Qed.

Lemma word8_ltb : forall u s s0, s / 8 = s0 / 8 -> (s <? u * 8) = (s0 <? u * 8).
Proof.
intros u s s0 E. destruct (Z.ltb_spec s (u * 8)), (Z.ltb_spec s0 (u * 8)); try reflexivity;
exfalso; Z.div_mod_to_equations; lia.
Qed.

Lemma seam_drop_word : forall ly R s s0, 0xa2000 <= s0 -> s0 + 8 <= TASK_SIZE -> s / 8 = s0 / 8 ->
  seam_drop ly R (CJM.wa s) = seam_drop ly R (CJM.wa s0).
Proof.
intros ly R s s0 H1 H2 E.
assert (Rs : 0xa2000 <= s /\ s + 1 <= TASK_SIZE) by (unfold TASK_SIZE in *; Z.div_mod_to_equations; lia).
unfold seam_drop. rewrite (cj_keep_shadow_rng s0 ltac:(lia) ltac:(lia)), (cj_keep_shadow_rng s (proj1 Rs) (proj2 Rs)).
rewrite !CJM.wa_unsigned by (unfold TASK_SIZE in *; lia). cbn [orb]. f_equal.
- unfold dz_shadow, shb, word_meets. f_equal; [f_equal|].
  + change AF.LOWMEM_END with (268431360 * 8). apply word8_leb. exact E.
  + change AF.HIGHMEM_BEG with (2199291686912 * 8). apply word8_ltb. exact E.
  + rewrite E. reflexivity.
- f_equal. unfold in_hulls. induction R as [|r R IH]; [reflexivity|]. cbn [existsb]. rewrite IH. f_equal.
  unfold hullb. f_equal; [apply word8_leb; exact E|].
  replace (shadow_addr (fst r + snd r - 1) / 8 * 8 + 8) with ((shadow_addr (fst r + snd r - 1) / 8 + 1) * 8) by lia.
  apply word8_ltb. exact E.
Qed.

(* the hull of a sub-range lies in the hull of the range *)
Lemma sd_hull_kept_sub : forall ly R p n p' k, sd_hull_kept ly R p n -> p <= p' -> 0 < k -> p' + k <= p + n ->
  sd_hull_kept ly R p' k.
Proof.
intros ly R p n p' k K H1 H2 H3 s Hs. apply K. unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* every hull byte shares its word with the shadow byte of a byte of the range *)
Lemma hull_of_sh_kept : forall ly R p n, sh_kept ly R p n -> 0 < n -> AF.app_ivl p (p + n) -> sd_hull_kept ly R p n.
Proof.
intros ly R p n K Hn A s Hs.
assert (X : exists i, 0 <= i < n /\ s / 8 = AF.shadow_addr (p + i) / 8).
{ unfold shadow_addr, SHADOW_OFF, AF.shadow_addr, AF.ASAN_K in *.
  destruct (Z_lt_le_dec s (2147450880 + p / 8)) as [L1|L1].
  - exists 0. split; [lia|]. rewrite Z.add_0_r. Z.div_mod_to_equations. lia.
  - destruct (Z_le_gt_dec s (2147450880 + (p + n - 1) / 8)) as [L2|L2].
    + destruct (Z_le_gt_dec (8 * (s - 2147450880)) p) as [Kp|Kp].
      * exists 0. split; [lia|]. rewrite Z.add_0_r. f_equal. Z.div_mod_to_equations. lia.
      * exists (8 * (s - 2147450880) - p). split; [Z.div_mod_to_equations; lia|].
        replace (p + (8 * (s - 2147450880) - p)) with ((s - 2147450880) * 8) by lia.
        rewrite Z.div_mul by lia. f_equal. lia.
    + exists (n - 1). split; [lia|]. replace (p + (n - 1)) with (p + n - 1) by lia. Z.div_mod_to_equations. lia. }
destruct X as (i & Hi & E). pose proof (K i Hi) as Ki.
pose proof (AF.shadow_of_app _ (A (p + i) ltac:(lia))) as Si.
assert (Bi : 0xa2000 <= AF.shadow_addr (p + i) /\ AF.shadow_addr (p + i) + 8 <= TASK_SIZE)
  by (unfold AF.in_shadow, AF.LOWMEM_END, AF.LOWSHADOW_END, AF.HIGHSHADOW_BEG, AF.HIGHMEM_BEG, TASK_SIZE in *; lia).
rewrite (seam_drop_word ly R s (AF.shadow_addr (p + i)) (proj1 Bi) (proj2 Bi) E). exact Ki.
Qed.

(* ---- back from cjnormv: what the walk's store says of the harness's (for READY's clauses) ---- *)
(* a shadow byte cjnormv reads is a kept byte, read the same in cjstore *)
Lemma mrd_cjnormv_shadow : forall ly R H mem s b, AF.in_shadow s ->
  CJM.mrd tfibsegs (cjnormv ly R H mem) (CJM.wa s) = Some b ->
  seam_drop ly R (CJM.wa s) = false /\ CJM.mrd tfibsegs (cjstore H mem) (CJM.wa s) = Some b.
Proof.
intros ly R H mem s b Hs E.
assert (Hr : AF.LOWMEM_END <= s < AF.HIGHMEM_BEG)
  by (unfold AF.in_shadow, AF.LOWMEM_END, AF.LOWSHADOW_END, AF.HIGHSHADOW_BEG, AF.HIGHMEM_BEG in *; lia).
assert (Hu : bv_unsigned (CJM.wa s) = s) by (apply CJM.wa_unsigned; unfold AF.LOWMEM_END, AF.HIGHMEM_BEG in Hr; lia).
destruct (seam_drop ly R (CJM.wa s)) eqn:D.
- exfalso. revert E. unfold CJM.mrd, cjnormv, NG.gdrop_normalize. cbv beta. rewrite D. cbv iota. intros E.
  apply (CJM.seg_rom_seg tfibsegs _ b E). destruct (find_segment tfibsegs (bv_unsigned (CJM.wa s)) 1) eqn:Ef; [|reflexivity].
  exfalso. pose proof (tfib_seg_top (CJM.wa s) ltac:(rewrite Ef; discriminate)). unfold AF.LOWMEM_END in Hr. lia.
- split; [reflexivity|]. rewrite <- (mrd_cjnormv_keep ly R H mem _ D). exact E.
Qed.

(* a range addressable in cjnormv is addressable in cjstore, and its shadow bytes are kept *)
Lemma pf_rng_cjnormv_back : forall ly R H mem p n, AF.pf_rng (cjnormv ly R H mem) p n ->
  AF.pf_rng (cjstore H mem) p n /\ sh_kept ly R p n.
Proof.
intros ly R H mem p n (HN & (A1 & A2 & A3 & AD) & EN & SV). split.
- split; [exact HN|]. split; [|split; [exact EN | exact SV]].
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  intros i Hi. destruct (AD i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  exact (proj2 (mrd_cjnormv_shadow ly R H mem _ b (AF.shadow_of_app _ Ha) Hb)).
- intros i Hi. destruct (AD i Hi) as (Ha & b & Hb & _).
  exact (proj1 (mrd_cjnormv_shadow ly R H mem _ b (AF.shadow_of_app _ Ha) Hb)).
Qed.

(* the shadow byte of each byte of a range addressable in cjnormv is present in cjnormv *)
Lemma cjnormv_present_of_pf_rng : forall ly R H mem p n i, AF.pf_rng (cjnormv ly R H mem) p n -> 0 <= i < n ->
  cjnormv ly R H mem (Z_to_bv 64 (shadow_addr (p + i))) <> None.
Proof.
intros ly R H mem p n i (_ & (_ & _ & _ & AD) & _) Hi E. destruct (AD i Hi) as (Ha & b & Hb & _).
pose proof (AF.shadow_of_app _ Ha) as Hs.
assert (Esh : AF.shadow_addr (p + i) = shadow_addr (p + i))
  by (unfold AF.shadow_addr, AF.ASAN_K, shadow_addr, SHADOW_OFF; lia).
rewrite Esh in Hs, Hb.
assert (Hr : AF.LOWMEM_END <= shadow_addr (p + i) < AF.HIGHMEM_BEG)
  by (unfold AF.in_shadow, AF.LOWMEM_END, AF.LOWSHADOW_END, AF.HIGHSHADOW_BEG, AF.HIGHMEM_BEG in *; lia).
assert (Hu : bv_unsigned (Z_to_bv 64 (shadow_addr (p + i))) = shadow_addr (p + i))
  by (apply CJM.wa_unsigned; unfold AF.LOWMEM_END, AF.HIGHMEM_BEG in Hr; lia).
assert (Hf : find_segment tfibsegs (bv_unsigned (Z_to_bv 64 (shadow_addr (p + i)))) 1 = None).
{ destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 (shadow_addr (p + i)))) 1) eqn:Ef; [|reflexivity].
  exfalso. pose proof (tfib_seg_top _ ltac:(rewrite Ef; discriminate)) as X. rewrite Hu in X.
  unfold AF.LOWMEM_END in Hr. lia. }
change (CJM.mrd tfibsegs (cjnormv ly R H mem) (Z_to_bv 64 (shadow_addr (p + i))) = Some b) in Hb.
unfold CJM.mrd in Hb. rewrite E in Hb. exact (CJM.seg_rom_seg tfibsegs _ b Hb Hf).
Qed.

Lemma cjnormv_store : forall ly R H mem a, cjnormv ly R H mem a <> None -> cjstore H mem a <> None.
Proof.
intros ly R H mem a Hn E. apply Hn. unfold cjnormv, NG.gdrop_normalize. cbv beta.
destruct (seam_drop ly R a); [reflexivity | exact E].
Qed.

(* a kept hull the harness sees is seen in cjnormv *)
Lemma hull_cjnormv : forall ly R H mem p n, sd_hull_kept ly R p n ->
  shadow_hull_vis (aview tfibsegs H mem) p n ->
  shadow_hull_vis (fun a => option_map (fun b : byte => bv_unsigned b) (CJM.mrd tfibsegs (cjnormv ly R H mem) (CJM.wa a))) p n.
Proof.
intros ly R H mem p n K HV s Hs. cbv beta. rewrite (mrd_cjnormv_keep ly R H mem _ (K s Hs)).
pose proof (HV s Hs) as X. rewrite aview_mrd in X. exact X.
Qed.

(* ===================================================================================== *)
(* 8. Step 3: vis0_word_pres at cjnormv                                                     *)
(* ===================================================================================== *)

(* every vis0 zone (YG0f.v:303-306) lies in [0, 2^47) for a layout_ok ly; for the 64 KiB context-map
   zone, layout_ok bounds only (ly_C, 256) (YG0f.v:296), which is enough *)
Lemma vis0_zone_bounds : forall ly z, layout_ok ly -> In z (vis0_zones ly) -> 0 <= fst z /\ fst z + snd z <= 2 ^ 47.
Proof.
intros ly z LO Hz. pose proof ASAN_CEIL_range as [C1 _].
pose proof (lo_app _ LO) as A. unfold owned_extents in A.
apply Forall_cons_iff in A as [AP A]. apply Forall_cons_iff in A as [AQ A]. apply Forall_cons_iff in A as [AT A].
apply Forall_cons_iff in A as [AFs A]. apply Forall_cons_iff in A as [ANB A]. apply Forall_cons_iff in A as [ASB A].
apply Forall_cons_iff in A as [AC A]. apply Forall_cons_iff in A as [AD _].
pose proof (lo_space_in _ LO) as SP. pose proof (lo_img _ LO) as (I1 & _ & I2 & _).
destruct (lo_extra _ LO) as (_ & EX & _).
unfold in_app in AP, AQ, AT, AFs, ANB, ASB, AC, AD. cbn [fst snd] in AP, AQ, AT, AFs, ANB, ASB, AC, AD.
unfold kHighMemBeg, kLowShadowBeg, kImgLo, kImgEnd, kPrimResvSize, kSpaceSize, kRegionInfoOff, kPtrArrayResv,
  kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize, kCtxMapSize in *.
unfold vis0_zones in Hz. apply in_app_iff in Hz as [Hz|Hz].
- destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd];
    unfold kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize, kCtxMapSize, kPtrArrayResv,
      kRegionInfoOff; lia.
- pose proof (proj1 (Forall_forall _ _) EX z Hz) as (_ & _ & E1 & E2 & _). lia.
Qed.

(* so every in_vis0 byte is in the word test's guard *)
Lemma vis0_shadow_rng : forall ly a, layout_ok ly -> in_vis0 ly a -> AF.LOWMEM_END <= a < AF.HIGHMEM_BEG.
Proof.
intros ly a LO Va. unfold in_vis0 in Va. apply Exists_exists in Va as (v & Hv & Hin).
pose proof (proj1 (Forall_forall _ _) (lo_vis0 _ LO) v Hv) as X. apply Exists_exists in X as (z & Hz & Z1 & Z2).
destruct (vis0_zone_bounds ly z LO Hz) as [B1 B2]. unfold in_zr in Hin.
unfold shadow_addr, SHADOW_OFF, AF.LOWMEM_END, AF.HIGHMEM_BEG in *. Z.div_mod_to_equations. lia.
Qed.

(* THE PRESENCE FACT AR DOES NOT CARRY, at cjnormv (FMgxaSeamReady.word_vis consumes it):
   a visible in_vis0 band byte a sharing its 8-aligned word with a byte b present in cjnormv is
   present.  a's word meets ly_vis0 and is in the guard (layout_ok), so the word test drops b unless
   a hull of R carves it out; b is present, so it is carved; the hull's ends are multiples of 8, so a
   is in that hull too, the hull is visible, and a is kept. *)
Theorem vis0_word_pres_cjnormv : forall ly R H mem,
  layout_ok ly ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs H mem) (fst r) (snd r)) R ->
  forall a b, in_band_rw a -> in_vis0 ly a -> a / 8 = b / 8 -> H (Z_to_bv 64 a) = false ->
    cjnormv ly R H mem (Z_to_bv 64 b) <> None -> cjnormv ly R H mem (Z_to_bv 64 a) <> None.
Proof.
intros ly R H mem LO HV a b Hb Va E Ha Pb.
assert (Ra : kLowShadowBeg <= a < kHighShadowEnd)
  by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
unfold kLowShadowBeg, kHighShadowEnd in Ra.
assert (Rb : 0 <= b < 2 ^ 64) by (clear - Ra E; Z.div_mod_to_equations; lia).
pose proof (vis0_shadow_rng ly a LO Va) as Ga.
assert (Db : dz_shadow ly b = true).
{ unfold dz_shadow. apply andb_true_iff. split.
  - unfold shb. apply andb_true_iff. unfold AF.LOWMEM_END, AF.HIGHMEM_BEG in *.
    split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ga E; Z.div_mod_to_equations; lia.
  - unfold in_vis0 in Va. apply Exists_exists in Va as (v & Hv & Hin). unfold in_zr in Hin.
    apply existsb_exists. exists v. split; [exact Hv|]. unfold word_meets. rewrite <- E.
    apply andb_true_iff. split; apply Z.ltb_lt; clear - Hin; Z.div_mod_to_equations; lia. }
assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by exact (CJM.wa_unsigned b Rb).
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by exact (CJM.wa_unsigned a ltac:(lia)).
assert (Kb : seam_drop ly R (Z_to_bv 64 b) = false).
{ destruct (seam_drop ly R (Z_to_bv 64 b)) eqn:D; [|reflexivity]. exfalso. apply Pb.
  unfold cjnormv, NG.gdrop_normalize. cbv beta. rewrite D. reflexivity. }
assert (Hh : in_hulls R b = true).
{ unfold seam_drop in Kb. rewrite Ub, Db in Kb. apply orb_false_iff in Kb as [_ Kb].
  cbn [andb] in Kb. apply negb_false_iff in Kb. exact Kb. }
unfold in_hulls in Hh. apply existsb_exists in Hh as (r & Hr & Hbr).
unfold hullb in Hbr. apply andb_true_iff in Hbr as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
set (l := shadow_addr (fst r) / 8) in *. set (u := shadow_addr (fst r + snd r - 1) / 8) in *.
assert (Har : l * 8 <= a < u * 8 + 8) by (clearbody l u; clear - B1 B2 E; Z.div_mod_to_equations; lia).
assert (Va' : aview tfibsegs H mem a <> None).
{ apply (proj1 (Forall_forall _ _) HV r Hr). exact Har. }
assert (Ka : seam_drop ly R (Z_to_bv 64 a) = false).
{ unfold seam_drop. rewrite Ua.
  assert (Hha : in_hulls R a = true).
  { unfold in_hulls. apply existsb_exists. exists r. split; [exact Hr|].
    unfold hullb. apply andb_true_iff. split; [apply Z.leb_le; exact (proj1 Har) | apply Z.ltb_lt; exact (proj2 Har)]. }
  rewrite Hha. cbn [negb]. rewrite andb_false_r, orb_false_r.
  apply (cj_keep_shadow_rng a); try unfold TASK_SIZE; lia. }
unfold cjnormv, NG.gdrop_normalize. cbv beta. rewrite Ka. unfold cjstore, mrestrict. rewrite Ha. cbv beta iota.
intros Hm. apply Va'. unfold aview, mbyte, mrestrict. rewrite Ha, Hm. cbv beta iota.
assert (Hs : find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1 = None).
{ destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) eqn:Ef; [|reflexivity].
  exfalso. pose proof (tfib_seg_top (Z_to_bv 64 a) ltac:(rewrite Ef; discriminate)). lia. }
change (option_map (fun b : byte => bv_unsigned b)
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.PropExec.seg_rom tfibsegs (Z_to_bv 64 a)) = None).
rewrite (MN.seg_rom_unmapped tfibsegs (Z_to_bv 64 a) Hs). reflexivity.
Qed.

(* the simple shape on record: R = [(D, dn)], the destination alone *)
Corollary vis0_word_pres_cjnormv_dest : forall ly H mem D dn,
  layout_ok ly -> shadow_hull_vis (aview tfibsegs H mem) D dn ->
  forall a b, in_band_rw a -> in_vis0 ly a -> a / 8 = b / 8 -> H (Z_to_bv 64 a) = false ->
    cjnormv ly [(D, dn)] H mem (Z_to_bv 64 b) <> None -> cjnormv ly [(D, dn)] H mem (Z_to_bv 64 a) <> None.
Proof.
intros ly H mem D dn LO HD. apply (vis0_word_pres_cjnormv ly [(D, dn)] H mem LO).
constructor; [exact HD | constructor].
Qed.

Corollary dest_hull_kept : forall ly D dn, 0 <= D -> D + dn <= AF.APPMEM_END -> sd_hull_kept ly [(D, dn)] D dn.
Proof. intros ly D dn H0 H1. exact (hull_kept_carved ly [(D, dn)] (D, dn) (or_introl eq_refl) H0 H1). Qed.

End V.
