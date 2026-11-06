(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMgxaSeamReadyX.v, with its module paths and addresses changed; 561 of its 1025 lines of code are new or changed and 294 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamReady.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 8 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMgxaSeamReady.table); by hand (numerals.py HAND, reason in the table): 0x20d00 -> 0x20f98; GXA symbol keys kept (0x1029e); names: record RT_IImgA -> A_img RecAsanVfA.N_img_asan_vf; hand checks: FMgxa_mem STOP: names differ: fm FMgxa_mem.copy_ready/set_ready = disco lib/<img>/RT_gxa_calls_mem.copy_ready/set_ready; fm memcpy_stack_contract_A/memset_stack_contract_A (at A_img) = disco lib/<img>/RT_gxa_calls_mem_vf.memcpy_stack_contract_Avf/_Avf (Y: _Bvf); map each use by hand. *)
(* Modified by Theorem Labs, 2026-10: hand check of the STOP module FMgxa_mem (G9 row P7-A-ready-FMgxaSeamReady): fm's FMgxa_mem.copy_ready / set_ready are disco lib/A/RT_gxa_calls_mem.v copy_ready / set_ready (same text; set_ready guarded by 0 <= n as fm 3899f140f93, a working branch 97f92fff44e), so the Require and the alias FMM name lib.A.RT_gxa_calls_mem; the comment address of sym 0x1029e is disco's 0x10b7c (lib/A/FMgxaSeamShadow.v sym_musl_prefix). The six lemmas that reach the world field w_H8 (word_vis .. seam_ready_holds) read it from G9 P1. Evidence: (internal path). *)
(* READINESS OF THE THREE INTERCEPTORS FROM LOCAL SHADOW FACTS, for the GXA seam at musl vfprintf
   (FMgxaSeam.v READY, :317-328).

   The interceptors' range check chk_ok (lib/A/Bz/A/I_qck.v:31) reads, for a range [p, p + n):
   - the shadow byte of each byte (acc), which GXA's pf_rng gives (AsanFacts.v:64-68 addr_byte);
   - for 1 <= n <= 64, the two 8-byte ALIGNED shadow words at al8 (shad p) and al8 (shad (p + n - 1))
     (qc_words), which pf_rng does not give: those words also hold the shadow bytes of the bytes
     around the range.
   FMgxa_bzcj.v:218 chk_ok_of_pf_rng takes the words from the GLOBAL AsanFacts.shadow_rw.  Here they
   come from the hull the harness states per named range, shadow_hull_vis (YG0d.v:310): every byte
   from shadow_addr x / 8 * 8 to shadow_addr (x + n - 1) / 8 * 8 + 8 is readable.  That interval is
   exactly the two aligned words and everything between them.

   1. the generic lemmas over any CJ store m, read through sview m (the reader aview reads cjstore
      with, FMgxaSeamBase.aview_mrd): qc_words_of_hull_m, hull_sub, chk_ok_of_pf_rng_loc;
   2. the forms over the harness's store (qc_words_of_hull, chk_ok_of_pf_rng_hull);
   3. moving a hull to a store that keeps the shadow (hull_kept), and from the harness's reader to
      any store that keeps the shadow of the per-call store GXA runs on, FMgxaSeamNorm.cjnormv ly R,
      when cjnormv keeps the hull's bytes (NM.sd_hull_kept) (hull_kept_v);
   4. the three ready predicates (FMgxa_mem.copy_ready / set_ready, RT_gxa_strnlen.strn_ready) from
      pf_rng and the hull of exactly the range each check reads, with the runtime cells as before:
      copy_ready_intro_loc, set_ready_intro_loc, strn_ready_intro_loc, and their cjnormv forms;
   5. READY's clauses (FMgxaSeamGuard.v seam_calls_ready) at cjnormv ly R from READY's premises:
      - what the premises give: the runtime's cells at every store READY quantifies over
        (seam_cells: the owned bytes are application memory, where cjnormv drops what cjnorm drops,
        NM.seam_drop_app), a visible hull over any stack range (stack_rng, stack_hull), kept by
        cjnormv inside the stack window R carves out (stack_rng_v), and the musl prefix's hull
        (prefix_hull: AR's zero shadow of the image's first range);
      - the clauses that close from these: memcpy into vfprintf's buffer from that buffer or the
        stack (seam_ready_copy_stack) and memset (seam_ready_set: FMgxa_mem.set_ready asks its facts
        only for 0 <= n, FMgxa_mem.v:222, so the clause's Dst + N + 8 <= q - 368 bounds sp);
      - the clauses that take the hull of a range named only by pf_rng as a premise: memcpy
        (seam_ready_copy_hull) and strnlen (seam_ready_strn_hull);
      - the destination's facts from READY's premises: R carves the destination out and its hull is
        visible; READY carries 0 <= D, dn <= 2 ^ 40 and its band bound 8 bytes past its end
        (amem_range D (dn + 8), the contract's GXA (5)), as its contract does.  The band bound gives
        the bytes past the destination's end that pf_rng reads (dest_tail_of_amem8), and with them
        the destination's pf_rng (seam_dest_rng) and the memcpy clause up to the source hull
        (seam_ready_dest).
   6. the hull of a range named only by pf_rng, from the world's w_H8 (YA0n.v:25), AR's shadow
      presence and the hulls of R, and READY from READY's premises (seam_ready_holds):
      - each shadow byte of the range is present in cjnormv (NM.cjnormv_present_of_pf_rng); a byte s
        of the two aligned words around them shares its word with one of those bytes s0, so w_H8
        makes s visible (word_vis) and s is readable: in U by upoisoned, a client byte by
        YG0q.client_band_vis, any other byte by ahs_pres (YG0n.v:442-444) when s is not in_vis0;
      - an in_vis0 byte that is not a client byte nor in U is NOT covered by AR: layout_ok's
        lo_vis0 (YG0f.v:332-333) puts every ly_vis0 entry inside the shadow of a vis0 zone (T, F, NB,
        SB, C, D, Q, region info, the image, the extra zones), so such bytes are band bytes, and
        ahs_pres gives no presence for a visible one.  cjnormv drops a band word that meets ly_vis0
        unless a hull of R carves it out, so s0 present in cjnormv puts s in a hull of R; the hulls
        of R are visible, so cjnormv keeps s and holds it (NM.vis0_word_pres_cjnormv), and so does
        the harness's store (NM.cjnormv_store);
      - seam_ready_holds: READY at fm's three predicates, for every R that carves out the
        destination and the stack window and whose hulls the harness sees.

   THE DOCUMENTED CONTROL AGAINST THE OLD set_ready.  Before 3899f140f93, FMgxa_mem.set_ready asked
   sp < 2 ^ 63 at every n (FMgxa_mem.v:219-224 at 8c70fb561b7).  Against that set_ready this file
   proved the two lemmas below (proofs at e36171fe839, lib/A/FMgxaSeamReady.v:419-440; SG is
   lib/A/FMgxaSeamGuard.v); cbe21760a93 removed them:

     Lemma seam_calls_ready_false : forall (m : word -> option byte) (q lo Fp CK D : Z) (dn : nat),
       ~ SG.seam_calls_ready FMM.copy_ready FMM.set_ready RSN.strn_ready m q lo Fp CK D dn.

     Lemma pc_guard_set_false : forall out_ready strn_ready (INV : (word -> option byte) -> Prop)
         (m : word -> option byte) (lo q : Z) (W : list (Z * Z)),
       ~ GCA.pc_guard out_ready FMM.set_ready strn_ready INV m lo q W.

   Both proofs instantiate the memset clause at sp = Dst = Z.max (lo + SET_DEPTH) (2 ^ 63) with the
   negative N = q - 376 - sp (q - 8 - sp for pc_guard), which the clause's only bound Dst + N + 8 <= ...
   allows, and read sp < 2 ^ 63 off set_ready.  They no longer build: set_ready is now
   0 <= n -> (...) (FMgxa_mem.v:222-223), so at that negative N it holds vacuously and gives no
   sp < 2 ^ 63.  The memset clause they refuted now closes (seam_ready_set). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YG0q YI04 YA0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMgxaSeamBase FMgxaSeamShadow.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.MemNorm.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_vfprintf_snf.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Common.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memcpyw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memsetw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec.StrFun.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNormG.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNorm.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_bridge_seam.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_calls_mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_strnlen.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamGuard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module CJM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Module GAF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Module GCC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.StrnlenCall.
Module BSh := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.Shadow.
Module BR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_m2s.
Module BK := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_qck.
Module BMW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_strnlenw.
Module NM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNorm.
Module NG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNormG.
(* this file does not Import RStep, where the image's symbol map `sym` lives *)
Module RSt := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RStep.
Module BC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_bridge_seam.
Module FMM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_calls_mem.
Module RSN := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_strnlen.
Module SG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamGuard.
Module BSF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec.StrFun.
Module MN := OSSVerify.Proofs.reac_pw.fuzz_link.lib.MemNorm.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Module GXI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GCA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GV := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_vfprintf_snf.
Module BzPE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Common.PropExec.
Module BzI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.ImageA.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Module BzCl := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Step.
(* strn_ready counts with the Bz tree's strnlen_res (RT_gxa_strnlen.v:100) *)
#[local] Abbreviation strnlen_res := BSF.strnlen_res.

#[local] Existing Instance N_img_asan_vf.

(* ===================================================================================== *)
(* 1. the generic lemmas, over any CJ store                                                *)
(* ===================================================================================== *)

(* the reader of a CJ store, the way the harness's aview reads cjstore (FMgxaSeamBase.aview_mrd) *)
Definition sview (m : word -> option byte) : Z -> option Z :=
  fun a => option_map (fun b : byte => bv_unsigned b) (CJM.mrd tfibsegs m (CJM.wa a)).

(* the quick check's aligned word is the hull's bound: al8 (shad a) = shadow_addr a / 8 * 8 *)
Lemma al8_shad_hull : forall a, BQ.al8 (BSh.shad a) = shadow_addr a / 8 * 8.
Proof.
intros a. unfold BQ.al8, BSh.shad, BSh.SHB, shadow_addr, SHADOW_OFF.
replace (a / 8 + 2147450880) with (2147450880 + a / 8) by lia. lia.
Qed.

Lemma hull_lo_le_hi : forall x n, 0 < n -> shadow_addr x / 8 * 8 <= shadow_addr (x + n - 1) / 8 * 8.
Proof.
intros x n Hn. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

(* the hull of a sub-range lies in the hull of the range *)
Lemma hull_sub : forall (rd : Z -> option Z) p n p' k,
  shadow_hull_vis rd p n -> p <= p' -> 0 < k -> p' + k <= p + n -> shadow_hull_vis rd p' k.
Proof.
intros rd p n p' k HV H1 H2 H3 s Hs. apply HV.
assert (L : shadow_addr p / 8 * 8 <= shadow_addr p' / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (U : shadow_addr (p' + k - 1) / 8 * 8 <= shadow_addr (p + n - 1) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Lemma hull_prefix : forall (rd : Z -> option Z) p n k,
  shadow_hull_vis rd p n -> 0 < k <= n -> shadow_hull_vis rd p k.
Proof. intros rd p n k HV Hk. exact (hull_sub rd p n p k HV ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* the quick check's two aligned shadow words, from the hull *)
Lemma qc_words_of_hull_m : forall (m : word -> option byte) p n,
  0 <= p -> 0 < n -> p + n <= 2 ^ 63 ->
  shadow_hull_vis (sview m) p n -> BQ.qc_words m p n.
Proof.
intros m p n Hp Hn Hpn HV _.
pose proof (hull_lo_le_hi p n Hn) as LH.
assert (B0 : 0 <= shadow_addr p / 8 * 8).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
  apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. }
assert (B1 : shadow_addr (p + n - 1) / 8 * 8 + 8 <= 2 ^ 64).
{ pose proof (Z.mul_div_le (shadow_addr (p + n - 1)) 8 ltac:(lia)).
  assert (shadow_addr (p + n - 1) <= SHADOW_OFF + (p + n - 1)).
  { unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
  unfold SHADOW_OFF in *. lia. }
assert (HB : forall s, shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 ->
           exists b, CJM.mrd tfibsegs m (CJM.wa s) = Some b).
{ intros s Hs. pose proof (HV s Hs) as V. unfold sview in V.
  destruct (CJM.mrd tfibsegs m (CJM.wa s)) as [b|]; [exists b; reflexivity | exfalso; apply V; reflexivity]. }
exists (BC.word_of_mem m (BQ.al8 (BSh.shad p))), (BC.word_of_mem m (BQ.al8 (BSh.shad (p + n - 1)))).
rewrite !al8_shad_hull.
split; apply BC.ro_C8_of_vis; try lia; intros j Hj.
- destruct (HB (shadow_addr p / 8 * 8 + j) ltac:(lia)) as (b & E).
  exists b. apply BC.bytes_at1_of_mrd; [lia | exact E].
- destruct (HB (shadow_addr (p + n - 1) / 8 * 8 + j) ltac:(lia)) as (b & E).
  exists b. apply BC.bytes_at1_of_mrd; [lia | exact E].
Qed.

(* the range check on [p, p + k) from pf_rng over [p, p + L) and the hull of exactly [p, p + k) *)
Lemma chk_ok_of_pf_rng_loc : forall (m : word -> option byte) p L k,
  GAF.pf_rng m p L -> (0 < k -> shadow_hull_vis (sview m) p k) -> 0 <= k <= L -> BQ.chk_ok m p k.
Proof.
intros m p L k (HN & (Hp & HL & HpL & AD) & _ & SEVEN) HV Hk.
unfold GAF.APPMEM_END in HpL.
split; [|split].
- intros i Hi. destruct (AD i ltac:(lia)) as (APP & b & Hb & Hok).
  exists b. split.
  + rewrite BC.shad_eq. apply BC.bytes_at1_of_mrd; [| exact Hb].
    unfold GAF.shadow_addr, GAF.ASAN_K. Z.div_mod_to_equations. lia.
  + apply BC.sh_ok_of_shadow_ok. exact Hok.
- destruct (Z.eq_dec k 0) as [->|Hk0]; [intros H; lia|].
  apply qc_words_of_hull_m; [lia | lia | lia | apply HV; lia].
- intros Hk0. split; [| lia].
  destruct (AD 0 ltac:(lia)) as (A0 & _). rewrite Z.add_0_r in A0.
  pose proof (SEVEN (k - 1) ltac:(lia)) as A7.
  unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd.
  unfold GAF.app_mem, GAF.LOWMEM_END, GAF.HIGHMEM_BEG, GAF.APPMEM_END in A0, A7. lia.
Qed.

(* the same with the hull of the whole range *)
Lemma chk_ok_of_pf_rng_hull_m : forall (m : word -> option byte) p n k,
  GAF.pf_rng m p n -> shadow_hull_vis (sview m) p n -> 0 <= k <= n -> BQ.chk_ok m p k.
Proof.
intros m p n k PF HV Hk. apply (chk_ok_of_pf_rng_loc m p n k PF); [|exact Hk].
intros Hk0. exact (hull_prefix _ p n k HV ltac:(lia)).
Qed.

(* ===================================================================================== *)
(* 2. over the harness's store                                                             *)
(* ===================================================================================== *)

Section V. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma aview_sview : forall H mem, aview tfibsegs H mem = sview (cjstore H mem).
Proof. reflexivity. Qed.

Lemma qc_words_of_hull : forall H mem p n, 0 <= p -> 0 < n -> p + n <= 2 ^ 63 ->
  shadow_hull_vis (aview tfibsegs H mem) p n -> BQ.qc_words (cjstore H mem) p n.
Proof. intros H mem p n Hp Hn Hpn HV. exact (qc_words_of_hull_m (cjstore H mem) p n Hp Hn Hpn HV). Qed.

Lemma chk_ok_of_pf_rng_hull : forall H mem p n k,
  GAF.pf_rng (cjstore H mem) p n -> shadow_hull_vis (aview tfibsegs H mem) p n ->
  0 <= k <= n -> BQ.chk_ok (cjstore H mem) p k.
Proof. intros H mem p n k PF HV Hk. exact (chk_ok_of_pf_rng_hull_m (cjstore H mem) p n k PF HV Hk). Qed.

End V.

(* ===================================================================================== *)
(* 3. a hull carries to every store that keeps the shadow                                 *)
(* ===================================================================================== *)

(* the hull of a range of application memory lies in ASan's shadow *)
Lemma hull_in_shadow : forall p n s, 0 < n -> GAF.app_ivl p (p + n) ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> GAF.in_shadow s.
Proof.
intros p n s Hn HA Hs.
pose proof (HA p ltac:(lia)) as A0. pose proof (HA (p + n - 1) ltac:(lia)) as A1.
unfold GAF.app_mem in A0, A1.
assert (C : p + n - 1 < GAF.LOWMEM_END \/ GAF.HIGHMEM_BEG <= p).
{ destruct (Z_lt_le_dec (p + n - 1) GAF.LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct A0 as [A0|A0]; [|lia].
  exfalso. pose proof (HA GAF.LOWMEM_END ltac:(lia)) as X.
  unfold GAF.app_mem, GAF.LOWMEM_END, GAF.HIGHMEM_BEG, GAF.APPMEM_END in X. lia. }
unfold GAF.in_shadow. unfold shadow_addr, SHADOW_OFF in Hs.
unfold GAF.LOWMEM_END, GAF.LOWSHADOW_END, GAF.HIGHSHADOW_BEG, GAF.HIGHMEM_BEG, GAF.APPMEM_END in *.
clear HA.
destruct C as [C|C]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma hull_kept : forall (m m' : word -> option byte) p n, GAF.meta_kept m m' ->
  0 < n -> GAF.app_ivl p (p + n) ->
  shadow_hull_vis (sview m) p n -> shadow_hull_vis (sview m') p n.
Proof.
intros m m' p n MK Hn HA HV s Hs.
pose proof (MK s (hull_in_shadow p n s Hn HA Hs)) as E. pose proof (HV s Hs) as V.
unfold sview in *.
destruct (CJM.mrd tfibsegs m (CJM.wa s)) as [b|] eqn:Em; [|exfalso; apply V; reflexivity].
assert (E' : CJM.mrd tfibsegs m' (CJM.wa s) = Some b) by (etransitivity; [exact E | exact Em]).
rewrite E'. discriminate.
Qed.

Lemma pf_rng_app : forall (m : word -> option byte) p n, GAF.pf_rng m p n -> GAF.app_ivl p (p + n).
Proof. intros m p n (_ & AD & _). exact (GAF.addressable_app m p n AD). Qed.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* from the harness's reader to a store m' that keeps the per-call store's shadow (the seam's m' of
   seam_calls_ready: meta_kept (cjnormv ly R H mem) m'), for a hull cjnormv keeps *)
Lemma hull_kept_v : forall ly R H mem (m' : word -> option byte) p n,
  GAF.meta_kept (NM.cjnormv ly R H mem) m' -> NM.sd_hull_kept ly R p n ->
  0 < n -> GAF.app_ivl p (p + n) ->
  shadow_hull_vis (aview tfibsegs H mem) p n -> shadow_hull_vis (sview m') p n.
Proof.
intros ly R H mem m' p n MK K Hn HA HV.
exact (hull_kept (NM.cjnormv ly R H mem) m' p n MK Hn HA (NM.hull_cjnormv ly R H mem p n K HV)).
Qed.

End K.

(* ===================================================================================== *)
(* 4. the three ready predicates from local facts                                         *)
(* ===================================================================================== *)

(* FMgxa_mem.copy_ready_intro (FMgxa_mem.v:199) with shadow_rw replaced by the hulls of the two
   ranges memcpy checks, [d, d + n) and [s, s + n) *)
Lemma copy_ready_intro_loc : forall (m : word -> option byte) sp d s n Ld Ls,
  BR.kHighShadowEnd < sp - GCC.COPY_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GCC.COPY_DEPTH \/ sp <= d) ->
  GAF.pf_rng m d Ld -> GAF.pf_rng m s Ls -> n <= Ld -> n <= Ls ->
  (0 < n -> shadow_hull_vis (sview m) d n) -> (0 < n -> shadow_hull_vis (sview m) s n) ->
  BR.m2s_cells m -> BMW.icells m ->
  FMM.copy_ready m sp d s n.
Proof.
intros m sp d s n Ld Ls H1 H2 N0 SEPD PD PS HD HS VD VS C1 C2.
split; [exact H1|]. split; [exact H2|].
split; [destruct PD as (_ & (_ & _ & Hpn & _) & _); unfold GAF.APPMEM_END in Hpn; lia|].
split; [destruct PS as (_ & (_ & _ & Hpn & _) & _); unfold GAF.APPMEM_END in Hpn; lia|].
split; [exact SEPD|].
split; [exact (chk_ok_of_pf_rng_loc m s Ls n PS VS ltac:(lia))|].
split; [exact (chk_ok_of_pf_rng_loc m d Ld n PD VD ltac:(lia))|].
exact (conj C1 C2).
Qed.

(* FMgxa_mem.set_ready_intro (FMgxa_mem.v:298) with the hull of [d, d + n) *)
Lemma set_ready_intro_loc : forall (m : word -> option byte) sp d n Ld,
  BR.kHighShadowEnd < sp - GSC.SET_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GSC.SET_DEPTH \/ sp <= d) ->
  GAF.pf_rng m d Ld -> n <= Ld -> (0 < n -> shadow_hull_vis (sview m) d n) ->
  BR.m2s_cells m -> BSW.icells_ms m ->
  FMM.set_ready m sp d n.
Proof.
intros m sp d n Ld H1 H2 N0 SEPD PD HD VD C1 C2 _.
split; [exact H1|]. split; [exact H2|].
split; [destruct PD as (_ & (_ & _ & Hpn & _) & _); unfold GAF.APPMEM_END in Hpn; lia|].
split; [exact SEPD|].
split; [exact (chk_ok_of_pf_rng_loc m d Ld n PD VD ltac:(lia))|].
exact (conj C1 C2).
Qed.

(* RT_gxa_strnlen.strn_ready_intro (RT_gxa_strnlen.v:153) with the hull of the bytes strnlen checks,
   [S, S + min (strnlen_res N buf + 1) N) *)
Lemma strn_ready_intro_loc : forall (m : word -> option byte) sp S N L buf,
  BR.kHighShadowEnd < sp - GNC.STRN_DEPTH -> sp < 2 ^ 63 ->
  GAF.pf_rng m S L -> Z.min (strnlen_res N buf + 1) N <= L ->
  (0 < Z.min (strnlen_res N buf + 1) N -> shadow_hull_vis (sview m) S (Z.min (strnlen_res N buf + 1) N)) ->
  BR.m2s_cells m -> BNW.icells_sn m -> BCW.icells_mc m -> BNW.icells_sns m ->
  RSN.strn_ready m sp S N buf.
Proof.
intros m sp S N L buf H1 H2 PR HL VS C1 C2 C3 C4.
assert (K0 : 0 <= Z.min (strnlen_res N buf + 1) N \/ Z.min (strnlen_res N buf + 1) N < 0) by lia.
split; [exact H1|]. split; [exact H2|]. split.
- destruct PR as (_ & (_ & HL0 & Hpn & _) & _). unfold GAF.APPMEM_END in Hpn. lia.
- split.
  + destruct K0 as [K0|K0].
    * exact (chk_ok_of_pf_rng_loc m S L _ PR VS ltac:(lia)).
    * split; [intros i Hi; lia|]. split; [intros Hk; lia | intros Hk; lia].
  + exact (conj C1 (conj C2 (conj C3 C4))).
Qed.

(* ---- the cjnormv forms: the facts at the harness's store, the predicate at a store m' that keeps
   the per-call store's shadow (m' = cjnormv ly R H mem itself, or any munch of it over application
   memory, AsanFacts.munch_meta).  The range's shadow bytes and the hull's bytes must be ones
   cjnormv keeps (NM.sh_kept, NM.sd_hull_kept) ---- *)
Section N. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma loc_of_view : forall ly R H mem (m' : word -> option byte) p L k,
  GAF.meta_kept (NM.cjnormv ly R H mem) m' -> GAF.pf_rng (cjstore H mem) p L -> NM.sh_kept ly R p L ->
  0 <= k <= L -> (0 < k -> NM.sd_hull_kept ly R p k) ->
  (0 < k -> shadow_hull_vis (aview tfibsegs H mem) p k) ->
  GAF.pf_rng m' p L /\ (0 < k -> shadow_hull_vis (sview m') p k).
Proof.
intros ly R H mem m' p L k MK PF KS Hk KH HV.
split; [exact (GAF.pf_rng_kept _ _ p L (NM.pf_rng_cjnormv ly R H mem p L KS PF) MK)|].
intros Hk0. apply (hull_kept_v ly R H mem m' p k MK (KH Hk0) Hk0); [|exact (HV Hk0)].
exact (GAF.app_ivl_sub p (p + L) p (p + k) (pf_rng_app _ p L PF) ltac:(lia) ltac:(lia)).
Qed.

Lemma copy_ready_intro_cjnormv : forall ly R H mem (m' : word -> option byte) sp d s n Ld Ls,
  GAF.meta_kept (NM.cjnormv ly R H mem) m' ->
  BR.kHighShadowEnd < sp - GCC.COPY_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GCC.COPY_DEPTH \/ sp <= d) ->
  GAF.pf_rng (cjstore H mem) d Ld -> NM.sh_kept ly R d Ld ->
  GAF.pf_rng (cjstore H mem) s Ls -> NM.sh_kept ly R s Ls -> n <= Ld -> n <= Ls ->
  (0 < n -> NM.sd_hull_kept ly R d n) -> (0 < n -> NM.sd_hull_kept ly R s n) ->
  (0 < n -> shadow_hull_vis (aview tfibsegs H mem) d n) ->
  (0 < n -> shadow_hull_vis (aview tfibsegs H mem) s n) ->
  BR.m2s_cells m' -> BMW.icells m' ->
  FMM.copy_ready m' sp d s n.
Proof.
intros ly R H mem m' sp d s n Ld Ls MK H1 H2 N0 SEPD PD KD PS KS HD HS KHD KHS VD VS C1 C2.
destruct (loc_of_view ly R H mem m' d Ld n MK PD KD ltac:(lia) KHD VD) as [PD' VD'].
destruct (loc_of_view ly R H mem m' s Ls n MK PS KS ltac:(lia) KHS VS) as [PS' VS'].
exact (copy_ready_intro_loc m' sp d s n Ld Ls H1 H2 N0 SEPD PD' PS' HD HS VD' VS' C1 C2).
Qed.

Lemma set_ready_intro_cjnormv : forall ly R H mem (m' : word -> option byte) sp d n Ld,
  GAF.meta_kept (NM.cjnormv ly R H mem) m' ->
  BR.kHighShadowEnd < sp - GSC.SET_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GSC.SET_DEPTH \/ sp <= d) ->
  GAF.pf_rng (cjstore H mem) d Ld -> NM.sh_kept ly R d Ld -> n <= Ld ->
  (0 < n -> NM.sd_hull_kept ly R d n) -> (0 < n -> shadow_hull_vis (aview tfibsegs H mem) d n) ->
  BR.m2s_cells m' -> BSW.icells_ms m' ->
  FMM.set_ready m' sp d n.
Proof.
intros ly R H mem m' sp d n Ld MK H1 H2 N0 SEPD PD KD HD KHD VD C1 C2.
destruct (loc_of_view ly R H mem m' d Ld n MK PD KD ltac:(lia) KHD VD) as [PD' VD'].
exact (set_ready_intro_loc m' sp d n Ld H1 H2 N0 SEPD PD' HD VD' C1 C2).
Qed.

Lemma strn_ready_intro_cjnormv : forall ly R H mem (m' : word -> option byte) sp S N L buf,
  GAF.meta_kept (NM.cjnormv ly R H mem) m' ->
  BR.kHighShadowEnd < sp - GNC.STRN_DEPTH -> sp < 2 ^ 63 ->
  GAF.pf_rng (cjstore H mem) S L -> NM.sh_kept ly R S L -> Z.min (strnlen_res N buf + 1) N <= L ->
  (0 < Z.min (strnlen_res N buf + 1) N -> NM.sd_hull_kept ly R S (Z.min (strnlen_res N buf + 1) N)) ->
  (0 < Z.min (strnlen_res N buf + 1) N ->
     shadow_hull_vis (aview tfibsegs H mem) S (Z.min (strnlen_res N buf + 1) N)) ->
  BR.m2s_cells m' -> BNW.icells_sn m' -> BCW.icells_mc m' -> BNW.icells_sns m' ->
  RSN.strn_ready m' sp S N buf.
Proof.
intros ly R H mem m' sp S N L buf MK H1 H2 PR KS HL KH VS C1 C2 C3 C4.
destruct (Z_le_gt_dec 0 (Z.min (strnlen_res N buf + 1) N)) as [K0|K0].
- destruct (loc_of_view ly R H mem m' S L (Z.min (strnlen_res N buf + 1) N) MK PR KS ltac:(lia) KH VS)
    as [PR' VS'].
  exact (strn_ready_intro_loc m' sp S N L buf H1 H2 PR' HL VS' C1 C2 C3 C4).
- apply (strn_ready_intro_loc m' sp S N L buf H1 H2); try assumption.
  + exact (GAF.pf_rng_kept _ _ S L (NM.pf_rng_cjnormv ly R H mem S L KS PR) MK).
  + intros Hk. lia.
Qed.

End N.

(* ===================================================================================== *)
(* 5. READY's clauses (FMgxaSeam.v:317-328, FMgxaSeamGuard.v:99-112): what closes          *)
(* ===================================================================================== *)

(* ---- the runtime's fixed cells as the interceptors read them.  bz_mrd_mbyte .. cells_cons8 are
   a working branch 3b35fff5df2 lib/A/FMrt_pre.v:77-233 (that file is not on this branch), proofs
   unchanged up to module names and SnUpoison.wz for its u64z ---- *)
Lemma bz_mrd_mbyte : forall (m : word -> option byte) a, BzM.mrd BzI.asegs m (BzM.wa a) = mbyte tfibsegs m a.
Proof. intros m a. reflexivity. Qed.

Lemma le_byte1 : forall v, 0 <= v < 256 -> Z_to_bv 8 (YO0f.le_byte v 1 0) = Z_to_bv 8 v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia.
reflexivity.
Qed.

Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le8_nth : forall v k, 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  nth_error (BzM.le8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (YO0f.le_byte v 8 k)).
Proof.
intros v k Hv Hk. unfold BzM.le8, word_to_le_bytes. rewrite nth_le_bytes by exact Hk.
rewrite (wz v Hv). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia.
change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c8_of_val_mem : forall (m : word -> option byte) a v,
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m a 8 v ->
  BzSt.ro_cells BzI.asegs m a [BzCl.C8 (Z_to_bv 64 v)].
Proof.
intros m a v Ha Ha8 Hv HV. unfold BzSt.ro_cells, BzCl.cells_at. split; [cbn; tauto|].
cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r.
split; [exact Ha|]. split; [rewrite BzM.length_le8; cbn; lia|].
intros i Hi. rewrite BzM.length_le8 in Hi. rewrite (le8_nth v i Hv Hi), bz_mrd_mbyte. exact (HV i Hi).
Qed.

Lemma c1_of_val_mem : forall (m : word -> option byte) a v,
  0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 -> val_mem tfibsegs m a 1 v ->
  BzSt.ro_cells BzI.asegs m a [BzCl.C1 (Z_to_bv 8 v)].
Proof.
intros m a v Ha Ha1 Hv HV. unfold BzSt.ro_cells, BzCl.cells_at. split; [cbn; tauto|].
cbn [BzCl.cells_bytes BzCl.cbytes app].
split; [exact Ha|]. split; [cbn; lia|].
intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
rewrite bz_mrd_mbyte. cbn [nth_error]. rewrite (HV 0%nat ltac:(lia)), (le_byte1 v Hv). reflexivity.
Qed.

Lemma wview_of_mrd : forall (m : word -> option byte) (x : word) b,
  BzM.mrd BzI.asegs m x = Some b -> BzM.ro_addr BzI.asegs x = false -> wview BzI.asegs m x <> None.
Proof.
intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
unfold BzM.mrd in H. rewrite E in H. unfold BzM.ro_addr in R. unfold BzPE.seg_rom, memory_read in H.
change (Z.of_N 1) with 1 in H.
destruct (find_segment BzI.asegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
apply negb_false_iff in R. rewrite R.
destruct (seg_readable s); [|discriminate H].
destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

Definition rw_range (a : Z) (n : nat) : bool :=
  forallb (fun i => negb (BzM.ro_addr BzI.asegs (BzM.wa (a + Z.of_nat i)))) (seq 0 n).

Lemma rw_of_ro : forall (m : word -> option byte) a cs,
  BzSt.ro_cells BzI.asegs m a cs -> rw_range a (BzCl.cells_size cs) = true -> BzSt.rw_cells BzI.asegs m a cs.
Proof.
intros m a cs HC HRO. split; [exact HC|]. destruct HC as (Hwf & Hb).
pose proof (BzM.bytes_at_bound BzI.asegs m a _ Hb) as (H0 & H1). rewrite (BzCl.cells_bytes_length cs Hwf) in H1.
split; [exact H0|]. split; [exact H1|]. intros i Hi.
destruct Hb as (_ & _ & Hb).
specialize (Hb (Z.to_nat i) ltac:(rewrite (BzCl.cells_bytes_length cs Hwf); lia)).
rewrite Z2Nat.id in Hb by lia.
destruct (nth_error (BzCl.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E;
  [| apply nth_error_None in E; rewrite (BzCl.cells_bytes_length cs Hwf) in E; lia].
apply (wview_of_mrd m _ b Hb).
unfold rw_range in HRO. pose proof (proj1 (forallb_forall _ _) HRO (Z.to_nat i)) as Hi'.
rewrite in_seq in Hi'. specialize (Hi' ltac:(lia)). rewrite Z2Nat.id in Hi' by lia.
apply negb_true_iff in Hi'. exact Hi'.
Qed.

Lemma cells_cons : forall (m : word -> option byte) a c cs,
  BzSt.ro_cells BzI.asegs m a [c] -> BzSt.ro_cells BzI.asegs m (a + Z.of_nat (BzCl.csize c)) cs ->
  BzSt.ro_cells BzI.asegs m a (c :: cs).
Proof.
intros m a c cs (W1 & B1) (W2 & B2). destruct W1 as (Wc & _).
split; [split; [exact Wc | exact W2]|].
cbn [BzCl.cells_bytes] in B1 |- *. rewrite app_nil_r in B1.
apply (proj2 (BzM.bytes_at_app BzI.asegs m a _ _)). split; [exact B1|].
rewrite (BzCl.cbytes_length c Wc). exact B2.
Qed.

Lemma cells_cons8 : forall (m : word -> option byte) a w cs,
  BzSt.ro_cells BzI.asegs m a [BzCl.C8 w] -> BzSt.ro_cells BzI.asegs m (a + 8) cs ->
  BzSt.ro_cells BzI.asegs m a (BzCl.C8 w :: cs).
Proof. intros m a w cs H1 H2. apply cells_cons; [exact H1 | exact H2]. Qed.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.

(* a store that agrees with the harness's restricted store on the owned bytes of the image's
   writable part holds the runtime's cells (their rows of Tfib_const are owned, YG0q.const_cells_owned) *)
Definition owned_agree (ly : alayout) (S : astate) (m0 m' : word -> option byte) : Prop :=
  forall x : word, aowned B ly S (bv_unsigned x) -> 0xa1000 <= bv_unsigned x < 0x654000 -> m' x = m0 x.

Lemma val_mem_const_at : forall ly S H mem0 (m' : word -> option byte) a (w : nat) v,
  ARm B ly S (aview tfibsegs H mem0) -> owned_agree ly S (mrestrict H mem0) m' ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  0xa1000 <= a -> a + Z.of_nat w <= 0x654000 ->
  val_mem tfibsegs m' a w v.
Proof.
intros ly S H mem0 m' a w v M AG E Ha Haw.
pose proof (tfib_const_lookup B TB ly S H mem0 a w v M E) as V.
pose proof (cell_lookup_In _ _ _ E) as Hin. rewrite <- (ts_const B TB ly) in Hin.
pose proof (proj1 (Forall_forall _ _) (const_cells_owned B ly S _ M) _ Hin) as OW.
intros k Hk.
assert (Hx : bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)) = a + Z.of_nat k) by (apply wz; lia).
assert (O : aowned B ly S (a + Z.of_nat k)).
{ pose proof (OW (Z.of_nat k) ltac:(cbn [c_w]; lia)) as O. cbn [c_at aeval] in O. exact O. }
specialize (V k Hk). unfold mbyte in V |- *.
rewrite (AG (Z_to_bv 64 (a + Z.of_nat k))); [exact V | rewrite Hx; exact O | rewrite Hx; lia].
Qed.

Lemma ro_c8_at : forall ly S H mem0 (m' : word -> option byte) a v,
  ARm B ly S (aview tfibsegs H mem0) -> owned_agree ly S (mrestrict H mem0) m' ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
  0xa1000 <= a -> a + 8 <= 0x654000 -> 0 <= v < 2 ^ 64 ->
  BzSt.ro_cells BzI.asegs m' a [BzCl.C8 (Z_to_bv 64 v)].
Proof.
intros ly S H mem0 m' a v M AG E H1 H2 Hv. apply c8_of_val_mem; [lia | lia | exact Hv |].
exact (val_mem_const_at ly S H mem0 m' a 8 v M AG E H1 ltac:(lia)).
Qed.

Lemma ro_c1_at : forall ly S H mem0 (m' : word -> option byte) a v,
  ARm B ly S (aview tfibsegs H mem0) -> owned_agree ly S (mrestrict H mem0) m' ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
  0xa1000 <= a -> a + 1 <= 0x654000 -> 0 <= v < 256 ->
  BzSt.ro_cells BzI.asegs m' a [BzCl.C1 (Z_to_bv 8 v)].
Proof.
intros ly S H mem0 m' a v M AG E H1 H2 Hv. apply c1_of_val_mem; [lia | lia | exact Hv |].
exact (val_mem_const_at ly S H mem0 m' a 1 v M AG E H1 ltac:(lia)).
Qed.

Local Ltac c8 M AG := eapply (ro_c8_at _ _ _ _ _ _ _ M AG); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M AG := eapply (ro_c1_at _ _ _ _ _ _ _ M AG); [vm_compute; reflexivity | lia | lia | lia].

(* the six cell predicates the three ready predicates carry *)
Lemma cells_of_agree : forall ly S H mem0 (m' : word -> option byte),
  ARm B ly S (aview tfibsegs H mem0) -> owned_agree ly S (mrestrict H mem0) m' ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros ly S H mem0 m' M AG.
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

(* READY's store: a munch of cjnormv over the footprint keeps every owned byte of the image's
   writable part (the stack window, the FILE and the cookie are high; the destination owns no byte).
   Those bytes are application memory, where cjnormv drops exactly what cjnorm drops
   (NM.seam_drop_app) *)
Lemma owned_agree_seam : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo -> lo <= spZ regs ->
  spZ regs <= Fp -> Fp + 232 <= CK -> dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  owned_agree ly S (mrestrict (w_H W) (unpoison U mem)) m'.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo Hq HFp HCK DD MU x Ho Hx.
pose proof HPRE as ((HAR & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
rewrite (MU x).
- unfold NM.cjnormv, NG.gdrop_normalize.
  rewrite (NM.seam_drop_app ly R x ltac:(unfold GAF.app_mem, GAF.LOWMEM_END; lia)).
  rewrite (NM.keep_of_writable x (NM.ro_addr_off x ltac:(lia)) ltac:(unfold TASK_SIZE; lia)).
  unfold cjstore, mrestrict. destruct (w_H W x); [reflexivity|].
  symmetry. exact (ARU_mem_low tfibsegs B ly S U W mem md x HU ltac:(unfold SHADOW_OFF; lia)).
- unfold GV.vf_snf_fp. cbn [CJF.outside]. unfold kHighMemBeg in SK.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
  intros Hd. destruct (DD (bv_unsigned x) Hd) as (_ & NO & _). exact (NO Ho).
Qed.

Lemma seam_cells : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo -> lo <= spZ regs ->
  spZ regs <= Fp -> Fp + 232 <= CK -> dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo Hq HFp HCK DD MU.
pose proof HPRE as ((HAR & _) & _).
exact (cells_of_agree ly S (w_H W) (unpoison U mem) m' (proj1 HAR)
         (owned_agree_seam ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo Hq HFp HCK DD MU)).
Qed.

(* ---- the stack: AR's zero shadow over [ly_stk_lo, ly_stk_hi) (zero_shadow_ranges, YG0n.v:188-191),
   both ends page-aligned (YG0f.v:322-323), and no live block there, so no user poison ---- *)
Lemma stack_view0 : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= a < ly_stk_hi ly -> aview tfibsegs (w_H W) mem (shadow_addr a) = Some 0.
Proof.
intros ly S U W mem md a HU Ha.
pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as HZ. unfold zshadow_ok in HZ. rewrite Forall_forall in HZ.
pose proof (HZ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ0.
cbn [fst snd] in HZ0. unfold zero_shadow in HZ0.
pose proof (lo_top ly (am_layout _ _ _ _ (proj1 HAR))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold page_aligned in T5, T6.
assert (E : shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (a / 8 - ly_stk_lo ly / 8) = shadow_addr a)
  by (unfold shadow_of_addr, shadow_addr; lia).
rewrite (ARU_view_out tfibsegs B ly S U W mem md (shadow_addr a) HU).
- rewrite <- E. apply HZ0. clear - Ha T5 T6. Z.div_mod_to_equations. lia.
- apply (ARU_shadow_out_block tfibsegs B ly S U W mem md a HU).
  + unfold kHighMemEnd in T4. unfold kHighMemBeg in T7. lia.
  + exact (ARU_stack_not_block tfibsegs B LAWS ly S U W mem md a HU Ha).
Qed.

(* the hull of a stack range is visible: every byte of it is a shadow byte of the stack *)
Lemma stack_hull : forall ly S U (W : world tfibsegs) mem md x n, ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= x -> 0 < n -> x + n <= ly_stk_hi ly ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros ly S U W mem md x n HU Hx Hn Hxn.
pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold page_aligned in T5, T6.
intros s Hs.
assert (Ea : shadow_addr (8 * (s - SHADOW_OFF)) = s)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
assert (Ha : ly_stk_lo ly <= 8 * (s - SHADOW_OFF) < ly_stk_hi ly).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF. clear - Hs Hx Hn Hxn T5 T6.
  Z.div_mod_to_equations. lia. }
rewrite <- Ea, (stack_view0 ly S U W mem md _ HU Ha). discriminate.
Qed.

(* a stack range is addressable for GXA and its hull is visible *)
Lemma stack_rng : forall ly S U (W : world tfibsegs) mem md x n, ARU tfibsegs B ly S U W mem md ->
  ly_stk_lo ly <= x -> 0 <= n -> x + n + 9 <= ly_stk_hi ly ->
  GAF.pf_rng (cjstore (w_H W) mem) x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros ly S U W mem md x n HU Hx Hn Hxn.
pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
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
    apply (stack_view0 ly S U W mem md y HU). lia.
- intros Hn0. exact (stack_hull ly S U W mem md x n HU Hx Hn0 ltac:(lia)).
Qed.

(* the same at the per-call store, for a stack range inside the window R carves out: its shadow
   bytes and its hull are kept, so pf_rng and the hull cross to cjnormv *)
Lemma stack_rng_v : forall ly R S U (W : world tfibsegs) mem md (lo q : Z) x n,
  ARU tfibsegs B ly S U W mem md -> NM.sd_hull_kept ly R lo (q - lo) ->
  ly_stk_lo ly <= lo -> lo <= x -> 0 <= n -> x + n <= q -> x + n + 9 <= ly_stk_hi ly ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) x n /\
  (0 < n -> NM.sd_hull_kept ly R x n) /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros ly R S U W mem md lo q x n HU KW Hlo Hx Hn Hxn Hq.
destruct (stack_rng ly S U W mem md x n HU ltac:(lia) Hn ltac:(lia)) as [PF HV].
assert (KH : 0 < n -> NM.sd_hull_kept ly R x n)
  by (intros Hn0; exact (NM.sd_hull_kept_sub ly R lo (q - lo) x n KW ltac:(lia) ltac:(lia) ltac:(lia))).
split; [|split; [exact KH | exact HV]].
apply (NM.pf_rng_cjnormv ly R (w_H W) mem x n); [|exact PF].
intros i Hi. exact (NM.sh_kept_of_hull ly R x n (KH ltac:(lia)) i Hi).
Qed.

(* the musl prefix's hull: the nine bytes at sym 0x1029e = 0x10b7d have their hull in the shadow of
   the image's first zero-shadow range [0x10000, 0x20fa0), which AR's am_zshadow fills with 0 *)
Lemma prefix_hull : forall ly S U (W : world tfibsegs) mem md,
  PcapSyms B -> ARU tfibsegs B ly S U W mem md ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) (@RSt.sym N_img_asan_vf 0x1029e) 9.
Proof.
intros ly S U W mem md HTB HU.
pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as HZ. unfold zshadow_ok in HZ. rewrite Forall_forall in HZ.
pose proof (HZ (0x10000, 0x20fa0 - 0x10000)
              ltac:(unfold zero_shadow_ranges; right; exact (zsh_rodata_of_tfib B HTB))) as HZ0.
cbn [fst snd] in HZ0. unfold zero_shadow in HZ0.
rewrite sym_musl_prefix. intros s Hs.
assert (Hr : 0x10000 <= 8 * (s - SHADOW_OFF) < 0x20fa0).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF. clear - Hs. Z.div_mod_to_equations. lia. }
assert (Ea : shadow_addr (8 * (s - SHADOW_OFF)) = s)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
assert (E : shadow_of_addr SHADOW_OFF 0x10000 + (s - SHADOW_OFF - 0x10000 / 8) = s)
  by (unfold shadow_of_addr; clear - Hr; Z.div_mod_to_equations; lia).
assert (Hv : aview tfibsegs (w_H W) (unpoison U mem) s = Some 0)
  by (rewrite <- E; apply HZ0; clear - Hr; Z.div_mod_to_equations; lia).
destruct (in_ush U (bv_unsigned (Z_to_bv 64 s))) eqn:EU.
- rewrite (ARU_poisoned tfibsegs B ly S U W mem md HU s).
  + discriminate.
  + rewrite <- (wz s ltac:(clear - Hr; unfold SHADOW_OFF in *; lia)). exact EU.
- rewrite (ARU_view_out tfibsegs B ly S U W mem md s HU EU), Hv. discriminate.
Qed.

(* ---- the clauses.  Premises: READY's (FMgxaSeam.v:318-327), only those each clause uses ---- *)

(* memcpy from ranges whose pf_rng and hull are known: the whole of copy_ready but the two ranges *)
Lemma seam_copy_of_rng : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
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
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD MU MK
  sp Dst P N H1 H2 HN SEP PD KD VD PP KP VP.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
destruct (seam_cells ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo ltac:(unfold GCA.OUT_DEPTH in HGEO; lia)
            HFp HCK DD MU) as (C1 & C2 & _).
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
Lemma seam_ready_copy_stack : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 ->
    spZ regs - 352 <= Dst /\ Dst + N <= spZ regs - 352 + GXI.SNF_CAP -> 0 <= N ->
    (P = spZ regs - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= spZ regs - 368) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD KW MU MK
  sp Dst P N H1 H2 [HD1 HD2] HN HP.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (G1 : lo + 4640 <= sp) by exact H1.
assert (G2 : lo + 4640 <= spZ regs - 368) by exact HGEO.
assert (G3 : Dst + N <= spZ regs - 352 + 80) by exact HD2.
destruct (stack_rng_v ly R S U W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia) ltac:(lia))
  as (PD & KD & VD).
assert (PS : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N /\ (0 < N -> NM.sd_hull_kept ly R P N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N)).
{ change GXI.SNF_CAP with 80 in HP.
  destruct HP as [[-> HP]|[HP1 HP2]];
    apply (stack_rng_v ly R S U W mem md lo (spZ regs) _ N HU KW Hlo); lia. }
destruct PS as (PP & KP & VP).
exact (seam_copy_of_rng ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD MU MK
         sp Dst P N H1 H2 HN ltac:(right; right; lia) PD KD VD PP KP VP).
Qed.

(* CLOSES: memset on printf_core's stack *)
Lemma seam_ready_set : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst N, lo + GSC.SET_DEPTH <= sp -> sp <= Dst -> Dst + N + 8 <= spZ regs - 368 ->
    FMM.set_ready m' sp Dst N.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD KW MU MK sp Dst N H1 H2 H3.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
unfold GCA.OUT_DEPTH, GSC.SET_DEPTH in *.
destruct (seam_cells ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo ltac:(lia) HFp HCK DD MU)
  as (C1 & _ & C3 & _).
destruct (Z_le_gt_dec 0 N) as [HN|HN]; [|intros HN'; lia].
destruct (stack_rng_v ly R S U W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia) ltac:(lia))
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
Lemma seam_ready_copy_hull : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) -> (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
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
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD HSEP KW KDD PDD VDD HULL MU MK
  sp Dst P N H1 H2 HDst HN HP.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
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
    destruct (stack_rng_v ly R S U W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia)
                ltac:(lia)) as (PD & KD & VD).
    split; [exact PD|]. split; [exact KD|]. split; [exact VD | lia]. }
destruct DR as (PD & KD & VD & SEP).
assert (PR : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N /\ (0 < N -> NM.sd_hull_kept ly R P N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N)).
{ destruct HP as [[-> HP]|[[HP1 HP2]|HP]].
  - unfold GXI.SNF_CAP, GCA.OUT_DEPTH in *.
    exact (stack_rng_v ly R S U W mem md lo (spZ regs) (spZ regs - 352) N HU KW Hlo ltac:(lia) HN
             ltac:(lia) ltac:(lia)).
  - unfold GCA.OUT_DEPTH in *.
    exact (stack_rng_v ly R S U W mem md lo (spZ regs) P N HU KW Hlo ltac:(lia) HN ltac:(lia)
             ltac:(lia)).
  - split; [exact HP|]. split; [|exact (HULL P N HP)].
    intros Hn0.
    exact (NM.hull_of_sh_kept ly R P N (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP))
             Hn0 (pf_rng_app _ P N (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP)))). }
destruct PR as (PP & KP & VP).
exact (seam_copy_of_rng ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD MU MK
         sp Dst P N H1 H2 HN SEP PD KD VD PP KP VP).
Qed.

(* the bytes past each destination byte that pf_rng reads (AsanFacts.v:80), app_mem (D + i + 7) for
   0 <= i < n, from the destination's band bound 8 bytes past its end (READY's amem_range D (dn + 8),
   the contract's GXA (5)).  Only the bound moves: the bytes past the end need be neither addressable
   nor shadow-clean, and nothing here asks either *)
Lemma dest_tail_of_amem8 : forall D n, 0 <= D -> amem_range D (n + 8) ->
  forall i, 0 <= i < n -> GAF.app_mem (D + i + 7).
Proof.
intros D n HD0 HAM8 i Hi. exact (app_mem_of_amem_range D (n + 8) (D + i + 7) HAM8 HD0 ltac:(lia) ltac:(lia)).
Qed.

(* the destination's pf_rng on the harness's store from READY's premises (FMgxaSeam.v READY):
   0 <= D, dn <= 2 ^ 40, amem_range and range_addressable, and the band bound 8 bytes past the end,
   which gives the bytes past each destination byte that pf_rng reads (dest_tail_of_amem8) *)
Lemma seam_dest_rng : forall H mem D (dn : nat),
  0 <= D -> Z.of_nat dn <= 2 ^ 40 -> amem_range D (Z.of_nat dn) -> amem_range D (Z.of_nat dn + 8) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF D (Z.of_nat dn) ->
  GAF.pf_rng (cjstore H mem) D (Z.of_nat dn).
Proof.
intros H mem D dn HD0 HDN HAM HAM8 HRA.
unfold GAF.pf_rng, GAF.end_in_app.
split; [exact HDN|].
split; [exact (addressable_of_view H mem D (Z.of_nat dn) HD0 ltac:(lia) HAM HRA)|].
split; [|exact (dest_tail_of_amem8 D (Z.of_nat dn) HD0 HAM8)].
right. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
unfold GAF.app_mem, GAF.LOWMEM_END, GAF.HIGHMEM_BEG, GAF.APPMEM_END. lia.
Qed.

(* the memcpy clause from READY's premises, through seam_ready_copy_hull: the destination's facts that
   lemma takes come from READY (seam_dest_rng, the hull, and R's carve-out); the hull of a source
   named only by pf_rng (HULL) is still seam_ready_copy_hull's own premise *)
Lemma seam_ready_dest : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
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
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD KW KDD HAM HAM8 HRA HV HD0 HDN
  HSEP HULL MU MK.
apply (seam_ready_copy_hull ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD HSEP KW KDD
         (NM.pf_rng_cjnormv ly R (w_H W) mem D (Z.of_nat dn) (NM.sh_kept_of_hull ly R D (Z.of_nat dn) KDD)
            (seam_dest_rng (w_H W) mem D dn HD0 HDN HAM HAM8 HRA))
         (fun _ => HV) HULL MU MK).
Qed.

(* the strnlen clause, given what it does not carry: the hull of the bytes strnlen checks *)
Lemma seam_ready_strn_hull : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp S0 N L buf, lo + GNC.STRN_DEPTH <= sp -> sp <= spZ regs - 368 ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) S0 L -> Z.min (strnlen_res N buf + 1) N <= L ->
    (0 < Z.min (strnlen_res N buf + 1) N ->
       shadow_hull_vis (aview tfibsegs (w_H W) mem) S0 (Z.min (strnlen_res N buf + 1) N)) ->
    RSN.strn_ready m' sp S0 N buf.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD MU MK sp S0 N L buf H1 H2 PR HL VS.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
destruct (seam_cells ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo ltac:(unfold GCA.OUT_DEPTH in HGEO; lia)
            HFp HCK DD MU) as (C1 & _ & _ & C4 & C5 & C6).
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
(* 6. the hull of a range named only by pf_rng (w_H8) and READY                             *)
(* ===================================================================================== *)

(* the band's four ends are multiples of 8: an 8-aligned word with a byte in the band lies in it *)
Lemma band_word : forall s0 s, in_band_rw s0 -> s / 8 = s0 / 8 -> in_band_rw s.
Proof.
intros s0 s Hb E. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *.
Z.div_mod_to_equations. lia.
Qed.

(* the shadow byte of a byte of application memory is in the band *)
Lemma shadow_band : forall x, GAF.app_mem x -> in_band_rw (shadow_addr x).
Proof.
intros x Hx. unfold GAF.app_mem, GAF.LOWMEM_END, GAF.HIGHMEM_BEG, GAF.APPMEM_END in Hx.
unfold in_band_rw, shadow_addr, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd.
Z.div_mod_to_equations. lia.
Qed.

(* a byte of the 8-aligned shadow word of a byte s0 the per-call store holds is readable.  The
   presence AR does not carry (a visible in_vis0 band byte, which ahs_pres, YG0n.v:442-444, leaves
   out) is exactly what cjnormv's own drop gives back: it drops such a byte unless a hull of R
   carves it out, so s0 present in cjnormv puts s in a visible hull of R
   (FMgxaSeamNorm.vis0_word_pres_cjnormv) *)
Lemma word_vis : forall ly R S U (W : world tfibsegs) mem md s0 s,
  ARU tfibsegs B ly S U W mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  in_band_rw s0 -> s / 8 = s0 / 8 ->
  NM.cjnormv ly R (w_H W) mem (Z_to_bv 64 s0) <> None ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
intros ly R S U W mem md s0 s HU HVR Hb0 E P0v.
pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as (M & L & _ & _ & HP & _).
pose proof (al_img_env tfibsegs ly S md (am_layout _ _ _ _ M) L) as IMG.
pose proof (am_layout _ _ _ _ M) as LO.
pose proof (band_word s0 s Hb0 E) as Hb.
assert (Hs64 : 0 <= s < 2 ^ 64)
  by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia).
assert (Hs064 : 0 <= s0 < 2 ^ 64)
  by (clear - Hb0; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb0; lia).
(* s0 is readable in the harness's store: cjnormv holds it, so the restricted store does *)
assert (R0 : aview tfibsegs (w_H W) mem s0 <> None).
{ pose proof (NM.cjnormv_store ly R (w_H W) mem (Z_to_bv 64 s0) P0v) as X.
  unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 s0)) as [b|] eqn:Em;
    [cbn; discriminate | exfalso; exact (X Em)]. }
(* s0 is visible and present, so by w_H8 s is visible *)
assert (Hh0 : w_H W (Z_to_bv 64 s0) = false).
{ destruct (w_H W (Z_to_bv 64 s0)) eqn:Eh; [|reflexivity]. exfalso.
  exact (R0 (aview_band_hidden tfibsegs (w_H W) mem s0 IMG Hb0 Eh)). }
assert (Hh : w_H W (Z_to_bv 64 s) = false).
{ assert (E8 : s - s mod 8 = s0 - s0 mod 8) by (rewrite (Z.mod_eq s 8), (Z.mod_eq s0 8) by lia; lia).
  rewrite (w_H8 W s Hb), E8, <- (w_H8 W s0 Hb0). exact Hh0. }
destruct (in_ush U s) eqn:EU.
- (* user-poisoned: read 0xf7 *)
  rewrite (ARU_poisoned tfibsegs B ly S U W mem md HU s EU). discriminate.
- rewrite (ARU_view_out tfibsegs B ly S U W mem md s HU ltac:(rewrite (wz s Hs64); exact EU)).
  assert (NNEM : forall P : Prop, ~ ~ (P \/ ~ P))
    by (intros P k; apply k; right; intros p; apply k; left; exact p).
  intros Hn. apply (NNEM (aclient_byte B ly S s)). intros [C|NC].
  + (* a client byte (a fake frame's shadow): AR's am_client *)
    exact (client_band_vis B ly S _ s M Hb C Hn).
  + apply (proj2 (aview_band tfibsegs (w_H W) (unpoison U mem) s IMG Hb Hh)); [|exact Hn].
    intros Hm. apply (NNEM (in_vis0 ly s)). intros [V|NV].
    * (* in_vis0: cjnormv keeps s, because it kept s0 and the hulls of R are visible *)
      assert (Em : mem (Z_to_bv 64 s) = None).
      { change (unpoison U mem (Z_to_bv 64 s) = None) in Hm.
        revert Hm. unfold unpoison. rewrite (wz s Hs64), EU. exact (fun h => h). }
      apply (NM.vis0_word_pres_cjnormv ly R (w_H W) mem LO HVR s s0 Hb V E Hh P0v).
      unfold NM.cjnormv, NG.gdrop_normalize. cbv beta.
      destruct (NM.seam_drop ly R (Z_to_bv 64 s)); [reflexivity|].
      unfold cjstore, mrestrict. rewrite Hh. exact Em.
    * (* not in_vis0: AR's ahs_pres *)
      exact (HP s Hb NC (or_intror NV) Hm).
Qed.

(* the hull of a range named only by pf_rng at the per-call store *)
Lemma hull_of_pf_rng_H8 : forall ly R S U (W : world tfibsegs) mem md P N,
  ARU tfibsegs B ly S U W mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> 0 < N ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) P N.
Proof.
intros ly R S U W mem md P N HU HVR PF HN s Hs.
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
  apply (word_vis ly R S U W mem md (shadow_addr P) s HU HVR B0); [|exact R0].
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
    exact (word_vis ly R S U W mem md s s HU HVR Bi eq_refl Ri).
  + (* the aligned word of the last byte's shadow byte *)
    destruct (RB (N - 1) ltac:(lia)) as [B1 R1].
    replace (P + (N - 1)) with (P + N - 1) in B1, R1 by lia.
    apply (word_vis ly R S U W mem md (shadow_addr (P + N - 1)) s HU HVR B1); [|exact R1].
    clear - Hs L2. Z.div_mod_to_equations. lia.
Qed.

(* the quick check's two aligned shadow words at any store that keeps the per-call store's shadow *)
Lemma qc_words_of_pf_rng_H8 : forall ly R S U (W : world tfibsegs) mem md (m' : word -> option byte) P N,
  ARU tfibsegs B ly S U W mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> BQ.qc_words m' P N.
Proof.
intros ly R S U W mem md m' P N HU HVR MK PF.
destruct (Z_lt_le_dec 0 N) as [HN|HN]; [|intros [Hn _]; lia].
pose proof PF as (_ & (Hp & _ & Hpn & _) & _). unfold GAF.APPMEM_END in Hpn.
destruct (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N PF) as [PF0 KS].
apply (qc_words_of_hull_m m' P N Hp HN ltac:(lia)).
apply (hull_kept_v ly R (w_H W) mem m' P N MK
         (NM.hull_of_sh_kept ly R P N KS HN (pf_rng_app _ P N PF0)) HN (pf_rng_app _ P N PF0)).
exact (hull_of_pf_rng_H8 ly R S U W mem md P N HU HVR PF HN).
Qed.

(* the memcpy clause with the source hull from w_H8: seam_ready_dest without its HULL premise *)
Lemma seam_ready_copy : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
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
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD KW KDD HAM HAM8 HRA HV HD0 HDN
  HSEP MU MK.
pose proof HPRE as ((HAR & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
exact (seam_ready_dest ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD KW KDD HAM HAM8 HRA
         HV HD0 HDN HSEP (fun P N PF HN => hull_of_pf_rng_H8 ly R S U W mem md P N HU HVR PF HN) MU MK).
Qed.

(* the strnlen clause with the hull from w_H8: seam_ready_strn_hull without its hull premise *)
Lemma seam_ready_strn : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat)
    (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 -> spZ regs <= Fp -> Fp + 232 <= CK ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  CJF.munch (GV.vf_snf_fp lo (spZ regs) Fp CK D dn) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp S0 N L buf, lo + GNC.STRN_DEPTH <= sp -> sp <= spZ regs - 368 ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) S0 L -> Z.min (strnlen_res N buf + 1) N <= L ->
    RSN.strn_ready m' sp S0 N buf.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD MU MK sp S0 N L buf H1 H2 PR HL.
pose proof HPRE as ((HAR & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
apply (seam_ready_strn_hull ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD MU MK
         sp S0 N L buf H1 H2 PR HL).
intros Hk.
apply (hull_prefix _ S0 L _ (hull_of_pf_rng_H8 ly R S U W mem md S0 L HU HVR PR ltac:(lia))). lia.
Qed.

(* READY (FMgxaSeam.v) at fm's three predicates, for any carve-out list R that holds the destination
   and the stack window and whose hulls the harness sees *)
Theorem seam_ready_holds : forall ly R S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat),
  ecall_preU tfibsegs B ly S U W regs mem md ->
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
  SG.seam_calls_ready FMM.copy_ready FMM.set_ready RSN.strn_ready
    (NM.cjnormv ly R (w_H W) mem) (spZ regs) lo Fp CK D dn.
Proof.
intros ly R S U W regs mem md lo Fp CK D dn HPRE InD InW HVR Hlo HGEO _ HFp HCK _ _ _ DD HAM HAM8 HRA
  HD0 HDN HSEP.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
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
- exact (seam_ready_copy ly R S U W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD KW KDD
           HAM HAM8 HRA HV HD0 HDN HSEP MU MK).
- exact (seam_ready_set ly R S U W regs mem md lo Fp CK D dn m' HPRE Hlo HGEO HFp HCK DD KW MU MK).
- intros sp S0 N L buf H1 H2 PR HL.
  exact (seam_ready_strn ly R S U W regs mem md lo Fp CK D dn m' HPRE HVR Hlo HGEO HFp HCK DD MU MK
           sp S0 N L buf H1 H2 PR HL).
Qed.

End C.
