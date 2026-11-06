(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 452 of its 508 lines of code are new or changed and 648 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeam.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 25 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset), plus :2 by hand (the tool reports no row for this line: fm.asan's musl vfprintf 0x8ede0 -> 0x8ede4, vfprintf+0x0, as the base relocation and lib/B/Bz/K/I_vprintfw.v have it); GXA / donor symbol keys kept (0x34288, 0x7f000400: lib/B/RT_IImgA.v maps that key space); name TfibSyms -> BoxregSyms (1x; boxreg's lib/B/AF0m.v record); re-pointed Requires: FMupoison, FMsnprintfPf, FMsnprintfShared, FMsnprintfSx -> lib.A.Rt; RT_IImgA, FMgxa_bridge -> lib.B; FMgxaSeamBase, FMgxaSeamPf, FMgxaSeamDef, FMgxaSeamShadow, FMgxaSeamCall, FMgxaSeamPost, FMgxaSeamCells, FMgxaSeamFam, FMgxaSeamGuard, FMgxaSeamNorm, FMgxaSeamReady -> lib.B.Rt. Replaces the base's 7e395de08f5 copy. *)
(* THE GXA SEAM AT MUSL VFPRINTF, ASSEMBLED: fuzz_boxreg.asan-ubsan's musl vfprintf (0x8ede4 = sym 0x7f000400) realizes
   the shared vfprintf contract in its final GXA form (sh_avfprintf_icpt_realizesUx, the one definition,
   in a Theorem Labs lane's lib/A/FMsnprintfSx.v, a working branch 00daeaf3796).

   Nothing here walks a machine step.  The walk is the released, unguarded GXA theorem at fm.asan
   (FMgxaSeamCall.v seam_vfprintf_a, lib/CJ/RL/GXA/G_vfprintf_snf.v vfprintf_snf_a_stmt, from
   a working branch efa2842e125); this file feeds it the contract's premises and reads its post back:
   - the arguments: GXA's (Fp CK D N OM bufp A VA dn fmt slots args lo canary r o) are the contract's
     (fp cp s0 n0 |T| bp f ap (sn_len n0 T) (fmtb ++ [0]) (map w64 ws) (map pt_parg args0) (sp - K)
     (w64 cval) |T| T); the format, its pieces and its arguments come from pf_family_ro;
   - the store: GXA runs on the per-call normalized store cjnormv ly R (w_H W) mem
     (FMgxaSeamNorm.v), which satisfies GXA's store invariant by construction.  R is the seam's
     carve-out list NM.seam_R (the destination, the format, the stack window, musl's prefix and each
     %s string): outside those hulls the normalization also drops a shadow word that meets a vis0
     zone, which is what makes the readiness of the three interceptors provable (FMgxaSeamReady.v).
     The contract's consts_view and ro_covered cr give the read agreement the normalization needs
     (ro_agree_of_consts); each store premise moves to it by FMgxaSeamNorm's *_cjnormv lemmas, whose
     extra side conditions are app_ivl (the data lies in application memory) and, for the shadow
     facts, NM.seam_drop_keeps at this R; GXA (4) keeps the FILE, the cookie and the slots below
     2^47, where the normalization keeps every byte; GXA (5), the destination's band bound 8 bytes
     past its end, goes to READY (the bytes past each destination byte that pf_rng reads);
   - the start state: the harness's register file is any bvmap, GXA's is `mkR x1 .. x31`.  They agree
     on every register but x0 (lib/Lib/Regs6ss.v xregs_eqv), which no instruction reads.  GXA's evt on
     the normalized store becomes an evt on the harness's store (FMgxaSeamNorm.evt_from_norm_MS_v), is
     carried to the harness's register file across Regs6ss.ms_eqv (sa_evt_eqv), and then into SRr by
     FMgxa_bridge.v srr_of_gxa_evt;
   - the post: GXA's post moves back to the harness's final store (FMgxaSeamNorm.post_from_norm_a_v),
     which is read through munrestrict (FMgxaSeamPost.v); its register file comes through the same
     equivalence, and its FP registers and fcsr become the post's FPState.

   One premise of the theorem the contract does not carry: the format's range.  GXA reads the
   format as image data below the GOT (65536 <= f and f + |fmt| <= sym 0x22e18,
   G_vfprintf_snf.v:210).  pf_family_ro's two bounds are that range: the theorem takes them as
   fam_lo / fam_hi with 65536 <= fam_lo, fam_hi <= sym 0x22e18.  And one static fact about the
   constant list, ro_covered cr: it covers every read-only byte of the image.

   The section's hypotheses are the three interceptor call contracts and their readiness predicates
   (as FMgxaSeamCall.v takes them), B with its laws and fm's symbols, and READY: the readiness
   predicates meet FMgxaSeamGuard.v's seam_calls_ready at this call site, on the normalized store. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison FMsnprintfPf FMsnprintfShared FMsnprintfSx.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require AF0m AF0x.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Mem Frame MState FP Cells Step Exec.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA Require
AsanFacts SetCall StrnlenCall CopyCall G_printf_core_common G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import RT_IImgA FMgxa_bridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import FMgxaSeamBase FMgxaSeamPf FMgxaSeamDef FMgxaSeamShadow FMgxaSeamCall FMgxaSeamPost FMgxaSeamCells FMgxaSeamFam FMgxaSeamGuard.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require FMgxaSeamNorm FMgxaSeamReady.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the modules below are named by their full paths: lib/Lib has modules of the same short names *)
Module RE := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Regs6ss.
Module CJE := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Exec.
Module CJC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Cells.
Module PRL := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Spec.Prelim.
Module GXC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GAF := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.AsanFacts.
Module GVA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GSA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_printf_snfsink.
Module GCA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module NM := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.FMgxaSeamNorm.
Module GCC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.StrnlenCall.
(* the AR facts the seam's carve-out list needs: the stack window's hull and musl's prefix hull *)
Module SR := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.FMgxaSeamReady.

#[local] Existing Instance A_img.

(* ---- a CJ walk read at an equivalent register file ---- *)
Lemma sa_mstep_eqv : forall segs a a' b, CJE.mstep segs a b -> RE.ms_eqv a a' ->
  exists b', CJE.mstep segs a' b' /\ RE.ms_eqv b b'.
Proof.
intros segs a a' b [Hsvc Hst] E.
pose proof (RE.step_accesses_eqv segs a a' E) as R.
pose proof E as (_ & _ & _ & Hs & _).
unfold RiscvSemantics.step in Hst. unfold CJE.mstep, RiscvSemantics.step.
revert R Hst.
destruct (RiscvSemantics.step_accesses segs a) as [[x acc]| |];
destruct (RiscvSemantics.step_accesses segs a') as [[y acc']| |];
cbn [RE.rep_eqv RiscvSemantics.drop_access_report RiscvSemantics.access_value RiscvSemantics.accessed_ranges];
intros R Hst; try discriminate; try contradiction.
injection Hst as <-. destruct R as [Hxy _].
exists y. split; [split; [congruence | reflexivity] | exact Hxy].
Qed.

Lemma sa_msteps_eqv : forall segs a b, CJE.msteps segs a b ->
  forall a', RE.ms_eqv a a' -> exists b', CJE.msteps segs a' b' /\ RE.ms_eqv b b'.
Proof.
intros segs a b H. induction H as [ms | ms ms1 ms2 Hs _ IH]; intros a' E.
- exists a'. split; [apply CJE.msteps_refl | exact E].
- destruct (sa_mstep_eqv segs ms a' ms1 Hs E) as (b1 & Hs' & E1).
  destruct (IH b1 E1) as (b2 & H2 & E2).
  exists b2. split; [eapply CJE.msteps_cons; eassumption | exact E2].
Qed.

Lemma sa_evt_eqv : forall segs (Q : machine_state -> Prop) a a', CJE.evt segs Q a -> RE.ms_eqv a a' ->
  CJE.evt segs (fun x => exists y, Q y /\ RE.ms_eqv y x) a'.
Proof.
intros segs Q a a' (b & Hb & HQ) E.
destruct (sa_msteps_eqv segs a b Hb a' E) as (b' & Hb' & E').
exists b'. split; [exact Hb' | exists b; split; assumption].
Qed.

Lemma sa_getr_nz : forall (R : bvmap 5 word) (r : bv 5), is_x0 r = false -> getr R r = reg_get R r.
Proof. intros R r H. unfold getr. rewrite bv_eqb0_is_x0, H. reflexivity. Qed.

(* ---- fm.asan's numbers ---- *)
Lemma sa_globals_top : @GXC.GLOBALS_TOP A_img = 0x5f6000.
Proof. vm_compute. reflexivity. Qed.
Lemma sa_globals_top_a : @GCA.GLOBALS_TOP A_img = 0x5f6000.
Proof. vm_compute. reflexivity. Qed.
Lemma sa_vfa_depth : GVA.VFA_DEPTH = 5552.
Proof. reflexivity. Qed.
Lemma sa_sym_got_ssp : @sym A_img 0x22e18 = 0x99f60.
Proof. vm_compute. reflexivity. Qed.
Lemma sa_sym_guard : @sym A_img 0x34288 = 0x5f4390.
Proof. vm_compute. reflexivity. Qed.

(* the GOT slot of __stack_chk_guard and the guard itself lie in a writable segment of fm.asan *)
Lemma sa_ssp_writable : forall (m : word -> option byte) a,
  (0x99f60 <= a < 0x99f68) \/ (0x5f4390 <= a < 0x5f4398) -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at, wview.
destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
assert (L : a = 0x99f60 \/ a = 0x99f61 \/ a = 0x99f62 \/ a = 0x99f63 \/ a = 0x99f64 \/ a = 0x99f65 \/
            a = 0x99f66 \/ a = 0x99f67 \/ a = 0x5f4390 \/ a = 0x5f4391 \/ a = 0x5f4392 \/ a = 0x5f4393 \/
            a = 0x5f4394 \/ a = 0x5f4395 \/ a = 0x5f4396 \/ a = 0x5f4397) by lia.
repeat (destruct L as [L|L]; [subst a; vm_compute; discriminate|]).
subst a. vm_compute. discriminate.
Qed.

(* ---- words, writability, the hidden set ---- *)
Lemma sa_aview_range : forall H mem a v, aview tfibsegs H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.

Lemma sa_rdword_range : forall H mem a v, rdword (aview tfibsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (sa_aview_range _ _ _ _ E0). pose proof (sa_aview_range _ _ _ _ E1).
pose proof (sa_aview_range _ _ _ _ E2). pose proof (sa_aview_range _ _ _ _ E3).
pose proof (sa_aview_range _ _ _ _ E4). pose proof (sa_aview_range _ _ _ _ E5).
pose proof (sa_aview_range _ _ _ _ E6). pose proof (sa_aview_range _ _ _ _ E7).
lia.
Qed.

(* a byte the store may write is a byte the harness reads (a writable segment byte of fm.asan is readable) *)
Lemma sa_writable_aview : forall H mem a,
  writable_at tfibsegs (cjstore H mem) a -> aview tfibsegs H mem a <> None.
Proof.
intros H mem a HW. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate|].
pose proof (seg_rom_of_wview (cjstore H mem) (Z_to_bv 64 a) HW E) as R.
destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | contradiction].
Qed.

(* ... and the world does not hide it: a hidden address lies outside every segment *)
Lemma sa_writable_vis : forall (W : world tfibsegs) mem a,
  writable_at tfibsegs (cjstore (w_H W) mem) a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W mem a HW. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso. apply HW.
unfold wview, cjstore, mrestrict. rewrite E, (w_Hoff W _ E). reflexivity.
Qed.

(* ---- the written part ---- *)
Lemma sa_sn_len_eq : forall N T, 0 <= N -> sn_len N T = Z.min N (Z.of_nat (length T)) + 1.
Proof.
intros N T HN. unfold sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length].
rewrite Nat2Z.inj_add, Nat2Z.inj_min, Z2Nat.id by exact HN. lia.
Qed.

Lemma sa_bv_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
intros c Hc. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 8) with 256. lia.
Qed.

Lemma sa_nth_zb_app : forall (l : list Z) (rest : list byte) (i : nat), (i <= length l)%nat ->
  nth i (G_fmt_fp_lib.zb l ++ Z_to_bv 8 0 :: rest) (Z_to_bv 8 0) = Z_to_bv 8 (nth i (l ++ [0]) 0).
Proof.
induction l as [|c l IH]; intros rest i Hi.
- cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [length] in Hi. exact (IH rest i ltac:(lia)).
Qed.

Lemma sa_nth_range : forall (l : list Z) i, Forall (fun c => 0 <= c < 256) l -> 0 <= nth i l 0 < 256.
Proof.
induction l as [|c l IH]; intros i H; [destruct i; cbn; lia|].
inversion H; subst. destruct i; cbn [nth]; [assumption | apply IH; assumption].
Qed.

Lemma sa_Forall_firstn : forall (P : Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
intros P n. induction n as [|n IH]; intros l H; [constructor|].
destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [firstn]. constructor; [assumption | apply IH; assumption].
Qed.

(* ---- the family: arguments, literals, the text's bytes ---- *)
Lemma sa_pf_args_asan_In : forall rd rs ws args a, pf_args_asan rd rs ws args -> In a args ->
  exists w, pf_arg_asan rd rs w a.
Proof.
intros rd rs ws args. revert ws.
induction args as [|a0 args IH]; intros ws a HA Hin; [destruct Hin|].
destruct ws as [|w ws]; [destruct HA|]. destruct HA as [Ha HA].
destruct Hin as [<-|Hin]; [exists w; exact Ha | exact (IH ws a HA Hin)].
Qed.

Definition sa_lit_ok (p : pf_piece) : Prop := match p with PLit b => 0 < b < 256 | _ => True end.

Lemma sa_pf_parse_lits : forall n f ps, (length f <= n)%nat -> pf_parse f = Some ps -> Forall sa_lit_ok ps.
Proof.
induction n as [|n IH]; intros f ps Hn HP.
- destruct f as [|b r]; [cbn in HP; injection HP as <-; constructor | cbn in Hn; lia].
- destruct f as [|b r]; [cbn in HP; injection HP as <-; constructor|]. cbn [length] in Hn.
  assert (T : forall r' k ps', (length r' <= n)%nat -> sa_lit_ok k ->
            option_map (cons k) (pf_parse r') = Some ps' -> Forall sa_lit_ok ps').
  { intros r' k ps' Hr' Hk E. destruct (pf_parse r') as [p'|] eqn:E'; cbn in E; [|discriminate].
    injection E as <-. constructor; [exact Hk | exact (IH r' p' Hr' E')]. }
  cbn [pf_parse] in HP.
  destruct (b =? 37).
  + destruct r as [|c r1]; [discriminate|]. cbn [length] in Hn.
    destruct (c =? 100); [exact (T r1 Pd ps ltac:(lia) I HP)|].
    destruct (c =? 99); [exact (T r1 Pc ps ltac:(lia) I HP)|].
    destruct (c =? 115); [exact (T r1 Ps ps ltac:(lia) I HP)|].
    destruct (c =? 48).
    { destruct r1 as [|c2 [|c3 r3]]; try discriminate. cbn [length] in Hn.
      destruct ((c2 =? 52) && (c3 =? 120)); [exact (T r3 Px04 ps ltac:(lia) I HP)|].
      destruct ((c2 =? 50) && (c3 =? 120)); [exact (T r3 Px02 ps ltac:(lia) I HP)|discriminate]. }
    destruct (c =? 108).
    { destruct r1 as [|c2 [|c3 r3]]; try discriminate. cbn [length] in Hn.
      destruct ((c2 =? 108) && (c3 =? 117)); [exact (T r3 Pllu ps ltac:(lia) I HP)|discriminate]. }
    destruct (c =? 46); [|discriminate].
    destruct r1 as [|c2 [|c3 r3]]; try discriminate. cbn [length] in Hn.
    destruct ((c2 =? 42) && (c3 =? 115)); [exact (T r3 Pps ps ltac:(lia) I HP)|discriminate].
  + destruct ((0 <? b) && (b <? 256)) eqn:Eb; [|discriminate].
    apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1, E2.
    exact (T r (PLit b) ps ltac:(lia) ltac:(cbn; lia) HP).
Qed.

(* the text of fm's pieces is bytes: literals the parser accepted and the %s / %.*s strings *)
Lemma sa_pf_text_bytes : forall ps args T, Forall sa_lit_ok ps -> Forall pf_fm_piece ps ->
  (forall s, In (APtr s) args -> Forall (fun c => 0 < c < 256) s) ->
  pf_text ps args = Some T -> Forall (fun c => 0 <= c < 256) T.
Proof.
induction ps as [|p ps IH]; intros args T HL HK HS HT.
- destruct args; cbn in HT; [injection HT as <-; constructor | discriminate].
- inversion HL as [|? ? Hl HL']; subst. inversion HK as [|? ? Hk HK']; subst.
  destruct p; cbn in Hk; try contradiction.
  + cbn [pf_text] in HT. destruct (pf_text ps args) as [T'|] eqn:E; cbn in HT; [|discriminate].
    injection HT as <-. constructor; [cbn in Hl; lia | exact (IH args T' HL' HK' HS E)].
  + destruct args as [|[v|u|s] args']; cbn [pf_text] in HT; try discriminate.
    destruct (pf_text ps args') as [T'|] eqn:E; cbn in HT; [|discriminate]. injection HT as <-.
    apply Forall_app. split.
    * eapply Forall_impl; [|exact (HS s (or_introl eq_refl))]. intros c Hc. cbv beta in *. lia.
    * apply (IH args' T' HL' HK'); [intros s' Hs'; apply HS; right; exact Hs' | exact E].
  + destruct args as [|[k|u|s0] args']; cbn [pf_text] in HT; try discriminate.
    destruct args' as [|[v|u|s] args'']; cbn [pf_text] in HT; try discriminate.
    destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate].
    destruct (pf_text ps args'') as [T'|] eqn:E; cbn in HT; [|discriminate]. injection HT as <-.
    apply Forall_app. split.
    * apply sa_Forall_firstn. eapply Forall_impl; [|exact (HS s (or_intror (or_introl eq_refl)))].
      intros c Hc. cbv beta in *. lia.
    * apply (IH args'' T' HL' HK'); [intros s' Hs'; apply HS; right; right; exact Hs' | exact E].
Qed.

(* ---- ARU at the model the run hands back ---- *)
Lemma sa_ARU_model_same : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B ly S U (W : world tfibsegs) mem md md',
  ARU tfibsegs B ly S U W mem md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
  ARU tfibsegs B ly S U W mem md'.
Proof.
intros fx rc B ly S U W mem md md' ((M & L & Bu & MW & HS) & OK & PO) Hv Hl.
split; [|split; [exact OK | exact PO]].
split; [exact M|]. split.
- apply (ALedger_same tfibsegs ly S md md' L Hv Hl). unfold eager_used. rewrite Hv, Hl. reflexivity.
- split; [exact Bu|]. split; [exact (amwf_same md md' Hv Hl MW) | exact HS].
Qed.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SYMS : AF0m.BoxregSyms B.

(* the three interceptor call contracts, with their readiness predicates (FMgxaSeamCall.v) *)
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.
Hypothesis SPEC_memcpy : @GCC.memcpy_stack_contract A_img copy_ready.
Hypothesis SPEC_memset : @GSC.memset_stack_contract A_img set_ready.
Hypothesis SPEC_strnlen : @GNC.strnlen_stack_contract A_img strn_ready.

(* READINESS at musl vfprintf's call: the stack window [lo, sp) below printf_core's depth, the FILE at
   Fp and the cookie at CK on the stack above sp and below 2^47, the destination [D, D + dn) writable,
   application memory with its band bound 8 bytes past its end (pf_rng's app_mem (D + i + 7),
   AsanFacts.v:80; those 8 bytes are asked nothing else), addressable, at or above 0, at most 2^40
   bytes and off the window, in a harness state that satisfies ecall_preU.
   The predicates must then meet FMgxaSeamGuard.v's seam_calls_ready on the per-call store GXA runs
   on, FMgxaSeamNorm.cjnormv ly R, for any carve-out list R that holds the destination (D, dn) and
   the stack window (lo, sp - lo) and whose hulls the harness sees.  The destination's own hull is
   that Forall at (D, dn), so READY does not state it twice. *)
Hypothesis READY : forall ly (R : list (Z * Z)) S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat),
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
  seam_calls_ready copy_ready set_ready strn_ready (NM.cjnormv ly R (w_H W) mem) (spZ regs) lo Fp CK D dn.

Theorem fm_vfprintf_seam :
  forall (K gc gv img_lo img_hi snw fam_lo fam_hi : Z) (cr : list (Z * Z)),
    GVA.VFA_DEPTH <= K -> gc = @sym A_img 0x22e18 -> gv = @sym A_img 0x34288 ->
    snw = @sym A_img GXC.K_SN_WRITE -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi ->
    65536 <= fam_lo -> fam_hi <= @sym A_img 0x22e18 -> NM.ro_covered cr ->
    sh_avfprintf_icpt_realizesUx tfibsegs B
      (pf_family_ro pf_fm_piece fam_lo fam_hi) K gc gv img_lo img_hi cr snw (@sym A_img 0x7f000400).
Proof.
intros K gc gv img_lo img_hi snw fam_lo fam_hi cr HKd Egc Egv Esnw Hilo Hihi Hflo Hfhi HCOV.
unfold sh_avfprintf_icpt_realizesUx.
intros ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HPRE HK HWIN Ha0 Ha1 Ha2 HFILE Hbp HCK DFP DCK
  Hfp0 Hfp1 Hcp0 Hcp1 HCR HCRb HCRd Hgc Hgv Hgc0 Hgc1 Hgv0 Hgv1 Dgc Dgv HAP Hap0 Hap1 Dap HFAM
  Hn0 HT Hs0 Hs1 HPW DS0 AMS RAS SHV DIMG FRM0 HNUL FO1 FO2 FO3 DSL HTK HD8.
destruct HFAM as (fmtb & ps & args0 & HFA & HPS & HPK & HPA & HPT & HPP & HFLO & HFHI & HSL).
(* ---- the harness state ---- *)
pose proof HPRE as ((HAR & HRET & _ & _ & HSPhi & _ & _ & _) & HUOK & HUP).
assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (HSTK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
unfold kHighMemBeg, kHighMemEnd in HSTK. pose proof sa_vfa_depth as VFA.
pose proof sa_globals_top as GT. pose proof sa_globals_top_a as GTA.
pose proof sa_sym_got_ssp as S22. pose proof sa_sym_guard as S34.
rewrite GT in Hihi. rewrite S22 in Hfhi.
assert (Esp : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
(* ---- the written part: GXA's dn ---- *)
assert (SNL : sn_len n0 T = Z.min n0 (Z.of_nat (length T)) + 1) by (apply sa_sn_len_eq; lia).
remember (Z.to_nat (sn_len n0 T)) as dn eqn:Edn.
assert (HDN : Z.of_nat dn = sn_len n0 T) by (subst dn; rewrite Z2Nat.id; lia).
assert (DS0' : dest_ok tfibsegs B ly S W regs mem s0 (Z.of_nat dn)) by (rewrite HDN; exact DS0).
assert (AMS' : amem_range s0 (Z.of_nat dn)) by (rewrite HDN; exact AMS).
assert (AMS8 : amem_range s0 (Z.of_nat dn + 8)) by (rewrite HDN; exact HD8).
assert (RAS' : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s0 (Z.of_nat dn))
  by (rewrite HDN; exact RAS).
assert (WD : forall a, s0 <= a < s0 + Z.of_nat dn -> writable_at tfibsegs (cjstore (w_H W) mem) a)
  by (intros a Ha; exact (proj1 (DS0' a Ha))).
destruct (rw_cells_block_hd0 (w_H W) mem s0 dn ltac:(lia) ltac:(lia) WD
            (fun a Ha => sa_writable_aview _ _ _ (WD a Ha)) HNUL ltac:(lia)) as (junkd & LJ & RD).
assert (DIMG' : s0 + Z.of_nat dn <= 65536 \/ 0x5f6000 <= s0).
{ rewrite HDN. unfold zdisjoint in DIMG. cbn [fst snd] in DIMG. lia. }
(* ---- the family: format, pieces, arguments, text ---- *)
pose proof HFA as (Hf0 & _ & _ & _ & HFRA & _).
assert (PKC : forall p, pf_fm_piece p -> match p with PLit _ | Ps | Pps => True | _ => False end)
  by (intros p Hp; exact Hp).
assert (HAI : forall v, In (AInt v) args0 -> -2 ^ 31 <= v < 2 ^ 31).
{ intros v Hin. destruct (sa_pf_args_asan_In _ _ _ _ _ HPA Hin) as [w Hw].
  cbv beta iota delta [pf_arg_asan] in Hw. exact (proj1 Hw). }
assert (HAS : forall s, In (APtr s) args0 -> Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31).
{ intros s Hin. destruct (sa_pf_args_asan_In _ _ _ _ _ HPA Hin) as [w Hw].
  cbv beta iota delta [pf_arg_asan] in Hw. destruct Hw as (Hb & _ & Hl & _). split; assumption. }
assert (HAS' : forall s, In (APtr s) args0 -> PRL.zlength s < 2147483647).
{ intros s Hin. destruct (HAS s Hin) as [_ Hl]. unfold PRL.zlength. lia. }
assert (HTl : PRL.zlength T <= 2147483647) by (unfold PRL.zlength; lia).
destruct (fm_model_agree pf_fm_piece PKC fmtb ps args0 T HPS HPK HPT HAI HAS' HTl) as (AM & AP1 & _).
assert (TB : Forall (fun c => 0 <= c < 256) T).
{ apply (sa_pf_text_bytes ps args0 T (sa_pf_parse_lits _ _ _ (le_n _) HPS) HPK); [|exact HPT].
  intros s Hin. exact (proj1 (HAS s Hin)). }
assert (HU : forall u, In (AU64 u) args0 -> 0 <= u < 2 ^ 64).
{ intros u Hin. exfalso. exact (fm_args_kind pf_fm_piece PKC ps args0 T HPK HPT u Hin). }
assert (ZL : PRL.zlength (fmtb ++ [0]) = Z.of_nat (length fmtb) + 1).
{ unfold PRL.zlength. rewrite length_app. cbn [length]. lia. }
assert (ERS : vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp
              = [(spZ regs - K, spZ regs - (spZ regs - K)); (s0, Z.of_nat dn); (fp, 232); (cp, 16)]).
{ unfold vfp_out. rewrite HDN. replace (spZ regs - (spZ regs - K)) with K by lia. reflexivity. }
(* ---- the FILE, the cookie, the stack-protector cells ---- *)
assert (Hbp64 : bp < 2 ^ 64).
{ assert (L11 : (11 < length (sn_file snw bp cp))%nat) by (unfold sn_file; cbn; lia).
  pose proof (HFILE 11%nat L11) as X. unfold sn_file in X. cbn [nth] in X.
  pose proof (sa_rdword_range _ _ _ _ X). lia. }
(* GXA (4) with the frame order: the FILE, the cookie and the slots lie below TASK_SIZE *)
assert (HTB : fp + 232 <= TASK_SIZE /\ cp + 16 <= TASK_SIZE /\ ap + 8 * PRL.zlength (map w64 ws) <= TASK_SIZE).
{ unfold TASK_SIZE, PRL.zlength. rewrite length_map. lia. }
(* the read agreement the normalized store needs, from the contract's constants *)
pose proof (NM.ro_agree_of_consts W mem cr HCR HCOV) as HRO.
assert (WGC : forall a, gc <= a < gc + 8 -> writable_at tfibsegs (cjstore (w_H W) mem) a).
{ intros a Ha. apply sa_ssp_writable. left. rewrite Egc, S22 in Ha. lia. }
assert (WGV : forall a, gv <= a < gv + 8 -> writable_at tfibsegs (cjstore (w_H W) mem) a).
{ intros a Ha. apply sa_ssp_writable. right. rewrite Egv, S34 in Ha. lia. }
(* ---- the seam's carve-out list: what the per-call normalization keeps, and its visible hulls.
   The window's hull and the musl prefix's hull are AR's, not the contract's (FMgxaSeamReady.v
   stack_hull, prefix_hull); the rest are the contract's own ---- *)
pose proof HFA as (_ & _ & _ & AMF & _ & _).
destruct (NM.seam_drop_keeps ly (spZ regs - K) K s0 (Z.of_nat dn) f fmtb ws args0
            (aview tfibsegs (w_H W) mem) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)
            ltac:(lia) ltac:(lia) ltac:(lia) Hs0 AMS' Hf0 AMF HPA) as (KD & KF & KW & KP & KA & KAPP).
assert (HVR : Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r))
                (NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0)).
{ apply (NM.seam_R_hulls (aview tfibsegs (w_H W) mem)
           (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)).
  - rewrite HDN. exact SHV.
  - exact HFA.
  - eapply SR.stack_hull; try exact LAWS; try exact HARU; lia.
  - eapply SR.prefix_hull; try exact SYMS; try exact HARU.
  - exact HPA. }
assert (InD : In (s0, Z.of_nat dn) (NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0))
  by (unfold NM.seam_R; apply in_eq).
assert (InW : In (spZ regs - K, spZ regs - (spZ regs - K))
                (NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0)).
{ replace (spZ regs - (spZ regs - K)) with K by lia. unfold NM.seam_R. apply in_cons, in_cons, in_eq. }
set (RN := NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0) in *.
(* ---- GXA's walk, at the harness's arguments ---- *)
assert (APF : GVA.args_pf (cjstore (w_H W) mem) (map w64 ws) (map pt_parg args0))
  by exact (args_pf_of_pf_args_asan (w_H W) mem _ ws args0 HPA HSL).
pose proof (seam_vfprintf_a copy_ready set_ready strn_ready SPEC_memcpy SPEC_memset SPEC_strnlen) as G.
unfold GVA.vfprintf_snf_a_stmt in G.
specialize (G (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
  (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
  (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) (NM.cjnormv ly RN (w_H W) mem)
  fp cp s0 n0 (PRL.zlength T) bp f ap dn junkd (fmtb ++ [0]) (map w64 ws) (map pt_parg args0)
  (spZ regs - K) (w64 cval) (PRL.zlength T) T).
cbv zeta in G. rewrite Esp in G.
eapply srr_of_gxa_evt.
{ exact AF0x.Hwx_tfa. }
{ eapply sa_evt_eqv.
  - eapply NM.evt_from_norm_MS_v; [exact HRO|]. apply G; clear G.
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + apply NM.file_cjnormv;
        [lia | lia | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia |].
      exact (rw_cells_snf_file (w_H W) mem fp snw bp cp Esnw Hfp0 ltac:(lia) HFILE (fun a Ha => proj1 (DFP a Ha))).
    + apply NM.cookie_cjnormv;
        [lia | lia | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia |].
      exact (rw_cells_pair (w_H W) mem cp s0 n0 Hcp0 ltac:(lia) HCK (fun a Ha => proj1 (DCK a Ha))).
    + apply NM.dest_cjnormv; [lia | unfold TASK_SIZE, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
                             | lia
                             | intros a Ha;
                               exact (app_mem_of_amem_range s0 (Z.of_nat dn) a AMS' ltac:(lia) ltac:(lia) ltac:(lia))
                             | exact RD].
    + exact LJ.
    + apply NM.fmt_cjnormv; [exact HRO | rewrite ZL; lia |].
      exact (fmt_bytes_of_fmt_at (w_H W) mem _ f fmtb HFA ltac:(lia)).
    + exact (fmt_bytes_small _ _ f fmtb ps HFA HPS).
    + exact AP1.
    + apply NM.va_area_cjnormv;
        [exact HRO | lia
        | apply GAF.high_stack_app;
          [unfold GAF.HIGHMEM_BEG; lia | unfold GAF.APPMEM_END, PRL.zlength; rewrite length_map; lia] |].
      exact (va_area_of_words_at (w_H W) mem ap ws Hap0 ltac:(lia) HAP).
    + apply NM.args_ok_cjnormv;
        [exact HRO | exact (NM.args_task_of_pf _ _ _ APF) | exact (NM.args_app_of_pf _ _ _ APF) |].
      exact (args_ok_of_pf_args_asan (w_H W) mem _ ws args0 fp (spZ regs - K) 0 cp 16 s0 (Z.of_nat dn)
               (spZ regs - K) (spZ regs) (spZ regs - K) HPA HSL HU ERS eq_refl eq_refl eq_refl ltac:(lia)).
    + exact AM.
    + lia.
    + unfold PRL.zlength. lia.
    + rewrite HDN, SNL. unfold PRL.zlength. lia.
    + lia.
    + apply NM.stk_window_cjnormv;
        [lia | unfold TASK_SIZE; lia | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia |].
      exact (stk_of_apresent (w_H W) mem (spZ regs - K) (spZ regs) ltac:(lia) ltac:(lia) HWIN).
    + lia.
    + lia.
    + lia.
    + apply NM.ssp_cells_cjnormv.
      exact (ssp_cells_of_view (w_H W) mem gc gv cval (w64 cval) Egc Egv Hgc Hgv eq_refl WGC WGV).
    + exact (NM.mem_inv_cjnormv ly RN (w_H W) mem).
    + exact FRM0.
    + rewrite ZL. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold PRL.zlength. rewrite length_map. lia.
    + lia.
    + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMS'. lia.
    + unfold PRL.zlength. rewrite length_map. lia.
    + lia.
    + assert (VR : GVA.vf_ready_a (GSA.snf_out_ready copy_ready) set_ready strn_ready copy_ready SEAM_INV
                     (NM.cjnormv ly RN (w_H W) mem) (spZ regs) (spZ regs - K) fp cp s0 dn n0 bp f ap
                     (fmtb ++ [0]) (map w64 ws) (map pt_parg args0)).
      { apply NM.vf_ready_cjnormv.
        * rewrite ZL. lia.
        * rewrite ZL. apply pf_rng_of_view; [lia | lia | lia | | exact HFRA].
          unfold amem_range, kLowMemEnd. left. lia.
        * rewrite ZL. exact (NM.sh_kept_of_hull ly RN f (Z.of_nat (length fmtb) + 1) KF).
        * exact (musl_prefix_of_ARU B ly S U W mem md (zsh_rodata_of_tfib B SYMS) HARU).
        * exact (NM.sh_kept_of_hull ly RN (@sym A_img 0x1029e) 9 KP).
        * exact APF.
        * exact KA.
        * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia.
        * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia.
        * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia.
        * intros a Ha. exact (app_mem_of_amem_range s0 (Z.of_nat dn) a AMS' ltac:(lia) ltac:(lia) ltac:(lia)).
        * unfold GCA.OUT_DEPTH. lia.
        * exact (READY ly RN S U W regs mem md (spZ regs - K) fp cp s0 dn HPRE InD InW HVR ltac:(lia)
                   ltac:(unfold GCA.OUT_DEPTH; lia) HWIN FO1 FO2 ltac:(unfold GAF.APPMEM_END, TASK_SIZE in *; lia)
                   DFP DCK DS0' AMS' AMS8 RAS' ltac:(lia) ltac:(lia) ltac:(lia)). }
      exact (proj2 VR).
  - split; [apply RE.xregs_eqv_sym, RE.mkR_eqv_of; reflexivity|]. repeat split. }
(* ---- GXA's post, read as the harness's ---- *)
intros ms' model' (y & (st0 & HQ & HREL & HSAME) & HEQ) HSBM _.
pose proof (NM.post_from_norm_a_v SEAM_INV ly RN (w_H W) mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              HRO HREL HSAME HQ) as HP.
clear HQ.
destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & fjunk & m'
                & Ey & MU & WM & FRM' & FREG & STK' & SSP' & DST' & CKC' & FPC').
subst y. rewrite Esp in MU.
destruct ms' as [R' F' pc' svc' rv' fc'' mm ro'].
destruct HEQ as (HR & HF & HPC & HSVC & HRV & HFC & HM & HROM).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom CJMS.MS] in HR, HF, HPC, HSVC, HRV, HFC, HM, HROM.
subst F' pc' svc' rv' fc'' mm ro'.
assert (EPC : CJMS.ret_pc (getr regs 1) = w64 (raZ regs)) by exact (ret_pc_raZ _ HRET).
assert (OWN : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a ->
          CJF.outside [(spZ regs - K, spZ regs); (fp, fp + 232); (cp, cp + 16); (s0, s0 + Z.of_nat dn)] a).
{ apply (win_owned B LAWS ly S U W regs mem md _ HPRE). intros a Ha HE.
  apply Exists_cons in HE; destruct HE as [HE|HE]; [cbn [fst snd] in HE; left; lia|].
  apply Exists_cons in HE; destruct HE as [HE|HE];
    [cbn [fst snd] in HE; right; exact (proj1 (proj2 (DFP a ltac:(lia))))|].
  apply Exists_cons in HE; destruct HE as [HE|HE];
    [cbn [fst snd] in HE; right; exact (proj1 (proj2 (DCK a ltac:(lia))))|].
  apply Exists_cons in HE; destruct HE as [HE|HE];
    [cbn [fst snd] in HE; right; exact (proj1 (proj2 (DS0' a ltac:(lia))))|].
  inversion HE. }
cbv beta. split; [reflexivity|].
exists (YK11.mkFP Ft fc'), R', (munrestrict (w_H W) mem m'), model'.
split.
{ rewrite cfg_of_ms. unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite EPC. reflexivity. }
split.
{ intros k Hk. exact (FREG k Hk). }
split; [exact FRM'|].
split.
{ destruct (aru_of_window B LAWS ly S U W regs mem md m' _ HPRE MU WM OWN) as (md2 & SB2 & ARU2).
  pose proof (same_but_materialized_frame md md2 SB2) as (_ & Hv2 & Hl2 & _).
  pose proof (same_but_materialized_frame md model' HSBM) as (_ & Hv' & Hl' & _).
  exact (sa_ARU_model_same B ly S U W _ md2 model' ARU2 ltac:(congruence) ltac:(congruence)). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct RR as [RR|RR];
    [subst r; rewrite !sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity|]).
  subst r; rewrite !sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity. }
split; [exact HSBM|].
split.
{ rewrite sa_getr_nz by reflexivity. rewrite <- (HR _) by reflexivity. reflexivity. }
split.
{ intros i Hi.
  destruct DST' as [[CW BA] _].
  cbn [CJC.cells_wf CJC.cell_wf CJC.cells_bytes CJC.cbytes] in CW, BA.
  rewrite app_nil_r in BA. destruct CW as [CWL _].
  match type of BA with CJM.bytes_at _ _ _ ?bs0 => set (bs := bs0) in BA, CWL end.
  assert (HV : forall a, s0 <= a < s0 + Z.of_nat (length bs) -> w_H W (Z_to_bv 64 a) = false).
  { intros a Ha. rewrite CWL in Ha. exact (sa_writable_vis W mem a (WD a Ha)). }
  pose proof (view_of_bytes_at (w_H W) mem m' s0 bs BA HV (Z.to_nat i) ltac:(rewrite CWL; lia)) as V.
  rewrite Z2Nat.id in V by lia. rewrite V. f_equal.
  unfold bs. rewrite sa_nth_zb_app by (rewrite length_firstn; lia).
  unfold sn_bytes. apply sa_bv_u8. apply sa_nth_range. apply Forall_app. split.
  - apply sa_Forall_firstn. exact TB.
  - constructor; [lia | constructor]. }
split.
{ intros a Ha Hd HN.
  apply (win_view_out (w_H W) mem m' _ MU a Ha). cbn [CJF.outside].
  assert (N1 : ~ (spZ regs - K <= a < spZ regs - K + K)) by (intros X; apply HN; apply Exists_cons_hd; exact X).
  assert (N2 : ~ (fp <= a < fp + 232)) by (intros X; apply HN; apply Exists_cons_tl; apply Exists_cons_hd; exact X).
  assert (N3 : ~ (cp <= a < cp + 16))
    by (intros X; apply HN; apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd; exact X).
  rewrite HDN. repeat split; lia. }
apply (win_present_off (w_H W) mem m' _ MU WM).
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.

End S.
