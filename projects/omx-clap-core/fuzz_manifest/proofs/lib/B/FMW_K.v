(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v, with its module paths and module names changed; 258 of its 515 lines of code are new or changed and 1100 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_K.v at a working branch 0d38fb8ac64, relocated A->B by
   Theorem Labs tools over the unstripped twins, every image numeral re-derived by symbol / section / string
   content and checked by revcheck (reports in (internal path)). Imports: lib.Reusable kernel kept;
   the per-image root files from lib.ReusableB; fm's own per-image files from lib.B; FMupoison shared from lib.A. *)
(* G5's walk kit for fm's ASan program part: the image facts the donor engine (YCbq.v aj_run / SRr_run_AJ) asks for,
   the entry symbolic state of a function with a stack frame, and the frame transfers below alloc_ceiling. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- fm's image ---- *)
Lemma fm_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))
  tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as H. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma fm_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* ---- the entry state of a function whose prologue is `addi sp, sp, -f` ---- *)
Definition fstk (f : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- f) 0 (- f) 0 [].
Definition fss0 (pc f : Z) : sstate :=
  mkSS pc sr_atoms [fstk f] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma fmw_sp : forall B STK ly S (W : world tfibsegs) regs mem md ch,
  afn_pre tfibsegs B STK ly S W regs mem md ch ->
  spZ regs mod 16 = 0 /\ alloc_ceiling + STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ 0 <= STK.
Proof.
intros B STK ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.
Lemma fmw_entry : forall B STK f ly S (W : world tfibsegs) regs mem md ch pc,
  afn_pre tfibsegs B STK ly S W regs mem md ch -> 0 <= f <= STK -> regions_wf [fstk f] = true ->
  st_ok tfibsegs (Ereg regs []) (fss0 pc f) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S W regs mem md ch pc HPRE Hf Hwf.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fmw_sp B STK ly S W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
rewrite restrict_mkst_fx.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold fss0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor].
  apply (region_ok_stack tfibsegs _ _ 2 (spZ regs) (- f) E2); [lia | lia |].
  intros a Ha. apply (apresent_writable tfibsegs). apply Hpres. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]].
Qed.

Lemma fmw_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. apply zcanon_id. unfold M64. apply u64_range.
Qed.

(* ---- memory unchanged below a bound (the run's stack writes are all above alloc_ceiling) ---- *)
Definition same_below (m m' : word -> option byte) (lo : Z) : Prop :=
  forall x, 0 <= x < lo -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Lemma same_below_refl : forall m lo, same_below m m lo.
Proof. intros m lo x _. reflexivity. Qed.
Lemma same_below_trans : forall m1 m2 m3 lo, same_below m1 m2 lo -> same_below m2 m3 lo -> same_below m1 m3 lo.
Proof. intros m1 m2 m3 lo H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.
Lemma same_below_mono : forall m m' lo lo', same_below m m' lo -> lo' <= lo -> same_below m m' lo'.
Proof. intros m m' lo lo' H Hl x Hx. apply H. lia. Qed.
(* a run whose one region is a stack window at or above lo leaves memory below lo unchanged *)
Lemma same_below_frame1 : forall E (r : YP09.region) m m' lo,
  frame_of E [r] m m' -> lo <= base_val E (YP09.r_base r) + YP09.r_wlo r -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E r m m' lo HF Hlo H64 x Hx.
apply (frame_of_one E m m' r lo (base_val E (YP09.r_base r) + YP09.r_whi r) (Z_to_bv 64 x) HF Hlo ltac:(lia)).
left. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma mbyte_below : forall (H : word -> bool) m m' lo a, same_below m m' lo -> 0 <= a < lo ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H m m' lo a Hs Ha. unfold mbyte, mrestrict. rewrite (Hs a Ha). reflexivity. Qed.
Lemma aview_below : forall (H : word -> bool) m m' lo a, same_below m m' lo -> 0 <= a < lo ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' lo a Hs Ha. unfold aview. rewrite (mbyte_below H m m' lo a Hs Ha). reflexivity. Qed.
Lemma val_mem_below : forall (H : word -> bool) m m' lo a (n : nat) v, same_below m m' lo ->
  0 <= a -> a + Z.of_nat n <= lo -> val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' lo a n v Hs H0 Hn Hv k Hk. rewrite (mbyte_below H m m' lo (a + Z.of_nat k) Hs ltac:(lia)). exact (Hv k Hk).
Qed.
Lemma fm_glob_below : forall (W : world tfibsegs) m m' live peak cnt fail,
  same_below m m' alloc_ceiling -> fm_glob tfibsegs W m live peak cnt fail -> fm_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hs (G1 & G2 & G3 & G4 & R).
pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hv. exact (val_mem_below (w_H W) m m' alloc_ceiling a 8 v Hs Ha Hb Hv). }
unfold fm_glob. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.
Lemma arodata_below : forall (B : asyms) (W : world tfibsegs) m m',
  same_below m m' alloc_ceiling -> arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros B W m m' Hs HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FM_RLO, FM_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fm_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia. }
rewrite (aview_below (w_H W) m m' alloc_ceiling a Hs Hb). exact (HR a Ha Ho He).
Qed.
Lemma cstr_ok_below : forall (W : world tfibsegs) m m' p l,
  same_below m m' alloc_ceiling -> cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' p l Hs ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; exact (aview_below (w_H W) m m' alloc_ceiling a Hs Ha)).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_below _ m m' alloc_ceiling a Hs). lia. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ intros x Hx. destruct (Hra x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
  rewrite AV; [exact Hs1|]. unfold shadow_of_addr, SHADOW_OFF. lia. }
split.
{ intros s Hsr. rewrite AV; [exact (Hhv s Hsr)|]. unfold shadow_addr, SHADOW_OFF in Hsr. lia. }
intros a Ha. rewrite AV; [exact (Htl a Ha)|]. pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
Qed.

(* ---- reading the symbolic state ---- *)
Lemma fmw_region_nth : forall E ss ms i r,
  st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok tfibsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma fmw_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem tfibsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok tfibsegs E m b od w e v Hck He Hv Hw).
Qed.
(* a register the run left as its entry atom still holds the entry value *)
Lemma fmw_reg_atom : forall (H : word -> bool) regs0 extra ss ms (r r' : bv 5) n,
  st_ok tfibsegs (Ereg regs0 extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs0 r'.
Proof.
intros H regs0 extra ss ms r r' n HS Hr Hn.
rewrite (st_ok_restrict_reg tfibsegs H _ ss ms r HS), Hr, fmw_SOff0. exact (ew_Ereg_nat regs0 extra n r' Hn).
Qed.
Lemma fmw_reg_off : forall (H : word -> bool) E ss ms (r : bv 5) n z v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 -> bv_unsigned (getr (ms_regs ms) r) = v + z.
Proof.
intros H E ss ms r n z v HS Hr Hv Hz.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, denot_SOff, Hv. apply zcanon_id. unfold M64. lia.
Qed.
Lemma fmw_reg_lit : forall (H : word -> bool) E ss ms (r : bv 5) z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> 0 <= z < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 z.
Proof.
intros H E ss ms r z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr.
apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)). rewrite U_lit by exact Hz.
rewrite unsigned_lit_small by exact Hz. reflexivity.
Qed.
(* a callee-saved register the caller left as its entry atom up to a call, read after the call *)
Lemma fmw_kept_reg : forall (H : word -> bool) regs0 extra0 ssC msC regs2 extra2 (r : bv 5) n,
  st_ok tfibsegs (Ereg regs0 extra0) ssC (restrict H msC) ->
  sr_get (ss_regs ssC) r = SOff n 0 -> Z.of_nat n = bv_unsigned r ->
  aregs_preserved (ms_regs msC) regs2 -> acallee_saved (bv_unsigned r) ->
  sv_denot (Ereg regs2 extra2) (SOff n 0) = getr regs0 r.
Proof.
intros H regs0 extra0 ssC msC regs2 extra2 r n HS Hr Hn HP Hcs.
rewrite fmw_SOff0, (ew_Ereg_nat regs2 extra2 n r Hn).
pose proof (HP (bv_unsigned r) Hcs) as E. rewrite Z_to_bv_bv_unsigned in E. rewrite E.
exact (fmw_reg_atom H regs0 extra0 ssC msC r r n HS Hr Hn).
Qed.
Lemma fmw_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hc. pose proof (HP _ Hc) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Lemma fmw_reg_extra : forall (H : word -> bool) regs extra ss ms (r : bv 5) j,
  st_ok tfibsegs (Ereg regs extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
  getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros H regs extra ss ms r j HS Hr. rewrite (st_ok_restrict_reg tfibsegs H _ ss ms r HS), Hr, fmw_SOff0.
apply ew_Ereg_extra.
Qed.
(* the value of an expected callee-saved register that is the frame's sp back up, or a reloaded extra atom *)
Lemma fmw_sp_back : forall regs extra regs0 f, bv_unsigned (ew (Ereg regs extra) 2) = spZ regs0 - f ->
  sv_denot (Ereg regs extra) (SOff 2 f) = getr regs0 2.
Proof.
intros regs extra regs0 f H. apply bv_eq. rewrite denot_SOff, H. unfold spZ.
replace (bv_unsigned (getr regs0 2) - f + f) with (bv_unsigned (getr regs0 2)) by lia.
apply zcanon_id. unfold M64. apply u64_range.
Qed.
Lemma fmw_extra_atom : forall regs extra j, sv_denot (Ereg regs extra) (SOff (32 + j) 0) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j. rewrite fmw_SOff0. apply ew_Ereg_extra. Qed.
(* a value chunk holds under any environment that denotes its value the same *)
Lemma chunk_ok_env : forall E E' m base o w e, sv_denot E e = sv_denot E' e ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk o (CVal w e)) -> YP09.chunk_ok tfibsegs E' m base (YP09.mkChunk o (CVal w e)).
Proof.
intros E E' m base o w e He Hc i Hi. destruct (Hc i Hi) as (b & H1 & H2). exists b.
cbn [YP09.cbyte YP09.c_val YP09.c_off] in *. rewrite <- He. split; assumption.
Qed.
(* the saved-register chunks of a frame (values: extra atoms) hold again after a call changes the register file *)
Lemma fmw_chunks_extra : forall regs regs' extra m base cs,
  Forall (fun c => exists j w, c = YP09.mkChunk (YP09.c_off c) (CVal w (SOff (32 + j) 0))) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs extra) m base) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) m base) cs.
Proof.
intros regs regs' extra m base cs Hsh Hcs. apply Forall_forall. intros c Hc.
destruct (proj1 (Forall_forall _ _) Hsh c Hc) as (j & w & Ec).
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hk. rewrite Ec in Hk |- *.
apply (chunk_ok_env (Ereg regs extra)); [rewrite !fmw_extra_atom; reflexivity | exact Hk].
Qed.
(* the callee-saved registers at the end, from what the symbolic state says of each *)
Lemma fmw_preserved : forall (H : word -> bool) E ss ms regs0 (expect : bv 5 -> sv),
  st_ok tfibsegs E ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (expect r)) CALLEE_SAVED = true ->
  (forall r, In r CALLEE_SAVED -> sv_denot E (expect r) = getr regs0 r) ->
  aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 expect HS Hcs Hex r Hr.
assert (Hin : In (Z_to_bv 5 r : bv 5) CALLEE_SAVED).
{ unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [->|Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms _ HS), Hq. exact (Hex _ Hin).
Qed.

(* ---- after a program call: the composed journal and the symbolic state at the return address ---- *)
Definition fstk_ret (f : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) 0 f 0 f cs.
Definition fss_ret (pc f : Z) (cs : list YP09.chunk) : sstate :=
  mkSS pc sr_atoms [fstk_ret f cs] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma chunk_ok_mbyte : forall E (m m' : word -> option byte) base (c : YP09.chunk),
  (forall i, 0 <= i < YP09.c_len c -> mbyte tfibsegs m' (base + YP09.c_off c + i) = mbyte tfibsegs m (base + YP09.c_off c + i)) ->
  YP09.chunk_ok tfibsegs E m base c -> YP09.chunk_ok tfibsegs E m' base c.
Proof. intros E m m' base c Hm Hc i Hi. destruct (Hc i Hi) as (b & H1 & H2). exists b. rewrite Hm by exact Hi. auto. Qed.
(* ajournal_sub (YCbq.v) when the callee's footprint lies in the caller's (fm's statics FM_PSTAT_FP are image bytes,
   not blocks, so ajournal_sub's block premise does not hold for them) *)
Lemma ajournal_sub_incl : forall B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 -> (forall a, inFP FP1 a -> inFP FP a) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
(HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2) Hlo Hhi HF.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact HAR2|].
split; [eapply layout_le_trans; [exact Hsecs | exact Hly | exact Hly2]|].
split; [lia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0). destruct (HF 0 (ex_intro _ r (conj Hr H0))) as (r' & Hr' & H0'). exists r'. split; [exact Hr' | exact H0']. }
split; [eapply aos_step_trans_fp; [exact HFo | exact Hio | exact Hio2]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | lia]. }
split.
{ intros p n i H1 H2 Hi Hnf.
  assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
  { destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [exact Hc|].
    exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
  rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
  intros Hf1. exact (Hnf (HF _ Hf1)). }
split.
{ intros a Hi Hns He Hnf Hsp. rewrite <- (F3 a Hi Hns He Hnf Hsp). apply (G3 a Hi Hns He).
  - intros Hf1. exact (Hnf (HF _ Hf1)).
  - intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  apply (G4 cid pos a HinC).
  - unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
  - intros Hf1. exact (Hnf (HF _ Hf1)). }
split.
{ intros p n i H1 H2 Hi.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc]; [|exact (Hgone p n i H1 Hc Hi)].
  exact (HF _ (Hgone2 p n i Hc H2 Hi)). }
split.
{ intros a Ha.
  destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb]; [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; lia|]].
  - eapply (apresent_transfer tfibsegs); [lia | intros Him; pose proof (fm_segs_low a Him); lia | apply G1; lia | apply Hpres; exact Ha].
  - eapply (apresent_transfer tfibsegs); [lia | intros Him; pose proof (fm_segs_low a Him); lia | apply G1; lia | apply Hpres; exact Ha]. }
split; [exact Hstatic|]. split; [|exact HQT2].
{ intros a HXa He. rewrite <- (F5 a HXa He).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.
Lemma fmw_after_call : forall B STK sp0 FP ly S W mem md lyc Sc Wc memC mdC k STKc FP1 f regsC ly' S' W' regs' mem' md' kc
  extra cs r,
  ajournal tfibsegs B STK sp0 FP ly S W mem md [] lyc Sc Wc memC mdC k ->
  ajournal tfibsegs B STKc (spZ regsC) FP1 lyc Sc Wc memC mdC [] ly' S' W' mem' md' kc ->
  (forall a, inFP FP1 a -> inFP FP a) ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H Wc) memC) (sp0 - f)) cs ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret r f cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W mem md lyc Sc Wc memC mdC k STKc FP1 f regsC ly' S' W' regs' mem' md' kc extra cs r
  HJ HJc HFP HP Hsp Hf HSc Hbud Hal Hwf Hin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W mem md [] ly' S' W' mem' md' (k + kc)).
{ pose proof (ajournal_sub_incl B STK sp0 FP ly S W mem md [] lyc Sc Wc memC mdC k
    STKc (spZ regsC) FP1 [] ly' S' W' mem' md' kc HJ HJc ltac:(lia) ltac:(lia) HFP) as H. exact H. }
split; [exact HJ2|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' extra) 2) = sp0 - f) by (rewrite (ew_Ereg_nat regs' extra 2 2%bv eq_refl); exact Usp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs). apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H Wc) memC)); [|exact Hck].
    destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs). apply F1; [lia | intros Hx; lia].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
Qed.
(* the same across two program calls (call sites HSc, HSe; the callees' aregs_preserved HP, HP') *)
Lemma fmw_kept_reg2 : forall (H1 H2 : word -> bool) regs0 extra0 ssC msC regs2 extra2 ssE msE regs3 extra3 (r : bv 5) n,
  st_ok tfibsegs (Ereg regs0 extra0) ssC (restrict H1 msC) -> sr_get (ss_regs ssC) r = SOff n 0 ->
  st_ok tfibsegs (Ereg regs2 extra2) ssE (restrict H2 msE) -> sr_get (ss_regs ssE) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r ->
  aregs_preserved (ms_regs msC) regs2 -> aregs_preserved (ms_regs msE) regs3 -> acallee_saved (bv_unsigned r) ->
  sv_denot (Ereg regs3 extra3) (SOff n 0) = getr regs0 r.
Proof.
intros H1 H2 regs0 extra0 ssC msC regs2 extra2 ssE msE regs3 extra3 r n HSc Hr1 HSe Hr2 Hn HP HP' Hcs.
rewrite fmw_SOff0, (ew_Ereg_nat regs3 extra3 n r Hn), (fmw_pres _ _ r HP' Hcs).
rewrite (fmw_reg_atom H2 regs2 extra2 ssE msE r r n HSe Hr2 Hn), (fmw_pres _ _ r HP Hcs).
exact (fmw_reg_atom H1 regs0 extra0 ssC msC r r n HSc Hr1 Hn).
Qed.
(* fm's statics footprint does not open the sink and misses the read-only bytes; the read-only view rides through a
   journal whose footprint does neither (the journal's image clause; FMH_Fn.v fpre) *)
Lemma pstat_closed : ~ YI16.sink_open_fp FM_PSTAT_FP.
Proof.
intros (r & Hr & Ha). cbv [FM_PSTAT_FP In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.
Lemma pstat_not_roP : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> ~ inFP FM_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z =>
  forallb (fun s => seg_writable s || (snd r <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r))
    tfibsegs && ((snd r <=? FM_RLO) || (FM_RHI <=? fst r))) FM_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply andb_prop in H as [Hs Hrl].
destruct Hro as [(s & Hin & Hw & Hsr) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hs s Hin) as Hq. cbv beta in Hq. rewrite Hw in Hq. cbn [orb] in Hq.
  apply Bool.orb_true_iff in Hq as [Hq|Hq]; apply Z.leb_le in Hq; lia.
- apply Bool.orb_true_iff in Hrl as [Hq|Hq]; apply Z.leb_le in Hq; lia.
Qed.
Lemma nil_not_roP : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> ~ inFP [] a.
Proof. intros a _ Ha. exact (inFP_nil a Ha). Qed.
Lemma roP_img : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FM_RLO) && (FM_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
Lemma arodata_kept : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  (forall a, in_roP tfibsegs FM_RLO FM_RHI a -> ~ inFP FP a) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hcl Hro HR a Ha Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (roP_img a Ha) Ho He (Hro a Ha) (fp_spares_closed FP a Hcl)). exact (HR a Ha Ho He).
Qed.

(* ---- many program calls: the callee-saved registers outside X keep their entry values ---- *)
Definition kept_from (regs0 regs : bvmap 5 word) (X : list Z) : Prop :=
  forall r, acallee_saved r -> ~ In r X -> getr regs (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Lemma kept_refl : forall regs X, kept_from regs regs X.
Proof. intros regs X r _ _. reflexivity. Qed.
(* the symbolic state left every callee-saved register outside X as its own entry atom *)
Definition atoms_kept (ss : sstate) (X : list Z) : bool :=
  forallb (fun r : bv 5 => existsb (Z.eqb (bv_unsigned r)) X || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    CALLEE_SAVED.
Lemma acs_bv : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r : bv 5) = r /\ In (Z_to_bv 5 r : bv 5) CALLEE_SAVED.
Proof.
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [->|Hc]; [split; [reflexivity | cbv [CALLEE_SAVED In]; repeat (first [left; apply bv_eq; reflexivity | right])]|]).
subst. split; [reflexivity | cbv [CALLEE_SAVED In]; repeat (first [left; apply bv_eq; reflexivity | right])].
Qed.
Lemma atoms_kept_get : forall ss X r, atoms_kept ss X = true -> acallee_saved r -> ~ In r X ->
  sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0.
Proof.
intros ss X r HA Hc HX. destruct (acs_bv r Hc) as [Eu Hin].
pose proof (proj1 (forallb_forall _ _) HA _ Hin) as H. cbv beta in H. rewrite Eu in H.
apply Bool.orb_true_iff in H as [H|H].
- exfalso. apply existsb_exists in H as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. subst x. exact (HX Hx).
- apply sv_eqb_eq in H. exact H.
Qed.
Lemma kept_step : forall (H : word -> bool) regs0 regs extra ss ms regs' X,
  kept_from regs0 regs X -> st_ok tfibsegs (Ereg regs extra) ss (restrict H ms) -> atoms_kept ss X = true ->
  aregs_preserved (ms_regs ms) regs' -> kept_from regs0 regs' X.
Proof.
intros H regs0 regs extra ss ms regs' X HK HS HA HP r Hc HX.
destruct (acs_bv r Hc) as [Eu _].
rewrite (HP r Hc), (st_ok_restrict_reg tfibsegs H _ ss ms _ HS), (atoms_kept_get ss X r HA Hc HX), fmw_SOff0.
assert (Hr : 0 <= r < 32) by (unfold acallee_saved in Hc; lia).
rewrite (ew_Ereg_nat regs extra (Z.to_nat r) (Z_to_bv 5 r) ltac:(rewrite Eu; lia)). exact (HK r Hc HX).
Qed.
(* a register outside X, read as its own atom of a later register file *)
Lemma fmw_kept_atom : forall regs0 regs extra X (r : bv 5) n,
  kept_from regs0 regs X -> Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) -> ~ In (bv_unsigned r) X ->
  sv_denot (Ereg regs extra) (SOff n 0) = getr regs0 r.
Proof.
intros regs0 regs extra X r n HK Hn Hc HX. rewrite fmw_SOff0, (ew_Ereg_nat regs extra n r Hn).
pose proof (HK _ Hc HX) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.
(* a callee-saved register a call site holds as atom n: its value after the call *)
Lemma fmw_carry : forall (H : word -> bool) regs extra ss ms regs' (r : bv 5) n v,
  st_ok tfibsegs (Ereg regs extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  ew (Ereg regs extra) n = v -> aregs_preserved (ms_regs ms) regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = v.
Proof.
intros H regs extra ss ms regs' r n v HS Hr Hv HP Hc.
rewrite (fmw_pres _ _ r HP Hc), (st_ok_restrict_reg tfibsegs H _ ss ms r HS), Hr, fmw_SOff0. exact Hv.
Qed.
(* the caller's frame-pointer chain over a journal (it lies at or above the entry sp) *)
Lemma fmw_achain_kept : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  achain ly (aview tfibsegs (w_H W) mem) sp0 v ch -> achain ly' (aview tfibsegs (w_H W') mem') sp0 v ch.
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ Hch.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly _ _ sp0 v ch sp0 Hch ltac:(lia) ltac:(lia)).
intros a Ha. apply F1; lia.
Qed.
Lemma nil_closed : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.
Lemma kept_get : forall regs0 regs X (r : bv 5), kept_from regs0 regs X ->
  acallee_saved (bv_unsigned r) -> ~ In (bv_unsigned r) X -> getr regs r = getr regs0 r.
Proof. intros regs0 regs X r HK Hc HX. pose proof (HK _ Hc HX) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
(* equal block lists, equal live bytes *)
Lemma bb_eq : forall B ly S ly' S', ablocks B ly' S' = ablocks B ly S -> blocks_bytes S' = blocks_bytes S.
Proof. intros B ly S ly' S' E. rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B ly S), E. reflexivity. Qed.
End e.
(* the acallee_saved side goal of a concrete register *)
Ltac fmw_cs_side :=
  unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.
(* the per-register goals of fmw_preserved: expectf gives the expected symbolic value (sp back up by the frame,
   reloaded extra atoms, or the entry atom kept across the calls: the tactic kept) *)
Ltac fmw_cs_cases_t expectf Esp kept :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [CALLEE_SAVED In] in Hr;
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (expectf ?q) = _ =>
    let e := eval vm_compute in (expectf q) in change (expectf q) with e end;
  first [ eapply fmw_sp_back; rewrite Esp; lia | rewrite fmw_SOff0; reflexivity | kept ].
(* after one program call: HSc is the call-site state, HP the callee's aregs_preserved, Esp the resumed sp *)
Ltac fmw_cs_cases expectf HSc HP Esp :=
  fmw_cs_cases_t expectf Esp ltac:(eapply fmw_kept_reg;
    [exact HSc | vm_compute; reflexivity | vm_compute; reflexivity | exact HP | fmw_cs_side]).
(* after two program calls *)
Ltac fmw_cs_cases2 expectf HSc HP HSe HP' Esp :=
  fmw_cs_cases_t expectf Esp ltac:(eapply fmw_kept_reg2;
    [exact HSc | vm_compute; reflexivity | exact HSe | vm_compute; reflexivity | vm_compute; reflexivity
    | exact HP | exact HP' | fmw_cs_side]).
(* the write-window obligation of a run resumed after a call (one stack region, base sp0 - f, window [0, f)) *)
Ltac fmw_awr_ret Esp f :=
  try (unfold fss_ret); cbn [add_cond ss_mem];
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - f);
  [reflexivity | exact Esp | cbn; lia | cbn; lia | apply awr_ok_nil].
(* every unrestricted run frame in context (one stack region at or above alloc_ceiling) as same_below, chained *)
Ltac fmw_sb Esp :=
  repeat match goal with
  | HF : frame_of ?E ?rs ?m1 ?m2 |- _ =>
      lazymatch m1 with mrestrict _ _ => fail | _ => idtac end;
      let H := fresh "SB" in
      assert (H : same_below m1 m2 alloc_ceiling)
        by (try (unfold fss_ret in HF); cbn [add_cond ss_mem] in HF;
            eapply (same_below_frame1 E _ m1 m2 alloc_ceiling HF);
            [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Esp; lia | lia]);
      clear HF
  end;
  repeat match goal with
  | H1 : same_below ?a ?b alloc_ceiling, H2 : same_below ?b ?c alloc_ceiling |- _ =>
      let H := fresh "SB" in pose proof (same_below_trans a b c alloc_ceiling H1 H2) as H; clear H1 H2
  end.
(* the return of a framed function: everything of fpost but its Q (cs: the callee-saved tactic) *)
Ltac fmw_ret_t tblok expectf HSf HJf Hra LAWS HSL cs :=
  lazymatch type of HSf with st_ok _ (Ereg ?regs2 ?extra) ?ssf (restrict (w_H ?W2) ?msf) =>
  let R1F := fresh "R1F" in
  pose proof (fmw_reg_extra _ regs2 extra _ msf 1%bv 0 HSf ltac:(vm_compute; reflexivity)) as R1F;
  eapply (SRr_ret_at tfibsegs _ tblok fm_wx); [exact HSf | reflexivity | vm_compute; reflexivity |];
  let mat2 := fresh "mat" in intros mat2;
  let Hpc := fresh "Hpc" in
  lazymatch type of Hra with YK0s.ret_ok (getr ?regs0 1) =>
    assert (Hpc : v_jalr (getr (ms_regs msf) 1) 0 = getr regs0 1) by (rewrite R1F; exact Hra);
    rewrite Hpc; unfold fpost, apost_base;
    rewrite ?wvb_collapse in HJf;
    do 5 eexists; split; [reflexivity|];
    split; [apply (ajournal_materialize tfibsegs _ LAWS HSL); exact HJf|];
    split; [apply (fmw_preserved _ _ _ msf regs0 expectf HSf); [vm_compute; reflexivity | cs]|]
  end end.
Ltac fmw_ret tblok expectf HSf HJf HSc HP Esp Hra LAWS HSL :=
  fmw_ret_t tblok expectf HSf HJf Hra LAWS HSL ltac:(fmw_cs_cases expectf HSc HP Esp).
Ltac fmw_ret2 tblok expectf HSf HJf HSc HP HSe HP' Esp Hra LAWS HSL :=
  fmw_ret_t tblok expectf HSf HJf Hra LAWS HSL ltac:(fmw_cs_cases2 expectf HSc HP HSe HP' Esp).

(* ~ In (bv_unsigned r) X of a concrete register and list *)
Ltac fmw_notin := let H := fresh in intro H; vm_compute in H; lia.
(* the registers of a kept_from final state: sp back up by the frame (Esp), reloaded from extra, or kept (HK) *)
Ltac fmw_cs_cases_k expectf Esp HK :=
  fmw_cs_cases_t expectf Esp ltac:(eapply fmw_kept_atom; [exact HK | vm_compute; reflexivity | fmw_cs_side | fmw_notin]).
(* a register outside X of a kept_from register file *)
Ltac fmw_kget HK r := exact (kept_get _ _ _ r HK ltac:(fmw_cs_side) ltac:(fmw_notin)).
