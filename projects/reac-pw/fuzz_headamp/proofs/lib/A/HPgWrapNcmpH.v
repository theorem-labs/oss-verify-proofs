(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_ubjson_encoder/lib/S8/AsanAcct.v, with its module paths and module names changed; 403 of its 523 lines of code are new or changed and 1138 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FMbz_clean.v, with its module paths and module names changed; 344 of its 386 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/A/HPgWrapNcmp.v's hd_strncmp_core (itself reac-pw/fuzz_pin's
   lib/A/PPgWrapNcmp.v pin_strncmp_core at 90722657971) re-run with the caller's frame hole of lib/A/HPgHole.v
   (ecall_preH in, the hole post out), as lib/A/Rt/FMrt_lift.v rt_post_roU_win re-runs rt_post_ro_win with
   lib/A/Rt/FMupoison.v ARU_frame: hd_rt_post_roH_win is rt_post_roU_win with HPgHole.ARH_frame in place of
   ARU_frame; the walk's premises that AR gives (the stack window, the runtime cells, the read-only views) are read
   off AR of the unpoisoned memory and carried to the memory itself, which agrees with it off the hole; the rest
   is pin's proof. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan f3e0669d2819; twin b5f352154c54): lib/A/HPgHole.v
   `hd_astrncmp_hole tfibsegs B 0x41ba4` for every symbol record B with TfibSyms B, the strncmp wrapper's contract in
   the form the parse calls it (reac_headamp_prop_parse_result 0x849c8, inside its poisoned real-stack frame: the
   frame's eight shadow bytes read PAT_KEY there). Proves no new function: the body walk is the one
   lib/A/HPgWrapNcmp.v reads (lib/A/Bz/A/I_strncmp.v istrncmp_spec behind the trampoline 0x41ba4 -> 0x4268c).

   WHY THE PLAIN TOP DOES NOT GIVE IT. hd_astrncmp asks ecall_pre of the memory itself; inside the hole only the
   memory with the hole's shadow bytes read as 0 (unpoison (hU fr pat) mem) has AR. The wrapper never reads those
   bytes as data that matter: its range check reads the shadow of the two strings (their bytes 0, as the contract
   states over the memory itself) and the 8-byte shadow words that hold them, value free (Bz/A/I_qck.v qc_words); the
   hole lies in the shadow band below the stack range (HPgHole.v hole_band), so it is neither in the callee's stack
   window [sp - 2 * ESTACK, sp), nor among the runtime cells (all below 0x1000000), nor in a read-only segment.

   HOW. Let U = hU fr pat and memU = unpoison U mem.
   - stack window: stk_of_pre at memU (whose ecall_pre_k is ecall_preH's ecall_pre plus the window's presence, which
     is the same at mem and memU off the hole) gives the walk's stk; Bz/A/D_kit.v stk_agree_nw carries it to mem.
   - runtime cells: m2s_of_ARm_clean / icells_sc_of_ARm_clean at memU; Bz/A/I_strncmpw.v m2s_cells_agree /
     icells_sc_agree carry them to the cleaned mem (the two cleaned stores agree below 0x1000000, and every byte the
     cleaned memU holds the cleaned mem holds too: off the hole they are equal, and a hole byte is a visible byte of
     mem, below 2^47 and outside every segment).
   - read-only views: the contract's read-only premise is rom_viewN at mem; rom_viewO comes from AR at memU
     (StrncmpView.v fm_rom_viewO_of_AR) and is the same at mem, every image byte lying below kLowMemEnd
     (HPgSiteA.v headamp_A_segs_low) and the hole above it.
   - the two strings' range checks: Rt/FMbz_str.v chk_ok_of_view over mem from the contract's own range_addressable /
     shadow_hull_vis over mem (chk_ok_of_preH below: FMrt_pre.v chk_ok_of_pre without its unused AR premise).
   - post: hd_rt_post_roH_win: the walk wrote nothing outside [sp - 2256, sp), so HPgHole.ARH_frame keeps ARH (the
     hole's bytes are outside the window, so hpat holds after the call too).
   The top lemma: hd_astrncmp_hole_A (every TfibSyms record) and hd_astrncmp_hole_TfibB (lib/A/AD2l.v's record). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMrt_lift FMrt_pre FMbz_clean.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrncmpFmh.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require StrncmpDef StrncmpView FMstrncmp FMbz_str WrapRo HeadRoPins.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgWrap HPgSiteA HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgWrapNcmp.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.IcptSpec.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_strncmpw.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_strncmp.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_tramp.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.D_kit.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib.Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SCS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.IcptSpec.
Module SCP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_strncmpw3.
Module SCW := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_strncmp.
Module SCC := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_strncmpw.
Module TRP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.R_isPoisoned.
Module DK := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.D_kit.
Module BFr := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.Lib.Frame.
Module SF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec.StrFun.
Module FMS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt.FMstrncmp.
Module SV := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt.StrncmpView.
Module HH := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.HPgHole.

(* ---- the range check over the memory itself: FMrt_pre.v chk_ok_of_pre, whose AR premise its proof does not use ---- *)
Lemma chk_ok_of_preH : forall (W : world tfibsegs) mem p n,
  0 <= p -> 0 <= n < 2 ^ 32 -> amem_range p (n + 7) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n) ->
  BQ.chk_ok (mrestrict (w_H W) mem) p n.
Proof.
  intros W mem p n Hp Hn Ham HRA HV.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - split; [intros i Hi; lia|]. split; [intros Hq; lia | intros Hq; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
    apply (FMbz_str.chk_ok_of_view (w_H W) mem p n); [exact Hp | lia | lia | lia | | exact HRA |
      apply FMbz_str.hull_of_shadow_hull_vis; exact (HV ltac:(lia))].
    unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- where the hole lies ---- *)
Lemma hole_s : forall ly fr pat s, layout_ok ly -> HH.hstack_ok ly fr pat ->
  in_ush (HH.hU fr pat) s = true ->
  kLowMemEnd <= s /\ s < ly_stk_lo ly /\ 0 <= s < 2 ^ 64 /\ s < kHighShadowEnd.
Proof.
  intros ly fr pat s LO OK H. apply HH.in_hU in H.
  pose proof (HH.hole_band ly fr pat LO OK s H) as (B1 & B2 & B3 & _ & B5). lia.
Qed.

Lemma not_hole_hi : forall ly fr pat s, layout_ok ly -> HH.hstack_ok ly fr pat -> ly_stk_lo ly <= s ->
  in_ush (HH.hU fr pat) s = false.
Proof.
  intros ly fr pat s LO OK Hs. destruct (in_ush (HH.hU fr pat) s) eqn:E; [|reflexivity].
  pose proof (hole_s ly fr pat s LO OK E). lia.
Qed.

Lemma not_hole_lo : forall ly fr pat s, layout_ok ly -> HH.hstack_ok ly fr pat -> s < kLowMemEnd ->
  in_ush (HH.hU fr pat) s = false.
Proof.
  intros ly fr pat s LO OK Hs. destruct (in_ush (HH.hU fr pat) s) eqn:E; [|reflexivity].
  pose proof (hole_s ly fr pat s LO OK E). lia.
Qed.

(* image A's segments lie below kLowMemEnd *)
Lemma img_low : forall a, in_img tfibsegs a -> a < kLowMemEnd.
Proof. intros a Ha. exact (proj2 (HPgSiteA.headamp_A_segs_low a Ha)). Qed.

(* a hole byte is a visible byte of the memory, kept by the cleaning *)
Lemma hole_clean_some : forall (W : world tfibsegs) mem ly fr pat (a : word),
  layout_ok ly -> HH.hstack_ok ly fr pat -> HH.hpat tfibsegs W mem fr pat ->
  in_ush (HH.hU fr pat) (bv_unsigned a) = true -> clean (mrestrict (w_H W) mem) a <> None.
Proof.
  intros W mem ly fr pat a LO OK HP Ha.
  pose proof (hole_s ly fr pat _ LO OK Ha) as (L1 & L2 & L3 & L4).
  pose proof Ha as Ha'. apply HH.in_hU in Ha'.
  pose proof (HP (bv_unsigned a - shadow_addr fr) ltac:(lia)) as E.
  replace (shadow_addr fr + (bv_unsigned a - shadow_addr fr)) with (bv_unsigned a) in E by lia.
  assert (Hn : ~ in_img tfibsegs (bv_unsigned a)) by (intros Hi; pose proof (img_low _ Hi); lia).
  assert (HD : Dc a = false).
  { unfold Dc. apply orb_false_intro.
    - unfold BM.ro_addr. destruct (find_segment BzI.asegs (bv_unsigned a) 1) as [sg|] eqn:Ef; [|reflexivity].
      exfalso. pose proof (YK04.find_segment_some_spec BzI.asegs _ _ sg Ef) as (Hin & Hlo & Hhi).
      apply Hn. exists sg. split; [exact Hin | lia].
    - apply Z.leb_gt. unfold BM.UTOP. unfold kHighShadowEnd in L4. lia. }
  unfold aview, mbyte, mrestrict in E. rewrite Z_to_bv_bv_unsigned in E.
  unfold clean, mrestrict. rewrite HD.
  destruct (w_H W a) eqn:EH.
  - rewrite <- (Z_to_bv_bv_unsigned _ a) in E. rewrite (YCbq.seg_rom_none tfibsegs (bv_unsigned a) L3 Hn) in E.
    discriminate E.
  - destruct (mem a) as [b|] eqn:EM; [discriminate|].
    rewrite <- (Z_to_bv_bv_unsigned _ a) in E. rewrite (YCbq.seg_rom_none tfibsegs (bv_unsigned a) L3 Hn) in E.
    discriminate E.
Qed.

Section s.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis ROP : SV.ro_owned_pinned tfibsegs B.

(* ---- the post in hole form, with the answer R ---- *)
Definition hd_rt_post_roH (STK : Z) ly S fr pat (W : world tfibsegs) regs mem md (R : Z -> Prop)
  : world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    AR tfibsegs B ly S W (unpoison (HH.hU fr pat) mem') md' /\ HH.hpat tfibsegs W mem' fr pat /\
    aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) ->
       aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* FMrt_lift.v rt_post_roU_win, with HPgHole.v ARH_frame in place of FMupoison.v ARU_frame *)
Theorem hd_rt_post_roH_win : forall (STK K : Z) ly S fr pat (W : world tfibsegs) regs mem md (R : Z -> Prop)
  ms0 ms' model' (v : Z),
  ecall_pre tfibsegs B ly S W regs (unpoison (HH.hU fr pat) mem) md -> HH.hstack_ok ly fr pat ->
  HH.hpat tfibsegs W mem fr pat -> ly_stk_lo ly + STK <= spZ regs ->
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) -> 0 <= K <= STK ->
  R6.ms_eqv ms0 ms' -> same_but_materialized md model' ->
  ms_pc_val ms0 = LMS.ret_pc (getr regs 1) -> ms_fregs ms0 = fp_regs -> ms_svc_pending ms0 = None ->
  ms_resv ms0 = None -> ms_fcsr ms0 = fp_csr -> ms_rom ms0 = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr (ms_regs ms0) 10 = w64 v -> 0 <= v < 2 ^ 64 -> R v ->
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) -> ms_mem ms0 x = mrestrict (w_H W) mem x) ->
  (forall a, spZ regs - K <= a < spZ regs -> ms_mem ms0 (Z_to_bv 64 a) <> None) ->
  hd_rt_post_roH STK ly S fr pat W regs mem md R W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros STK K ly S fr pat W regs mem md R ms0 ms' model' v HEP HOK HPAT Hslo HpresS HK Heqv Hsbm P0 F0 S0 R0 C0
    RO0 KEEP A10 Hv HR MOUT MIN.
  pose proof HEP as (HAR & Hra & _ & _ & Hshi & _ & _ & _).
  pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
  pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _). rewrite Emem in MOUT, MIN.
  destruct (win_mem (w_H W) mem (ms_mem ms') (spZ regs - K) (spZ regs) MOUT MIN
              ltac:(intros a Ha; apply HpresS; lia)) as (AV & VIS & HB & PRS).
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
  assert (HARH : HH.ARH tfibsegs B ly S fr pat W mem md) by (split; [exact HAR | split; [exact HOK | exact HPAT]]).
  assert (HARH' : HH.ARH tfibsegs B ly S fr pat W (munrestrict (w_H W) mem (ms_mem ms')) model').
  { apply (HH.ARH_frame tfibsegs B ly S fr pat W mem md _ model' HARH); [| exact VIS | exact E1 | exact E2 | exact E3 | |].
    - intros a Hr Hown _. apply AV; [exact Hr|]. intros Hw.
      exact (al_stack _ _ LAWS ly S W (unpoison (HH.hU fr pat) mem) md a HAR ltac:(lia) Hown).
    - intros a _ Hh. exact (HB a Hh).
    - intros i Hi. pose proof (HPAT i Hi) as Ei.
      assert (Hs : in_ush (HH.hU fr pat) (shadow_addr fr + i) = true) by (apply HH.in_hU; lia).
      pose proof (hole_s ly fr pat _ LO HOK Hs) as (_ & L2 & L3 & _).
      rewrite (AV (shadow_addr fr + i) L3 ltac:(lia)). exact Ei. }
  destruct HARH' as (HAR' & _ & HPAT').
  unfold hd_rt_post_roH. split; [reflexivity|].
  exists (ms_regs ms'), (munrestrict (w_H W) mem (ms_mem ms')), model', v.
  split; [unfold cfg_at; f_equal; exact (unrestrict_ret regs (w_H W) mem ms0 ms' Heqv Hra P0 F0 S0 R0 C0 RO0)|].
  split; [exact HAR'|]. split; [exact HPAT'|].
  split; [intros r Hr; rewrite (ms_eqv_getr ms0 ms' _ Heqv); exact (KEEP r Hr)|].
  split; [exact Hsbm|].
  split; [rewrite (ms_eqv_getr ms0 ms' _ Heqv); exact A10|].
  split; [exact Hv|]. split; [exact HR|].
  split; [intros a Ha Hn; apply AV; [exact Ha | lia] | exact PRS].
Qed.

(* FMbz_clean.v rt_post_ro_win_clean for the hole *)
Theorem hd_rt_post_roH_win_clean : forall (STK K : Z) ly S fr pat (W : world tfibsegs) regs mem md (R : Z -> Prop)
  msc ms' model' (v : Z),
  ecall_pre tfibsegs B ly S W regs (unpoison (HH.hU fr pat) mem) md -> HH.hstack_ok ly fr pat ->
  HH.hpat tfibsegs W mem fr pat -> ly_stk_lo ly + STK <= spZ regs ->
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) -> 0 <= K <= STK ->
  hclean Dc msc ->
  R6.ms_eqv (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
  ms_pc_val msc = LMS.ret_pc (getr regs 1) -> ms_fregs msc = fp_regs -> ms_svc_pending msc = None ->
  ms_resv msc = None -> ms_fcsr msc = fp_csr -> ms_rom msc = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs msc) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr (ms_regs msc) 10 = w64 v -> 0 <= v < 2 ^ 64 -> R v ->
  (forall x : word, ~ (spZ regs - K <= bv_unsigned x < spZ regs) ->
     ms_mem msc x = clean (mrestrict (w_H W) mem) x) ->
  (forall a, spZ regs - K <= a < spZ regs -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  hd_rt_post_roH STK ly S fr pat W regs mem md R W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros STK K ly S fr pat W regs mem md R msc ms' model' v HEP HOK HPAT Hslo HpresS HK Hcl Heqv Hsbm
    P0 F0 S0 R0 C0 RO0 KEEP A10 Hv HR MOUT MIN.
  destruct (clean_window (mrestrict (w_H W) mem) msc (spZ regs - K) (spZ regs) Hcl MOUT MIN) as (MO & MN).
  exact (hd_rt_post_roH_win STK K ly S fr pat W regs mem md R (unrestrict Dc (mrestrict (w_H W) mem) msc) ms' model' v
           HEP HOK HPAT Hslo HpresS HK Heqv Hsbm P0 F0 S0 R0 C0 RO0 KEEP A10 Hv HR MO MN).
Qed.

(* ---- the walk inside the hole ---- *)
Lemma hd_strncmp_core_hole : forall ly S W regs mem md x y n (ls rs : list byte) (d : Z) fr pat,
  HH.ecall_preH tfibsegs B (2 * ESTACK) ly S fr pat W regs mem md ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  HPgWrap.awrap_str tfibsegs W mem regs x ls -> HPgWrap.awrap_str tfibsegs W mem regs y rs ->
  amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
  SF.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
  WrapRo.aro_unowned tfibsegs B (aview tfibsegs (w_H W) mem) ->
  SRr tfibsegs W (cfg_at tfibsegs StrncmpDef.STRNCMP_ENTRY regs mem md)
    (hd_rt_post_roH STK_RT_STR ly S fr pat W regs mem md (fun v => v = 0 <-> d = 0)).
Proof.
  intros ly S W regs mem md x y n ls rs d fr pat HEPH G10 G11 G12 Hn S1 S2 AM1 AM2 HMOD HRO.
  destruct HEPH as (HEPU & HOK & HPAT & HSLO & HPRS).
  set (U := HH.hU fr pat) in *.
  set (memU := unpoison U mem) in *.
  pose proof HEPU as (HARU & _).
  pose proof (am_layout B ly S _ (proj1 HARU)) as LO.
  pose proof (lo_top ly LO) as (_ & _ & _ & KHI & _ & _ & KLO).
  (* memU and mem agree off the hole *)
  assert (AGU : forall w : word, in_ush U (bv_unsigned w) = false -> memU w = mem w).
  { intros w Hw. unfold memU. apply unpoison_out. exact Hw. }
  assert (AGview : forall a, 0 <= a < 2 ^ 64 -> in_ush U a = false ->
            aview tfibsegs (w_H W) memU a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hu. unfold memU. apply aview_unpoison_out. rewrite (HH.hw64 a Ha). exact Hu. }
  (* the window's presence at memU *)
  assert (HPRSU : forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) memU a).
  { intros a Ha. destruct (HPRS a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b.
    rewrite AGU; [exact Hb|].
    assert (Hsp : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
    rewrite (HH.hw64 a ltac:(unfold kHighMemBeg in KLO; lia)).
    apply (not_hole_hi ly fr pat a LO HOK). lia. }
  assert (HPRE : ecall_pre_k tfibsegs B STK_RT_STR ly S W regs memU md).
  { split; [exact HEPU|]. split.
    - exact (lo_stk_ceil _ LO).
    - unfold StrncmpDef.FM_STK_RT_STR. split; [exact HSLO | exact HPRSU]. }
  (* the read-only views, at mem and at memU *)
  assert (ROAG : forall a, in_rom tfibsegs a -> aview tfibsegs (w_H W) memU a = aview tfibsegs (w_H W) mem a).
  { intros a Ha.
    assert (Hi : in_img tfibsegs a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
    pose proof (HPgSiteA.headamp_A_segs_low a Hi) as Hl.
    apply AGview; [unfold kLowMemEnd in Hl; lia|]. apply (not_hole_lo ly fr pat a LO HOK). lia. }
  assert (HROM : rom_viewN tfibsegs B W mem) by exact HRO.
  assert (HROMU : rom_viewN tfibsegs B W memU).
  { intros a Ha Ho He. rewrite (ROAG a Ha). exact (HROM a Ha Ho He). }
  assert (HROMOU : rom_viewO tfibsegs B W memU)
    by exact (SV.fm_rom_viewO_of_AR tfibsegs B ly S W memU md ROP HARU).
  assert (HROMO : rom_viewO tfibsegs B W mem).
  { intros a Ha Ho. rewrite <- (ROAG a Ha). exact (HROMOU a Ha Ho). }
  (* the strings, over mem, as in hd_strncmp_core *)
  destruct S1 as (Hx0 & HxN & Hx32 & Hx63 & GA1 & SRC1 & WIN1 & AMR1 & RA1 & HV1 & TL1).
  destruct S2 as (Hy0 & HyN & Hy32 & Hy63 & GA2 & SRC2 & WIN2 & AMR2 & RA2 & HV2 & TL2).
  set (l1 := u8s ls) in *. set (l2 := u8s rs) in *.
  assert (LL1 : length l1 = length ls) by (unfold l1, u8s; apply length_map).
  assert (LL2 : length l2 = length rs) by (unfold l2, u8s; apply length_map).
  assert (CS1 : cstr tfibsegs W mem x l1) by (split; [exact GA1 | exact (u8s_ok ls HxN)]).
  assert (CS2 : cstr tfibsegs W mem y l2) by (split; [exact GA2 | exact (u8s_ok rs HyN)]).
  pose proof alloc_ceiling_lt as HCL.
  assert (Hxu : x + Z.of_nat (length ls) + 8 <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AM1; lia).
  assert (Hyu : y + Z.of_nat (length rs) + 8 <= 2 ^ 47 - 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AM2; lia).
  destruct (bytes_of_cstr W mem x l1 CS1 ltac:(lia) ltac:(rewrite LL1; lia)) as (BY1m & _ & F1).
  destruct (bytes_of_cstr W mem y l2 CS2 ltac:(lia) ltac:(rewrite LL2; lia)) as (BY2m & _ & F2).
  destruct (FMS.strncmp_strs n l1 l2 ltac:(lia) F1 F2) as (OK & SZ1 & SZ2 & RES).
  set (b1 := map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) in *.
  set (b2 := map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) in *.
  set (sz := SCS.strncmp_sz n b1 b2) in *.
  set (r := SCS.strncmp_res n b1 b2) in *.
  assert (CK1m : BQ.chk_ok (mrestrict (w_H W) mem) x sz).
  { apply (chk_ok_of_preH W mem x sz); [lia | rewrite LL1 in SZ1; lia | |
      apply (ra_prefix _ _ _ _ RA1); rewrite LL1 in SZ1; lia |
      intros Hs0; apply (hull_prefix _ _ _ _ HV1); rewrite LL1 in SZ1; lia].
    apply (amem_range_mono _ _ _ AM1). rewrite LL1 in SZ1. lia. }
  assert (CK2m : BQ.chk_ok (mrestrict (w_H W) mem) y sz).
  { apply (chk_ok_of_preH W mem y sz); [lia | rewrite LL2 in SZ2; lia | |
      apply (ra_prefix _ _ _ _ RA2); rewrite LL2 in SZ2; lia |
      intros Hs0; apply (hull_prefix _ _ _ _ HV2); rewrite LL2 in SZ2; lia].
    apply (amem_range_mono _ _ _ AM2). rewrite LL2 in SZ2. lia. }
  (* the stack window: at memU, carried to mem *)
  destruct (stk_of_pre B ly S W regs memU md STK_RT_STR HPRE ltac:(unfold StrncmpDef.FM_STK_RT_STR, ESTACK; lia))
    as (ST0U & HC0 & HCs & Hsp47).
  assert (ST0 : BF.stk BI.asegs (mrestrict (w_H W) mem) (spZ regs - STK_RT_STR) (spZ regs)).
  { apply (DK.stk_agree_nw BI.asegs (mrestrict (w_H W) memU) (mrestrict (w_H W) mem) _ _ ST0U).
    intros a Ha. unfold mrestrict. destruct (w_H W a); [reflexivity|]. symmetry. apply AGU.
    apply (not_hole_hi ly fr pat _ LO HOK). unfold STK_RT_STR, StrncmpDef.FM_STK_RT_STR in *. lia. }
  pose proof (rom_eq_of_views B W mem TB HROM HROMO) as RE.
  pose proof (rom_eq_of_views B W memU TB HROMU HROMOU) as REU.
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - STK_RT_STR) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - STK_RT_STR) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  (* the runtime cells: at memU, carried to mem *)
  assert (AGlow : DK.agree_on (fun z => 0 <= z < 0x1000000)
            (clean (mrestrict (w_H W) memU)) (clean (mrestrict (w_H W) mem))).
  { intros a Ha. unfold clean, mrestrict. destruct (Dc a); [reflexivity|]. destruct (w_H W a); [reflexivity|].
    symmetry. apply AGU. apply (not_hole_lo ly fr pat _ LO HOK). unfold kLowMemEnd. lia. }
  assert (WMc : BFr.wmono BI.asegs (clean (mrestrict (w_H W) memU)) (clean (mrestrict (w_H W) mem))).
  { intros a Hw. unfold wview in Hw |- *.
    destruct (in_ush U (bv_unsigned a)) eqn:Ei.
    - destruct (clean (mrestrict (w_H W) mem) a) eqn:E; [discriminate|].
      exfalso. exact (hole_clean_some W mem ly fr pat a LO HOK HPAT Ei E).
    - assert (Eq : clean (mrestrict (w_H W) mem) a = clean (mrestrict (w_H W) memU) a).
      { unfold clean, mrestrict. destruct (Dc a); [reflexivity|]. destruct (w_H W a); [reflexivity|].
        symmetry. apply AGU. exact Ei. }
      rewrite Eq. exact Hw. }
  pose proof (SCC.m2s_cells_agree _ _ (m2s_of_ARm_clean B TB ly S (w_H W) memU REU (proj1 HARU)) AGlow WMc) as M2S.
  pose proof (SCC.icells_sc_agree _ _ (icells_sc_of_ARm_clean B TB ly S (w_H W) memU REU (proj1 HARU)) AGlow WMc)
    as IC.
  assert (BY1 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x b1).
  { apply (bytes_at_clean _ x _ RE);
      [unfold b1; rewrite length_app, length_map; cbn [length]; rewrite LL1; unfold BM.UTOP; lia | exact BY1m]. }
  assert (BY2 : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) y b2).
  { apply (bytes_at_clean _ y _ RE);
      [unfold b2; rewrite length_app, length_map; cbn [length]; rewrite LL2; unfold BM.UTOP; lia | exact BY2m]. }
  assert (CK1 : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x sz).
  { apply (chk_ok_clean _ x _ RE); [lia | rewrite LL1 in SZ1; lia | exact CK1m]. }
  assert (CK2 : BQ.chk_ok (clean (mrestrict (w_H W) mem)) y sz).
  { apply (chk_ok_clean _ y _ RE); [lia | rewrite LL2 in SZ2; lia | exact CK2m]. }
  assert (SEP1 : x + sz <= spZ regs - 2256 \/ spZ regs <= x).
  { apply (sep_of_win x (Z.of_nat (length ls)) (spZ regs) (2 * ESTACK) sz); [lia | rewrite LL1 in SZ1; lia |
      unfold ESTACK; lia | exact WIN1]. }
  assert (SEP2 : y + sz <= spZ regs - 2256 \/ spZ regs <= y).
  { apply (sep_of_win y (Z.of_nat (length rs)) (spZ regs) (2 * ESTACK) sz); [lia | rewrite LL2 in SZ2; lia |
      unfold ESTACK; lia | exact WIN2]. }
  assert (HDR : r = 0 <-> d = 0).
  { rewrite RES. symmetry. exact (model_zero ls rs n d ltac:(lia) HxN HyN HMOD). }
  set (lo := spZ regs - STK_RT_STR) in *.
  set (m := mrestrict (w_H W) mem) in *.
  eapply (bz_run_clean B TB W StrncmpDef.STRNCMP_ENTRY regs mem md _ _ HROM HROMO).
  - apply bz_canon. apply TRP.tramp_strncmp.
    eapply (SCW.istrncmp_spec RIP.rip_proof) with (p1 := x) (p2 := y) (n := n) (b1 := b1) (b2 := b2) (lo := lo).
    + exact G10.
    + exact G11.
    + exact G12.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo, StrncmpDef.FM_STK_RT_STR, ESTACK. lia.
    + unfold OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz.A.R_m2s.kHighShadowEnd. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + lia.
    + exact BY1.
    + exact BY2.
    + exact OK.
    + lia.
    + lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact SEP1.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact SEP2.
    + exact CK1.
    + exact CK2.
    + exact M2S.
    + exact IC.
    + exact MI.
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    unfold SCP.istrncmp_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST').
    destruct (bz_window (clean m) m' (spZ regs) 2256 lo MU ST') as (MO & MN).
    { unfold lo, StrncmpDef.FM_STK_RT_STR, ESTACK. lia. }
    { unfold TFIB_IMG_END. lia. }
    eapply (hd_rt_post_roH_win_clean STK_RT_STR 2256 ly S fr pat W regs mem md _ _ ms' model' (r mod 2 ^ 64)
              HEPU HOK HPAT HSLO HPRS).
    + unfold StrncmpDef.FM_STK_RT_STR, ESTACK. lia.
    + exact Hcl.
    + exact Heqv.
    + exact Hsbm.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + transitivity (Z_to_bv 64 r); [reflexivity|]. unfold w64. rewrite Z_to_bv64_mod. reflexivity.
    + apply Z.mod_pos_bound. lia.
    + rewrite <- HDR. pose proof (FMS.strncmp_res_range n b1 b2) as Hr. fold r in Hr.
      Z.div_mod_to_equations. lia.
    + exact MO.
    + exact MN.
Qed.

End s.
End h.

(* ---- the top lemmas: HPgHole.v's hd_astrncmp_hole at image A's trampoline ---- *)
Theorem hd_astrncmp_hole_A : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms),
  TfibSyms B -> HH.hd_astrncmp_hole tfibsegs B 0x41ba4.
Proof.
  intros fx rc B TB. unfold HH.hd_astrncmp_hole.
  intros ly S W regs mem md x y n ls rs d fr pat HEPH G10 G11 G12 Hn S1 S2 AM1 AM2 HMOD HRO.
  rewrite <- PC_strncmp_hd.
  eapply SRr_mono.
  - exact (hd_strncmp_core_hole B (YG0q.AR_laws_ok tfibsegs B) TB (HeadRoPins.hd_ro_owned_pinned B TB)
             ly S W regs mem md x y n ls rs d fr pat HEPH G10 G11 G12 Hn S1 S2 AM1 AM2 HMOD HRO).
  - intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & HP' & Hpres & Hsbm & G10' & Hv & HR & Hwin & Hp).
    split; [reflexivity|]. exists regs', mem', md'.
    assert (HV0 : w64 v = w64 0 <-> d = 0).
    { rewrite <- HR. split; intros E; [|subst v; reflexivity].
      apply (f_equal bv_unsigned) in E. unfold w64 in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
      change (bv_modulus 64) with (2 ^ 64) in E. rewrite (Z.mod_small v) in E by lia. rewrite Z.mod_0_l in E by lia.
      exact E. }
    split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hpres|]. split; [exact Hsbm|].
    split; [exists (w64 v); split; [exact G10' | exact HV0]|].
    split; [exact Hwin | exact Hp].
Qed.

(* image A's own symbol record (lib/A/AD2l.v) *)
Theorem hd_astrncmp_hole_TfibB : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  HH.hd_astrncmp_hole tfibsegs AD2l.TfibB 0x41ba4.
Proof. intros fx rc. exact (hd_astrncmp_hole_A AD2l.TfibB AD2l.TfibB_syms). Qed.

Print Assumptions hd_astrncmp_hole_A.
Print Assumptions hd_astrncmp_hole_TfibB.
