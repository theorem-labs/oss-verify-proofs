(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module names changed; 310 of its 359 lines of code are new or changed and 477 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4: parse_string's DECODE stretch (part C of WalkS4's split, 08:2xZ), the theorem
   ps_seg_dec of S4_PsBase.v. The loop at PS_DEC (offset 328) is walked by the symbolic engine from the cut ps_at_dec
   (dec_entry) through one turn: the success tail (offset 1352: ps_seg_retok), the free cut (offset 1276:
   ps_seg_free, the free path's stretch), the plain byte and the eight one-byte escapes back to PS_DEC (the induction's
   turn: ps_dec_after), and the \u case, which is split off before the run (ps_seg_u, the \u stretch: its leaves in
   this run, the hex loop at offset 452 and the short \u refusal, are refuted by the split). The induction measure is
   text + len - r.
   HYPOTHESES (Section): the slice's cut statements ps_seg_retok (S4_PsBase.v), ps_seg_free and ps_seg_u
   (S4_PsDecKit.v; WalkS4's split, proved by the free and \u stretches); LAWS / PST_ok (S4_PsBase.v's own Section
   hypotheses, same text); HW (the kit's prh_head_wide, discharged at the preset instance by a Theorem Labs lane's preset_head_wide).
   FILE SET: as the kit's cut 7cdbb61b5fa0 carries it (WalkS4's base of record at the merge was
   a working branch 844c6152eb9 on the kit walkkit preview 0687b776b39, engine / YCbqG 63997a07aa6).
   THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z; base 44a91d58bb5, S4_PsBase.v
   a59ce5bfcbe3): Section c proves ps_seg_dec_holdsP : ps_seg_decP .. P over an ABSTRACT invariant P with its laws PLAW
   (srr_inv_laws segs P; the stretch makes no call, so no srr_inv_call), from the P-form cut statements HRETOK /
   HFREEC / HU. Every run goes through YSRrMemnorm's runner twin (paj_run_x_inv / paj_run_to_x_inv at P, PLAW;
   now YC1fPx.v 7814b594066f) from the carry's P mem (HMN) and re-introduces HMN at the run's end memory; a branch
   (paj_branch) keeps the state, so HMN stands; each leaf hands the last run's HMN to its keep lemma (retok_close /
   free_close / dec_close1), which puts it in the cut's ps_carryP. Section c0: the stable ps_seg_dec_holds, statement
   byte-identical, is the P := (fun _ => True) instance (S4_PsBase.v ps_seg_dec_of_True / ps_seg_retok_of_True,
   S4_PsDecKit.v ps_seg_free_of_True / ps_seg_u_of_True). Requires YAkMemnorm and YSRrMemnorm only (no LiaTwx2).
   Built at the cut's image A' listing (Listing_prog.v 7ed1529926bd, PAImg_prog.v 505a51ff7d08).
   Numerals: 328 / 1276 / 1352 / 452 (DERIVED offsets inside parse_string), 24 / 8 (LENGTH of the in struct and
   in->end), 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (DERIVED bounds), the byte values 34 92 117 and the escape letters (WORD); no
   ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YGcfNames YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ S4_PsBase S4_PsDecModel S4_PsDecKit S4_PsDecWalk.
(* the re-hiding move's SRr' / SRrG / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the invariant every cut carries and every run keeps (S4_PsBase.v Section gp), abstract here *)
Variable P : (word -> option byte) -> Prop.
Variable CTX : list (list Z).
Variable CW : list (list Z).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HW : prh_head_wide.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis HRETOK : ps_seg_retokP B ARx SK P CTX CW.
Hypothesis HFREEC : ps_seg_freeP B ARx SK P CTX CW.
Hypothesis HU : ps_seg_uP B ARx SK P CTX CW.

(* ONE TURN of the loop from PS_DEC when the text at r is not a backslash followed by u. Its runs are at wle, into
   S4_PsBase's hand-off form ps_finP: the free cut and the back edge may cross the bad escape's fuzz_free (ps_finP_hand),
   the success tail ends at wle (ps_finP_of_postP) *)
Lemma dec_turn : forall D ly S Hp W regs mem md out w r Q,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  ~ (nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0 = 92 /\ nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0 = 117) ->
  ps_dec_afterP B ARx SK P CW D r ->
  SRr segs W (cfg_at segs (ps_pc PS_DEC) regs mem md) (ps_finP B ARx SK P CW D).
Proof.
  intros D ly S Hp W regs mem md out w r Q HPRE HDEC Hnu AFT.
  destruct (dec_entry B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC) as [HS SHOK].
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  assert (HRR : pi_text D <= r < pi_text D + Z.of_nat (length (pi_tb D))) by lia.
  pose proof HDEC as ((k & HJ & _ & _ & HSRC & _ & HMN) & HAL & (S24 & S23 & S25) & (G3 & G4) & HCST & HIN & HROD & HSC & R2 & R18 & R19 & R20 & R11 & R8 & R9 & HREL).
  pose proof HPRE as ((HPX & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq1 & Hq2 & _).
  pose proof HPX as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HWIN as (He0 & He16 & Hetop & Hepres).
  pose proof (ajx_ly HJ) as Hly.
  (* the in struct lies on the machine stack: its shadow reads 0 at every ARx state (alx_zshadow_byte) *)
  assert (Hqstk : ly_stk_lo ly <= pi_q D /\ pi_q D + 24 <= ly_stk_hi ly).
  { destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _). rewrite Elo, Ehi. split; lia. }
  pose proof HSRC as (_ & _ & _ & _ & HTRA & _).
  pose proof asan_consts as (C1 & _). pose proof HW as Hh8. unfold prh_head_wide in Hh8.
  remember (EK regs (pi_tb D) (pi_text D) r) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EK; apply Eimg_env).
  assert (E24 : ew E 24 = w64 SHADOW_OFF) by (subst E; rewrite (EK_reg regs _ _ r 24 24%bv eq_refl); exact S24).
  assert (E20 : ew E 20 = w64 r) by (subst E; rewrite (EK_reg regs _ _ r 20 20%bv eq_refl); exact R20).
  assert (E19 : ew E 19 = w64 w) by (subst E; rewrite (EK_reg regs _ _ r 19 19%bv eq_refl); exact R19).
  assert (E9 : ew E 9 = w64 (pi_q D + 8)) by (subst E; rewrite (EK_reg regs _ _ r 9 9%bv eq_refl); exact R9).
  assert (E11 : ew E 11 = w64 (pi_text D + pi_len D)) by (subst E; rewrite (EK_reg regs _ _ r 11 11%bv eq_refl); exact R11).
  assert (E2 : ew E 2 = w64 (PS_SP D)) by (subst E; rewrite (EK_reg regs _ _ r 2 2%bv eq_refl); exact R2).
  assert (E23 : ew E 23 = w64 (SHADOW_OFF + pi_q D / 8)) by (subst E; rewrite (EK_reg regs _ _ r 23 23%bv eq_refl); exact S23).
  assert (E18 : ew E 18 = w64 out) by (subst E; rewrite (EK_reg regs _ _ r 18 18%bv eq_refl); exact R18).
  assert (E8 : ew E 8 = w64 (pi_q D)) by (subst E; rewrite (EK_reg regs _ _ r 8 8%bv eq_refl); exact R8).
  assert (E3 : ew E 3 = getr (pi_regs D) 3) by (subst E; rewrite (EK_reg regs _ _ r 3 3%bv eq_refl); exact G3).
  assert (E4 : ew E 4 = getr (pi_regs D) 4) by (subst E; rewrite (EK_reg regs _ _ r 4 4%bv eq_refl); exact G4).
  pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HG8 & _).
  assert (EB0 : ew E 32 = Z_to_bv 64 (nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0)).
  { subst E. pose proof (EK_byte regs (pi_tb D) (pi_text D) r 0 ltac:(lia)) as X. cbn [Nat.add Z.of_nat] in X.
    rewrite Z.add_0_r in X. exact X. }
  assert (EB1 : ew E 33 = Z_to_bv 64 (nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0)).
  { subst E. pose proof (EK_byte regs (pi_tb D) (pi_text D) r 1 ltac:(lia)) as X. cbn [Nat.add Z.of_nat] in X. exact X. }
  assert (Hb0r := tx12_byte (pi_tb D) (pi_text D) r 0 ltac:(lia) (garr8_bytes _ _ _ HG8)). change (Z.of_nat 0) with 0 in Hb0r. rewrite Z.add_0_r in Hb0r.
  assert (Hb1r := tx12_byte (pi_tb D) (pi_text D) r 1 ltac:(lia) (garr8_bytes _ _ _ HG8)). change (Z.of_nat 1) with 1 in Hb1r.
  remember (nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0) as b0 eqn:Hb0.
  remember (nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0) as b1 eqn:Hb1.
  clear HE.
  pose (RUN := paj_run_x_inv (SK := SK) (PL := PS_PAListing) (PI := PS_PAImg) B prh_pst ARx LAWS P PLAW).
  pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PS_PAListing) (PI := PS_PAImg) B prh_pst ARx LAWS P PLAW).
  pose (BR := paj_branch (PI := PS_PAImg)).
  unfold cfg_at. replace (w64 (ps_pc PS_DEC)) with (Z_to_bv 64 (BASE + (PSO + PS_DEC))) by (unfold ps_pc, PSO, w64; f_equal; lia).
  pose proof (dec_w_ns B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC) as HNS.
  (* the walk's invariant between runs: the memory differs from the entry's at most at the out byte w, and grows *)
  assert (HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by reflexivity.
  pose proof (mem_grows_refl (mrestrict (w_H W) mem)) as HGc.
  (* the shadow obligations: a text byte (the entry's src_rd range) or in->end (the machine stack) *)
  let ob_tac := idtac;
    lazymatch goal with
    | HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) ?mc x = mrestrict (w_H W) mem x
      |- range_addressable (rd_of _ (mrestrict (w_H W) ?mc)) (U ?E' dBx) (U ?E' (SOff 20 ?i)) ?m =>
      apply (ob_range_w (w_H W) mem mc E' dBx (SOff 20 i) (pi_text D) (Z.of_nat (length (pi_tb D))) (r + i) m w HMc HNS);
      [ lia | lia | exact HTRA
      | unfold dBx; rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E24, Z.add_0_r; unfold w64;
        rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); apply zcanon_id; unfold SHADOW_OFF, M64; lia
      | rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E20; unfold w64; rewrite unsigned_lit_small by lia;
        apply zcanon_id; unfold M64; lia
      | lia | lia ]
    | HJc : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc ?mdc _
      |- range_addressable (rd_of _ (mrestrict (w_H W) ?mc)) (U ?E' dBx) (U ?E' (SOff 9 0)) ?m =>
      apply (ob_stack (w_H W) mc E' dBx (SOff 9 0) (pi_q D + 8) m);
      [ intros a Ha; apply (alx_zshadow_byte segs B ARx LAWS ly S Hp W mc mdc); [exact (ajx_ar HJc) | lia]
      | unfold dBx; rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E24, Z.add_0_r; unfold w64;
        rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); apply zcanon_id; unfold SHADOW_OFF, M64; lia
      | rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E9; unfold w64; rewrite unsigned_lit_small by lia;
        rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia ]
    end in
  (* the write premise: the run writes only the out byte, in the block made since the entry *)
  let wr_tac := idtac;
    lazymatch goal with |- awr_ok ?E' ?rs _ _ _ _ _ _ _ =>
      apply (awr_w E' rs _ _ _ _ _ _ _ w);
      [ vm_compute; reflexivity
      | cbn [ew ewset Nat.eqb]; rewrite E19; unfold w64; apply unsigned_lit_small; lia
      | exact (dec_tmp_w B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC) ]
    end in
  (* after a run: fold its frame and growth into the invariant *)
  let fold_inv := idtac;
    lazymatch goal with
    | HFr : frame_of ?E' ?rs (mrestrict (w_H W) ?m1) (mrestrict (w_H W) ?m2),
      HG : mem_grows (mrestrict (w_H W) ?m1) (mrestrict (w_H W) ?m2),
      HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) ?m1 x = mrestrict (w_H W) mem x,
      HGc : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) ?m1) |- _ =>
      let HM2 := fresh "HMc" in
      assert (HM2 : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) m2 x = mrestrict (w_H W) mem x)
        by (intros x Hx; rewrite (frame_w E' rs _ _ w ltac:(vm_compute; reflexivity)
              ltac:(cbn [ew ewset Nat.eqb]; rewrite E19; unfold w64; apply unsigned_lit_small; lia) HFr x Hx); exact (HMc x Hx));
      let HG2 := fresh "HGc" in pose proof (mem_grows_trans _ _ _ HGc HG) as HG2;
      clear HFr HG HMc HGc;
      try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end
    end in
  (* a branch's fact in Z over the bytes b0 b1, r and text + len *)
  let uval := idtac; rewrite ?U_SOff, ?U_SLit; cbn [ew ewset Nat.eqb]; rewrite ?E20, ?E11, ?EB0, ?EB1, ?E19, ?E9; unfold w64;
    rewrite ?unsigned_lit_small by lia; rewrite ?zcanon_id by (unfold M64; lia); lia in
  let cn := idtac;
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      try (rewrite bt_lt_U in Hc by uval); try (rewrite bt_ge_U in Hc by uval);
      rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
      rewrite ?U_SOff, ?U_SLit in Hc; cbn [ew ewset Nat.eqb] in Hc;
      rewrite ?E20, ?E11, ?EB0, ?EB1, ?E19, ?E9 in Hc; unfold w64 in Hc;
      rewrite ?unsigned_lit_small in Hc by lia;
      rewrite ?(zcanon_id (_ + _)) in Hc by (unfold M64; lia); rewrite ?zcanon_id in Hc by (unfold M64; lia);
      rewrite ?Z.add_0_r in Hc; bnorm Hc;
      let Hn := fresh "Hcond" in rename Hc into Hn
    end in
  let rec sbm := idtac;
    lazymatch goal with
    | |- same_but_materialized ?a ?a => apply same_but_materialized_refl
    | |- same_but_materialized ?a (with_vm_backing _ _ ?X) =>
        apply (same_but_materialized_trans a X); [sbm | apply same_but_materialized_wvb_any]
    end in
  (* a register at a leaf *)
  let regeq := idtac;
    lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict (w_H W) ?ms) |- getr (ms_regs ?ms) ?n = _ =>
      let e := eval vm_compute in (sr_get (ss_regs ss) n) in
      rewrite (st_reg (w_H W) E' ss ms n e HS ltac:(vm_compute; reflexivity));
      first
      [ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset Nat.eqb];
        rewrite ?E2, ?E3, ?E4, ?E8, ?E9, ?E11, ?E18, ?E19, ?E20, ?E23, ?E24; reflexivity
      | cbn [sv_denot]; cbn [ew ewset Nat.eqb];
        rewrite ?E2, ?E3, ?E4, ?E8, ?E9, ?E11, ?E18, ?E19, ?E20, ?E23, ?E24; unfold w64;
        rewrite ?unsigned_lit_small by lia; f_equal; lia
      | apply (sv_shx E' 9 (pi_q D + 8)); [cbn [ew ewset Nat.eqb]; exact E9 | lia | cbn [ew ewset Nat.eqb]; exact E24] ]
    end in
  (* LEAF 1352: the closing quote, the success tail *)
  let leaf_retok := idtac;
    lazymatch goal with
    | HS : st_ok_pi _ _ ?E' ?ss (restrict (w_H W) ?ms), HJc : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?kc,
      HPMc : P (ms_mem ?ms),
      HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) (ms_mem ?ms) x = mrestrict (w_H W) mem x,
      HGc : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ?ms))
      |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdc |} _ =>
      apply (leaf_cfg W E' ss ms mdc _ 1352 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
      apply ps_finP_of_postP; apply (HRETOK D ly S Hp W (ms_regs ms) (ms_mem ms) mdc out w r Q HPRE);
      apply (retok_close B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs mem md out w r Q (ms_regs ms) (ms_mem ms) mdc kc HPRE HDEC);
      [ rewrite <- Hb0; lia | exact HJc | exact HPMc | sbm | exact HMc | exact HGc
      | split; [regeq | split; regeq] | split; regeq | regeq | regeq | regeq | regeq | regeq | regeq ]
    end in
  (* the \u leaves: refuted by the split *)
  let nu_tac := idtac; exfalso; apply Hnu; split; lia in
  (* why decoding the text from r is refused, at a free leaf *)
  let none_tac := idtac;
    first
    [ solve [nu_tac]
    | solve [apply (lw_none_ctl _ _ _ HRR); rewrite <- ?Hb0, <- ?Hb1; lia]
    | solve [apply (lw_none_plain_end _ _ _ HRR); rewrite <- ?Hb0, <- ?Hb1; lia]
    | solve [apply (lw_none_bs_end _ _ _ HRR); rewrite <- ?Hb0, <- ?Hb1; lia]
    | solve [apply (lw_none_bad _ _ _ HRR); rewrite <- ?Hb0, <- ?Hb1; [lia | lia | lia | apply lw_escape_none; lia]]
    | solve [eapply (lw_none_esc_end _ _ _ HRR); rewrite <- ?Hb0, <- ?Hb1;
             [lia | lia | lia | match goal with H : b1 = ?v |- _ => rewrite H; reflexivity end | lia]] ] in
  (* LEAF 1276: the free cut *)
  let leaf_free := idtac;
    lazymatch goal with
    | HS : st_ok_pi _ _ ?E' ?ss (restrict (w_H W) ?ms), HJc : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?kc,
      HPMc : P (ms_mem ?ms),
      HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) (ms_mem ?ms) x = mrestrict (w_H W) mem x,
      HGc : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ?ms))
      |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdc |} _ =>
      apply (leaf_cfg W E' ss ms mdc _ 1276 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
      apply ps_finP_hand; apply (HFREEC D ly S Hp W (ms_regs ms) (ms_mem ms) mdc out Q HPRE);
      apply (free_close B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs mem md out w r Q (ms_regs ms) (ms_mem ms) mdc kc HPRE HDEC);
      [ none_tac | exact HJc | exact HPMc | sbm | exact HMc | exact HGc | split; regeq | regeq | regeq | regeq ]
    end in
  (* LEAF 328: the back-edge after one stored byte (a plain byte, kk = 1, or a one-byte escape, kk = 2) *)
  let leaf_back := idtac;
    lazymatch goal with
    | HS : st_ok_pi _ _ ?E' ?ss (restrict (w_H W) ?ms), HJc : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?kc,
      HPMc : P (ms_mem ?ms),
      HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) (ms_mem ?ms) x = mrestrict (w_H W) mem x,
      HGc : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ?ms))
      |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdc |} _ =>
      let e20 := eval vm_compute in (sr_get (ss_regs ss) 20) in
      let kk := lazymatch e20 with SOff 20 ?kk => kk end in
      let rs := eval vm_compute in (ss_mem ss) in
      let i19 := eval vm_compute in (idx_base 19 rs 0) in
      let rg := eval vm_compute in (nth i19 rs (rg_t 0)) in
      let ev := lazymatch rg with context [CVal 1 ?ev] => ev end in
      let cv := lazymatch kk with
                | 1 => constr:(b0)
                | 2 => lazymatch goal with H : b1 = ?v |- _ =>
                         let o := eval vm_compute in (PjGrammar.escape v) in lazymatch o with Some ?c => c end end
                end in
      apply (leaf_cfg W E' ss ms mdc _ 328 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
      apply ps_finP_hand; apply (AFT ly S Hp W (ms_regs ms) (ms_mem ms) mdc out (w + 1) (r + kk) Q); [|lia];
      pose proof (region_of_st E' ss (restrict (w_H W) ms) i19 rg HS ltac:(vm_compute; reflexivity)) as Hrg;
      apply (dec_close1 B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs mem md out w r Q (ms_regs ms) (ms_mem ms) mdc kc (r + kk) cv HPRE HDEC);
      [ lazymatch kk with
        | 1 => rewrite Hb0; exact (proj1 (lw_step_plain _ _ _ HRR ltac:(rewrite <- Hb0; lia) ltac:(rewrite <- Hb0; lia) ltac:(rewrite <- Hb0; lia)))
        | 2 => exact (proj1 (lw_step_esc _ _ _ HRR cv ltac:(rewrite <- Hb0; lia) ltac:(lia) ltac:(rewrite <- Hb1; lia)
                 ltac:(rewrite <- Hb1; match goal with H : b1 = ?v |- _ => rewrite H; reflexivity end)))
        end
      | lazymatch kk with
        | 1 => exact (proj2 (lw_step_plain _ _ _ HRR ltac:(rewrite <- Hb0; lia) ltac:(rewrite <- Hb0; lia) ltac:(rewrite <- Hb0; lia)))
        | 2 => exact (proj2 (lw_step_esc _ _ _ HRR cv ltac:(rewrite <- Hb0; lia) ltac:(lia) ltac:(rewrite <- Hb1; lia)
                 ltac:(rewrite <- Hb1; match goal with H : b1 = ?v |- _ => rewrite H; reflexivity end)))
        end
      | lia | lia | exact HJc | exact HPMc | sbm | exact HMc | exact HGc
      | destruct Hrg as (_ & _ & _ & Hch); cbn [YP09.r_chunks base_val YP09.r_base] in Hch;
        apply Forall_inv in Hch; cbn [ew ewset Nat.eqb] in Hch; rewrite E19 in Hch; unfold w64 in Hch;
        rewrite unsigned_lit_small in Hch by lia;
        apply (val_mem_chunk1 E' _ w ev cv Hch);
        [ rewrite ?U_SOff, ?U_SLit; cbn [ew ewset Nat.eqb]; rewrite ?EB0, ?EB1; rewrite ?unsigned_lit_small by lia;
          rewrite ?zcanon_id by (unfold M64; lia); lia
        | lia ]
      | split; [regeq | split; regeq] | split; regeq | unfold dc_regs; repeat (split; [regeq|]); regeq
      | regeq | regeq | regeq | regeq | regeq | regeq | regeq ]
    end in
  (* THE WALK: run to the next branch or cut, branch, and close the leaves *)
  let rec go := idtac;
    lazymatch goal with
    | |- range_addressable _ _ _ _ => ob_tac
    | |- awr_ok _ _ _ _ _ _ _ _ _ => wr_tac
    | |- _ => try fold_inv;
    lazymatch goal with HS : st_ok_pi _ _ _ ?ss _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss - PSO) in
    lazymatch pc with
    | 328 => leaf_back
    | 1276 => leaf_free
    | 1352 => leaf_retok
    | 452 => nu_tac
    | _ =>
      lazymatch goal with HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HMN : P _ |- _ =>
      let K := eval vm_compute in (run_K A_LIM dBx SH_o ss) in
      let c := eval vm_compute in (cut_of K ss) in
      lazymatch c with
      | 0 => paj_run_tok_x_inv RUN HS HJ SHOK HMN dBspan; br
      | _ => paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN dBspan (PSO + c); go
      end
      end
    end end end
  with br := idtac;
    lazymatch goal with
    | |- SRr _ _ _ _ => try fold_inv; lazymatch goal with HS' : st_ok_pi _ _ _ ?ss' _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
        let K := eval vm_compute in (run_K A_LIM dBx SH_o ss') in
        let why := eval vm_compute in (snd (sym_runN_pi_tok TPIx TWx K dBx dBspan SH_o 1 ss')) in
        lazymatch why with
        | PTS_stopped (SR_branch _ _ _) => psrr_branch_tok RUN BR HS' SHOK' dBspan; [cn; go | cn; go]
        (* the escape letter at r + 1: the text region gains that byte, read under the branch r + 1 < text + len *)
        | PTS_stopped (SR_load (Some 20%nat) 1) =>
          lazymatch type of HS' with st_ok_pi _ _ ?E' _ (restrict (w_H W) ?ms) =>
          lazymatch goal with HMc : forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x |- _ =>
          let rs := eval vm_compute in (ss_mem ss') in
          let HSn := fresh "HS" in
          assert (HSn : st_ok_pi segs VAL E' (mkSS (ss_pc ss') (ss_regs ss') (rg_t 1 :: ss_mem ss') (ss_resv ss') (ss_facts ss'))
                          (restrict (w_H W) ms));
          [ apply st_ok_pi_add_region;
            [ exact HS' | vm_compute; reflexivity
            | apply (rok_t E' _ r 1 b1);
              [ cbn [ew ewset Nat.eqb]; rewrite E20; reflexivity
              | cbn [ew ewset Nat.eqb Nat.add]; exact EB1
              | lia | lia | lia
              | cbn [ms_mem restrict]; cbn [Z.of_nat]; rewrite Hb1;
                apply (txt_cur W mem (ms_mem ms) w (pi_text D) (pi_tb D) (r + 1) HMc HG8);
                [lia | destruct (Hap (r + 1)); lia | lia] ]
            | apply all_disjoint_of_extents; change (ss_mem ss') with rs;
              cbn [map zall_disjoint]; unfold YA0q.extent_of_region, zdisj;
              cbn [fst snd rg_t YP09.r_base YP09.r_lo YP09.r_hi base_val ew ewset Nat.eqb Z.of_nat];
              rewrite ?E20, ?E2, ?E9, ?E19; unfold w64; rewrite ?unsigned_lit_small by lia;
              repeat split; first [lia | destruct (Hap (r + 1)); lia] ]
          | clear HS'; go ] end end
        end end
    | |- _ => go
    end in
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HMN : P _ |- _ =>
    paj_run_tok_x_inv RUN HS HJ SHOK HMN dBspan; br end.
Qed.

(* THE STRETCH over P: by induction on text + len - r; the \u case by ps_seg_uP, every other turn by dec_turn *)
Theorem ps_seg_dec_holdsP : ps_seg_decP B ARx SK P CTX CW.
Proof.
  intros D.
  assert (IND : forall n ly S Hp W regs mem md out w r Q, (Z.to_nat (pi_text D + pi_len D - r) <= n)%nat ->
    ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
    SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_DEC) regs mem md)
      (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D)).
  { induction n as [|n IH]; intros ly S Hp W regs mem md out w r Q Hn HPRE HDEC;
      destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
        as (_ & _ & _ & _ & _ & _ & _ & _ & Hr & _).
    - lia.
    - assert (AFT : ps_dec_afterP B ARx SK P CW D r).
      { intros ly' S' Hp' W' regs' mem' md' out' w' r' Q' HDEC' Hrr.
        destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly' S' Hp' W' regs' mem' md' out' w' r' Q' HPRE HDEC')
          as (_ & _ & _ & _ & _ & _ & _ & _ & Hr' & _).
        apply (IH ly' S' Hp' W' regs' mem' md' out' w' r' Q'); [lia | exact HPRE | exact HDEC']. }
      destruct (Z.eq_dec (nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0) 92) as [H92|H92];
      [destruct (Z.eq_dec (nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0) 117) as [H117|H117]|].
      + exact (HU D ly S Hp W regs mem md out w r Q HPRE HDEC H92 H117 AFT).
      + apply ps_finP_SRr'. apply (dec_turn D ly S Hp W regs mem md out w r Q HPRE HDEC); [intros [_ H]; exact (H117 H) | exact AFT].
      + apply ps_finP_SRr'. apply (dec_turn D ly S Hp W regs mem md out w r Q HPRE HDEC); [intros [H _]; exact (H92 H) | exact AFT]. }
  intros ly S Hp W regs mem md out w r Q HPRE HDEC.
  exact (IND _ ly S Hp W regs mem md out w r Q (le_n _) HPRE HDEC).
Qed.
End c.

(* THE STABLE STRETCH: ps_seg_dec_holds, the P := (fun _ => True) instance of ps_seg_dec_holdsP *)
Section c0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HW : prh_head_wide.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis HRETOK : ps_seg_retok B ARx SK CTX CW.
Hypothesis HFREEC : ps_seg_free B ARx SK CTX CW.
Hypothesis HU : ps_seg_u B ARx SK CTX CW.

Theorem ps_seg_dec_holds : ps_seg_dec B ARx SK CTX CW.
Proof.
  apply (proj1 (ps_seg_dec_of_True B ARx SK CTX CW)).
  exact (ps_seg_dec_holdsP B ARx SK (fun _ => True) CTX CW LAWS HW PST_ok srr_inv_laws_True
    (proj2 (ps_seg_retok_of_True B ARx SK CTX CW) HRETOK)
    (proj2 (ps_seg_free_of_True B ARx SK CTX CW) HFREEC)
    (proj2 (ps_seg_u_of_True B ARx SK CTX CW) HU)).
Qed.
End c0.
