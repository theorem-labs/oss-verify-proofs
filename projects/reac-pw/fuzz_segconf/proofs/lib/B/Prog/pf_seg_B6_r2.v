(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 416 of its 466 lines of code are new or changed and 5003 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the REF3 walk of
   segment B6 of reac_segconf_parse_file, b6_ref3_ok : HA_TAIL n -> H_REF3 n (the B6 segment lane of the image-B G3 walk owner,
   2026-10-30). proves no function (kind: segment piece of reac_segconf_parse_file's walk, the cut REF3).
   ADAPTED from lib/B/Prog/reac_segconf_parse.v (this lane's base: the shape of a program call, cl_callSF and
   the lift of apost_baseF to the FP state the callee returned) and from the image-A G3 walk owner's lib/A/Prog/pf_a5_k.v
   through this lane's pf_seg_B6_k.v.
   The code (two instructions): 0x882b4 `jal 892f8 <refuse>` (return 0x882b8), 0x882b8 `j 0x88600` (TAIL).
   The call's premises are pf_seg_B6_r.v's b6r_refuse_site. The cut at TAIL is rebuilt from refuse's OWN
   ajournal, which cl_callSF returns beside the caller's: its above-ceiling clause keeps the 23 slots, c's slot
   0xc8, the cur slot 0xc0 and the 13 saved registers (all at or above s1 > alloc_ceiling, and refuse's
   footprint lies in the block c, below it); its frames clause keeps the class-5 frame, its flag word, cur_name
   and the 144 shadow cells; its blocks clause keeps the text's bytes (reader_pre's sa_disj keeps the text's
   read span off the block c); its image clause keeps the literals, the catalogue and the read-only window;
   the text's and the block's shadow are re-derived from AR at the state refuse returned (b6_addr_of_heap,
   b6_tail_of_heap), the stack-protector cells from SSPX, and c's new bytes are refuse's own post.
   Section hypotheses: REFUSE, SIGP, VRO, SSPX (as pf_seg_B6_r.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B6_k pf_seg_B6_a pf_seg_B6_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma b6r_set_fs2 : forall f g s, set_fs f (set_fs g s) = set_fs f s.
Proof. intros f g s. destruct s. reflexivity. Qed.

(* refuse's footprint is a closed set of ranges above 0, so the journal's image clause applies off it *)
Lemma b6r_rfw_closed : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos.
assert (Hz : 0 <= Z.of_nat (length (rc_refusal rcs))) by lia.
unfold refuse_W. unfold seg_spec.refusal_addr.
unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF.
destruct ((length (rc_refusal rcs) <? 8)%nat);
  repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil.
Qed.

Ltac b6r_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.

(* a reader reads an address by its word, so it agrees at a and at a mod 2 ^ 64 *)
Lemma b6r_aview_mod : forall segs (H : word -> bool) (m : word -> option byte) a,
  aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity. }
rewrite E. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* the return address of the call: 0x882b8, the `j 0x88600` *)
Definition PF_REF3_RET : Z := AF_reac_segconf_parse_file + 0x480.

(* ---------- the seeds: every register its own atom, no region ---------- *)
Definition b6r_ssr : sstate := mkSS PF_REF3_RET sr_atoms [] None (mkFacts [] [] []).
Definition b6r_ss : sstate := mkSS PF_REF3 sr_atoms [] None (mkFacts [] [] []).
Lemma b6r_seed_ret : forall (f1 : YK11.FPState) (W : world SEGS) (rg : bvmap 5 word) mm,
  @st_ok_pi SEGS VAL f1 (Eimg (Ereg rg [])) b6r_ssr
    (restrict (w_H W) (@mkst f1 rg (Z_to_bv 64 (BASE + PF_REF3_RET)) mm (seg_rom SEGS))).
Proof.
intros f1 W rg mm. rewrite restrict_mkst_fx. unfold b6r_ssr. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.
Lemma b6r_seed : forall (f1 : YK11.FPState) (W : world SEGS) (rg : bvmap 5 word) mm,
  @st_ok_pi SEGS VAL f1 (Eimg (Ereg rg [])) b6r_ss
    (restrict (w_H W) (@mkst f1 rg (Z_to_bv 64 (BASE + PF_REF3)) mm (seg_rom SEGS))).
Proof.
intros f1 W rg mm. rewrite restrict_mkst_fx. unfold b6r_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------- REF3 -> TAIL ---------- *)
Lemma b6_ref3 : forall n, HA_TAIL B n -> H_REF3 (fx := fx) B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 HI.
pose proof HI as HI0.
destruct HI as (HBASE & HMID & HST & HREF & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HMID as (HmidO & HmidLe & Hlctx).
destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
destruct (b6_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (GEO & Hin & EF & Hfrs & HAR & HlyE).
destruct (b6a_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (GEOA & _ & _ & _ & _).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HSLC & HRG0).
pose proof HTF as (C0 & C16 & TF1 & TF2 & LS).
pose proof HCX as (HPRE & HROD0 & _ & HcB & _ & _ & _ & _ & (fe & HPF) & HROOM & HEV).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof GEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4).
pose proof STK_values as (STRIM & SREF & SCC & SPF & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof (b6r_refuse_site B n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 HI0) as SITE.
destruct (b6_chain B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HBASE) as [ch1 HCH].
destruct SITE as (SROD & SR10 & SRc & SR11 & SRln & SR12 & SRfa & SPRE & SROOM & SEV).
(* the seed at REF3 and the one jal *)
pose proof (b6r_seed fx Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
unfold cfg_at. change (w64 (BASE + PF_REF3)) with (Z_to_bv 64 (BASE + PF_REF3)).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ apply awr_ok_nil. }
b6_clear_md.
(* the jal writes no byte *)
assert (UN : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E (ss_mem b6r_ss) (w_H Wc) memc (ms_mem ms)
    (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
assert (RDEQ : rdW Wc (ms_mem ms) = rdW Wc memc).
{ apply functional_extensionality_dep. intros a.
  rewrite (b6r_aview_mod SEGS (w_H Wc) (ms_mem ms) a), (b6r_aview_mod SEGS (w_H Wc) memc a).
  apply UN. apply Z.mod_pos_bound. lia. }
assert (UV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
(* the registers at the call: every one but ra is the cut's *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 10; 11; 12; 13; 14; 15; 16; 17] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b6r_rreg HS; rewrite b6_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (QB : forall (r : bv 5) k, bv_unsigned r = k ->
    In k [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 10; 11; 12; 13; 14; 15; 16; 17] ->
    getr (ms_regs ms) r = getr rX r).
{ intros r k Hr Hk. pose proof (QK k Hk) as Q. subst k. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (RA : forall (r : bv 5) k x, bv_unsigned r = k ->
    In (k, x) [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)] ->
    getr rX r = w64 x)
  by (intros r k x Hr Hk; apply (b6a_bvr rX r k); [exact Hr | exact (b6_rg rX _ k x HRG0 Hk)]).
assert (Qsp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. rewrite (QB (2%bv) 2 eq_refl ltac:(b6_in)), (RA (2%bv) 2 _ eq_refl ltac:(b6_in)).
  unfold w64. apply unsigned_lit_small. lia. }
assert (Qs0 : s0Z (ms_regs ms) = pf_sp0 v).
{ unfold s0Z. rewrite (QB (8%bv) 8 eq_refl ltac:(b6_in)), (RA (8%bv) 8 _ eq_refl ltac:(b6_in)).
  unfold w64. apply unsigned_lit_small. lia. }
prreg HS (1%bv : bv 5) Q1.
pmkst HS.
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_REF3_RET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (SegModel.refuse cf (ln + 1) f args) /\ sa_noalloc B lyc Sc ly2 S2)
    HJ).
  - rewrite Qsp. lia.
  - replace (pf_s1 v - pf_sp0 v) with (- (pf_sp0 v - pf_s1 v)) by lia.
    rewrite Z.mod_opp_l_z; [reflexivity|lia|].
    replace (pf_sp0 v - pf_s1 v) with ((pf_sp0 v - 0x160) mod 32 + 0x160) by (unfold pf_s1; lia).
    pose proof (Z.mod_pos_bound (pf_sp0 v - 0x160) 32 ltac:(lia)) as MB.
    assert (E16 : (pf_sp0 v - 0x160) mod 16 = 0)
      by (replace (pf_sp0 v - 0x160) with (pf_sp0 v + (-22) * 16) by lia; rewrite Z_mod_plus_full; exact S3).
    pose proof (Z.div_mod (pf_sp0 v - 0x160) 32 ltac:(lia)) as D32.
    pose proof (Z.div_mod (pf_sp0 v - 0x160) 16 ltac:(lia)) as D16.
    assert (HM : (pf_sp0 v - 0x160) mod 32 = 0 \/ (pf_sp0 v - 0x160) mod 32 = 16) by lia.
    destruct HM as [HM | HM]; rewrite HM; reflexivity.
  - lia.
  - rewrite SREF. lia.
  - rewrite SREF, SPF. lia.
  - rewrite (QB (3%bv) 3 eq_refl ltac:(b6_in)). exact (RA (3%bv) 3 _ eq_refl ltac:(b6_in)).
  - rewrite (QB (4%bv) 4 eq_refl ltac:(b6_in)). exact (RA (4%bv) 4 _ eq_refl ltac:(b6_in)).
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold PF_REF3_RET, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold PF_REF3_RET, AF_reac_segconf_parse_file; lia).
    unfold PF_REF3_RET, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia. rewrite Qs0.
    apply (achain_kept lyc (rdW Wc memc) (rdW Wc (ms_mem ms)) (pf_s1 v) (pf_sp0 v) ch1 0 HCH); [lia | | exact UN].
    pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2) & _). rewrite HlyE. lia.
  - intros HPRE1. eapply SRr_mono.
    { apply (REFUSE fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 (p_c v) (ln + 1) (seg_litA_rc f) (ln + 1)
        cf f args HPRE1); rewrite ?RDEQ; try assumption.
      - rewrite (QB (10%bv) 10 eq_refl ltac:(b6_in)). exact SR10.
      - rewrite (QB (11%bv) 11 eq_refl ltac:(b6_in)). exact SR11.
      - rewrite (QB (12%bv) 12 eq_refl ltac:(b6_in)). exact SR12.
      - revert SPRE. rewrite (QB (13%bv) 13 eq_refl ltac:(b6_in)), (QB (14%bv) 14 eq_refl ltac:(b6_in)),
          (QB (15%bv) 15 eq_refl ltac:(b6_in)), (QB (16%bv) 16 eq_refl ltac:(b6_in)),
          (QB (17%bv) 17 eq_refl ltac:(b6_in)).
        assert (Esp : spZ rX = pf_s1 v)
          by (unfold spZ; rewrite (RA (2%bv) 2 _ eq_refl ltac:(b6_in)); unfold w64; apply unsigned_lit_small; lia).
        unfold refuse_pre. rewrite Qsp, Esp. exact (fun H => H). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (b6_rfw_sub (p_c v) cf a Ha)|].
    pose proof (b6_rfw_in (p_c v) cf a Ha) as Hrng.
    destruct HOBJ as (_ & _ & _ & _ & (b & m & Hbin & Hb1 & Hb2) & _).
    exists b, m. split; [exact Hbin|].
    destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdv b m ltac:(exact (proj1 HJ)) Hbin)
      as (_ & _ & _ & _ & _ & _ & Hm0).
    pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hb2; lia)) as [_ Hrq]. lia. }
cbv beta. intros WR c2 _ (fx1 & lyR & SR & rR & mR & mdR & Hfx1 & -> & HJ2 & HJc2 & HP2 & HQ2).
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
destruct HQ2 as (HRC2 & HNA2). destruct HNA2 as (HPM2 & HlyR & (fS & HSfs)).
pose proof HJc2 as (HAR2 & Hly2 & Hsec2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & KF1 & KF2 & KF3 & KF4 & KF5 &
  Hpres2 & Hstk2 & Hext2 & HQT2).
pose proof HOBJ as (HTXT & HTAD & HTHP & HCAD & HCHP & HCAT & HLITS & HROD & HSSP).
pose proof HCHP as (bc & mc & Hbcin & Hbc1 & Hbc2).
pose proof HTHP as (bt & mt & Hbtin & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbcin) as (_ & Hbc4 & Hbcc & Hbcapp & _ & _ & Hbcm).
pose proof (req_size_pos mc ltac:(unfold seg_spec.SEG_C_SIZE in Hbc2; lia)) as [_ Hbcrq].
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bt mt HAR Hbtin) as (_ & Hbt4 & Hbtc & Hbtapp & _ & _ & Hbtm).
pose proof (req_size_pos mt ltac:(unfold pf_len in Hbt2; lia)) as [_ Hbtrq].
destruct (b6a_SHb v pos GEOA) as (ESH & SH1 & SH2 & EF8 & SH4).
(* refuse's footprint lies in the block c, below the allocator's ceiling and off the frame and the shadow band *)
assert (NFPC : forall a, inFP (refuse_W (p_c v) cf) a -> bc <= a < bc + req_size mc).
{ intros a HFa. pose proof (b6_rfw_in (p_c v) cf a HFa) as Hr. unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (NFPH : forall a, alloc_ceiling <= a -> ~ inFP (refuse_W (p_c v) cf) a)
  by (intros a Ha HFb; pose proof (NFPC a HFb); lia).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hbcin Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EF in Hsep.
change (fs_frame_bytes 5) with 2048 in Hsep.
assert (NFPF : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> ~ inFP (refuse_W (p_c v) cf) a)
  by (intros a Ha HFc; pose proof (NFPC a HFc); lia).
assert (NFPS : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ inFP (refuse_W (p_c v) cf) a).
{ intros a Ha HFd. pose proof (NFPC a HFd) as Hr.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbcapp.
  unfold kLowMemEnd, kHighShadowEnd in Ha. lia. }
(* the four keep families refuse's journal gives *)
assert (KST : forall a, pf_s1 v <= a -> a < 2 ^ 64 -> rdW WR mR a = rdW Wc (ms_mem ms) a).
{ intros a H1 H2. apply KF1; [lia | lia | apply NFPH; lia]. }
assert (KFR : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rdW WR mR a = rdW Wc (ms_mem ms) a).
{ intros a Ha. apply (KF4 5 pos a Hin); [|exact (NFPF a Ha)].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 5) with 2048. lia. }
assert (KSH : forall i, 0 <= i < 256 -> rdW WR mR (pf_SH v pos + i) = rdW Wc (ms_mem ms) (pf_SH v pos + i)).
{ intros i Hi. apply (KF4 5 pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF.
    change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos). lia.
  - apply NFPS. unfold kLowMemEnd, kHighShadowEnd. lia. }
assert (KTX : forall a, p_t v <= a < p_t v + pf_len v -> rdW WR mR a = rdW Wc (ms_mem ms) a).
{ intros a Ha.
  replace a with (bt + (a - bt)) by lia.
  apply (KF2 bt mt (a - bt) Hbtin); [exact (Permutation_in _ (Permutation_sym HPM2) Hbtin) | lia |].
  intros HFe. pose proof (b6_rfw_in (p_c v) cf _ HFe) as Hr.
  destruct (b6_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HBASE) as
    (_ & _ & _ & _ & _ & _ & HDJ & _).
  unfold sa_disj, seg_spec.cstr_span, seg_spec.SEG_C_SIZE, pf_len in *.
  pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)).
  lia. }
(* the keeps, against the cut's own reader *)
assert (KSTc : forall a, pf_s1 v <= a -> a < 2 ^ 64 -> rdW WR mR a = rdW Wc memc a)
  by (intros a H1 H2; rewrite (KST a H1 H2), RDEQ; reflexivity).
assert (KFRc : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rdW WR mR a = rdW Wc memc a)
  by (intros a Ha; rewrite (KFR a Ha), RDEQ; reflexivity).
assert (KSHc : forall i, 0 <= i < 256 -> rdW WR mR (pf_SH v pos + i) = rdW Wc memc (pf_SH v pos + i))
  by (intros i Hi; rewrite (KSH i Hi), RDEQ; reflexivity).
assert (KTXc : forall a, p_t v <= a < p_t v + pf_len v -> rdW WR mR a = rdW Wc memc a)
  by (intros a Ha; rewrite (KTX a Ha), RDEQ; reflexivity).
(* the image bytes the journal keeps *)
assert (KIM : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> rdW WR mR a = rdW Wc memc a).
{ intros a Hi Ho He. rewrite <- RDEQ. apply KF3; [exact Hi | exact Ho | exact He |].
  apply fp_spares_closed; [apply b6r_rfw_closed; lia|].
  intros HFz. pose proof (b6_rfw_in (p_c v) cf a HFz) as Hr.
  destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR) as [_ Hn].
  { left. exists bc, mc. split; [exact Hbcin | unfold seg_spec.SEG_C_SIZE in *; lia]. }
  exact (Hn Hi). }
assert (ROIMG : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a).
{ intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr]|].
  destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
  unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
assert (KLIT : forall a ss, sa_lit SEGS B (rdW Wc memc) a ss -> sa_lit SEGS B (rdW WR mR) a ss).
{ intros a ss (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
  split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
  split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
  intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & Hown & Herr).
  rewrite (KIM _ Himg Hown Herr). exact (Hz i Hi'). }
rename ms into ms1. rename HFr into HFr1. rename HS into HS1. rename HG into HG1.
(* the registers: the jal wrote ra only, refuse kept the callee-saved ones *)
assert (QBL : forall L, incl L [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (20, SHADOW_OFF); (18, 0x23); (21, pf_SH v pos); (26, -1);
    (25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)] -> pf_rg rX L -> pf_rg rR L).
{ intros L HL HR. apply (b6_rg_pres (ms_regs ms1) rR L HP2).
  - unfold pf_rg in HR. rewrite Forall_forall. intros rv Hiv.
    pose proof (HL rv Hiv) as Hm. cbn [In] in Hm.
    repeat (destruct Hm as [<- | Hm]; [cbn [fst]; unfold acallee_saved; lia|]). destruct Hm.
  - unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hiv.
    pose proof (HL rv Hiv) as Hm. cbn [In] in Hm.
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 2) 2 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 3) 3 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 4) 4 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 8) 8 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 9) 9 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 20) 20 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 18) 18 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 21) 21 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 26) 26 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 25) 25 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QB (Z_to_bv 5 22) 22 eq_refl ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm. }
(* the state at 0x882b8, and the `j 0x88600` *)
pose proof (b6r_seed_ret fx1 WR rR mR) as HS2.
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg rR []))) by apply Eimg_env.
change (0 + EV_refuse) with 0 in HJ2.
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_TAIL.
{ apply awr_ok_nil. }
b6_clear_md.
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> rdW WR (ms_mem ms) a = rdW WR mR a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) (Eimg (Ereg rR [])) (ss_mem b6r_ssr) (w_H WR) mR
    (ms_mem ms) (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
assert (RD3 : rdW WR (ms_mem ms) = rdW WR mR).
{ apply functional_extensionality_dep. intros a.
  rewrite (b6r_aview_mod SEGS (w_H WR) (ms_mem ms) a), (b6r_aview_mod SEGS (w_H WR) mR a).
  apply UN3. apply Z.mod_pos_bound. lia. }
assert (QR : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rR (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [b6r_rreg HS2; rewrite b6_den_atom0; apply ew_Eimg_Ereg_nat; reflexivity |]). destruct Hr. }
assert (QRL : forall L, incl L [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (20, SHADOW_OFF); (18, 0x23); (21, pf_SH v pos); (26, -1);
    (25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)] -> pf_rg rR L -> pf_rg (ms_regs ms) L).
{ intros L HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hiv.
  pose proof (HL rv Hiv) as Hm. cbn [In] in Hm.
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 2 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 3 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 4 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 8 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 9 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 20 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 18 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 21 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 26 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 25 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm as [<- | Hm]; [cbn [fst snd]; rewrite (QR 22 ltac:(b6_in)); exact (HR _ Hiv)|].
    destruct Hm. }
pmkst HS2.
lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?rg ?pc ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg pc mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx)
end.
pose proof (proj1 HJ2) as HARf.
assert (KSTd : forall a, pf_s1 v <= a -> a < 2 ^ 64 -> rdW WR (ms_mem ms) a = rdW Wc memc a)
  by (intros a H1 H2; rewrite RD3; apply KSTc; assumption).
assert (KFRd : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rdW WR (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha; rewrite RD3; apply KFRc; assumption).
assert (KSHd : forall i, 0 <= i < 256 ->
    rdW WR (ms_mem ms) (pf_SH v pos + i) = rdW Wc memc (pf_SH v pos + i))
  by (intros i Hi; rewrite RD3; apply KSHc; assumption).
assert (KTXd : forall a, p_t v <= a < p_t v + pf_len v -> rdW WR (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha; rewrite RD3; apply KTXc; assumption).
assert (KIMd : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> rdW WR (ms_mem ms) a = rdW Wc memc a)
  by (intros a H1 H2 H3; rewrite RD3; apply KIM; assumption).
assert (KLITd : forall a ss, sa_lit SEGS B (rdW Wc memc) a ss -> sa_lit SEGS B (rdW WR (ms_mem ms)) a ss)
  by (intros a ss H; rewrite RD3; apply KLIT; exact H).
apply (TAIL fx1 v pos lyR SR WR (ms_regs ms) (ms_mem ms) mdv0 (SegModel.refuse cf (ln + 1) f args) cur' nm
  (pf_next (p_s v) o) (ln + 1) d).
assert (INCL6 : incl [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)]
   [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF); (18, 0x23);
    (21, pf_SH v pos); (26, -1); (25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)])
  by (intros x Hx; cbn [In] in *; tauto).
assert (INCL5 : incl (PF_RL v pos ++ [(25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)])
   [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF); (18, 0x23);
    (21, pf_SH v pos); (26, -1); (25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)])
  by (intros x Hx; unfold PF_RL in Hx; cbn [In app] in *; tauto).
assert (HRGT : pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)])).
{ unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hiv. apply HRG.
  unfold PF_RL, PF_RM in *. cbn [In app] in *. tauto. }
split; [|split; [|split; [|split]]].
- (* pf_base at the state refuse returned *)
  split; [exact HCX|].
  split.
  { split; [exact HJ2|].
    split; [rewrite HlyR; exact HlyE|].
    split; [destruct HSc as (f0 & E0); exists fS; rewrite HSfs, E0; apply b6r_set_fs2|].
    split; [exact (Permutation_trans HPM2 HPERM)|].
    split.
    { intros j r Hj.
      assert (Hj13 : (j < 13)%nat)
        by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
      rewrite (rdword_ext (rdW Wc memc) (rdW WR (ms_mem ms))); [exact (HSAV j r Hj)|].
      intros k Hk. apply KSTd; lia. }
    split.
    { rewrite (rdword_ext (rdW Wc memc) (rdW WR (ms_mem ms))); [exact HFLAG|].
      intros k Hk. apply KFRd. change (fs_frame_bytes 5) with 2048. lia. }
    split; [exact (fxrel_frm0 fx fx1 HFRM Hfx1)|].
    split; [exact HTF|].
    split.
    { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
      rewrite (rdword_ext (rdW Wc memc) (rdW WR (ms_mem ms))); [exact (HSLC ov Hov)|].
      cbn [In] in Hov. destruct Hov as [<- | []]. cbn [fst].
      intros k Hk. apply KSTd; lia. }
    exact (QRL _ INCL6 (QBL _ INCL6 HRG0)). }
  split.
  { split.
    { destruct HTXT as ((Hz & Hn) & Ht). split; [split; [|exact Hn]|].
      - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
        rewrite KTXd by (unfold pf_len; lia). exact (Hz i Hi).
      - apply (b6_tail_of_heap B lyR SR WR (ms_mem ms) mdv0 (p_t v) (p_s v) HARf).
        exists bt, mt. split; [exact (Permutation_in _ (Permutation_sym HPM2) Hbtin)|].
        unfold pf_len in Hbt2. lia. }
    split.
    { refine (proj1 (b6_addr_of_heap B lyR SR WR (ms_mem ms) mdv0 (p_t v) (pf_len v) HARf _ _ _)).
      - exists bt, mt. split; [exact (Permutation_in _ (Permutation_sym HPM2) Hbtin) | lia].
      - destruct HTAD as (Ht0 & _). lia.
      - unfold pf_len. lia. }
    split.
    { exists bt, mt. split; [exact (Permutation_in _ (Permutation_sym HPM2) Hbtin) | lia]. }
    split.
    { refine (proj1 (b6_addr_of_heap B lyR SR WR (ms_mem ms) mdv0 (p_c v) seg_spec.SEG_C_SIZE HARf _ _ _)).
      - exists bc, mc. split; [exact (Permutation_in _ (Permutation_sym HPM2) Hbcin) | lia].
      - lia.
      - unfold seg_spec.SEG_C_SIZE. lia. }
    split.
    { exists bc, mc. split; [exact (Permutation_in _ (Permutation_sym HPM2) Hbcin) | lia]. }
    split.
    { destruct HCAT as (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
      intros i Hni. destruct (Hrows i Hni) as (tp & Htp & Hl). exists tp. split; [|exact (KLITd tp _ Hl)].
      rewrite (rdword_ext (rdW Wc memc) (rdW WR (ms_mem ms))); [exact Htp|].
      intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hni; lia).
      destruct (Hi (pin_spec.row_addr catA i + k)
        ltac:(unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES; lia)) as (Himg & Hown & Herr).
      exact (KIMd _ Himg Hown Herr). }
    split; [intros x Hx; exact (KLITd _ _ (HLITS x Hx))|].
    split.
    { intros a Hro Ho He. rewrite (KIMd a (ROIMG a Hro) Ho He). exact (HROD a Hro Ho He). }
    exact (SSPX lyR SR WR (ms_mem ms) mdv0 HARf). }
  split.
  { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
    pose proof (b6_PF_SL_offs v pos ov Hov) as Hof.
    rewrite (rdword_ext (rdW Wc memc) (rdW WR (ms_mem ms))); [exact (HSL ov Hov)|].
    intros k Hk. apply KSTd; lia. }
  intros i Hi. rewrite (KSHd i ltac:(lia)). exact (HFSH i Hi).
- exact Hlctx.
- pose proof (pf_next_skipn_lt (p_s v) o HmidO). lia.
- split; [rewrite RD3; exact HRC2|].
  split.
  { destruct (refuse_proj cf (ln + 1) f args) as (Hseg & _).
    unfold pf_cur_ok in *. destruct cur' as [i|]; [rewrite Hseg; exact HCUR | exact I]. }
  split.
  { destruct HNM as (fl & Hfl & Hfe). exists fl. split; [|exact Hfe].
    intros i Hi. destruct Hfe as [Hlen _].
    rewrite KFRd; [exact (Hfl i Hi) | unfold PF_O_CN; lia]. }
  split.
  { apply (pf_cnt_refuse cf (ln + 1) f args (length (skipn o (p_s v)))); [|exact HCNT].
    exact (pf_next_skipn_lt (p_s v) o HmidO). }
  rewrite (rdword_ext (rdW Wc memc) (rdW WR (ms_mem ms))); [exact HCURS|].
  intros k Hk. apply KSTd; lia.
- exact (QRL _ INCL5 (QBL _ INCL5 HRGT)).
Qed.

End x.
End d.
