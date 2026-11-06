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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 414 of its 496 lines of code are new or changed and 4971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B2.v; 101 of its 169 lines of code are new or changed and 428 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B11c_l.v, with its addresses and numbers changed; 71 of its 191 lines of code are new or changed and 49 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the KOUT piece
   of segment B11c of reac_segconf_parse_file's walk: after the F_badmodel refusal returns (0x88bf0), known and
   ntok go out of scope and the walk falls into LOWOUT (0x88c70). The B11c segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma).
   KOUT (0x88bf0, BASE + AF_reac_segconf_parse_file + 0xdb8) is a walk-internal cut of B11c: no other segment
   names it. Its state is INV_LOWOUT's with known and ntok still IN scope (PF_SC_KNOWN) and a0 free: refuse
   returned with c holding the refused state cf, the counters' room of the next line, cur in slot 0xc0.
   ADAPTED from the image-A G3 walk owner's image-A join piece lib/A/Prog/pf_a10b_j.v (commit
   c6f2a9302a3c), the same form at another set of cells; A11b's twin of this stretch is A's 0x886ec-0x88770
   (a working branch's pf_a11b_d.v head comment).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 0x88bf0 .. 0x88c6c, 32 instructions, no call,
   no inline check, no UBSan trap branch:
     0x88bf0 li a0,-8
     0x88bf4 .. 0x88c6c 31 x `sb a0,X(s5)`, X = 0x80, 0x81, 0x8a, 0x68 .. 0x6b, 0x64 .. 0x67, 0x70 .. 0x73,
             0x6c .. 0x6f, 0x78 .. 0x7b, 0x74 .. 0x77, 0x7c .. 0x7f: known's 30 cells (0x64-0x81) and ntok's cell
             (0x8a) back to 0xf8; then LOWOUT's first instruction 0x88c70.
   The seed: every register its own atom; the two cell ranges writable regions on s5's atom (s5 = SH, PF_RL).
   Section hypotheses: none. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11c_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x88bf0, where the F_badmodel refusal (jal 0x88bec) returns *)
Definition PF_KOUT : Z := AF_reac_segconf_parse_file + 0xdb8.
Lemma pf_kout_pc : seg_text + PF_KOUT = 0x88bf0.
Proof. vm_compute. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.

(** *** KOUT (0x88bf0): the refusal is done, c holds cf, known and ntok are still in scope *)
Definition INV_KOUT {fx : YK11.FPState} (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate)
  (Wc : world SEGS) (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_KOUT {fx : YK11.FPState} (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi, INV_KOUT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KOUT) rX memc mdc) (pf_postm B v (cf, Some gi, nm) o ln).
Definition HA_KOUT (n : nat) : Prop := forall f1 : YK11.FPState, H_KOUT (fx := f1) n.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b11_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

(* ---------- the seed at KOUT ---------- *)
Definition b11O_regions : smem :=
  [YP09.mkRegion (Some 21%nat) 0x64 0x82 0x64 0x82 []; YP09.mkRegion (Some 21%nat) 0x8a 0x8b 0x8a 0x8b []].
Definition b11O_ss : sstate := mkSS PF_KOUT sr_atoms b11O_regions None (mkFacts [] [] []).
Lemma b11O_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc,
  b11_geoP v pos ->
  getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos) ->
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b11O_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KOUT)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc HG R21 Hsh.
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & F8 & _).
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b11O_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b11O_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite U21; (split; [lia|]); (split; [lia|]); (split; [|constructor]);
    intros o Ho; apply (apresent_writable SEGS); apply Hsh; lia.
- unfold b11O_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U21. repeat split; lia.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ---------- the piece: KOUT -> LOWOUT ---------- *)
Lemma b11_kout : forall n, H_LOWOUT (fx := fx) B n -> H_KOUT (fx := fx) n.
Proof.
intros n LOW v pos lyc Sc Wc rX memc mdc cf nm o ln d gi HI.
destruct HI as (HBASE & HMID & HST & HRG).
destruct HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos HGEO) as (ESH & SH1 & SH2 & F8 & _).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HSLC & HRG0).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EF in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
pose proof asan_consts as (C1 & _).
unfold PF_RL, PF_RM in HRG.
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (b11_rg rX _ 21 _ HRG); b11_in).
pose proof (b11O_seed v pos Wc rX memc HGEO R21 (fun i Hi => proj1 (Hsh i Hi))) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_KOUT)) with (Z_to_bv 64 (BASE + PF_KOUT)).
(* 0x88bf0 .. 0x88c6c: a0 = -8, the 31 shadow stores, into LOWOUT *)
paj_run_to_sh b11_RUNTO HS HJ PF_LOWOUT.
{ intros a (r & Hr & Ha). unfold b11O_ss, b11O_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  (right; right; right; left; exists 5, pos; split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
   rewrite EF; change (fs_frame_bytes 5 / 8) with 256; change (shadow_addr (pf_F v pos)) with (pf_SH v pos);
   rewrite U21 in Ha; lia). }
cbn [ms_mem mkst] in HFr, HG, HF.
b11_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (pf_SH v pos + 0x64 <= a < pf_SH v pos + 0x82 \/ pf_SH v pos + 0x8a <= a < pf_SH v pos + 0x8b) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem b11O_ss) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_SH v pos + 0x64 <= a < pf_SH v pos + 0x82 \/ pf_SH v pos + 0x8a <= a < pf_SH v pos + 0x8b) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
cbn [ms_mem restrict] in HR0, HR1.
assert (C8a : forall i, 0x64 <= i < 0x82 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0xf8).
{ intros i Hi. apply (b11_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR0 U21). revert i Hi.
  apply (b11_zrange (fun i => b11_cell_ok _ i 0xf8) 0x64 30). vm_compute. reflexivity. }
assert (C8b : rdW Wc (ms_mem ms) (pf_SH v pos + 0x8a) = Some 0xf8).
{ apply (b11_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ 0x8a _ HR1 U21). vm_compute. reflexivity. }
assert (KP : b11_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split.
  - intros a Ha Hn. apply K1; [exact Ha|]. intros Hw. apply Hn. unfold b11_Wr. lia.
  - intros a _ Hv. exact (M1 a Hv). }
(* the registers at LOWOUT: a0 = -8, the rest the cut's *)
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (-8)).
{ b11_rreg HS. cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b11_rreg HS; rewrite b11_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_LOWOUT) rg mm mdx) end.
apply (LOW v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi).
destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [|split; [exact HMID|split]].
- (* pf_base at PF_SC_L146 *)
  split; [exact HCX|].
  split.
  { split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split; [exact (b11_keep_saved v pos _ _ _ HGEO KP HSAV)|].
    split; [exact (b11_keep_flag v pos _ _ HGEO KP HFLAG)|].
    split; [exact HFRM|]. split; [exact HTF|].
    split; [apply (b11_keep_slots v pos _ _ _ HGEO KP); [repeat constructor; cbn [fst]; lia | exact HSLC]|].
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b11_rg rX _ _ _ HRG0); b11_in | b11_in]). }
  split; [exact (b11_keep_obj B v pos lyc Sc Wc memc mdc _ _ HGEO HAR Hin EF KP HOBJ)|].
  split; [exact (b11_keep_sl v pos _ _ HGEO KP HSL)|].
  intros i Hi.
  destruct (Z_lt_le_dec i 0x64) as [H1 | H1];
    [|destruct (Z_lt_le_dec i 0x82) as [H2 | H2];
      [|destruct (Z_lt_le_dec i 0x8a) as [H3 | H3];
        [|destruct (Z_lt_le_dec i 0x8b) as [H4 | H4]]]].
  + rewrite K1 by lia. rewrite b11_shb_l146_same by (unfold b11_kcell; lia). exact (HFSH i Hi).
  + rewrite (C8a i ltac:(lia)). rewrite b11_shb_l146_k by lia. reflexivity.
  + rewrite K1 by lia. rewrite b11_shb_l146_same by (unfold b11_kcell; lia). exact (HFSH i Hi).
  + replace i with 0x8a by lia. rewrite C8b, b11_shb_l146_n. reflexivity.
  + rewrite K1 by lia. rewrite b11_shb_l146_same by (unfold b11_kcell; lia). exact (HFSH i Hi).
- split; [exact (b11_keep_rconf B v pos lyc Sc Wc memc mdc _ _ _ HGEO HAR Hin EF KP HC5 HRC)|].
  split; [exact HCUR|]. split; [exact (b11_keep_nm v pos _ _ nm HGEO KP HNM)|]. split; [exact HCNT|].
  pose proof (b11_keep_slots v pos _ _ [(0xc0, pf_cur_ptr (p_c v) (Some gi))] HGEO KP
    ltac:(repeat constructor; cbn [fst]; lia) ltac:(unfold pf_sl; repeat constructor; exact HCURS)) as Hq.
  unfold pf_sl in Hq. exact (Forall_inv Hq).
- unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [exact Q10 | rewrite QK; [apply (b11_rg rX _ _ _ HRG); b11_in | b11_in]].
Qed.
End x.

(* the KOUT piece at every FP state *)
Theorem b11_kout_ok : forall (n : nat), (forall f1 : YK11.FPState, H_LOWOUT (fx := f1) B n) -> HA_KOUT n.
Proof. intros n L f1. exact (b11_kout (fx := f1) n (L f1)). Qed.
End d.
