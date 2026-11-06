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
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the LOWOUT piece
   of segment B11c of reac_segconf_parse_file's walk, b11_lowout : HA_TAIL n -> H_LOWOUT n (the second half of
   pf_pieces.v S_B11c). The B11c segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma).
   ADAPTED from the image-A G3 walk owner's image-A join piece lib/A/Prog/pf_a10b_j.v (commit c6f2a9302a3c,
   pj_join: a seed on the shadow cells, one run of the plain executor to TAIL, the cells read back, every other
   byte kept, H_TAIL at the next line's offset), re-derived on image B's code.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), LOWOUT 0x88c70 .. 0x88c7c, 4 instructions,
   no call, no inline check, no UBSan trap branch:
     0x88c70 sb a0,92(s5); 0x88c74 sb a0,93(s5); 0x88c78 sb a0,94(s5)   model low's three shadow cells (0x5c-0x5e)
                                                                         back to 0xf8 (a0 = -8, INV_LOWOUT)
     0x88c7c j 0x88600                                                   TAIL
   The seed: every register its own atom but a0, which is the literal 2 ^ 64 - 8 (INV_LOWOUT's a0 = -8, YCbn
   regs_ok_rereg), and the three cells a writable region on s5's atom (s5 = SH, PF_RL). Section hypotheses:
   none. *)
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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b11_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

(* ---------- the seed at LOWOUT (0x88c70) ---------- *)
(* every register its own atom but a0 = 2 ^ 64 - 8; model low's three shadow cells writable on s5's atom *)
Definition b11L_regions : smem := [YP09.mkRegion (Some 21%nat) 0x5c 0x5f 0x5c 0x5f []].
Definition b11L_ss : sstate :=
  mkSS PF_LOWOUT (sr_set sr_atoms 10%bv (SLit 18446744073709551608)) b11L_regions None (mkFacts [] [] []).
Lemma b11L_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc,
  b11_geoP v pos ->
  getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos) -> getr rX (Z_to_bv 5 10) = w64 (-8) ->
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b11L_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_LOWOUT)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc HG R21 R10 Hsh.
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & F8 & _).
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b11L_ss. apply pa_entry_st_ok_full.
- apply regs_ok_rereg; [subst E; apply regs_ok_Eimg_Ereg | reflexivity |].
  assert (E10 : (10%bv : bv 5) = Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  rewrite E10, R10. cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity.
- vm_compute. reflexivity.
- unfold b11L_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hsh. lia.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ---------- the piece: LOWOUT -> TAIL ---------- *)
Lemma b11_lowout : forall n, HA_TAIL B n -> H_LOWOUT (fx := fx) B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cf nm o ln d gi HI.
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
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (-8)) by (apply (b11_rg rX _ 10 _ HRG); b11_in).
pose proof (b11L_seed v pos Wc rX memc HGEO R21 R10 (fun i Hi => proj1 (Hsh i Hi))) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_LOWOUT)) with (Z_to_bv 64 (BASE + PF_LOWOUT)).
(* 0x88c70 .. 0x88c7c: the three shadow stores, the jump to TAIL *)
paj_run_to_sh b11_RUNTO HS HJ PF_TAIL.
{ intros a (r & Hr & Ha). unfold b11L_ss, b11L_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
  rewrite U21 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b11_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 0x5c <= a < pf_SH v pos + 0x5f) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem b11L_ss) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_SH v pos + 0x5c <= a < pf_SH v pos + 0x5f) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (C8 : forall i, 0x5c <= i < 0x5f -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0xf8).
{ intros i Hi. apply (b11_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR0 U21). revert i Hi.
  apply (b11_zrange (fun i => b11_cell_ok _ i 0xf8) 0x5c 3). vm_compute. reflexivity. }
assert (KP : b11_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split.
  - intros a Ha Hn. apply K1; [exact Ha|]. intros Hw. apply Hn. unfold b11_Wr. lia.
  - intros a _ Hv. exact (M1 a Hv). }
(* the registers at TAIL: those of the cut *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b11_rreg HS; rewrite b11_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx) end.
unfold pf_postm.
apply (TAIL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf (Some gi) nm (pf_next (p_s v) o) (ln + 1) d).
destruct HMID as (Ho & Hn & HCTX).
destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [|split; [exact HCTX|split; [|split]]].
- (* pf_base at PF_SC_LINE *)
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
  intros i Hi. destruct (Z_lt_le_dec i 0x5c) as [Hlo | Hlo]; [|destruct (Z_lt_le_dec i 0x5f) as [Hhi | Hhi]].
  + rewrite K1 by lia. rewrite b11_shb_line_same by lia. exact (HFSH i Hi).
  + rewrite (C8 i ltac:(lia)). rewrite b11_shb_line by lia. reflexivity.
  + rewrite K1 by lia. rewrite b11_shb_line_same by lia. exact (HFSH i Hi).
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
- split; [exact (b11_keep_rconf B v pos lyc Sc Wc memc mdc _ _ _ HGEO HAR Hin EF KP HC5 HRC)|].
  split; [exact HCUR|]. split; [exact (b11_keep_nm v pos _ _ nm HGEO KP HNM)|]. split; [exact HCNT|].
  pose proof (b11_keep_slots v pos _ _ [(0xc0, pf_cur_ptr (p_c v) (Some gi))] HGEO KP
    ltac:(repeat constructor; cbn [fst]; lia) ltac:(unfold pf_sl; repeat constructor; exact HCURS)) as Hq.
  unfold pf_sl in Hq. exact (Forall_inv Hq).
- unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b11_rg rX _ _ _ HRG); b11_in | b11_in]).
Qed.
End x.

(* the LOWOUT half of S_B11c at every FP state *)
Theorem b11_lowout_ok : forall (f0 : YK11.FPState) (n : nat), HA_TAIL B n -> H_LOWOUT (fx := f0) B n.
Proof. intros f0 n T. exact (b11_lowout (fx := f0) n T). Qed.
End d.
