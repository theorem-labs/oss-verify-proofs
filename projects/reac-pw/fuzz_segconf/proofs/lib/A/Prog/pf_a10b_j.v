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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 413 of its 483 lines of code are new or changed and 4983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a2.v, with its module names changed; 165 of its 260 lines of code are new or changed and 388 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the join piece of segment A10b of reac_segconf_parse_file's
   walk, pa10_j_ok : PA10_J B (lib/A/Prog/pf_a10b_k.v: HA_TAIL n -> H_JOIN n). Part of segment A10b's proof, by
   the G3 walk owner, 2026-10-30. proves no function (kind: segment lemma).
   The code (dis/reac_segconf_parse_file.fuzz_segconf.asan.s), JOIN 0x8888c .. 0x888b8, 11 instructions, no call,
   no inline check:
     0x8888c ld s3,0x98(s1)             s3 = slot 0x98 = SH + 8 (pf_pieces.PF_SL)
     0x88890 addi a0,zero,-8
     0x88894 .. 0x888b0 sb a0,0x54..0x57(s11); sb a0,0x50..0x53(s11)   low's eight shadow cells back to 0xf8
     0x888b4 j 0x88068                  TAIL
   The proof: a seed at JOIN (pj_seed: the slot 0x98 as a read-only region on s1's atom, the eight cells as a
   writable region on s11's atom), one run of the PLAIN executor to TAIL (the run writes shadow bytes:
   check_words_chain_s2.v:11-14), the eight bytes read back from the region, every other byte kept, and H_TAIL at
   the next line's offset. The cut's objects are carried across the run by segment A2's lib/A/Prog/pf_a2_g.v
   (pa2_geo, pa2_kept, pa2_keep_obj / _rconf / _saved / _flag): its write set pa2_Wr holds the frame's 144 shadow
   cells, so low's eight cells are inside it. pf_a5_k.v's keep lemmas do not apply to this run: their write set
   a5_Wrx does not hold low's cells (0x50 .. 0x57), which this run changes. No Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a10b_k pf_a2_g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pj_rreg, pj_clear_md and pj_cell_of_region come from segment A2's pf_a2.v) ---------- *)
Ltac pj_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pj_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* low's eight cells: 0x00 in PF_SC_LOW, 0xf8 in PF_SC_LINE; every other cell the same in both *)
Lemma pj_shb_line : forall i, 0x50 <= i < 0x58 -> pf_shb PF_SC_LINE i = 0xf8.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (pa2_zrange (fun i => pf_shb PF_SC_LINE i =? 0xf8) 0x50 8). vm_compute. reflexivity.
Qed.
Lemma pj_shb_same : forall i, ~ (0x50 <= i < 0x58) -> pf_shb PF_SC_LINE i = pf_shb PF_SC_LOW i.
Proof.
intros i Hi. unfold pf_shb, PF_SC_LINE, PF_SC_LOW. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|]. destruct (i <? 8); [reflexivity|].
destruct (i <? 72); [reflexivity|]. destruct (i <? 80) eqn:E80; [reflexivity|].
destruct (i <? 88) eqn:E88; [|reflexivity].
apply Z.ltb_ge in E80. apply Z.ltb_lt in E88. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let pj_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Lemma PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x20 <= fst ov <= 0xb8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ---------- reading a region the run wrote (pf_a2.v) ---------- *)
Definition pj_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma pj_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> pj_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.

(* ---------- the frame's shadow and the two objects pf_a2_g.v does not carry ---------- *)
Lemma pj_SHb : forall v pos, pa2_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.
(* the 19 slots s1 + 0x20 .. s1 + 0xb8 lie in the real stack, which the run does not write (pa2_Wr holds them, so
   pa2_kept does not give them) *)
Lemma pj_keep_sl : forall v pos (rd rd' : reader), pa2_geoP v pos ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> rd' a = rd a) ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' HG K H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
pose proof (PF_SL_offs v pos ov Hov) as Ho.
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
rewrite (rdword_ext rd rd'); [exact (H ov Hov)|].
intros k Hk. apply K. lia.
Qed.
(* cur_name, the frame's bytes 0x20 .. 0x30: outside pa2_Wr *)
Lemma pj_keep_nm : forall v pos (rd rd' : reader) nm, pa2_geoP v pos -> pa2_kept v pos rd rd' ->
  pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm HG K (f & Hb & Henc). exists f. split; [|exact Henc].
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pj_SHb v pos HG) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN in *.
rewrite (proj1 K (pf_F v pos + 0x20 + Z.of_nat i)); [exact (Hb i ltac:(lia)) | lia |].
unfold pa2_Wr, ESTACK. lia.
Qed.

(* ---------- the seed at JOIN (0x8888c) ---------- *)
(* every register its own atom; the slot 0x98 (SH + 8 as s11's atom + 8) read-only on s1's atom; low's eight
   shadow cells writable on s11's atom *)
Definition pj_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x98 0xa0 0 0 [YP09.mkChunk 0x98 (CVal 8 (SOff 27 8))];
   YP09.mkRegion (Some 27%nat) 0x50 0x58 0x50 0x58 []].
Definition pj_ss : sstate := mkSS PF_JOIN sr_atoms pj_regions None (mkFacts [] [] []).
Lemma pj_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc,
  pa2_geoP v pos ->
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) -> getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos) ->
  rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_SH v pos + 8) ->
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) pj_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_JOIN)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc HG R9 R27 W98 Hsh.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pj_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold pj_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pj_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x98 8 (SOff 27 8) (pf_SH v pos + 8)).
    * cbn [sv_denot]. rewrite U27. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W98).
  + rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hsh. lia.
- unfold pj_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U27. repeat split; lia.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ---------- the piece: JOIN -> TAIL ---------- *)
Lemma pj_join : forall n, HA_TAIL B n -> H_JOIN (fx := fx) B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi HI.
destruct HI as (HBASE & HMID & HST & HRG).
destruct HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (pa2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pj_SHb v pos HGEO) as (ESH & SH1 & SH2 & F8).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HRG0).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EF in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
pose proof asan_consts as (C1 & _).
unfold PF_RM in HRG.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pf_a5_k.a5_rg_get rX _ 9 _ HRG0); pa2_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (pf_SH v pos)) by (apply (pf_a5_k.a5_rg_get rX _ 27 _ HRG); pa2_in).
pose proof (proj1 (Forall_forall _ _) HSL (0x98, pf_SH v pos + 8) ltac:(unfold PF_SL; pa2_in)) as W98.
cbn [fst snd] in W98.
pose proof (pj_seed v pos Wc rX memc HGEO R9 R27 W98 (fun i Hi => proj1 (Hsh i Hi))) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pf_SH v pos)
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_JOIN)) with (Z_to_bv 64 (BASE + PF_JOIN)).
(* 0x8888c .. 0x888b4: the reload of s3, the eight shadow stores, the jump to TAIL *)
paj_run_to_sh pj_RUNTO HS HJ PF_TAIL.
{ intros a (r & Hr & Ha). unfold pj_ss, pj_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    rewrite U27 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
pj_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 0x50 <= a < pf_SH v pos + 0x58) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem pj_ss) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_SH v pos + 0x50 <= a < pf_SH v pos + 0x58) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U27 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
cbn [ms_mem restrict] in HR1.
assert (C8 : forall i, 0x50 <= i < 0x58 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0xf8).
{ intros i Hi. apply (pj_cell_of_region E (w_H Wc) (ms_mem ms) 27 _ _ _ _ _ _ i _ HR1 U27). revert i Hi.
  apply (pa2_zrange (fun i => pj_cell_ok _ i 0xf8) 0x50 8). vm_compute. reflexivity. }
assert (KP : pa2_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split.
  - intros a Ha Hn. apply K1; [exact Ha|]. intros Hw. apply Hn. unfold pa2_Wr. right; right. lia.
  - intros a _ Hv. exact (M1 a Hv). }
assert (KS : forall a, alloc_ceiling <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha; apply K1; lia).
(* the registers at TAIL: s3 reloaded, the rest the cut's *)
assert (Q19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (pf_SH v pos + 8)).
{ pj_rreg HS. cbn [sv_denot]. rewrite U27. reflexivity. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 22; 18; 24; 27; 21; 26; 20] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pj_rreg HS; rewrite pa2_crt_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx) end.
unfold pf_postm.
apply (TAIL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cfx (Some gi) nm (pf_next (p_s v) o) (ln + 1) d).
destruct HMID as (Ho & Hn & HCTX).
destruct HST as (HRC & HCUR & HNM & HCNT).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [|split; [exact HCTX|split; [|split]]].
- (* pf_base at PF_SC_LINE *)
  split; [exact HCX|].
  split.
  { split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split; [exact (pa2_keep_saved v pos _ _ _ HGEO KP HSAV)|].
    split; [exact (pa2_keep_flag v pos _ _ HGEO KP HFLAG)|].
    split; [exact HFRM|].
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (pf_a5_k.a5_rg_get rX _ _ _ HRG0); pa2_in | pa2_in]). }
  split; [exact (pa2_keep_obj B v pos lyc Sc Wc memc mdc _ _ HGEO HAR Hin EF KP HOBJ)|].
  split; [exact (pj_keep_sl v pos _ _ HGEO KS HSL)|].
  intros i Hi. destruct (Z_lt_le_dec i 0x50) as [Hlo | Hlo]; [|destruct (Z_lt_le_dec i 0x58) as [Hhi | Hhi]].
  + rewrite K1 by lia. rewrite pj_shb_same by lia. exact (HFSH i Hi).
  + rewrite (C8 i ltac:(lia)). rewrite pj_shb_line by lia. reflexivity.
  + rewrite K1 by lia. rewrite pj_shb_same by lia. exact (HFSH i Hi).
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
- split; [exact (pa2_keep_rconf B v pos lyc Sc Wc memc mdc _ _ _ HGEO HAR Hin EF KP HC5 HRC)|].
  split; [exact HCUR|]. split; [exact (pj_keep_nm v pos _ _ nm HGEO KP HNM)|]. exact HCNT.
- unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [exact Q19
          | change (pf_cur_ptr (p_c v) (Some gi)) with (seg_spec.rseg_addr (p_c v) gi);
            rewrite QK; [apply (pf_a5_k.a5_rg_get rX _ _ _ HRG); pa2_in | pa2_in]].
Qed.
End x.

(* the piece of pf_a10b_k.v at every FP state *)
Theorem pa10_j_ok : PA10_J B.
Proof. intros f0 n T. exact (pj_join (fx := f0) n T). Qed.
End d.
