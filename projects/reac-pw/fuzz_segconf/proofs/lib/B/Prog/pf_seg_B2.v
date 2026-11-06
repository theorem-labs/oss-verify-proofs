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
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3;
   the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s): segment B2 of
   reac_segconf_parse_file's walk (0x87edc .. 0x88074, 102 instructions, no conditional branch, one call, no
   instrumented check, no UBSan trap site), the theorem S_B2_holds : S_B2 B of lib/B/Prog/pf_pieces.v (the image-B piece statements at
   80a6c9c97a8b; FTAKEN -> FRAME). The B2 segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B2; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict none).
   ADAPTED from commit c181e576cd21 lib/A/Prog/pf_a2.v (image A, 0x87b24 .. 0x87cc4), re-derived
   on image B's code; closed against G3 FINAL at 6f783602b5e3 (lib/B/Prog/reac_segconf_parse_file_c.v, the B-kit copy lane).
   The code (BASE + AF_reac_segconf_parse_file = 0x87e38, SegList AF = 0x3078; offsets below from 0x87e38):
     0x87edc sd a0,136(s1) (slot 0x88 = F); 0x87ee0 sd a3,240(s1) (slot 0xf0 = F, never read); 0x87ee4 .. 0x87f14
     the frame header F + 0 / 8 / 16 (the magic 0x41b58ab3, the description .rodata 0x11b81, the pc 0x87e38) and
     0x87f10 sd a3,152(s1) (slot 0x98 = F); 0x87ef0 / 0x87f1c s5 = (a3 >> 3) + s4 = SH; 0x87ef4 s2 = -14, 0x87ef8
     s6 = -8, 0x87f18 a0 = -15; 0x87f20 .. 0x87f3c cells 0..7 (f8 f8 f2 f2 for cur_name, f1 f1 f1 f1); 0x87f48
     sd a0,216(s1) (slot 0xd8 = SH + 8); 0x87f4c jal __asan_set_shadow_f8 (meta_fill_f8 0x58b88; a0 = SH + 8,
     a1 = 0x40: buf's 64 cells); 0x87f50 .. 0x88070 cells 0x48..0x8f inline (f2 / f8, a0 = -13 at 0x88050 for f3).
   Counts against PLAN-pf-asanubsan.md section 5.2 row B2 (0x87edc-0x88074, 102 insns, 0 cond br, meta_fill_f8,
   no check, no trap): 29 instructions in the first run (0x87edc .. 0x87f4c, the call), 73 in the second
   (0x87f50 .. 0x88070) = 102; checks 0 / 0; UBSan trap sites 0 / 0 (none of the 34 branches to 0x891c8 lies in
   0x87edc .. 0x88074).
   Image B's differences from A2 (plan sections 1.1-1.3, 5.2, 7): F in a0 and a3 (A s7), the shadow base s4 (A s6),
   SH in s5 (A s11), the redzone values in s2 / s6 (A s2 / s5); the slots 0x88 / 0x98 = F and 0xd8 = SH + 8 (A 0x88 /
   0x98 = F / SH + 8), plus the dead slot 0xf0; c lives only in slot 0xc8 (pf_fi), which the segment keeps; the real
   frame 352 (s1 = (sp0 - 0x160) & -32). The 144 cell values are A's (plan section 1.3; pf_shb PF_SC0).
   The proof, in check_round_trip.v's frame-laying form (A2's): a run of the PLAIN symbolic executor from a seed at
   FTAKEN to the call (pb2_s1), the call by the step aj_set_shadow_atS (lib/B/Prog/pf_seg_B2_k.v, carried from
   check_round_trip_k.v through A's pf_a2_k.v), a second plain run from a fresh seed at 0x87f50 to FRAME (pb2_s2),
   and the cut's objects carried across both by pb2_kept (lib/B/Prog/pf_seg_B2_g.v). The one Section hypothesis is
   pf_pieces.v's for B2: aset_shadow_realizes (lib/B/Rt/RtShadow.v) at pa_sigma SS___asan_set_shadow_f8 (SegAddr
   0x58b88) with value 0xf8, at every FP state. Positional names: none from an image-A table (registers, slot
   offsets and cell indices are read off image B's excerpt; SS_ / AF_ are B's SegSyms / SegList names). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B2_k pf_seg_B2_g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- tactics ---------- *)
Ltac pb2_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pb2_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac pb2_inS := solve [cbn [In app]; repeat first [left; reflexivity | right]].
Ltac pb2_atom HS EE rX R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    pb2_rreg HS; rewrite pb2_crt_den_atom0; transitivity (getr rX (Z_to_bv 5 k));
    [apply EE; reflexivity | apply R; pb2_in] end.
Lemma pb2_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pb2_rg_sub : forall rX L L', pf_rg rX L -> (forall x, In x L' -> In x L) -> pf_rg rX L'.
Proof. intros rX L L' H Hs. unfold pf_rg in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hs x Hx)). Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASHF8 : forall fx0 : YK11.FPState,
  @aset_shadow_realizes fx0 rc SEGS B (pa_sigma SS___asan_set_shadow_f8) 0xf8.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let pb2_RUNP := SRr_run_pi_AJ B LAWS.
Let pb2_RUNC := SRr_run_pi_AJ_call B LAWS.
Let pb2_RUNTO := SRr_run_to_pi_AJ B LAWS.

(* ---------- reading a region the run wrote ---------- *)
Definition pb2_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma pb2_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> pb2_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
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
Lemma pb2_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.
Lemma pb2_shb_f8 : forall i, 8 <= i < 72 -> pf_shb PF_SC0 i = 0xf8.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (pb2_zrange (fun i => pf_shb PF_SC0 i =? 0xf8) 8 64). vm_compute. reflexivity.
Qed.
Lemma pb2_SHb : forall v pos, pb2_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\ pf_SH v pos + 256 <= 0x10007fff8000 /\
  pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.


(* ---------- the run from FTAKEN (0x87edc) to the call of __asan_set_shadow_f8 (0x87f4c, return 0x87f50) ---------- *)
(* every register its own atom, atom 32 the frame's shadow SH: the alias rewrites s5 = (a3 >> 3) + s4 to it, so the
   eight shadow stores (0x87f20-0x87f3c) land in the region on atom 32. The stores to s1 + N land in three regions on
   atom 9 (slots 0x88 / 0x98, 0xd8, 0xf0), so that c's slot 0xc8 stays outside every write window; the header in the
   region on atom 13 (a3 = F). *)
Definition pb2_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 13 0) (SLit 3)) (SOff 20 0).
Definition pb2_ss1 : sstate := mkSS (AF_reac_segconf_parse_file + 0xa4) sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x88 0xa0 0x88 0xa0 []; YP09.mkRegion (Some 9%nat) 0xd8 0xe0 0xd8 0xe0 [];
   YP09.mkRegion (Some 9%nat) 0xf0 0xf8 0xf0 0xf8 []; YP09.mkRegion (Some 13%nat) 0 24 0 24 [];
   YP09.mkRegion (Some 32%nat) 0 8 0 8 []] None
  (mkFacts [(13%nat, mkAF 4096 (2 ^ 47) 0)] [] [(pb2_shx, SOff 32 0)]).
Lemma pb2_seed1 : forall v pos lyc Sc Wc rX memc mdc, INV_FTAKEN B v pos lyc Sc Wc rX memc mdc ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (pf_SH v pos)])) pb2_ss1
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0xa4))) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc HI.
pose proof HI as (HCX & HFI & _ & _ & _ & _ & HRG).
destruct (pb2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pb2_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hpres.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & Hfb & Hsh).
rewrite EF in Hfb, Hsh. change (fs_frame_bytes 5) with 2048 in Hfb. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [w64 (pf_SH v pos)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (pf_SH v pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb2_rg rX _ 9 _ HRG0); pb2_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (pb2_rg rX _ 20 _ HRG0); pb2_in).
assert (R13 : getr rX (Z_to_bv 5 13) = w64 (pf_F v pos)) by (apply (pb2_rg rX _ 13 _ HRG); pb2_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = pf_F v pos)
  by (rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl), R13; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_SH v pos) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U13. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hfb (pf_F v pos + o) ltac:(lia))).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hsh o ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U13, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U13, Z.pow_0_r, Z.mod_1_r.
    repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. unfold pb2_shx. apply U_inj.
    rewrite U_SAlu, U_srl3.
    rewrite (U_atom E 13 (pf_F v pos) ltac:(rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl), R13; reflexivity) ltac:(lia)).
    rewrite (U_atom E 20 SHADOW_OFF ltac:(rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; reflexivity)
      ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom E 32 (pf_SH v pos) E32 ltac:(lia)).
    cbn [zalu_raw]. replace (pf_F v pos / 8 + SHADOW_OFF) with (pf_SH v pos) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.

(* the state after the call (0x87f50): the run's slots and cells 0..7, the fill's cells 8..0x47; s2 = -14 (0x87ef4),
   s6 = -8 (0x87ef8), s5 = SH (0x87f1c), callee-saved across the fill *)
Definition PB2_R1 (v : pfv) (pos : Z) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF);
   (18, 2 ^ 64 - 14); (22, 2 ^ 64 - 8); (21, pf_SH v pos); (19, p_lp v); (27, p_t v)].
Definition pb2_MID (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memA : word -> option byte)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  pb2_kept v pos (rdW Wc memA) (rdW Wc memc) /\
  rdword (rdW Wc memc) (pf_s1 v + 0x88) = Some (pf_F v pos) /\
  rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_F v pos) /\
  rdword (rdW Wc memc) (pf_s1 v + 0xd8) = Some (pf_SH v pos + 8) /\
  (forall i, 0 <= i < 72 -> rdW Wc memc (pf_SH v pos + i) = Some (pf_shb PF_SC0 i)) /\
  pf_rg rX (PB2_R1 v pos).
Lemma pb2_s1 : forall v pos lyc Sc Wc rX memc mdc (Q : world SEGS -> config -> Prop),
  INV_FTAKEN B v pos lyc Sc Wc rX memc mdc ->
  (forall rX1 memc1 mdc1, pb2_MID v pos lyc Sc Wc memc rX1 memc1 mdc1 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x118)) rX1 memc1 mdc1) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FTAKEN) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc rX memc mdc Q HI Kc.
pose proof HI as (HCX & HFI & _ & _ & _ & _ & HRG).
destruct (pb2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pb2_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HCX as (_ & _ & _ & Hc0 & _ & Ht0 & _ & Hl0 & _).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof asan_consts as (C1 & _).
pose proof (pb2_seed1 v pos lyc Sc Wc rX memc mdc HI) as HS.
set (E := Eimg (Ereg rX [w64 (pf_SH v pos)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (pf_SH v pos))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (RA : forall r val, In (r, val) [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (20, SHADOW_OFF)] -> getr rX (Z_to_bv 5 r) = w64 val) by (intros r val H; exact (pb2_rg rX _ r val HRG0 H)).
assert (RB : forall r val, In (r, val) [(10, pf_F v pos); (13, pf_F v pos); (19, p_lp v); (27, p_t v)] ->
    getr rX (Z_to_bv 5 r) = w64 val) by (intros r val H; exact (pb2_rg rX _ r val HRG H)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (RA 9 _ ltac:(pb2_in)); unfold w64; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = pf_F v pos)
  by (rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl), (RB 13 _ ltac:(pb2_in)); unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_SH v pos) by (rewrite E32; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_FTAKEN)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0xa4))).
paj_run_shc pb2_RUNP pb2_RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold pb2_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite U9 in Ha. rewrite ESTK. lia.
  - left. rewrite U9 in Ha. rewrite ESTK. lia.
  - left. rewrite U9 in Ha. rewrite ESTK. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5) with 2048. rewrite U13 in Ha. lia.
  - right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
    rewrite U32 in Ha. lia. }
pb2_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ pb2_Wr v pos a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem pb2_ss1) (w_H Wc) memc (ms_mem ms) (pb2_Wr v pos) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin'];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U13, ?U32 in Hrr; unfold pb2_Wr, ESTACK; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG0 Hv)).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4 end.
cbn [ms_mem restrict] in HR0, HR1, HR4.
assert (W88 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 136) = Some (pf_F v pos)).
{ eapply (pb2_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 136 (SOff 10 0) (pf_F v pos) HR0 U9);
    [pb2_in | | lia].
  rewrite pb2_crt_den_atom0, (EE 10%nat (Z_to_bv 5 10) eq_refl), (RB 10 _ ltac:(pb2_in)). reflexivity. }
assert (W98 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 152) = Some (pf_F v pos)).
{ eapply (pb2_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 152 (SOff 13 0) (pf_F v pos) HR0 U9);
    [pb2_in | | lia].
  rewrite pb2_crt_den_atom0, (EE 13%nat (Z_to_bv 5 13) eq_refl), (RB 13 _ ltac:(pb2_in)). reflexivity. }
assert (WD8 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 216) = Some (pf_SH v pos + 8)).
{ eapply (pb2_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 216 (SOff 32 8) (pf_SH v pos + 8) HR1 U9);
    [pb2_in | | lia].
  exact (pb2_den_off E 32 (pf_SH v pos) 8 E32 ltac:(lia)). }
assert (C0 : forall i, 0 <= i < 8 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some (pf_shb PF_SC0 i)).
{ intros i Hi. apply (pb2_cell_of_region E (w_H Wc) (ms_mem ms) 32 _ _ _ _ _ _ i _ HR4 U32). revert i Hi.
  apply (pb2_zrange (fun i => pb2_cell_ok _ i (pf_shb PF_SC0 i)) 0 8). vm_compute. reflexivity. }
(* the registers at the call *)
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + 12688)) by (pb2_rreg HS; apply (codeptr_val _ 12688 HEI)).
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_SH v pos + 8))
  by (pb2_rreg HS; exact (pb2_den_off E 32 (pf_SH v pos) 8 E32 ltac:(lia))).
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 64) by (pb2_rreg HS; reflexivity).
assert (QA : forall r val, In (r, val) [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v);
    (20, SHADOW_OFF)] -> getr (ms_regs ms) (Z_to_bv 5 r) = w64 val).
{ intros r val Hr. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-; pb2_atom HS EE rX RA |]). destruct Hr. }
assert (QB : forall r val, In (r, val) [(19, p_lp v); (27, p_t v)] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = w64 val).
{ intros r val Hr. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [injection Hr as <- <-; pb2_atom HS EE rX RB |]). destruct Hr. }
assert (Q18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (2 ^ 64 - 14)) by (pb2_rreg HS; reflexivity).
assert (Q22 : getr (ms_regs ms) (Z_to_bv 5 22) = w64 (2 ^ 64 - 8)) by (pb2_rreg HS; reflexivity).
assert (Q21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (pb2_rreg HS; rewrite pb2_crt_den_atom0; exact E32).
assert (Q2 := QA 2 _ ltac:(pb2_in)). assert (Q3 := QA 3 _ ltac:(pb2_in)). assert (Q4 := QA 4 _ ltac:(pb2_in)).
pmkst HS.
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (pa_sigma SS___asan_set_shadow_f8) 0xf8 (ASHF8 fx) Wc
    (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 12688)) 5 pos
    (pf_SH v pos + 8) 64 HJ).
  - left. reflexivity.
  - unfold spZ. match goal with |- context [getr (ms_regs ms) ?r] => rewrite (pb2_bvr (ms_regs ms) r 2 _ eq_refl Q2) end.
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (pb2_m16 _ _ S6 S3).
  - lia.
  - rewrite ESTK. unfold ESTACK. lia.
  - apply (pb2_bvr _ _ 3); [reflexivity | exact Q3].
  - apply (pb2_bvr _ _ 4); [reflexivity | exact Q4].
  - apply (pb2_bvr _ _ 1); [reflexivity | exact Q1].
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (pb2_bvr _ _ 10); [reflexivity | exact Q10].
  - apply (pb2_bvr _ _ 11); [reflexivity | exact Q11].
  - lia.
  - rewrite EF. change (shadow_addr (pf_F v pos)) with (pf_SH v pos). lia.
  - rewrite EF. change (shadow_addr (pf_F v pos)) with (pf_SH v pos). change (fs_frame_bytes 5 / 8) with 256. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hval & HK2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HK2 by lia.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 12688)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x118)) regs2 mem2 md2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite ESTK in Hpres2.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ pb2_Wr v pos a -> rdW Wc mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hn. apply (HK2 a Ha); intros Hq; apply Hn; unfold pb2_Wr, ESTACK in *; lia. }
apply Kc. split; [exact HJ2|].
split.
{ split.
  - intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
  - intros a Ha Hv.
    destruct (Z_lt_le_dec a (pf_SH v pos + 8)) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec a (pf_SH v pos + 72)) as [Hhi | Hhi]].
    + destruct (Z_lt_le_dec a (pf_s1 v - ESTACK)) as [Hs1 | Hs1];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hs2 | Hs2]].
      * rewrite (HK2 a Ha) by (unfold ESTACK in *; lia). exact (M1 a Hv).
      * apply (aview_some_of_apresent SEGS). apply Hpres2. unfold ESTACK in *. lia.
      * rewrite (HK2 a Ha) by (unfold ESTACK in *; lia). exact (M1 a Hv).
    + replace a with (pf_SH v pos + 8 + (a - (pf_SH v pos + 8))) by lia. rewrite Hval by lia. discriminate.
    + destruct (Z_lt_le_dec a (pf_s1 v - ESTACK)) as [Hs1 | Hs1];
      [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hs2 | Hs2]].
      * rewrite (HK2 a Ha) by (unfold ESTACK in *; lia). exact (M1 a Hv).
      * apply (aview_some_of_apresent SEGS). apply Hpres2. unfold ESTACK in *. lia.
      * rewrite (HK2 a Ha) by (unfold ESTACK in *; lia). exact (M1 a Hv). }
split.
{ rewrite (rdword_ext (rdW Wc (ms_mem ms)) (rdW Wc mem2)); [exact W88|].
  intros k Hk. apply HK2; unfold ESTACK; lia. }
split.
{ rewrite (rdword_ext (rdW Wc (ms_mem ms)) (rdW Wc mem2)); [exact W98|].
  intros k Hk. apply HK2; unfold ESTACK; lia. }
split.
{ rewrite (rdword_ext (rdW Wc (ms_mem ms)) (rdW Wc mem2)); [exact WD8|].
  intros k Hk. apply HK2; unfold ESTACK; lia. }
split.
{ intros i Hi. destruct (Z_lt_le_dec i 8) as [H8 | H8].
  - rewrite (HK2 (pf_SH v pos + i)) by (unfold ESTACK; lia). exact (C0 i ltac:(lia)).
  - rewrite (pb2_shb_f8 i ltac:(lia)). replace (pf_SH v pos + i) with (pf_SH v pos + 8 + (i - 8)) by lia.
    apply Hval. lia. }
unfold pf_rg, PB2_R1. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  rewrite HP2 by (unfold acallee_saved; lia);
  first [apply QA; pb2_inS | apply QB; pb2_inS | assumption].
Qed.

(* ---------- the inline cells 0x48 .. 0x8f (0x87f50 .. 0x88070): the run to FRAME (0x88074) ---------- *)
(* s2 = -14 and s6 = -8 pinned to the literals the fill kept; the 72 stores through s5 = SH land in the region on
   atom 21 *)
Definition pb2_ss2 : sstate := mkSS (AF_reac_segconf_parse_file + 0x118)
  (sr_set (sr_set sr_atoms (Z_to_bv 5 18) (SLit (2 ^ 64 - 14))) (Z_to_bv 5 22) (SLit (2 ^ 64 - 8)))
  [YP09.mkRegion (Some 21%nat) 0x48 0x90 0x48 0x90 []] None (mkFacts [] [] []).
Definition PB2_R2 (v : pfv) (pos : Z) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF);
   (21, pf_SH v pos); (19, p_lp v); (27, p_t v)].
Definition pb2_FIN (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memA : word -> option byte)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  pb2_kept v pos (rdW Wc memA) (rdW Wc memc) /\
  rdword (rdW Wc memc) (pf_s1 v + 0x88) = Some (pf_F v pos) /\
  rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_F v pos) /\
  rdword (rdW Wc memc) (pf_s1 v + 0xd8) = Some (pf_SH v pos + 8) /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC0 /\
  pf_rg rX (PB2_R2 v pos).
Lemma pb2_s2 : forall v pos lyc Sc Wc memA rX memc mdc (Q : world SEGS -> config -> Prop),
  pb2_geoP v pos -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pb2_MID v pos lyc Sc Wc memA rX memc mdc ->
  (forall rX2 memc2 mdc2, pb2_FIN v pos lyc Sc Wc memA rX2 memc2 mdc2 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + PF_FRAME) rX2 memc2 mdc2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x118)) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc memA rX memc mdc Q HG Hin EF (HJ & HK & HW88 & HW98 & HWD8 & HSH & HRG) Kc.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pb2_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & _).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EF in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (R : forall r val, In (r, val) (PB2_R1 v pos) -> getr rX (Z_to_bv 5 r) = w64 val)
  by (intros r val H; exact (pb2_rg rX _ r val HRG H)).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), (R 21 _ ltac:(unfold PB2_R1; pb2_in)); unfold w64;
      apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pb2_ss2
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x118))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS (AF_reac_segconf_parse_file + 0x118) sr_atoms
    [YP09.mkRegion (Some 21%nat) 0x48 0x90 0x48 0x90 []] None (mkFacts [] [] []))
    (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x118))) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U21.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hsh o ltac:(lia))).
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [exact I | split; exact I]. }
  pose proof (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 18) (2 ^ 64 - 14) HS0 (R 18 _ ltac:(unfold PB2_R1; pb2_in)) eq_refl) as HS1.
  exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 22) (2 ^ 64 - 8) HS1 (R 22 _ ltac:(unfold PB2_R1; pb2_in)) eq_refl). }
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x118)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x118))).
paj_run_to_sh pb2_RUNTO HS HJ (AF_reac_segconf_parse_file + 0x23c).
{ intros a (r & Hr & Ha). unfold pb2_ss2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
  rewrite U21 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG0, HF.
pb2_clear_md.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 72 <= a < pf_SH v pos + 144) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem pb2_ss2) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_SH v pos + 72 <= a < pf_SH v pos + 144) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21 in Hrr; lia |]).
  destruct Hin'. }
assert (M3 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG0 Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (C2 : forall i, 72 <= i < 144 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some (pf_shb PF_SC0 i)).
{ intros i Hi. apply (pb2_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR0 U21). revert i Hi.
  apply (pb2_zrange (fun i => pb2_cell_ok _ i (pf_shb PF_SC0 i)) 72 72). vm_compute. reflexivity. }
assert (QR : forall r val, In (r, val) (PB2_R1 v pos) -> r <> 18 -> r <> 22 ->
    getr (ms_regs ms) (Z_to_bv 5 r) = w64 val).
{ intros r val Hr N18 N22. unfold PB2_R1 in Hr, R. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr];
    [injection Hr as <- <-; first [exfalso; lia | pb2_atom HS EE rX R] |]). destruct Hr. }
pmkst HS.
change (Z_to_bv 64 (BASE + 12980)) with (w64 (BASE + PF_FRAME)).
apply Kc. split; [exact HJ|].
split.
{ apply (pb2_kept_trans v pos _ (rdW Wc memc)); [exact HK|]. split.
  - intros a Ha Hn. apply K3; [exact Ha|]. intros Hq. apply Hn. unfold pb2_Wr. lia.
  - intros a _ Hv. exact (M3 a Hv). }
split.
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [exact HW88|].
  intros k Hk. apply K3; lia. }
split.
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [exact HW98|].
  intros k Hk. apply K3; lia. }
split.
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [exact HWD8|].
  intros k Hk. apply K3; lia. }
split.
{ intros i Hi. destruct (Z_lt_le_dec i 72) as [H72 | H72].
  - rewrite K3 by lia. exact (HSH i ltac:(lia)).
  - exact (C2 i ltac:(lia)). }
unfold pf_rg, PB2_R2. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  (apply QR; [unfold PB2_R1; pb2_inS | lia | lia]).
Qed.

(* ---------- the segment ---------- *)
Lemma pb2_main : H_FRAME B -> H_FTAKEN B.
Proof.
intros HF v pos lyc Sc Wc rX memc mdc HI.
pose proof HI as (HCX & HFI & HOBJ & HLAB & HRC & _ & _).
destruct (pb2_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ0 & Hly & HSc & HPm & HSAV & HFL & HFRM & HTF & HC8 & HRG0).
apply (pb2_s1 v pos lyc Sc Wc rX memc mdc _ HI).
intros rX1 memc1 mdc1 HM.
apply (pb2_s2 v pos lyc Sc Wc memc rX1 memc1 mdc1 _ HG Hin EF HM).
intros rX2 memc2 mdc2 (HJ2 & HK2 & HW88 & HW98 & HWD8 & HSH & HRG2).
apply (HF v pos lyc Sc Wc rX2 memc2 mdc2).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [exact HCX|].
split.
{ split; [exact HJ2|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPm|].
  split; [exact (pb2_keep_saved v pos _ _ _ HG HK2 HSAV)|].
  split; [exact (pb2_keep_flag v pos _ _ HG HK2 HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [exact (pb2_keep_c8 v pos _ _ _ HG HK2 HC8)|].
  apply (pb2_rg_sub _ _ _ HRG2). intros x Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [unfold PB2_R2; pb2_in |]). destruct Hx. }
split; [exact (pb2_keep_obj B v pos lyc Sc Wc memc mdc _ _ HG HAR Hin EF HK2 HOBJ)|].
split; [exact (pb2_keep_lab B v pos lyc Sc Wc memc mdc _ _ HG HAR Hfrs EF Hly HPm HCX HK2 HLAB)|].
split; [exact (pb2_keep_rconf B v pos lyc Sc Wc memc mdc _ _ _ HG HAR Hin EF HK2 HC5 HRC)|].
split; [unfold pf_sl; repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption|].
split; [exact HSH|].
apply (pb2_rg_sub _ _ _ HRG2). intros x Hx. cbn [In] in Hx.
repeat (destruct Hx as [<- | Hx]; [unfold PB2_R2; pb2_in |]). destruct Hx.
Qed.
End x.

(* the segment statement of pf_pieces.v at every FP state *)
Theorem S_B2_holds : S_B2 B.
Proof. intros f0 HF. exact (pb2_main (fx := f0) (HF f0)). Qed.
End d.
