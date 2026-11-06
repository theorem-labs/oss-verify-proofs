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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B2.v; 387 of its 493 lines of code are new or changed and 390 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the join piece of
   segment B10b of reac_segconf_parse_file's walk, pb10_j_ok : PB10_J B (lib/B/Prog/pf_seg_B10b_k.v:
   HA_TAIL n -> H_JOIN n). The B10b segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment lemma of
   reac_segconf_parse_file's walk, piece PB10_J of segment B10b).
   ADAPTED from a working branch's lib/A/Prog/pf_a10b_j.v (a B10b sub-lane, b0c590d766e1), re-derived on
   image B's code: B's join stores through s5 (A: s11) and does not reload s3 (A: `ld s3,0x98(s1)`); B's frame
   is 352 bytes (s1 in [sp0 - 368, sp0 - 352]; A: 320), STK 12832 (A: 12800); B's PF_SL has 23 slots at
   s1 + 0x00 .. 0xd8 (A: 0x20 .. 0xb8); B's pf_fi carries c's slot 0xc8 and s4 = SHADOW_OFF (A: s6), B's pf_st
   cur's slot 0xc0. The reader-keeping lemmas are A's (the image-A A2 segment lane's pf_a2_g.v form) with the write set the
   frame's 144 shadow cells.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), JOIN 0x88dc8 .. 0x88dec, 10 instructions,
   no call, no inline check, no UBSan trap:
     0x88dc8 li a0,-8
     0x88dcc .. 0x88de8 sb a0,84..87(s5); sb a0,80..83(s5)   low's eight shadow cells 0x50 .. 0x57 back to 0xf8
     0x88dec j 0x88600                                        TAIL
   The proof: a seed at JOIN (b10j_seed: every register its own atom, the eight cells as a writable region on
   s5's atom), one run of the PLAIN executor to TAIL, the eight bytes read back from the region, every other byte
   kept (the cut's objects by b10j_keep_*: each is an application, stack or image byte, and its shadow is not one
   of low's cells), and H_TAIL at the next line's offset. No Section hypothesis. *)
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
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic and small tools (A's pf_a10b_j.v, from pf_a2_g.v / pf_a2.v of the image-A A2 segment lane) ---------- *)
Lemma b10j_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b10j_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* a byte outside an 8-aligned range [F, F + 2048) has its shadow outside the range's 256 cells *)
Lemma b10j_granule : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 2048) -> 0 <= x ->
  ~ (F / 8 <= x / 8 < F / 8 + 256).
Proof.
intros F x HF Hx H0 [H1 H2]. apply Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. rewrite HF in DF. lia.
Qed.
Lemma b10j_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b10j_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Lemma b10j_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Ltac b10j_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b10j_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b10j_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* low's eight cells: 0x00 in PF_SC_LOW, 0xf8 in PF_SC_LINE; every other cell the same in both *)
Lemma b10j_shb_line : forall i, 0x50 <= i < 0x58 -> pf_shb PF_SC_LINE i = 0xf8.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b10j_zrange (fun i => pf_shb PF_SC_LINE i =? 0xf8) 0x50 8). vm_compute. reflexivity.
Qed.
Lemma b10j_shb_same : forall i, ~ (0x50 <= i < 0x58) -> pf_shb PF_SC_LINE i = pf_shb PF_SC_LOW i.
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
Let b10j_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Lemma b10j_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x00 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.


(* ---------- reading a region the run wrote (pf_a2.v) ---------- *)
Definition b10j_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma b10j_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> b10j_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
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

(* ---------- the geometry at JOIN and what the run keeps (pf_a2_g.v, write set = the 144 shadow cells) ---------- *)
Definition b10j_Wr (v : pfv) (pos a : Z) : Prop := pf_SH v pos <= a < pf_SH v pos + 144.
Definition b10j_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ b10j_Wr v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Definition b10j_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b10j_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b10j_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b10j_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b10j_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold b10j_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma b10j_SHb : forall v pos, b10j_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b10j_geoP v pos.
(* a byte the run never touches, nor its shadow cell: below the allocator's ceiling, an application byte, and
   outside the class-5 frame *)
Definition b10j_out (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
Lemma b10j_out_nw : forall x, b10j_out x ->
  0 <= x < 2 ^ 64 /\ ~ b10j_Wr v pos x /\ 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b10j_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx2 & Hx3).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (b10j_granule (pf_F v pos) x F8 Hx3 ltac:(lia)) as Gr.
unfold b10j_Wr, pf_SH, shadow_addr, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.
Lemma b10j_out_img : forall x, 0x10000 <= x < kImgEnd -> b10j_out x.
Proof.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1). pose proof asan_consts as (C1 & _).
unfold kImgEnd in *. split; [lia|]. split; [lia|]. exact (I1 x Hx).
Qed.
Lemma b10j_out_inimg : forall x, in_img SEGS x -> b10j_out x.
Proof. intros x Hx. apply b10j_out_img. exact (pa_img_range x Hx). Qed.
(* the real stack (the saved registers, the slots) and the class-5 frame's own bytes are outside the cells *)
Lemma b10j_stack_nw : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ b10j_Wr v pos a.
Proof.
intros a Ha. destruct (b10j_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
unfold b10j_Wr. lia.
Qed.
Lemma b10j_frame_nw : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> 0 <= a < 2 ^ 64 /\ ~ b10j_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b10j_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (C1 & _).
unfold b10j_Wr. lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : b10j_kept v pos rd rd'.
Lemma b10j_k_byte : forall x, b10j_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (b10j_out_nw x Hx) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma b10j_k_shadow : forall x, b10j_out x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (b10j_out_nw x Hx) as (_ & _ & H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma b10j_k_zs : forall p l, (forall i, (i < length l)%nat -> b10j_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b10j_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b10j_k_bytes : forall p l, (forall i, (i < length l)%nat -> b10j_out (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b10j_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b10j_k_rdword : forall a, (forall k, 0 <= k < 8 -> b10j_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (b10j_k_byte _ (Ho k Hk)). Qed.
Lemma b10j_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma b10j_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b10j_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> b10j_out x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (b10j_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (b10j_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma b10j_k_addr : forall q n, (forall x, q <= x < q + n -> b10j_out x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (b10j_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b10j_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b10j_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b10j_k_str a s); [|exact Hs]. intros x Hx. apply b10j_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma b10j_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b10j_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (b10j_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply b10j_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b10j_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b10j_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply b10j_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply b10j_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b10j_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> b10j_out (a + k))
  by (intros a Ha k Hk; apply b10j_out_img; lia).
split; [rewrite (b10j_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b10j_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* a range inside a live heap block of the cut's state lies outside the frame *)
Lemma b10j_out_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc b m x,
  b10j_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> b10j_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold b10j_out. lia.
Qed.
Lemma b10j_out_sa_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  b10j_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_heap B lyc Sc q n -> q <= x < q + n -> b10j_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc q n x HG HAR Hin EF (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
apply (b10j_out_heap v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb). lia.
Qed.

(* ---------- the cut's objects, carried across the run ---------- *)
Lemma b10j_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  b10j_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b10j_kept v pos rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR Hin EF K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> b10j_out v pos x)
  by (intros x Hx; exact (b10j_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H3 Hx)).
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> b10j_out v pos x)
  by (intros x Hx; exact (b10j_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H5 Hx)).
split; [apply (b10j_k_str v pos HG rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (b10j_k_addr v pos HG rd rd' K _ _ Ht H2)|]. split; [exact H3|].
split; [exact (b10j_k_addr v pos HG rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (b10j_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (b10j_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (b10j_k_rod v pos HG rd rd' K H8) | exact (b10j_k_ssp v pos HG rd rd' K H9)].
Qed.
Lemma b10j_keep_rconf : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf,
  b10j_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b10j_kept v pos rd rd' -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf HG HAR Hin EF K Hh (bs & Hb & Henc).
exists bs. split; [|exact Henc]. apply (b10j_k_bytes v pos HG rd rd' K); [|exact Hb].
intros i Hi. destruct Henc as [Hl _].
apply (b10j_out_sa_heap v pos lyc Sc Wc memc mdc _ _ _ HG HAR Hin EF Hh). lia.
Qed.
Lemma b10j_keep_saved : forall v pos rd rd' regs, b10j_geoP v pos -> b10j_kept v pos rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs HG K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof HG as (S1 & S2 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (proj1 K); [lia|]. apply (b10j_stack_nw v pos HG). lia.
Qed.
Lemma b10j_keep_flag : forall v pos rd rd', b10j_geoP v pos -> b10j_kept v pos rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos rd rd' HG K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (b10j_frame_nw v pos HG (pf_F v pos + 2048 - 8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma b10j_keep_sl : forall v pos rd rd', b10j_geoP v pos -> b10j_kept v pos rd rd' ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' HG K H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
pose proof (b10j_PF_SL_offs v pos ov Hov) as Ho.
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
rewrite (rdword_ext rd rd'); [exact (H ov Hov)|].
intros k Hk. apply (proj1 K); [lia|]. apply (b10j_stack_nw v pos HG). lia.
Qed.
Lemma b10j_keep_nm : forall v pos rd rd' nm, b10j_geoP v pos -> b10j_kept v pos rd rd' ->
  pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm HG K (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN.
destruct (b10j_frame_nw v pos HG (pf_F v pos + 0x20 + Z.of_nat i) ltac:(lia)) as (H0 & H1).
rewrite (proj1 K _ H0 H1). exact (Hb i ltac:(lia)).
Qed.


(* ---------- the seed at JOIN (0x88dc8) ---------- *)
(* every register its own atom; low's eight shadow cells writable on s5's atom (x21 = SH, PF_RL) *)
Definition b10j_regions : smem := [YP09.mkRegion (Some 21%nat) 0x50 0x58 0x50 0x58 []].
Definition b10j_ss : sstate := mkSS PF_JOIN sr_atoms b10j_regions None (mkFacts [] [] []).
Lemma b10j_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc,
  b10j_geoP v pos ->
  getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos) ->
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b10j_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_JOIN)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc HG R21 Hsh.
destruct (b10j_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b10j_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b10j_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hsh. lia.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* the slots of the real frame s1 + 0x00 .. 0xd8 (pf_fi's 0xc8, pf_st's 0xc0, PF_SL) are not shadow cells *)
Lemma b10j_keep_slot : forall v pos rd rd' off w, b10j_geoP v pos -> b10j_kept v pos rd rd' ->
  0 <= off <= 0xd8 -> rdword rd (pf_s1 v + off) = Some w -> rdword rd' (pf_s1 v + off) = Some w.
Proof.
intros v pos rd rd' off w HG K Ho H. rewrite (rdword_ext rd rd'); [exact H|].
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (proj1 K); [lia|]. apply (b10j_stack_nw v pos HG). lia.
Qed.

(* ---------- the piece: JOIN -> TAIL ---------- *)
Lemma b10j_join : forall n, HA_TAIL B n -> H_JOIN (fx := fx) B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi HI.
destruct HI as (HBASE & HMID & HST & HRG).
destruct HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10j_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b10j_SHb v pos HGEO) as (ESH & SH1 & SH2 & F8).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & _ & Hsh).
rewrite EF in Hsh. change (fs_frame_bytes 5 / 8) with 256 in Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
pose proof asan_consts as (C1 & _).
unfold PF_RL, PF_RM in HRG.
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (b10j_rg rX _ 21 _ HRG); b10j_in).
pose proof (b10j_seed v pos Wc rX memc HGEO R21 (fun i Hi => proj1 (Hsh i Hi))) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_JOIN)) with (Z_to_bv 64 (BASE + PF_JOIN)).
(* 0x88dc8 .. 0x88dec: a0 = -8, the eight shadow stores, the jump to TAIL *)
paj_run_to_sh b10j_RUNTO HS HJ PF_TAIL.
{ intros a (r & Hr & Ha). unfold b10j_ss, b10j_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
  rewrite U21 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG, HF.
b10j_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 0x50 <= a < pf_SH v pos + 0x58) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem b10j_ss) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_SH v pos + 0x50 <= a < pf_SH v pos + 0x58) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (C8 : forall i, 0x50 <= i < 0x58 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0xf8).
{ intros i Hi. apply (b10j_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR0 U21). revert i Hi.
  apply (b10j_zrange (fun i => b10j_cell_ok _ i 0xf8) 0x50 8). vm_compute. reflexivity. }
assert (KP : b10j_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split.
  - intros a Ha Hn. apply K1; [exact Ha|]. intros Hw. apply Hn. unfold b10j_Wr. lia.
  - intros a _ Hv. exact (M1 a Hv). }
(* the registers at TAIL: a0 = -8, the rest the cut's *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10j_rreg HS; rewrite b10j_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx) end.
unfold pf_postm.
apply (TAIL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cfx (Some gi) nm (pf_next (p_s v) o) (ln + 1) d).
destruct HMID as (Ho & Hn & HCTX).
destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [|split; [exact HCTX|split; [|split]]].
- (* pf_base at PF_SC_LINE *)
  split; [exact HCX|].
  split.
  { split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split; [exact (b10j_keep_saved v pos _ _ _ HGEO KP HSAV)|].
    split; [exact (b10j_keep_flag v pos _ _ HGEO KP HFLAG)|].
    split; [exact HFRM|]. split; [exact HTF|].
    split.
    { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
      exact (b10j_keep_slot v pos _ _ 0xc8 _ HGEO KP ltac:(lia) HC8). }
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b10j_rg rX _ _ _ HRG0); b10j_in | b10j_in]). }
  split; [exact (b10j_keep_obj v pos lyc Sc Wc memc mdc _ _ HGEO HAR Hin EF KP HOBJ)|].
  split; [exact (b10j_keep_sl v pos _ _ HGEO KP HSL)|].
  intros i Hi. destruct (Z_lt_le_dec i 0x50) as [Hlo | Hlo]; [|destruct (Z_lt_le_dec i 0x58) as [Hhi | Hhi]].
  + rewrite K1 by lia. rewrite b10j_shb_same by lia. exact (HFSH i Hi).
  + rewrite (C8 i ltac:(lia)). rewrite b10j_shb_line by lia. reflexivity.
  + rewrite K1 by lia. rewrite b10j_shb_same by lia. exact (HFSH i Hi).
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
- split; [exact (b10j_keep_rconf v pos lyc Sc Wc memc mdc _ _ _ HGEO HAR Hin EF KP HC5 HRC)|].
  split; [exact HCUR|]. split; [exact (b10j_keep_nm v pos _ _ nm HGEO KP HNM)|]. split; [exact HCNT|].
  exact (b10j_keep_slot v pos _ _ 0xc0 _ HGEO KP ltac:(lia) HC0).
- unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b10j_rg rX _ _ _ HRG); b10j_in | b10j_in]).
Qed.
End x.

(* the piece of pf_seg_B10b_k.v at every FP state *)
Theorem pb10_j_ok : PB10_J B.
Proof. intros f0 n T. exact (b10j_join (fx := f0) n T). Qed.
End d.
