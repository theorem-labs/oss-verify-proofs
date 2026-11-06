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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 521 of its 608 lines of code are new or changed and 4966 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B8b_s.v; 382 of its 484 lines of code are new or changed and 506 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the JOIN piece of
   segment B8b of reac_segconf_parse_file's walk, pb8b_join_holds : forall n, HA_TAIL B n -> H_B8B_JOIN B n
   (lib/B/Prog/pf_seg_B8b_d.v's INV_B8B_JOIN / H_B8B_JOIN at 0x88f00). A B8b sub-lane of the image-B G3 walk owner,
   2026-10-30. proves function reac_segconf_parse_file (segment B8b, piece JOIN -> TAIL; reuse search and CONFIRM:
   the rule-24 lookup record, verdict none).
   ADAPTED from a working branch (an image-A segment lane: pf_a8b_m.v pfa8b_rconf_seengen / pfa8b_cstr_splice0 /
   pfa8b_snprintf_name16, ported as pf_seg_B8b_m.v's pb8b_ names) and a working branch's pf_a8a.v (the seed on
   the block c with a shadow entry, the token run), re-derived on image B's code.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 21 instructions 0x88f00 .. 0x88f50, then the
   shared 0x88e4c / 0x88e50:
     0x88f00 sd a3,192(s1)          slot 0xc0 = cur = &c->seg[i] (a3 = s3, INV_B8B_JOIN's x13)
     0x88f04 andi a0,a3,3; bnez     T34 (-> unimp 0x891c8): decided not taken by the executor from the seed's
                                    alignment fact on cur's atom (4-aligned: pb8b_seg_al4, c mod 16 = 0 by pf_tf)
     0x88f0c ld a0,24(s1); lb a0,0(a0); 0x88f14 bnez -> 0x89090      B#38 (load4 of c->gen; slot 0x18 =
                                    shadow_addr (c + RC_GEN)): the shadow byte is covered by the seed's shadow
                                    entry on c (the block's 16616 bytes are addressable: pf_obj's sa_addr c), so
                                    the token executor reads 0 and the branch is decided; the slow arm 0x89090 ..
                                    0x890a0 is not reached
     0x88f18 ld a0,192(s1); addi 352; srli; add s4; lb a2,0(a1)       B#39 (store4 of cur->seen_gen): covered by
                                    the shadow entry on cur ([cur, cur + 360) inside the block), branch 0x88f34
                                    decided; the slow arm 0x890a4 .. 0x890b0 is not reached
     0x88f2c ld a1,32(s1); lw a1,0(a1)                                c->gen (slot 0x20)
     0x88f38 sw a1,0(a0)                                              cur->seen_gen = c->gen (in the block,
                                    parse_file's footprint [c, c + RC_N + 4): pb8b_fp_block)
     0x88f3c auipc/addi a2 = "%s" (listing object 35 = 0x21340, OBJ); li a1,16; ld a0,64(s1) (cur_name, slot 0x40);
     mv a3,s7 (np); 0x88f50 j 0x88e4c
     then pf_seg_B8b_s.v's pb8b_snp_tail: snprintf(cur_name, 16, "%s", name) and j TAIL.
   One token run of the executor (YCbn through SegPaLib.paj_run_to) from a seed at JOIN (pb8bj_ss: the s1 slots
   0x18 / 0x20 / 0x40 read and 0xc0 written, c->gen read, cur->seen_gen written; shadow entries on c and on cur) to
   0x88e4c, no branch left open, no obligation. The model: pb8b_rconf_seengen (r_upd cf i (rs_with_gen (rc_gen
   cf))), cur_name = snprintf_s 16 "%s" [name] = name (pb8b_snprintf_name16; the field's bytes after the new NUL
   kept: pb8b_cstr_splice0 over INV_B8B_JOIN's pf_st0 pf_nm). TAIL at o' = pf_next s o, ln' = ln + 1.
   Section hypotheses: SNP (the snprintf), OBJ (the literal atom of 0x88f3c). Instructions walked: 21 of 21 in
   0x88f00 .. 0x88f50, plus the shared 2 (0x88e4c, 0x88e50); the slow arms 0x89090 .. 0x890b0 are unreachable
   (checks B#38 and B#39 discharged by the shadow entries, shadow byte 0); UBSan trap T34 discharged. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces pf_seg_B8b_d pf_seg_B8b_t pf_seg_B8b_s pf_seg_B8b_pj_u.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B8b_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ small tools ================================ *)
Lemma pb8bj_upd_fields : forall (cf : rconf) i f,
  length (rc_seg (r_upd cf i f)) = length (rc_seg cf) /\ rc_refused (r_upd cf i f) = rc_refused cf /\
  rc_overflow (r_upd cf i f) = rc_overflow cf.
Proof. intros cf i f. unfold r_upd, r_set_segs. cbn [rc_seg rc_refused rc_overflow]. rewrite upd_nth_len. auto. Qed.
Lemma pb8bj_rconf_ext : forall (rd rd' : reader) c cf,
  (forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rd' x = rd x) -> sa_rconf rd c cf -> sa_rconf rd' c cf.
Proof.
intros rd rd' c cf K (bs & Hb & Henc). exists bs. split; [|exact Henc].
destruct Henc as [Hl _]. intros i Hi. rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma pb8bj_sl_get : forall (rd : reader) b L off v, pf_sl rd b L -> In (off, v) L -> rdword rd (b + off) = Some v.
Proof. intros rd b L off v H Hin. unfold pf_sl in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
Lemma pb8bj_soff : forall E n z x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n z) = Z_to_bv 64 (x + z).
Proof. intros E n z x Hx. cbn [sv_denot]. rewrite Hx. reflexivity. Qed.
(* the value slot 0x18 holds (0x8810c): sh(&c->gen), as the seed's chunk (pf_a8a.v a8_shaddr_den at RC_GEN) *)
Definition pb8bj_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 seg_spec.RC_GEN) (SLit 3)) (SOff 20 0).
Lemma pb8bj_shx_den : forall E c, bv_unsigned (ew E 32) = c -> bv_unsigned (ew E 20) = SB ->
  0 <= c /\ c + seg_spec.RC_GEN < 2 ^ 47 -> sv_denot E pb8bj_shx = Z_to_bv 64 (shadow_addr (c + seg_spec.RC_GEN)).
Proof.
intros E c Hc Hs Hr. unfold pb8bj_shx, seg_spec.RC_GEN in *.
change (Z_to_bv 64 (shadow_addr (c + 16608))) with (sv_denot E (SLit (shadow_addr (c + 16608)))). apply U_inj.
rewrite !U_SAlu, !U_SOff, !U_SLit, Hc, Hs. rewrite Z.add_0_r.
rewrite (zcanon_small (c + 16608)) by (unfold M64; lia). change (zcanon 3) with 3.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D : 0 <= (c + 16608) / 8 <= c + 16608)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (zcanon_small ((c + 16608) / 8)) by (unfold M64; lia).
rewrite (zcanon_small SB) by (unfold SB, M64; lia).
unfold shadow_addr, SHADOW_OFF, SB. f_equal. lia.
Qed.
(* reading back an 8-byte chunk of a region (pf_seg_B2.v pb2_word_of_region) *)
Lemma pb8bj_word_of_region : forall {segs : list Segment} E H m n b lo hi wlo whi cs od e v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs H m) (b + od) = Some v.
Proof.
intros segs E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := segs) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.
(* buf's 64 shadow cells are 0 at the line scope *)
Lemma pb8bj_shb_buf : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (pb8b_zrange (fun i => pf_shb PF_SC_LINE i =? 0) 8 64). vm_compute. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the slots of PF_SL miss 0xc0 .. 0xc7, the slot JOIN writes *)
Lemma pb8bj_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0 <= fst ov <= 0xb8 \/ 0xd0 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* a C string inside buf, at the line scope: its bytes and NUL are addressable (buf's cells 0x08 .. 0x47 are 0) *)
Lemma pb8bj_buf_addr : forall v pos (rd : reader) np (name : list Z), pb8b_geoP v pos ->
  pf_fsh rd (pf_SH v pos) PF_SC_LINE -> (forall i, 0 <= i < 256 -> rd (pf_SH v pos + i) <> None) ->
  pf_inb (pf_F v pos + PF_O_BUF) np name -> sa_addr rd np (Z.of_nat (length name) + 1).
Proof.
intros v pos rd np name HG HF HP (Hb1 & Hb2).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5).
destruct (pb8b_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold PF_O_BUF in *.
split; [lia|]. split; [lia|].
split; [apply amem_range_high; lia|].
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Ex : shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8).
  { unfold shadow_of_addr. rewrite ESH.
    replace x with ((x - pf_F v pos) + (pf_F v pos / 8) * 8) at 1 by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Hq : 8 <= (x - pf_F v pos) / 8 < 72).
  { split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite Ex, HF by lia. rewrite pb8bj_shb_buf by lia. reflexivity.
- intros Hn s Hs. unfold shadow_addr in Hs.
  pose proof (Z.div_mod np 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound np 8 ltac:(lia)) as Mn.
  pose proof (Z.div_mod (np + (Z.of_nat (length name) + 1) - 1) 8 ltac:(lia)) as De.
  pose proof (Z.mod_pos_bound (np + (Z.of_nat (length name) + 1) - 1) 8 ltac:(lia)) as Me.
  pose proof (Z.div_mod (SHADOW_OFF + np / 8) 8 ltac:(lia)) as Dsn.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + np / 8) 8 ltac:(lia)) as Msn.
  pose proof (Z.div_mod (SHADOW_OFF + (np + (Z.of_nat (length name) + 1) - 1) / 8) 8 ltac:(lia)) as Dse.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (np + (Z.of_nat (length name) + 1) - 1) / 8) 8 ltac:(lia)) as Mse.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia. apply HP.
  rewrite ESH. unfold SHADOW_OFF in *. lia.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* ================================ the seed at JOIN (0x88f00) ================================ *)
(* every register its own atom; the extra atoms 32 = c, 33 = c->gen, 34 = cur_name. Regions: the s1 slots 0x18
   (sh(&c->gen)), 0x20 (&c->gen), 0x40 (cur_name), writable 0xc0 (cur); c->gen; cur->seen_gen (writable).
   Shadow entries: the block c (16616 bytes) and [cur, cur + 360). *)
Definition pb8bj_S1F : afact := mkAF 0x7fff7f800000 (2 ^ 47) 5.
Definition pb8bj_ss : sstate := mkSS PF_B8B_JOIN sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x18 0xc8 0xc0 0xc8
     [YP09.mkChunk 0x18 (CVal 8 pb8bj_shx); YP09.mkChunk 0x20 (CVal 8 (SOff 32 seg_spec.RC_GEN));
      YP09.mkChunk 0x40 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 32%nat) seg_spec.RC_GEN (seg_spec.RC_GEN + 4) 0 0
     [YP09.mkChunk seg_spec.RC_GEN (CVal 4 (SOff 33 0))];
   YP09.mkRegion (Some 13%nat) 352 356 352 356 []] None
  (mkFacts [(2%nat, pb8bj_S1F); (9%nat, pb8bj_S1F); (20%nat, mkAF SB SB 0); (13%nat, mkAF 4096 140737479966720 2);
            (32%nat, PTR 4); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 4096 (2 ^ 47) 0)] [] []).
Definition pb8bj_Bx : sv := SOff 20 0.
Definition pb8bj_SH : list shent := [mkSHE 32 0 seg_spec.SEG_C_SIZE; mkSHE 13 0 360].
Definition pb8bj_E (rX : bvmap 5 word) (c g cn : Z) : env := Eimg (Ereg rX [w64 c; w64 g; w64 cn]).

Lemma pb8bj_seed : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  INV_B8B_JOIN B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  st_ok_pi SEGS VAL (pb8bj_E rX (p_c v) (rc_gen cf) (pf_F v pos + PF_O_CN)) pb8bj_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_B8B_JOIN)) memc (seg_rom SEGS))) /\
  sh_ok SEGS pb8bj_Bx pb8bj_SH (pb8bj_E rX (p_c v) (rc_gen cf) (pf_F v pos + PF_O_CN)) (mrestrict (w_H Wc) memc).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i HI.
destruct HI as (HB & HMID & HST0 & HSTR & HINB & HLEN & HI & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL0 & HFSH).
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4096 & Hcceil & HcA & HcH & Hcap).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hpres.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pb8b_rc_vals as (ERN & EGN & ERR & ESG & EIF & ERS & ESZ).
destruct HST0 as (HRC & HNM & HCNT).
pose proof HRC as (bs & Hbs & Henc).
pose proof Henc as (Lbs & L32 & _ & _ & _ & _ & _ & _ & _ & _ & HGEN).
pose proof HGEN as (Hg0 & _).
assert (Hi32 : (i < 32)%nat) by lia.
pose proof (pb8b_seg_in (p_c v) i 0 356 Hi32 ltac:(lia) ltac:(lia) ltac:(lia)) as (Hs1 & Hs2).
pose proof (pb8b_seg_al4 (p_c v) i Hc16) as Hal4.
destruct HcH as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & Hbapp & Hbp & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrqc].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
set (E := pb8bj_E rX (p_c v) (rc_gen cf) (pf_F v pos + PF_O_CN)).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = w64 (p_c v))
  by (subst E; unfold pb8bj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 (rc_gen cf))
  by (subst E; unfold pb8bj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 (pf_F v pos + PF_O_CN))
  by (subst E; unfold pb8bj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (UR : forall k w, (k < 32)%nat -> getr rX (Z_to_bv 5 (Z.of_nat k)) = w64 w -> 0 <= w < 2 ^ 64 ->
    bv_unsigned (ew E k) = w).
{ intros k w Hk Hr Hw. rewrite (EE k (Z_to_bv 5 (Z.of_nat k))).
  - rewrite Hr. unfold w64. apply unsigned_lit_small. exact Hw.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia. }
assert (U2 : bv_unsigned (ew E 2) = pf_s1 v) by (apply (UR 2%nat); [lia | apply (pb8b_rg rX _ 2 _ HRG0); pb8b_in | lia]).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v) by (apply (UR 9%nat); [lia | apply (pb8b_rg rX _ 9 _ HRG0); pb8b_in | lia]).
assert (U20 : bv_unsigned (ew E 20) = SB)
  by (apply (UR 20%nat); [lia | apply (pb8b_rg rX _ 20 _ HRG0); pb8b_in | unfold SB; lia]).
assert (U13 : bv_unsigned (ew E 13) = seg_spec.rseg_addr (p_c v) i)
  by (apply (UR 13%nat); [lia | apply (pb8b_rg rX _ 13 _ HRG); unfold PF_RL, PF_RM; pb8b_in | lia]).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = rc_gen cf) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pf_F v pos + PF_O_CN)
  by (rewrite E34; unfold w64; apply unsigned_lit_small; unfold PF_O_CN; lia).
split.
- rewrite restrict_mkst_fx. unfold pb8bj_ss. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split.
      { intros o0 Ho0. apply (apresent_writable SEGS). apply Hpres. unfold pf_sp0 in *. lia. }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x18 8 _ (shadow_addr (p_c v + seg_spec.RC_GEN)));
           [apply (pb8bj_shx_den E (p_c v) U32 U20); lia
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold shadow_addr, SHADOW_OFF;
             split; [pose proof (Z.div_pos (p_c v + seg_spec.RC_GEN) 8 ltac:(lia) ltac:(lia)); lia
                    | pose proof (Z.div_le_upper_bound (p_c v + seg_spec.RC_GEN) 8 (p_c v + seg_spec.RC_GEN) ltac:(lia) ltac:(lia)); lia]
           | cbn; lia |].
         apply val_mem_of_rdword. apply (pb8bj_sl_get _ _ (PF_SL v pos) _ _ HSL0). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x20 8 _ (p_c v + seg_spec.RC_GEN));
           [apply (pb8bj_soff E 32 _ _ U32) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
         apply val_mem_of_rdword. apply (pb8bj_sl_get _ _ (PF_SL v pos) _ _ HSL0). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x40 8 _ (pf_F v pos + PF_O_CN));
           [rewrite pb8b_den_atom0; exact E34 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold PF_O_CN; lia | cbn; lia |].
         apply val_mem_of_rdword. apply (pb8bj_sl_get _ _ (PF_SL v pos) _ _ HSL0). unfold PF_SL. cbn [In]. tauto.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (p_c v) seg_spec.RC_GEN 4 (SOff 33 0) (rc_gen cf));
        [rewrite pb8b_den_atom0; exact E33 | cbn; lia | cbn; lia |].
      apply pb8bj_val_mem_of_sa. apply (pb8bj_u32_at _ (p_c v) bs seg_spec.RC_GEN (rc_gen cf) Hbs); [lia | lia | exact HGEN].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U13. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o0 Ho0. apply (apresent_writable SEGS).
      exact (proj1 (Hbp (seg_spec.rseg_addr (p_c v) i + o0) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia))).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U13.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, pb8bj_S1F, PTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U20, U13, U32, U33, U34. change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, PF_O_CN. repeat split; try lia.
- unfold sh_ok, pb8bj_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold shent_ok, app_apart, pb8bj_Bx. cbn [she_m she_lo she_hi].
    assert (UB : U E (SOff 20 0) = SB) by (rewrite U_SOff, U20, Z.add_0_r; apply zcanon_small; unfold SB, M64; lia).
    assert (UC : U E (SOff 32 0) = p_c v) by (rewrite U_SOff, U32, Z.add_0_r; apply zcanon_small; unfold M64; lia).
    rewrite UB, UC. split.
    * rewrite Z.add_0_r, Z.sub_0_r. exact (proj1 (proj2 (proj2 (proj2 HcA)))).
    * intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. unfold SB in *. lia.
  + unfold shent_ok, app_apart, pb8bj_Bx. cbn [she_m she_lo she_hi].
    assert (UB : U E (SOff 20 0) = SB) by (rewrite U_SOff, U20, Z.add_0_r; apply zcanon_small; unfold SB, M64; lia).
    assert (UK : U E (SOff 13 0) = seg_spec.rseg_addr (p_c v) i)
      by (rewrite U_SOff, U13, Z.add_0_r; apply zcanon_small; unfold M64; lia).
    rewrite UB, UK. split.
    * rewrite Z.add_0_r, Z.sub_0_r.
      exact (range_addressable_sub _ _ (p_c v) seg_spec.SEG_C_SIZE (seg_spec.rseg_addr (p_c v) i) 360
        (proj1 (proj2 (proj2 (proj2 HcA)))) ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
    * intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. unfold SB in *. lia.
Qed.

(* ================================ the piece: JOIN -> 0x88e4c -> TAIL ================================ *)
Theorem pb8b_join_holds : forall n, HA_TAIL B n -> H_B8B_JOIN B n.
Proof.
intros n TAIL v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i HI.
destruct (pb8bj_seed n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i HI) as [HS SHOK].
destruct HI as (HB & HMID & HST0 & HSTR & HINB & HLEN & HI & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL0 & HFSH).
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5).
destruct (pb8b_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4096 & Hcceil & HcA & HcH & Hcap).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pb8b_rc_vals as (ERN & EGN & ERR & ESG & EIF & ERS & ESZ).
destruct HST0 as (HRC & HNM & HCNT).
destruct HMID as (Ho & Hn & HCTX).
pose proof HRC as (bs & Hbs & Henc).
pose proof Henc as (Lbs & L32 & _ & _ & _ & _ & _ & _ & _ & _ & HGEN).
pose proof HGEN as (Hg0 & _).
assert (Hi32 : (i < 32)%nat) by lia.
pose proof (pb8b_seg_in (p_c v) i 0 356 Hi32 ltac:(lia) ltac:(lia) ltac:(lia)) as (Hs1 & Hs2).
destruct HcH as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & Hbapp & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrqc].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hbc) as Hcoff.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
pose proof HOBJ as (_ & _ & HtH & _).
destruct HtH as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bt mt HAR Hbt) as (_ & _ & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrqt].
assert (Htceil : p_t v + pf_len v <= alloc_ceiling) by lia.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (RP & _)) & _).
pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJ & _).
unfold sa_disj, seg_spec.cstr_span in HDJ.
clear RP fe.
pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)) as Hspt.
assert (NZ : ~ In 0 name) by (destruct HSTR as [[_ Hz] _]; exact Hz).
pose proof HINB as (Hnb1 & Hnb2). unfold PF_O_BUF in Hnb1, Hnb2.
set (cur := seg_spec.rseg_addr (p_c v) i) in *.
set (E := pb8bj_E rX (p_c v) (rc_gen cf) (pf_F v pos + PF_O_CN)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E33 : ew E 33 = w64 (rc_gen cf))
  by (subst E; unfold pb8bj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 (pf_F v pos + PF_O_CN))
  by (subst E; unfold pb8bj_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v).
{ rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), (pb8b_rg rX _ 9 _ HRG0 ltac:(pb8b_in)). unfold w64.
  apply unsigned_lit_small. lia. }
assert (U13 : bv_unsigned (ew E 13) = cur).
{ rewrite (EE 13%nat (Z_to_bv 5 13) eq_refl), (pb8b_rg rX _ 13 _ HRG ltac:(unfold PF_RL, PF_RM; pb8b_in)).
  unfold w64. apply unsigned_lit_small. lia. }
unfold cfg_at. change (w64 (BASE + PF_B8B_JOIN)) with (Z_to_bv 64 (BASE + PF_B8B_JOIN)).
(* ---- 0x88f00 .. 0x88f50: one token run to 0x88e4c ---- *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_PROV2.
{ unfold pb8bj_ss; cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U9 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. rewrite ESTK. unfold pf_sp0 in *. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U13 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - apply pb8b_fp_block; unfold seg_spec.RC_N in *; lia.
  - exists bc, mc. split; [exact Hbc | unfold seg_spec.SEG_C_SIZE in *; lia]. }
pb8bs_clear_md.
set (Wr0 := fun a => (pf_s1 v + 0xc0 <= a < pf_s1 v + 0xc8) \/ (cur + 352 <= a < cur + 356)).
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ Wr0 a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hnn. apply (kept_of_frame (segs:=SEGS) E _ (w_H Wc) memc (ms_mem ms) Wr0 HFr); [|exact Ha | exact Hnn].
  intros b0 wlo whi a0 Hin0 Hrr. vm_compute in Hin0. unfold Wr0.
  repeat (destruct Hin0 as [Hq | Hin0];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U13 in Hrr; lia |]).
  destruct Hin0. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG0 Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2 end.
cbn [ms_mem restrict] in HR0, HR2.
(* slot 0xc0 holds cur *)
assert (W0C : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0xc0) = Some cur).
{ eapply (pb8bj_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0xc0 (SOff 13 0) cur HR0 U9);
    [pb8b_in | | lia].
  rewrite pb8b_den_atom0, (EE 13%nat (Z_to_bv 5 13) eq_refl). exact (pb8b_rg rX _ 13 _ HRG ltac:(unfold PF_RL, PF_RM; pb8b_in)). }
(* cur->seen_gen holds c->gen *)
assert (SG : sa_bytes (rdW Wc (ms_mem ms)) (cur + 352) (PMem.le4 (Z_to_bv 64 (rc_gen cf)))).
{ pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H Wc) (ms_mem ms)) 13 cur _ _ _ _ _ 352 4
    (SExt true 32 (SOff 33 0)) HR2 U13 ltac:(pb8b_in) ltac:(cbn; lia)) as HV.
  change (bv_unsigned (sv_denot E (SExt true 32 (SOff 33 0)))) with (U E (SExt true 32 (SOff 33 0))) in HV.
  rewrite U_SExt in HV. cbv iota in HV.
  rewrite (U_atom E 33 (rc_gen cf) E33) in HV by lia.
  unfold zcanon, M64 in HV. rewrite (pb8bj_sext_lo (rc_gen cf) Hg0) in HV. change (N.to_nat 4) with 4%nat in HV.
  exact (pb8bj_bytes_of_val_mem SEGS (w_H Wc) (ms_mem ms) (cur + 352) (rc_gen cf) Hg0 HV). }
(* the registers at 0x88e4c *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pb8bs_rreg HS; rewrite pb8b_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pf_F v pos + PF_O_CN))
  by (pb8bs_rreg HS; rewrite pb8b_den_atom0; exact E34).
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 16) by (pb8bs_rreg HS; reflexivity).
assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_s)).
{ pb8bs_rreg HS. rewrite pb8b_den_atom0. rewrite (img_env_atomP E 276%nat HEI) by (unfold A_TEXT, A_LIM; lia).
  change 276%nat with (A_OBJ 35). rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64. f_equal; vm_compute; reflexivity. }
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 np).
{ pb8bs_rreg HS. rewrite pb8b_den_atom0, (EE 23%nat (Z_to_bv 5 23) eq_refl).
  exact (pb8b_rg rX _ 23 _ HRG ltac:(unfold PF_RL, PF_RM; pb8b_in)). }
pmkst HS.
lazymatch goal with |- SRr ?S ?W _ ?Q =>
  change (SRr S W (cfg_at SEGS (BASE + PF_PROV2) (ms_regs ms) (ms_mem ms) mdv) Q) end.
set (rd0 := rdW Wc memc) in *.
set (rdm := rdW Wc (ms_mem ms)) in *.
(* what the run kept *)
assert (KP0 : pb8b_kp Wr0 rd0 rdm) by (split; [exact K1 | intros a _ Hv; exact (M1 a Hv)]).
assert (NI0 : forall x, 0x10000 <= x < kImgEnd -> ~ Wr0 x).
{ intros x Hx [Hq | Hq]; unfold off_img, kImgEnd in *; lia. }
assert (NS0 : forall x, kLowMemEnd <= x < kHighMemBeg -> ~ Wr0 x).
{ intros x Hx [Hq | Hq]; unfold seg_spec.SEG_C_SIZE in *; lia. }
pose proof (proj1 HJ) as HARm.
destruct (al_frames _ _ LAWS lyc Sc Wc (ms_mem ms) mdv 5 pos HARm Hin) as (_ & _ & _ & HFshm).
rewrite EF in HFshm. change (fs_frame_bytes 5 / 8) with 256 in HFshm.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in HFshm.
assert (HFSHm : pf_fsh rdm (pf_SH v pos) PF_SC_LINE).
{ intros j Hj. rewrite (pb8b_kp_byte Wr0 rd0 rdm KP0); [exact (HFSH j Hj) | lia | apply NS0; lia]. }
assert (HSTRm : sa_str rdm np name).
{ apply (pb8b_kp_str Wr0 rd0 rdm KP0); [lia | lia | | exact HSTR].
  intros x Hx [Hq | Hq]; [lia | destruct Hcap; unfold seg_spec.SEG_C_SIZE in *; lia]. }
assert (Hl15 : (length name <= 15)%nat) by lia.
assert (Hrng : Forall (fun z => 0 <= z < 256) name).
{ pose proof (pb8b_bytes_range_aview SEGS (w_H Wc) memc np name HSTR) as R.
  rewrite Forall_forall in R |- *. intros z Hz. pose proof (R z Hz). lia. }
unfold pf_postm.
apply (pb8b_snp_tail B SNP n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (r_upd cf i (rs_with_gen (rc_gen cf)))
  (Some i) (snprintf_s 16 F_s [AS name]) (pf_next (p_s v) o) (ln + 1) d (pf_F v pos + PF_O_CN) 16 np name TAIL).
- (* pf_base after the run: the slot 0xc0 and cur->seen_gen are the only bytes written *)
  split; [exact HCX|].
  split.
  { split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split.
    { intros j r Hj. assert (Hj13 : (j < 13)%nat)
        by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
      rewrite (pb8b_kp_rdword Wr0 rd0 rdm KP0); [exact (HSAV j r Hj) | lia | lia |].
      intros k Hk [Hq | Hq]; unfold seg_spec.SEG_C_SIZE in *; lia. }
    split.
    { rewrite (pb8b_kp_rdword Wr0 rd0 rdm KP0); [exact HFLAG | change (fs_frame_bytes 5) with 2048; lia
        | change (fs_frame_bytes 5) with 2048; lia |].
      change (fs_frame_bytes 5) with 2048. intros k Hk [Hq | Hq]; [lia | destruct Hcap; unfold seg_spec.SEG_C_SIZE in *; lia]. }
    split; [exact HFRM|]. split; [exact HTF|].
    split.
    { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
      rewrite (pb8b_kp_rdword Wr0 rd0 rdm KP0); [exact HC8 | lia | lia |].
      intros k Hk [Hq | Hq]; unfold seg_spec.SEG_C_SIZE in *; lia. }
    apply (pb8bs_rg_tr rX); [exact HRG0|]. intros r w Hrw. apply QK.
    cbn [In] in Hrw |- *. repeat (destruct Hrw as [Hq | Hrw]; [injection Hq as <- _; pb8b_in |]). destruct Hrw. }
  split.
  { apply (pb8b_kp_obj B Wr0 rd0 rdm KP0 NI0 NS0 v lyc Sc HOBJ Htceil ltac:(lia)).
    intros x Hx [Hq | Hq]; unfold pf_len in *; [lia | unfold seg_spec.SEG_C_SIZE in *; lia]. }
  split.
  { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
    pose proof (pb8bj_PF_SL_offs v pos ov Hov) as Ho'.
    rewrite (pb8b_kp_rdword Wr0 rd0 rdm KP0); [exact (HSL0 ov Hov) | lia | lia |].
    intros k Hk [Hq | Hq]; unfold seg_spec.SEG_C_SIZE in *; lia. }
  exact HFSHm.
- exact HCTX.
- pose proof (pf_next_skipn_lt (p_s v) o Ho). lia.
- apply (pb8bs_rg_tr rX); [apply (pb8b_rg_sub _ _ _ HRG); intros x Hx; unfold PF_RL, PF_RM in *; cbn [In app] in Hx |- *; tauto|].
  intros r w Hrw. apply QK. unfold PF_RL in Hrw. cbn [In app] in Hrw |- *.
  repeat (destruct Hrw as [Hq | Hrw]; [injection Hq as <- _; pb8b_in |]). destruct Hrw.
- unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; assumption.
- right. split; reflexivity.
- lia.
- exact HSTRm.
- apply (pb8bj_buf_addr v pos rdm np name HG HFSHm); [|exact HINB].
  intros j Hj. exact (aview_some_of_apresent SEGS _ _ _ (proj1 (HFshm j Hj))).
- apply Nat2Z.inj_le. assert (E1 : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity). rewrite E1. lia.
- lia.
- apply amem_range_high; lia.
- unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (np + Z.of_nat (length name) + 1)) 8 ltac:(lia)). lia.
- unfold sa_disj, PF_O_CN. lia.
- (* pf_st once name and its NUL are in cur_name *)
  intros rd' Hw Hk.
  rewrite (pf_seg_B8b_m.pb8b_snprintf_name16 name NZ Hl15) in Hw, Hk |- *.
  assert (KB : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> rd' x = rdm x).
  { intros x Hx. apply Hk; [lia | unfold PF_O_CN; destruct Hcap; unfold seg_spec.SEG_C_SIZE in *; lia | lia]. }
  set (rdp := fun x => if (p_c v <=? x) && (x <? p_c v + seg_spec.SEG_C_SIZE) then rdm x else rd0 x).
  assert (Hrdp_in : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> rdp x = rdm x).
  { intros x Hx. unfold rdp. replace ((p_c v <=? x) && (x <? p_c v + seg_spec.SEG_C_SIZE)) with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (HRCp : sa_rconf rdp (p_c v) (r_upd cf i (rs_with_gen (rc_gen cf)))).
  { apply (pf_seg_B8b_m.pb8b_rconf_seengen rd0 rdp (p_c v) cf i (rc_gen cf) (PMem.le4 (Z_to_bv 64 (rc_gen cf)))
      HRC HI ltac:(lia) ltac:(split; [exact Hg0 | reflexivity])).
    - intros x Hx Hnd. unfold rdp.
      destruct ((p_c v <=? x) && (x <? p_c v + seg_spec.SEG_C_SIZE)) eqn:Eb; [|reflexivity].
      apply andb_prop in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.ltb_lt in Eb2.
      apply K1; [lia|]. intros [Hq | Hq]; [unfold seg_spec.SEG_C_SIZE in *; lia | apply Hnd; fold cur; lia].
    - intros k0 Hk0. rewrite Hrdp_in by (rewrite pf_seg_B8b_m.pb8b_u32_len with (v := rc_gen cf) in Hk0 by
        (split; [exact Hg0 | reflexivity]); fold cur; lia).
      fold cur. replace (cur + seg_spec.RS_SEEN_GEN) with (cur + 352) by lia. exact (SG k0 Hk0). }
  split; [exact (pb8bj_rconf_ext rdp rd' (p_c v) _ (fun x Hx => eq_trans (KB x Hx) (eq_sym (Hrdp_in x Hx))) HRCp)|].
  split; [cbn [pf_cur_ok]; rewrite (proj1 (pb8bj_upd_fields cf i _)); exact HI|].
  split.
  { destruct HNM as (f & Hfb & Hfe). pose proof Hfe as [Hfl _].
    assert (Lnw : length (seg_spec.zb (name ++ [0])) = S (length name))
      by (unfold seg_spec.zb; rewrite length_map, length_app; cbn [length]; lia).
    assert (Hr0 : Forall (fun z => 0 <= z < 256) (name ++ [0]))
      by (apply Forall_app; split; [exact Hrng | constructor; [cbv beta; lia | constructor]]).
    exists (pf_seg_B8b_m.pb8b_splice 0 (seg_spec.zb (name ++ [0])) f).
    split; [|exact (pf_seg_B8b_m.pb8b_cstr_splice0 16 f name Hfl ltac:(lia) NZ Hrng)].
    intros j Hj. rewrite pf_seg_B8b_m.pb8b_splice_len in Hj by lia.
    apply (pf_seg_B8b_m.pb8b_sa_splice rd' (pf_F v pos + PF_O_CN) f (seg_spec.zb (name ++ [0])) 0 (fun _ => False));
      [lia | | | exact Hj | intros []].
    - intros j' Hj' Hout _. rewrite Lnw in Hout.
      rewrite Hk; [| unfold PF_O_CN; lia | unfold PF_O_CN; lia | unfold PF_O_CN; lia].
      rewrite K1; [exact (Hfb j' Hj') | unfold PF_O_CN; lia |].
      unfold PF_O_CN. intros [Hq | Hq]; [lia | destruct Hcap; unfold seg_spec.SEG_C_SIZE in *; lia].
    - intros k Hk'. rewrite Lnw in Hk'.
      replace (pf_F v pos + PF_O_CN + Z.of_nat 0 + Z.of_nat k) with (pf_F v pos + PF_O_CN + Z.of_nat k) by lia.
      rewrite (Hw k ltac:(lia)). f_equal.
      unfold seg_spec.zb, ZB0. rewrite (map_nth (Z_to_bv 8) (name ++ [0]) 0 k).
      rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256.
      rewrite Forall_forall in Hr0. apply Hr0. apply nth_In. rewrite length_app. cbn [length]. lia. }
  split.
  { unfold pf_cnt in *. rewrite (proj1 (proj2 (pb8bj_upd_fields cf i _))), (proj2 (proj2 (pb8bj_upd_fields cf i _))).
    exact HCNT. }
  cbn [pf_cur_ptr]. fold cur.
  rewrite (rdword_ext rdm rd'); [exact W0C|].
  intros k0 Hk0. apply Hk; [lia | unfold PF_O_CN; lia | lia].
Qed.
End x.
End e.
End f.
End d.
