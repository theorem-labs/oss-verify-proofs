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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 214 of its 259 lines of code are new or changed and 5008 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B10b_s.v, with its module paths and module names changed; 430 of its 497 lines of code are new or changed and 192 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_5 of
   segment B9 of reac_segconf_parse_file's walk, its first piece: from J4 0x88440 (lib/B/Prog/pf_seg_B9_d.v; a0 =
   |v0|, s3 = vp0) to K5 0x88570 (|v0| < 2, or v0[0] neither quote: the value is v0) or to an arm cut of
   lib/B/Prog/pf_seg_B9_s5k.v (B9S5_SQ 0x88530 when v0[0] = SQ, B9S5_DQ 0x88480 when v0[0] = DQ).
   A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: a piece of stretch SB9_5).
   ADAPTED from lib/B/Prog/trim_l.v (a load with its inline check, the byte branch by psrr_branch_tok),
   lib/B/Prog/pf_seg_B5_r2.v of the B5 segment lane (a UBSan trap refuted from its branch condition with YI08.U_not) and
   a working branch's lib/A/Prog/pf_a9_s1.v (cur's slot as a read-only region with an extra atom):
     0x88440 li a1,2; 0x88444 bltu a0,a1 -> 0x884c4      |v0| < 2: 0x884c4 ld a5,192(s1); 0x884c8 j K5
     0x88448 srli a1,s3,3; add a1,a1,s4; lb a1,0(a1); 0x88454 ld a5,192(s1); 0x88458 bnez a1 -> 0x88f9c
                                                          check B#10 (load1 at vp0), by the token executor with
                                                          the shadow entry of vp0; its slow arm 0x88f9c andi /
                                                          0x88fa0 blt back to 0x8845c / 0x88fa4 j 0x89274 (mv a0,s3;
                                                          0x89278 errpath_load1) is not reached
     0x8845c lbu a1,0(s3); li a2,39; 0x88464 beq a1,a2 -> 0x88520
     0x88468 li a2,34; 0x8846c bne a1,a2 -> K5
     0x88470 / 0x88520 addi a1,a0,-1; not a2,s3; bltu a2,a1 -> 0x891c8   UBSan traps T12 (DQ arm 0x88478) and
                                                          T14 (SQ arm 0x88528), vp0 + |v0| - 1 wraps: refuted from
                                                          the branch condition (vp0 + |v0| < buf + 512 < 2 ^ 47)
     0x8847c / 0x8852c add a0,s3,a1 -> B9S5_DQ / B9S5_SQ
   Instructions walked: 0x88440 .. 0x8847c (16), 0x884c4 .. 0x884c8 (2), 0x88520 .. 0x8852c (4). Check B#10, traps
   T12, T14. No call. No Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
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
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c pf_seg_B9_s5k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac b9s5m_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b9s5m_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = getr _ (Z_to_bv 5 ?r) =>
    let Hk := fresh "Hk" in prreg HS (Z_to_bv 5 r) Hk; rewrite Hk; apply EE; reflexivity end.
(* a register of the state after a run, as the executor wrote it (pf_seg_B5_r2.v b5r2_rreg) *)
Ltac b9s5m_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Lemma b9s5m_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma b9s5m_den_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma b9s5m_br_eq : forall E (n : nat) b z r, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = r -> (b =? z) = r.
Proof. intros E n b z r H Hb Hz Hc. rewrite branch_eq_U, (U_atom E n b H Hb), (U_lit E z Hz) in Hc. exact Hc. Qed.
Lemma b9s5m_br_ne : forall E (n : nat) b z r, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = r -> negb (b =? z) = r.
Proof. intros E n b z r H Hb Hz Hc. rewrite branch_ne_U, (U_atom E n b H Hb), (U_lit E z Hz) in Hc. exact Hc. Qed.
Lemma b9s5m_br_ltu : forall E (n : nat) b z r, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = r -> (b <? z) = r.
Proof. intros E n b z r H Hb Hz Hc. rewrite branch_ltu_U, (U_atom E n b H Hb), (U_lit E z Hz) in Hc. exact Hc. Qed.
(* the traps T12 / T14 `bltu a2,a1` with a2 = not s3 = 2 ^ 64 - 1 - vp0 and a1 = a0 - 1 = |v0| - 1: taken only
   when vp0 + |v0| - 1 >= 2 ^ 64 *)
Lemma b9s5m_trap : forall E (m n : nat) p N, ew E m = Z_to_bv 64 p -> ew E n = Z_to_bv 64 N ->
  0 <= p -> 1 <= N -> p + N < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff m 0) (SLit (-1)))) (sv_denot E (SOff n (-1))) = true -> False.
Proof.
intros E m n p N Hm Hn Hp HN HpN Hc.
rewrite branch_ltu_U, (U_not E m p Hm ltac:(lia)), (U_atom_off E n N (-1) Hn ltac:(lia) ltac:(lia)) in Hc.
apply Z.ltb_lt in Hc. lia.
Qed.
(* a word read through the reader is a 64-bit value (pf_a9_s1.v s1_rdword_rng) *)
Lemma b9s5m_rdword_rng : forall (rd : reader) a v, (forall x b, rd x = Some b -> 0 <= b < 256) ->
  rdword rd a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros rd a v HR H. unfold rdword in H.
destruct (rd a) as [b0|] eqn:E0; [|discriminate H].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|discriminate H].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|discriminate H].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|discriminate H].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|discriminate H].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|discriminate H].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|discriminate H].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|discriminate H].
injection H as <-.
pose proof (HR _ _ E0). pose proof (HR _ _ E1). pose proof (HR _ _ E2). pose proof (HR _ _ E3).
pose proof (HR _ _ E4). pose proof (HR _ _ E5). pose proof (HR _ _ E6). pose proof (HR _ _ E7).
lia.
Qed.

(* the seed at J4: every register its own atom; cur's slot s1 + 0xc0 a read-only region of atom 9 whose chunk is
   the extra atom 33 (cur), the byte at vp0 a read-only region of atom 19 whose chunk is the extra atom 32; range
   facts for a0 = |v0|, s3 = vp0 (the check's shadow entry), the shadow base s4 = SB and the byte *)
Definition b9s5m_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0 [YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 19%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition b9s5m_facts : facts :=
  mkFacts [(10%nat, mkAF 0 511 0); (19%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0);
           (32%nat, mkAF 0 255 0)] [] [].
Definition b9s5m_ss : sstate := mkSS B9_J4 sr_atoms b9s5m_regions None b9s5m_facts.
Definition b9s5m_Bx : sv := SOff 20 0.
Definition b9s5m_SH : list shent := [mkSHE 19 0 1].
(* the registers the run from J4 does not write *)
Definition b9s5m_keep : list Z := [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 23; 19].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma b9s5m_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 N vp0 b0 cp,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 10) = w64 N -> getr rX (Z_to_bv 5 19) = w64 vp0 ->
  getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF ->
  alloc_ceiling <= s1 <= 2 ^ 47 -> 0 <= N <= 511 -> 4096 <= vp0 -> vp0 + 1 <= alloc_ceiling ->
  0 <= b0 <= 255 -> 0 <= cp < 2 ^ 64 ->
  rdW Wc memc vp0 = Some b0 -> rdword (rdW Wc memc) (s1 + 0xc0) = Some cp ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [Z_to_bv 64 b0; Z_to_bv 64 cp])) b9s5m_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_J4)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 N vp0 b0 cp H9 H10 H19 H20 Hs1 HN Hv Hv1 Hb Hcp Hrb Hrc.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [Z_to_bv 64 b0; Z_to_bv 64 cp])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = N)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = vp0)
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), H19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), H20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF, SB; lia).
assert (E32 : ew E 32 = Z_to_bv 64 b0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U32 : bv_unsigned (ew E 32) = b0) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b9s5m_ss. apply pa_entry_st_ok_full.
- unfold E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b9s5m_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s1 0xc0 8 (SOff 33 0) cp);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r; rewrite unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
    exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hrc).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi.
    assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H Wc) memc vp0 b0 Hrb) as (b & Hbb & Hvb & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
      rewrite !Z.add_0_r, (unsigned_lit_small b0), (unsigned_lit_small b0) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. rewrite Hvb. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hbb.
- unfold b9s5m_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. repeat split; lia.
- split; [|split; exact I]. cbn [b9s5m_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U19, U20, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

(* K5 at the end of a run from J4 that wrote nothing, the value v0 *)
Lemma b9s5m_to_K5 : forall n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc',
  INV_J4 B n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r b9s5m_keep -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 15) = w64 (b9_cp x) ->
  b9_val x ei = b9_v0 x ei ->
  INV_K5 B n x ei kp vp0 lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HI HJ' KM KV QK Q15 HVAL.
pose proof (b9s5_D_of_J4 B _ _ _ _ _ _ _ _ _ _ _ HI) as HD.
pose proof HI as (_ & _ & _ & _ & _ & HRG).
pose proof HD as ((HB & _) & _).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
unfold B9_R, PF_RL, PF_RM in HRG.
apply (b9s5_k5_keep B n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HD HJ' KM KV); [| |exact HVAL].
- unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HFI); unfold b9_FI; b9s5m_in | unfold b9s5m_keep; b9s5m_in]).
- unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [ exact Q15
          | rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s5m_in | unfold b9s5m_keep; b9s5m_in] ].
Qed.

(* an arm's cut at the end of a run from J4 that wrote nothing *)
Lemma b9s5m_to_Q : forall n q x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc',
  INV_J4 B n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r b9s5m_keep -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  getr rX' (Z_to_bv 5 15) = w64 (b9_cp x) ->
  getr rX' (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length (b9_v0 x ei)) - 1) ->
  getr rX' (Z_to_bv 5 11) = w64 (Z.of_nat (length (b9_v0 x ei)) - 1) ->
  getr rX' (Z_to_bv 5 12) = w64 (2 ^ 64 - 1 - vp0) ->
  (2 <= length (b9_v0 x ei))%nat -> nth 0 (b9_v0 x ei) 0 = q ->
  b9s5_Q B q n x ei kp vp0 lyc Sc Wc rX' memc' mdc'.
Proof.
intros n q x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HI HJ' KM KV QK Q15 Q10 Q11 Q12 HL2 Hq0.
pose proof (b9s5_D_of_J4 B _ _ _ _ _ _ _ _ _ _ _ HI) as HD.
pose proof HI as (_ & _ & _ & _ & _ & HRG).
pose proof HD as ((HB & _) & _).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
unfold B9_R, PF_RL, PF_RM in HRG.
assert (HFI' : pf_rg rX' (b9_FI B (y_v x))).
{ unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HFI); unfold b9_FI; b9s5m_in | unfold b9s5m_keep; b9s5m_in]). }
split; [exact (b9s5_D_move B n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HD HJ' KM KV HFI')|].
split; [exact HL2|]. split; [exact Hq0|].
unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  first [ exact Q15 | exact Q10 | exact Q11 | exact Q12
        | rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s5m_in | unfold b9s5m_keep; b9s5m_in] ].
Qed.

Lemma b9s5_j4_ok : forall n, from_K5 B n -> from_Q5 B DQ B9S5_DQ n -> from_Q5 B SQ B9S5_SQ n -> from_J4 B n.
Proof.
intros n HK5 HDQ HSQ x ei kp vp0 lyc Sc Wc rX memc mdc HI.
pose proof (b9s5_D_of_J4 B _ _ _ _ _ _ _ _ _ _ _ HI) as HD.
pose proof (b9s5_D_rng B _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & HNZ).
pose proof HD as (HC & HCH & HKEY & HKLT & HV0).
pose proof HC as (HB & HM & HST & HL & HD0 & HDL).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & (HJ & _) & _).
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ HB) as HST0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof HV0 as [HSTR _].
pose proof HSTR as [[HZS _] _].
pose proof HI as (_ & _ & _ & _ & _ & HRG).
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5.
unfold B9_R, PF_RL, PF_RM in HRG.
rewrite SPF in G1.
set (V := b9_v0 x ei) in *.
(* the first byte of v0 (or its NUL) and cur's slot *)
set (b0 := nth 0 (V ++ [0]) 0).
assert (VB : rdW Wc memc vp0 = Some b0).
{ pose proof (HZS 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0. rewrite Z.add_0_r in H0. exact H0. }
assert (HB0 : 0 <= b0 <= 255) by (destruct (aview_byte SEGS (w_H Wc) memc _ b0 VB) as (_ & _ & _ & Hr); lia).
pose proof HST as (_ & _ & _ & _ & WC0).
change (pf_cur_ptr (p_c (y_v x)) (y_cur x)) with (b9_cp x) in WC0.
assert (HCP : 0 <= b9_cp x < 2 ^ 64).
{ apply (b9s5m_rdword_rng (rdW Wc memc) _ _ ltac:(intros x0 b Hb; destruct (aview_byte SEGS (w_H Wc) memc x0 b Hb)
    as (_ & _ & _ & Hr); exact Hr) WC0). }
(* the registers at J4 *)
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x))) by (apply (b9_rg_get rX _ 9 _ HFI); unfold b9_FI; b9s5m_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat (length V))) by (apply (b9_rg_get rX _ 10 _ HRG); b9s5m_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 vp0) by (apply (b9_rg_get rX _ 19 _ HRG); b9s5m_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b9_rg_get rX _ 20 _ HFI); unfold b9_FI; b9s5m_in).
(* the seed *)
pose proof (b9s5m_seed Wc rX memc (pf_s1 (y_v x)) (Z.of_nat (length V)) vp0 b0 (b9_cp x) R9 R10 R19 R20
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB0 HCP VB WC0) as HS.
set (E := Eimg (Ereg rX [Z_to_bv 64 b0; Z_to_bv 64 (b9_cp x)])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat (length V))) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E19 : ew E 19 = Z_to_bv 64 vp0) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew E 32 = Z_to_bv 64 b0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (b9_cp x))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
clearbody E.
(* the shadow entry of vp0: check B#10 *)
destruct (b9_addr_buf B _ _ _ _ _ _ _ vp0 1 HST0
  ltac:(unfold b9_bufp, PF_O_BUF; lia) ltac:(lia) ltac:(unfold b9_bufp, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _).
assert (UB : U E b9s5m_Bx = SHADOW_OFF) by (unfold b9s5m_Bx; apply (U_atom E 20 _ E20); unfold SHADOW_OFF; lia).
assert (UW : U E (SOff 19 0) = vp0) by (apply (U_atom E 19 _ E19); lia).
assert (SHOK : sh_ok SEGS b9s5m_Bx b9s5m_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b9s5m_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E b9s5m_Bx 19%nat vp0 1 vp0 0 1 HRA UB UW); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B9_J4)) with (Z_to_bv 64 (BASE + B9_J4)).
(* 0x88440 li a1,2; 0x88444 bltu a0,a1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* |v0| < 2: 0x884c4 ld a5,192(s1); j K5; the value is v0 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5m_br_ltu E1 10 (Z.of_nat (length V)) 2 true E10 ltac:(lia) ltac:(lia) Hc) as BC end.
  apply Z.ltb_lt in BC. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9_K5.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv0 := with_vm_backing _ _ _) in *; clearbody mdv0.
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM1 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms0) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (KV1 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5m_keep -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5m_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5m_kept HS EE |]). destruct Hr. }
  prreg HS (Z_to_bv 5 15) Q15.
  assert (Q15' : getr (ms_regs ms0) (Z_to_bv 5 15) = w64 (b9_cp x)) by (rewrite Q15; exact E33).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9_K5) rg mm mdx) end.
  apply (HK5 x ei kp vp0 lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0).
  apply (b9s5m_to_K5 n x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms0) (ms_mem ms0) mdv0 HI HJ KM2 KV2 QK Q15').
  unfold b9_val. fold V. apply (b9_unq_short V HNZ). lia. }
(* |v0| >= 2: check B#10, the first byte, `beq a1,a2` (a2 = 39) *)
lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
  pose proof (b9s5m_br_ltu E1 10 (Z.of_nat (length V)) 2 false E10 ltac:(lia) ltac:(lia) Hc) as BC end.
apply Z.ltb_ge in BC. clear Hc.
assert (HB0' : b0 = nth 0 V 0) by (unfold b0; rewrite app_nth1 by lia; reflexivity).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv0 := with_vm_backing _ _ _) in *; clearbody mdv0.
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha. rewrite <- (KM1 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
  apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV2 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms0) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms) (ms_mem ms0) a HG (KV1 a Hv))).
clear HFr HG HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* v0[0] = SQ: 0x88520 addi a1,a0,-1; not a2,s3; bltu a2,a1 (trap T14) *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5m_br_eq E1 32 b0 39 true E32 ltac:(lia) ltac:(lia) Hc) as BQ end.
  apply Z.eqb_eq in BQ. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv1 := with_vm_backing _ _ _) in *; clearbody mdv1.
  assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM2 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms0) (ms_mem ms1) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV3 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms1) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms0) (ms_mem ms1) a HG (KV2 a Hv))).
  clear HFr HG HF.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
      exact (b9s5m_trap E1 19 10 vp0 (Z.of_nat (length V)) E19 E10 ltac:(lia) ltac:(lia) ltac:(lia) Hc) end. }
  clear Hc.
  (* 0x8852c add a0,s3,a1: the SQ arm's cut *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9S5_SQ.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  assert (KM4 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM3 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV4 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms2) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms2) a HG (KV3 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5m_keep -> getr (ms_regs ms2) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5m_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5m_kept HS EE |]). destruct Hr. }
  prreg HS (Z_to_bv 5 15) Q15. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
  assert (Q15' : getr (ms_regs ms2) (Z_to_bv 5 15) = w64 (b9_cp x)) by (rewrite Q15; exact E33).
  assert (Q10' : getr (ms_regs ms2) (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1)).
  { rewrite Q10, E19, E10, b9s5m_w64_off, alu64_add_lit. unfold w64. f_equal; lia. }
  assert (Q11' : getr (ms_regs ms2) (Z_to_bv 5 11) = w64 (Z.of_nat (length V) - 1)).
  { rewrite Q11, E10, b9s5m_w64_off. unfold w64. f_equal; lia. }
  assert (Q12' : getr (ms_regs ms2) (Z_to_bv 5 12) = w64 (2 ^ 64 - 1 - vp0)).
  { b9s5m_rreg HS. apply b9s5m_den_U. apply (U_not _ 19 vp0); [exact E19 | lia]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9S5_SQ) rg mm mdx) end.
  apply (HSQ x ei kp vp0 lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2).
  apply (b9s5m_to_Q n SQ x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 HI HJ KM4 KV4 QK
    Q15' Q10' Q11' Q12'); [change (b9_v0 x ei) with V; lia|].
  change (b9_v0 x ei) with V. rewrite <- HB0'. exact BQ. }
(* v0[0] <> SQ: `bne a1,a2` (a2 = 34) *)
lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
  pose proof (b9s5m_br_eq E1 32 b0 39 false E32 ltac:(lia) ltac:(lia) Hc) as BQ end.
apply Z.eqb_neq in BQ. clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv1 := with_vm_backing _ _ _) in *; clearbody mdv1.
assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha. rewrite <- (KM2 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
  apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms0) (ms_mem ms1) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV3 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms1) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms0) (ms_mem ms1) a HG (KV2 a Hv))).
clear HFr HG HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* v0[0] neither quote: K5, the value is v0 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    pose proof (b9s5m_br_ne E1 32 b0 34 true E32 ltac:(lia) ltac:(lia) Hc) as BD end.
  apply Bool.negb_true_iff, Z.eqb_neq in BD. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B9_K5.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  assert (KM4 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KM3 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
  assert (KV4 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms2) a <> None)
    by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms2) a HG (KV3 a Hv))).
  clear HFr HG HF.
  assert (QK : forall r, In r b9s5m_keep -> getr (ms_regs ms2) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold b9s5m_keep in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s5m_kept HS EE |]). destruct Hr. }
  prreg HS (Z_to_bv 5 15) Q15.
  assert (Q15' : getr (ms_regs ms2) (Z_to_bv 5 15) = w64 (b9_cp x)) by (rewrite Q15; exact E33).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9_K5) rg mm mdx) end.
  apply (HK5 x ei kp vp0 lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2).
  apply (b9s5m_to_K5 n x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 HI HJ KM4 KV4 QK Q15').
  unfold b9_val. fold V. apply (b9_unq_keep V HNZ ltac:(lia)).
  rewrite <- HB0'. intros [[H1 _] | [H1 _]]; [apply BD | apply BQ]; exact H1. }
(* v0[0] = DQ: 0x88470 addi a1,a0,-1; not a2,s3; bltu a2,a1 (trap T12) *)
lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
  pose proof (b9s5m_br_ne E1 32 b0 34 false E32 ltac:(lia) ltac:(lia) Hc) as BD end.
apply Bool.negb_false_iff, Z.eqb_eq in BD. clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
assert (KM4 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha. rewrite <- (KM3 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
  apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV4 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms2) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem ms2) a HG (KV3 a Hv))).
clear HFr HG HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?E1 _) _ = _ =>
    exact (b9s5m_trap E1 19 10 vp0 (Z.of_nat (length V)) E19 E10 ltac:(lia) ltac:(lia) ltac:(lia) Hc) end. }
clear Hc.
(* 0x8847c add a0,s3,a1: the DQ arm's cut *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan B9S5_DQ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3.
assert (KM5 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms3) a = rdW Wc memc a).
{ intros a Ha. rewrite <- (KM4 a Ha). lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
  apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms2) (ms_mem ms3) (fun _ => False) HFr);
    [|exact Ha | tauto] end.
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq' | Hin']; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV5 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms3) a <> None)
  by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms2) (ms_mem ms3) a HG (KV4 a Hv))).
clear HFr HG HF.
assert (QK : forall r, In r b9s5m_keep -> getr (ms_regs ms3) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b9s5m_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b9s5m_kept HS EE |]). destruct Hr. }
prreg HS (Z_to_bv 5 15) Q15. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
assert (Q15' : getr (ms_regs ms3) (Z_to_bv 5 15) = w64 (b9_cp x)) by (rewrite Q15; exact E33).
assert (Q10' : getr (ms_regs ms3) (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1)).
{ rewrite Q10, E19, E10, b9s5m_w64_off, alu64_add_lit. unfold w64. f_equal; lia. }
assert (Q11' : getr (ms_regs ms3) (Z_to_bv 5 11) = w64 (Z.of_nat (length V) - 1)).
{ rewrite Q11, E10, b9s5m_w64_off. unfold w64. f_equal; lia. }
assert (Q12' : getr (ms_regs ms3) (Z_to_bv 5 12) = w64 (2 ^ 64 - 1 - vp0)).
{ b9s5m_rreg HS. apply b9s5m_den_U. apply (U_not _ 19 vp0); [exact E19 | lia]. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9S5_DQ) rg mm mdx) end.
apply (HDQ x ei kp vp0 lyc Sc Wc (ms_regs ms3) (ms_mem ms3) mdv3).
apply (b9s5m_to_Q n DQ x ei kp vp0 lyc Sc Wc rX memc mdc (ms_regs ms3) (ms_mem ms3) mdv3 HI HJ KM5 KV5 QK
  Q15' Q10' Q11' Q12'); [change (b9_v0 x ei) with V; lia|].
change (b9_v0 x ei) with V. rewrite <- HB0'. exact BD.
Qed.

End x.
End d.
