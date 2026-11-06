(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of plugin-hostd's relay_finish, in the form of the cgif fake-frame
   walks of proofs/cgif/cgif_file_fuzzer/lib/A/ACk1.v (prologue, stack_malloc, exit), lib/A/AC8h.v (call sites) and
   lib/A/ACfj.v:157-163 (a loop closed by induction on its trip count). *)
(* Modified by Theorem Labs, 2026-10: lane W5 relay_finish_h (a Theorem Labs lane): started from W_relay_finish.v's text at
   a working branch 273def0a61d, which stops after the pthread_mutex_lock call; this file walks the rest. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record)), row C1 of
   a Theorem Labs lane's pool (a Theorem Labs lane): the walk is pb_relay_finish_h_x, stated over any allocator relation ARx with its laws
   (W_contract_x.v rf_spec_x; Section c below, the AR Section's hypotheses as their twins plus PST / ARx / hl / LAWS /
   HP0 and the frame twins' hypotheses of W_frame_x.v); pb_relay_finish_h keeps its statement, byte-identical,
   re-derived from pb_relay_finish_h_x at ARx := ARi0, PST := [] (W_contract_x.v rf_spec_x_AR0; Section cAR, which
   takes LX0 in place of LAWS). *)
(* Modified by Theorem Labs, 2026-10: the room round (ROOM-TEXTS.md v3 (sha256 767baa12f13c; internal record)): the walk
   takes RP and threads rf_spec_x's rp_RM budget (each round: the free's 1, then gestures_end's charge) and its
   cnt_ok_pk count premise to the free and to gestures_end; the fake frame's seat and release keep the room by roomp's
   law rp_RPF; the seat is W_frame_x.v's aj_stack_malloc_pres_at_raw_x, whose post states S2 = set_fs f Sc. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_relay_finish_h.v, with its module paths, module names and numbers changed; 305 of its 347 lines of code are new or changed and 6137 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove = 0x8b258), segment G4: answer's return 0x8b3a0 (SR_T) .. `ret` 0x8b430.

   The segment releases the class-0 side-stack frame and returns. It seats a FRESH symbolic state at
   BASE + (AF_sup_remove + SR_T) over the registers of the cut (sup_remove_s1.v's sr_cut), with eleven extra atoms:
   atom 32 the frame's flag address FL, atoms 33 .. 42 the ten entry registers the prologue saved (ra, s0 .. s8),
   so that every chunk is a closed term. The regions, in this order:
   - the flag byte [FL, FL + 1) (base atom 32), a write window with no chunk: the allocator owns it, so it lies
     outside the frame and the frame's shadow (sup_resp's A walk, an earlier version of lib/A/Prog/sup_resp.v:618-640);
   - the frame's shadow [SB + F / 8, SB + F / 8 + 8) (base s6, atom 22), a write window with NO chunks (the eight
     f5 bytes of 0x8b3b4 .. 0x8b3d0);
   - the frame header [F, F + 8) (base s7, atom 23), a write window with no chunk (the magic 0x45e0360e of 0x8b3a8);
   - the frame's flag word [F + 56, F + 64) (base s2, atom 18), read-only, holding FL (the `ld a1,56(s2)` of
     0x8b3d4);
   - the ten saves [sp0 - 80, sp0) (base s0, atom 8), read-only, the epilogue's restores at 0x8b404 .. 0x8b428.
   The run is the plain flag-store run (PaLibF's aj_flag_store_pi through paj_run_flag_sh): the token executor
   refuses a writable region in the shadow band. `beqz s2` at 0x8b3ac falls through (F <> 0, the HPTR fact on
   atom 18), so the real-stack arm 0x8b3e0 .. 0x8b3fc is not walked.
   The post is the statement's apost_baseF at the ambient FP state fx (the release reaches no printf wrapper, so
   apost_baseF_of_base takes the left disjunct): the final state is (lyc, stack_free_state 0 pos Sc), the registers
   are the entry's (the epilogue restores them from the saves), and sr_post is the one that already held at the cut
   (a0 is not written between 0x8b3a0 and `ret`, blocks_stack_free_state keeps the blocks, rec_repA and astr_atR
   survive because g_rec, record.spill, the recorder's blocks and the reply's block lie outside the three write
   windows, and mo_le passes through mo_le_set_fs_r). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns sup_remove_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- a recorder block is a live block (CmdRecAns.rca_rep_blocks) ---- *)
Lemma sr4_rep_live : forall B ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros B ly S rd R O pn (Q & HQ & HO) Hin. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.
(* g_rec and record.spill are the program's statics the image holds (CmdGlob's cmd_PG) *)
Lemma sr4_inPG : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> inFP cmd_PG a.
Proof.
intros a [Ha | Ha]; unfold cmd_PG.
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn; unfold REC_SIZE in Ha; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn; unfold SC_SIZE in Ha; lia].
Qed.

(* ---- the symbolic state at SR_T ---- *)
(* the flag byte, the only cell of the release outside the frame and its shadow *)
Definition sr4_flagb : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
(* the frame's shadow at s6 = SB + F / 8 (atom 22): eight bytes, written f5, no chunk read *)
Definition sr4_sh : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 8 [].
(* the frame header at s7 = F (atom 23): the magic word at F + 0 *)
Definition sr4_hdr : YP09.region := YP09.mkRegion (Some 23%nat) 0 8 0 8 [].
(* the frame's flag word at s2 = F (atom 18), read-only, holding FL *)
Definition sr4_flagw : YP09.region := YP09.mkRegion (Some 18%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
(* the saves below sp0 = s0 (atom 8), read-only: the slot sp0 - 8 - 8 j holds atom 33 + j *)
Definition sr4_saves : YP09.region :=
YP09.mkRegion (Some 8%nat) (-80) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0))].
Definition sr4_regions : smem := [sr4_flagb; sr4_sh; sr4_hdr; sr4_flagw; sr4_saves].
(* atom 18 is the frame address (nonzero: `beqz s2` falls through), atom 32 the flag address *)
Definition sr4_atoms : list (nat * afact) := [ (18%nat, HPTR 5); (32%nat, HPTR 0) ].
Definition ss_sr4 : sstate := mkSS (AF_sup_remove + SR_T) sr_atoms sr4_regions None (mkFacts sr4_atoms [] []).
(* the extra atoms: the flag address, then the entry's ra, s0 .. s8 *)
Definition sr4_extra (regs : bvmap 5 word) (fl : Z) : list word :=
[Z_to_bv 64 fl; getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
 getr regs 21; getr regs 22; getr regs 23; getr regs 24].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a byte outside a run's write windows keeps its view *)
Lemma sr4_frame_kept : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' a Hf Ha Hw. apply aview_eq_of. apply Hf. rewrite unsigned_lit_small by lia. exact Hw. Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk hypotheses, with cgif's names; the release reads no image object through an atom and
   calls nothing, so TL, TLF, SMP, MTL, SIGP and the statement's own hypotheses are not needed here *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let RUNF := aj_flag_store_pi (PL := PL_cmd) (PI := PI) (fx := fx) B LAWS ML ASF FFL.

Theorem sr_g4 : sr_g4_stmt B MT.
Proof.
unfold sr_g4_stmt.
intros ly S W regs mem md ch id R O lyc Sc Wc regsc memc mdc pos HPRE HCUT HPOST.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HPRE0 & Hfr7 & HROD & HRO & H10 & Hid & HREP0 & Hev & Hlive & MOK).
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCUT as (HJ & Hflag & Esp & V8 & V9 & V18 & V19 & V20 & V22 & V23 & V24 & V3 & V4 & V25 & V26 & V27 & HSAV).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkj & _).
assert (FFS : SUP_REMOVE_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_STK in exact v)) by reflexivity.
assert (Hfin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR Hfin) as (HF64 & _ & _).
destruct (FFL lyc Sc Wc memc mdc 0 pos HAR Hfin) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in *.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres. change (64 / 8) with 8 in HFSpres.
pose proof HFLrng as ((HFLapp & HFLni) & HFL4096 & HFLz & HFLceil).
(* the frame bytes and the flag byte are no image bytes *)
assert (HNFimg : forall a, frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64 -> ~ in_img SEGS a)
  by (intros a Ha; exact (frm_img SEGS B LAWS lyc Sc Wc memc mdc 0 pos a HAR Hfin ltac:(change (fs_frame_bytes 0) with 64; lia))).
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8m : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HF8nn : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HFz : F + 64 <= SB \/ 0x10007fff8000 <= F)
  by (clear - HFhigh C1; unfold in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SB, ASAN_CEIL in *; lia).
(* the flag byte lies outside the frame and outside the frame's shadow (the allocator owns it) *)
assert (HnoF : FL < F \/ F + 64 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_ge_dec FL (F + 64)) as [Hh|Hh]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
assert (HnoS : FL < SB + F / 8 \/ SB + F / 8 + 8 <= FL).
{ destruct (Z_lt_ge_dec FL (SB + F / 8)) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_ge_dec FL (SB + F / 8 + 8)) as [Hh|Hh]; [exfalso | right; lia].
  pose proof (proj2 (HFSpres (FL - (SB + F / 8)) ltac:(lia))) as Hn.
  replace (SB + F / 8 + (FL - (SB + F / 8))) with FL in Hn by lia. exact (Hn HFLown). }
(* ---- the symbolic state ---- *)
remember (Eimg (Ereg regsc (sr4_extra regs FL))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (sr4_extra regs FL)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j (sr4_extra regs FL) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (EE 3%nat 3%bv eq_refl); exact V3).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (EE 4%nat 4%bv eq_refl); exact V4).
assert (E8 : ew E 8 = getr regs 2) by (rewrite (EE 8%nat 8%bv eq_refl); exact V8).
assert (E10 : ew E 10 = getr regsc 10) by (apply EE; reflexivity).
assert (E18 : ew E 18 = Z_to_bv 64 F) by (rewrite (EE 18%nat 18%bv eq_refl); exact V18).
assert (E22 : ew E 22 = Z_to_bv 64 (SB + F / 8)) by (rewrite (EE 22%nat 22%bv eq_refl); exact V22).
assert (E23 : ew E 23 = Z_to_bv 64 F) by (rewrite (EE 23%nat 23%bv eq_refl); exact V23).
assert (E25 : ew E 25 = getr regs 25) by (rewrite (EE 25%nat 25%bv eq_refl); exact V25).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (EE 26%nat 26%bv eq_refl); exact V26).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EE 27%nat 27%bv eq_refl); exact V27).
assert (E32 : ew E 32 = Z_to_bv 64 FL) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 1) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 8) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 9) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr regs 18) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr regs 19) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr regs 20) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = getr regs 21) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = getr regs 22) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = getr regs 23) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = getr regs 24) by exact (EX 10%nat ltac:(lia)).
clear EX.
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; reflexivity).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; unfold ASAN_CEIL in *; lia).
assert (U22 : bv_unsigned (ew E 22) = SB + F / 8)
  by (rewrite E22; apply unsigned_lit_small; unfold SB, ASAN_CEIL in *; lia).
assert (U23 : bv_unsigned (ew E 23) = F) by (rewrite E23; apply unsigned_lit_small; unfold ASAN_CEIL in *; lia).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; unfold ASAN_CEIL in *; lia).
pose proof HSAV as (SV1 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24).
assert (SAV : forall (j : Z) (n : nat) (v : word), ew E n = v -> 0 <= j ->
  rdword (rdW Wc memc) (spZ regs - 8 - 8 * j) = Some (bv_unsigned v) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs) (YP09.mkChunk (-8 - 8 * j) (CVal 8 (SOff n 0)))).
{ intros j n v Hn Hj Hrd.
  apply (chunk_ok_val SEGS E _ _ _ 8 _ (bv_unsigned v)).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 v) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - replace (spZ regs + (-8 - 8 * j)) with (spZ regs - 8 - 8 * j) by lia.
    exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hrd). }
assert (HS : st_ok_pi SEGS VAL E ss_sr4
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_remove + SR_T))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sr4. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold sr4_regions, sr4_flagb, sr4_sh, sr4_hdr, sr4_flagw, sr4_saves.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLpres.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U22.
      split; [unfold SB; lia|]. split; [unfold SB, ASAN_CEIL in *; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U23.
      split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
      split; [lia|]. split; [unfold ASAN_CEIL in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F 56 8 (SOff 32 0) FL).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold ASAN_CEIL in *. lia.
      * cbn. lia.
      * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hflag).
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
      split; [unfold ASAN_CEIL in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [exact (SAV 0 33%nat _ E33 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 0) with (spZ regs - 8) by lia; exact SV1))|].
      apply Forall_cons; [exact (SAV 1 34%nat _ E34 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 1) with (spZ regs - 16) by lia; exact SV8))|].
      apply Forall_cons; [exact (SAV 2 35%nat _ E35 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 2) with (spZ regs - 24) by lia; exact SV9))|].
      apply Forall_cons; [exact (SAV 3 36%nat _ E36 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 3) with (spZ regs - 32) by lia; exact SV18))|].
      apply Forall_cons; [exact (SAV 4 37%nat _ E37 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 4) with (spZ regs - 40) by lia; exact SV19))|].
      apply Forall_cons; [exact (SAV 5 38%nat _ E38 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 5) with (spZ regs - 48) by lia; exact SV20))|].
      apply Forall_cons; [exact (SAV 6 39%nat _ E39 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 6) with (spZ regs - 56) by lia; exact SV21))|].
      apply Forall_cons; [exact (SAV 7 40%nat _ E40 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 7) with (spZ regs - 64) by lia; exact SV22))|].
      apply Forall_cons; [exact (SAV 8 41%nat _ E41 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 8) with (spZ regs - 72) by lia; exact SV23))|].
      apply Forall_cons; [exact (SAV 9 42%nat _ E42 ltac:(lia) ltac:(replace (spZ regs - 8 - 8 * 9) with (spZ regs - 80) by lia; exact SV24))|].
      apply Forall_nil.
  - apply pairwise_disjoint_of_extents.
    unfold sr4_regions, sr4_flagb, sr4_sh, sr4_hdr, sr4_flagw, sr4_saves, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U22, U23, U18, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite FFS in Hstk0, Hslo, Hbot.
    clear - HnoF HnoS HFz HF4096 HFceil HF8lo HF8m HF8nn HFL4096 HFLceil Hslo Hshi H47 Hceil C1 C3 Hstk0.
    unfold SB, ASAN_CEIL in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok sr4_atoms]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (HFq : F mod 32 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
    repeat match goal with |- _ /\ _ => split end;
      first [exact HFq | unfold ASAN_CEIL in *; lia]. }
(* ---- 0x8b3a0 .. 0x8b430: the magic, the eight shadow bytes f5, the flag byte, the epilogue and `ret` ---- *)
clear HSAV SAV SV1 SV8 SV9 SV18 SV19 SV20 SV21 SV22 SV23 SV24 Hflag.
paj_run_flag_sh RUNF HS HJ.
- lia.
- let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr;
      rewrite ?U32, ?U22, ?U23, ?U18, ?U8; intros Hr;
      first [ exfalso; clear - Hr; lia
            | right; change (flag_addr lyc 0 pos) with FL; clear - Hr; lia
            | left; right; right; right; left; exists 0, pos; split; [left; reflexivity|];
              change (frame_addr lyc 0 pos) with F;
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; clear - Hr; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
                      change (fs_frame_bytes 0 / 8) with 8; clear - Hr; unfold SB in *; lia ] ] | ]);
  destruct Hin.
- intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR end.
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region E (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
    ltac:(exact U32) ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0.
  rewrite Z.add_0_r in V0. change (flag_addr lyc 0 pos) with FL. exact V0.
- collapse_md.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ => rename msX into msF end.
  rename HFr into HFrF. cbn [ms_mem mkst] in HFrF.
  (* the bytes outside the three write windows keep their view *)
  assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (FL <= a < FL + 1) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
    ~ (F <= a < F + 8) -> rdW Wc (ms_mem msF) a = rdW Wc memc a).
  { intros a Ha H1 H2 H3. apply (sr4_frame_kept E _ (w_H Wc) memc (ms_mem msF) a HFrF Ha).
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr;
        rewrite ?U32, ?U22, ?U23, ?U18, ?U8; intros Hr; clear - Hr H1 H2 H3; lia | ]);
    destruct Hin. }
  (* a byte of a live block is outside all three *)
  assert (KBLK : forall p m a, In (p, m) (ablocks B lyc Sc) -> p <= a < p + req_size m ->
    rdW Wc (ms_mem msF) a = rdW Wc memc a).
  { intros p m a Hin Hr.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p m HAR Hin) as (_ & Hp4096 & Hpceil & Hpapp & Hpown & _ & Hn0).
    pose proof (req_size_pos m (proj1 Hn0)) as [Hrq1 Hrq2].
    assert (Happ : p + req_size m <= kLowShadowBeg \/ kHighMemBeg <= p)
      by (destruct Hpapp as [_ [Hx | [Hx _]]]; [left; exact Hx | right; exact Hx]).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p m 0 pos HAR Hin Hfin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 0) with 64 in Hsep. fold F in Hsep.
    apply KEPT.
    - unfold ASAN_CEIL in *. lia.
    - intros Hc. assert (Heq : a = FL) by lia. rewrite Heq in Hr. exact (proj2 (Hpown FL Hr) HFLown).
    - clear - Happ Hr Hp4096 Hpceil HF8lo HF8m HF8nn HF4096 HFceil C1.
      unfold kLowShadowBeg, kHighMemBeg, SB, ASAN_CEIL in *. lia.
    - lia. }
  (* a byte of g_rec or of record.spill is an image byte, so outside all three *)
  assert (KPG : forall a, inFP cmd_PG a -> rdW Wc (ms_mem msF) a = rdW Wc memc a).
  { intros a Hpg.
    pose proof (CmdRecBase.cif_prog_img _ _ IMG a Hpg) as Himg.
    pose proof (pa_img_range a Himg) as Hrng.
    apply KEPT.
    - lia.
    - intros Hc. assert (Heq : a = FL) by lia. rewrite Heq in Himg. exact (HFLni Himg).
    - clear - Hrng HF8lo HF8m HF8nn HF4096 HFceil C1. unfold SB, ASAN_CEIL in *. lia.
    - intros Hc. exact (HNFimg a ltac:(lia) Himg). }
  (* 0x8b430: ret *)
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10.
  prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26.
  prreg HS (27%bv : bv 5) F27.
  eapply (RET Wc E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (apost_baseF_of_base SEGS).
  unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?dm = _ /\ _ =>
    exists lyc, (stack_free_state 0 pos Sc), r, m, dm end.
  (* the configuration *)
  split.
  { rewrite F1, E33. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  (* the journal *)
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); assumption|].
  (* the callee-saved registers, restored from the saves *)
  split.
  { apply aregs_preserved_eqs;
      first [ rewrite F2, E8; reflexivity
            | rewrite F3, E3; reflexivity
            | rewrite F4, E4; reflexivity
            | rewrite F8, E34; reflexivity
            | rewrite F9, E35; reflexivity
            | rewrite F18, E36; reflexivity
            | rewrite F19, E37; reflexivity
            | rewrite F20, E38; reflexivity
            | rewrite F21, E39; reflexivity
            | rewrite F22, E40; reflexivity
            | rewrite F23, E41; reflexivity
            | rewrite F24, E42; reflexivity
            | rewrite F25, E25; reflexivity
            | rewrite F26, E26; reflexivity
            | rewrite F27, E27; reflexivity ]. }
  (* the post, kept across the release *)
  assert (Eabf : ablocks B lyc (stack_free_state 0 pos Sc) = ablocks B lyc Sc)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold sr_post in HPOST.
  destruct HPOST as (R' & O' & q & Hm & HPOST2). cbv zeta in HPOST2.
  destruct HPOST2 as (Hq10 & (Hq4096 & Hq64) & HREP' & HO'1 & HO'2 & HO'3 & Hqin & Hqold & Hqfresh
    & Hstr & Hbb & HMLE).
  unfold sr_post. exists R', O', q. cbv zeta.
  split; [exact Hm|].
  split; [rewrite F10, E10; exact Hq10|].
  split; [split; [exact Hq4096 | exact Hq64]|].
  split.
  { eapply rec_repA_kept; [exact HREP'| |].
    - intros pn Hpn. rewrite Eabf. exact (sr4_rep_live B lyc Sc (rdW Wc memc) R' O' pn HREP' Hpn).
    - intros a [Ha | [Ha | Ha]].
      + exact (KPG a (sr4_inPG a (or_introl Ha))).
      + exact (KPG a (sr4_inPG a (or_intror Ha))).
      + destruct (inFP_ablocks_fp_inv O' a Ha) as (p & m & Hin & Hr).
        exact (KBLK p m a (sr4_rep_live B lyc Sc (rdW Wc memc) R' O' (p, m) HREP' Hin) Hr). }
  split; [exact HO'1|].
  split; [rewrite Eabf; exact HO'2|].
  split; [rewrite Eabf; exact HO'3|].
  split; [rewrite Eabf; exact Hqin|].
  split; [exact Hqold|].
  split; [exact Hqfresh|].
  split.
  { assert (KQ : forall a, q <= a < q + (Z.of_nat (length (snd (sup_remove_m R id))) + 1) ->
      rdW Wc (ms_mem msF) a = rdW Wc memc a).
    { intros a Ha. apply (KBLK q (Z.of_nat (length (snd (sup_remove_m R id))) + 1) a); [exact Hqin|].
      pose proof (req_size_pos (Z.of_nat (length (snd (sup_remove_m R id))) + 1) ltac:(lia)) as [_ Hrq]. lia. }
    destruct Hstr as [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
    rewrite length_app in Hi. cbn [length] in Hi.
    rewrite KQ by lia.
    exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
  split; [change (blocks_bytes (stack_free_state 0 pos Sc)) with (blocks_bytes Sc); exact Hbb|].
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). exact HMLE.
Qed.
End e.
End f.
End d.
