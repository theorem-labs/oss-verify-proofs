(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 298 of its 329 lines of code are new or changed and 983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanSetup.v at a1fdf6ce036f for
   reac-pw/fuzz_rate's image A: role's pcs (E 0x8212c, O 0x821bc, MAL 0x823fc, ABS 0x82380) become rate's (0x82930,
   0x829c0, 0x82c9c, 0x82b7c), the registers are renamed as rate's code has them (pp + 0x4000 s5 -> s7, the shadow
   offset s7 -> s2, ra := -1 -> s11 := -1, n_ent t2 -> t3, s4 -> s3, s10 -> s9, the operands s11 t3 -> s10 t2), the
   real-frame cells 0x68 / 0x78 / 0x80 / 0x28 become 0xa8 / 0xb8 / 0xc0 / 0x78, the exits' kept registers are rate's
   (s6 and s10 at MAL), the cut file is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_), the list lemmas come from
   lib/A/RtPgScanKit.v, the memory facts from lib/A/RtPgMem.v and the image facts from lib/A/RtPgSteps.v. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the set-up of the inlined
   expect_rate (fuzz_rate.c:63-70) inside LLVMFuzzerTestOneInput (0x80714), from the cut E 0x82930 to the outer scan
   head O 0x829c0, the malformed check MAL 0x82c9c or the absent check ABS 0x82b7c. Proves no function (kind: segment
   lemma): lib/A/RtPgSeg.v's piece statement rs_piece_W11a_setup_stmt at image A's segments (rk_setup_A).

   THE CODE (s7 = pp + 0x4000, s1 = R, s2 = the runtime's shadow offset K, s11 = pp)
     0x82930 .. 0x8293c  a0 := pp + 0x4008; the instrumented check of a0 (srli, add s2, lb); 0x82940 bnez -> 0x831d4
     0x82944  lw a0,0(a0)       pp->is_props; 0x82948 beqz -> MAL
     0x8294c .. 0x82958  a0 := pp + 0x4010; its instrumented check; 0x8295c bnez -> 0x83208
     0x82960  lw a0,0(a0)       pp->params_struct; 0x82964 beqz -> ABS
     0x82968 .. 0x82970  ld a0,0xa8(s1) (the shadow index (pp + 0x4d14) >> 3 the preheader stored), add s2, lb;
                         0x82974 bnez -> 0x8323c
     0x82978 .. 0x829bc  a1 := 0, t3 := pp->n_ent (through R+0xb8 = pp + 0x4d14), a4 := 0x68, s9 := 8,
                         t2 and s10 := pp + 0x4014, t4 := pp + 0x401c (pp from R+0xc0), t5 := s10 + 8,
                         t6 := s10 + 4, s3 := n_ent - 1, s11 := -1; falls through to O.
   No store, no call, no float instruction. MAL and ABS are left before s10 is written (0x82998), so s6 = F and
   s10 = the flags byte hold there as at E.

   HOW. su_blk is the piece as a block lemma, stated for any float state and applied at the run's own fx2. Its
   entry state holds the registers as atoms, with s7 written as the atom of s11 (pp) plus 0x4000, the three
   real-frame cells as one region at R (the cell R+0xa8 holding the shift of pp + 0x4d14 by 3, so the third check
   reads a shadow address of the same form as the first two) and the three fields as one region at pp; is_props and
   params_struct are split before the run, so each run is straight-line. The engine's shadow tokens use s2 as the
   shadow base and one shadow entry over the whole first block (atom pp, [0, 0x4d20)), paid by RtPgMem.rtm_blk_ra:
   every byte of the block is marked usable, so each of the three `lb` reads 0 and no `bnez` is taken. The region
   list has no write window, so the memory at each exit is the memory at E. rk_setup_A reads E's cut, runs su_blk
   and rebuilds MAL's cut (answer (None, -1), RtPgScanF.rk_expect_not_props), ABS's (None, 0, rk_expect_no_struct)
   or O's at at = 0 (rk_inv_start), the parse's answer being the scan's by rk_parse_expect. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgScanF RtPgScanKit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgMem RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the code: the 36 words 0x82930 .. 0x829bc ---- *)
Definition su_tbl : ctable := build_table rsegs RS_E 36 TEmpty.
Lemma su_tbl_ok : table_ok rsegs su_tbl.
Proof. apply build_table_ok0. unfold RS_E. lia. Qed.

(* ---- the shadow base of the instrumented checks: s2 holds the runtime's shadow offset (atom 18) ---- *)
Definition su_Bx : sv := SOff 18 0.
Definition su_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the first block [pp, pp + 0x4d20), pp the atom of s11 (x27) *)
Definition su_SH : list shent := [mkSHE 27 0 0x4d20].

(* ---- the entry state ----
   s7 (x23) = pp + 0x4000 is written as the atom of s11 plus 0x4000; the real frame's cells R+0xa8, R+0xb8,
   R+0xc0 (R = s1, atom 9) and the first block's fields is_props (pp + 0x4008), params_struct (pp + 0x4010) and
   n_ent (pp + 0x4d14) are chunks; n_ent is the extra atom 32. *)
Definition su_ov : list (bv 5 * sv) := [((23%bv : bv 5), SOff 27 0x4000)].
Definition su_regions (ipz psz : Z) : smem :=
[ YP09.mkRegion (Some 9%nat) 0xa8 0xc8 0 0
  [ YP09.mkChunk 0xa8 (CVal 8 (SAlu ALU_SRL (SOff 27 0x4d14) (SLit 3)));
    YP09.mkChunk 0xb8 (CVal 8 (SOff 27 0x4d14));
    YP09.mkChunk 0xc0 (CVal 8 (SOff 27 0)) ];
  YP09.mkRegion (Some 27%nat) 0x4008 0x4d18 0 0
  [ YP09.mkChunk 0x4008 (CVal 4 (SLit ipz));
    YP09.mkChunk 0x4010 (CVal 4 (SLit psz));
    YP09.mkChunk 0x4d14 (CVal 4 (SOff 32 0)) ] ].
Definition su_facts : facts :=
mkFacts [ (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF 4096 (2 ^ 47 - 0x4d20) 0); (32%nat, mkAF 0 32 0) ]
[] [].
Definition su_ss (ipz psz : Z) : sstate := mkSS RS_E (sk_sr su_ov) (su_regions ipz psz) None su_facts.

(* the extra atoms: slot 32 is n_ent *)
Definition su_extra (nent : Z) : list word := [Z_to_bv 64 nent].

(* ---- the registers the cuts after the set-up read and the set-up does not write ----
   O: sp, gp, tp and rs_L_chk's s0, s1, s2, s4, s5, and s8 (rc); MAL and ABS: those and s6 (F), s10 (the flags) *)
Definition SU_KEPT_O : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 24].
Definition SU_KEPT_X : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 26].

(* ---- the walk's plumbing ---- *)
Ltac su_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok su_tbl_ok HS HJ SHOK su_Bspan stop; [awr_ok_tac | ] end.
Ltac su_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac su_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* the state at one exit of the set-up: the world, the journal and the memory as at E (the run writes no byte),
   the I/O state, the kept registers, and what the exit computes *)
Definition su_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (kept : list (bv 5))
(Rr : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r, In r kept -> getr regs2 r = getr regs r) /\ Rr regs2.

Lemma su_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept
(Rr : bvmap 5 word -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r, In r kept -> getr (ms_regs ms) r = getr regs r) -> Rr (ms_regs ms) ->
su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept Rr W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept Rr E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.

(* what the run to O computes, in rs_L_scan's order: s11 = -1, s9 = 8 (POD_STRING), t3 = n_ent,
   s3 = n_ent - 1, t2 = s10 = pp + 0x4014, t6 = pp + 0x4018, t4 = t5 = pp + 0x401c, a1 = 0 (at), a4 = 104 *)
Definition su_RO (pp nent : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 27) = w64 (-1) /\ getr regs2 (Z_to_bv 5 25) = w64 8 /\
getr regs2 (Z_to_bv 5 28) = w64 nent /\ getr regs2 (Z_to_bv 5 19) = w64 (nent - 1) /\
getr regs2 (Z_to_bv 5 7) = w64 (pp + 0x4014) /\ getr regs2 (Z_to_bv 5 26) = w64 (pp + 0x4014) /\
getr regs2 (Z_to_bv 5 31) = w64 (pp + 0x4018) /\ getr regs2 (Z_to_bv 5 29) = w64 (pp + 0x401c) /\
getr regs2 (Z_to_bv 5 30) = w64 (pp + 0x401c) /\ getr regs2 (Z_to_bv 5 11) = w64 0 /\
getr regs2 (Z_to_bv 5 14) = w64 104.

(* THE BLOCK. From E with s1 = R, s2 = K, s11 = pp, s7 = pp + 0x4000, the three real-frame cells and the three
   fields of the first block: is_props = 0 goes to MAL, params_struct = 0 to ABS, else the set-up runs to O. *)
Lemma su_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R pp nent : Z) (ip ps : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 18) = w64 SHADOW_OFF ->
getr regs (Z_to_bv 5 27) = w64 pp -> getr regs (Z_to_bv 5 23) = w64 (pp + 0x4000) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb8) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 (Z.b2z ip) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 (Z.b2z ps) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 nent -> 0 <= nent <= 32 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF pp 0x4d20 ->
in_app pp 0x4d20 -> 4096 <= pp -> pp + 0x4d20 <= 2 ^ 47 -> pp + 0x4d20 <= R -> R + 0xc8 <= 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs RS_E regs memc mdc)
(if ip then
   if ps then su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_O SU_KEPT_O (su_RO pp nent)
   else su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_ABS SU_KEPT_X (fun _ => True)
 else su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_MAL SU_KEPT_X (fun _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp nent ip ps
HJ H9 H18 H27 H23 Va8 Vb8 Vc0 Vip Vps Vn Hn HRA Happ Hpp0 Hpp1 HppR HR1.
pose proof RtPgSteps.rts_wx as Hwx. pose proof RtPgSteps.rts_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
set (E := Ereg regs (su_extra nent)).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (exact (eq_trans (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
  by (exact (eq_trans (ew_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl) H18)).
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (exact (eq_trans (ew_Ereg_nat regs _ 27 (Z_to_bv 5 27) eq_refl) H27)).
assert (E32 : ew E 32 = Z_to_bv 64 nent) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (HE : forall ipz psz, (ipz = 0 \/ ipz = 1) -> (psz = 0 \/ psz = 1) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 ipz ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 psz ->
  st_ok rsegs E (su_ss ipz psz) (restrict (w_H W) (mkst regs (Z_to_bv 64 RS_E) memc (seg_rom rsegs)))).
{ intros ipz psz Hi Hp Vi Vp. rewrite restrict_mkst_fx. unfold su_ss. apply (entry_st_ok_full rsegs).
  - apply sk_regs_ok. repeat constructor.
    + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    + cbn [fst snd]. exact (eq_trans (sk_soff _ 27 pp 0x4000 E27) (eq_sym H23)).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (RtPgMem.rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0xa8 8 _ (Z.shiftr (pp + 0x4d14) 3)); [| | lia | exact Va8].
        -- rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U27. cbn [zalu_raw].
           unfold zcanon, M64. rewrite (Z.mod_small (pp + 0x4d14)) by lia. change (3 mod 2 ^ 64) with 3.
           change (Z.land 3 63) with 3. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia.
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        -- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
      * apply (chunk_ok_val rsegs E _ R 0xb8 8 _ (pp + 0x4d14)); [apply sk_soff; exact E27 | | lia | exact Vb8].
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * apply (chunk_ok_val rsegs E _ R 0xc0 8 _ pp); [| | lia | exact Vc0].
        -- rewrite (sk_soff E 27 pp 0 E27), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + apply (RtPgMem.rtm_ro_region rsegs E (w_H W) memc 27 pp); [exact U27 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ pp 0x4008 4 _ ipz); [reflexivity | | lia | exact Vi].
        change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * apply (chunk_ok_val rsegs E _ pp 0x4010 4 _ psz); [reflexivity | | lia | exact Vp].
        change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * apply (chunk_ok_val rsegs E _ pp 0x4d14 4 _ nent); [| | lia | exact Vn].
        -- rewrite (sk_soff E 32 nent 0 E32), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  - apply pairwise_disjoint_of_extents. unfold su_regions. cbn [map zpairwise_disjoint zall_disjoint].
    unfold extent_of_region, zdisj. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U27. lia.
  - split; [|split; [exact I | exact I]]. cbn [su_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E18, E27, E32. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
(* the three instrumented checks read the first block, every byte of which is marked usable *)
assert (SHOK : sh_ok rsegs su_Bx su_SH E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc E su_Bx 27 pp 0x4d20 pp 0 0x4d20 HRA).
  - unfold su_Bx. apply U_atom; [exact E18 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E27 | lia].
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (HAE : env_agree 32 (Ereg regs (su_extra nent)) E) by (subst E; apply env_agree_refl).
clearbody E.
unfold cfg_at. change (w64 RS_E) with (Z_to_bv 64 RS_E).
destruct ip, ps; cbn [Z.b2z] in Vip, Vps; cbv beta iota;
pose proof (fun H1 H2 => HE _ _ H1 H2 Vip Vps) as HS; clear HE; specialize (HS ltac:(lia) ltac:(lia));
[su_run RS_O | su_run RS_ABS | su_run RS_MAL | su_run RS_MAL];
lazymatch goal with
| HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem; rewrite Hmem in HJ;
  apply SRr_ret;
  apply (su_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' ss' ms _ HS eq_refl eq_refl Hmem HJ);
  [ su_io
  | lazymatch goal with |- forall r, In r ?kl -> _ =>
      intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs (su_extra nent) kl HS HAE
        ltac:(vm_compute; reflexivity) r Hr) end
  | ];
  try exact I;
  unfold su_RO; rewrite !(st_ok_restrict_reg rsegs (w_H W) E' ss' ms _ HS)
end.
repeat split; su_sv;
first [ exact (sk_soff E 27 pp _ E27)
      | rewrite (sk_soff E 32 nent _ E32); unfold w64; f_equal; lia
      | reflexivity
      | cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity ].
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* membership in a concrete list of facts *)
Ltac su_in := unfold rs_L_chk, rs_Hc; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac su_kin := first [unfold SU_KEPT_O | unfold SU_KEPT_X]; apply in_map; cbn [In]; lia.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* THE PIECE: rs_piece_W11a_setup_stmt at image A's segments *)
Theorem rk_setup_A : rs_piece_W11a_setup_stmt rsegs B MT.
Proof.
unfold rs_piece_W11a_setup_stmt. intros cx POST inp Hst HO HA HM.
unfold rs_from_E. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HE.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HE as (Hbase & Hat & Hhz & Hfl & Hcorr & _).
pose proof Hbase as (Hcore & _ & _ & _ & Hpp & Hwf & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
destruct Hst as (Hpre & _).
unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (_ & _ & _ & _ & _ & HeS & _ & HRsz & HRstk & _ & _ & _ & Hppin & _).
cbn [hi_rsz rate_himg_A] in HRsz.
set (e := x_e cx) in *.
(* the first block: live, marked usable, apart from the shadow map, below the real frame *)
assert (Hin : In (q_pp e, Layout.PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hppin).
assert (Hrq : req_size Layout.PP_SIZE = 0x4d20) by reflexivity.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (q_pp e) Layout.PP_SIZE HAR Hin) as (_ & H4096 & Hpc & Happ & _).
rewrite Hrq in Hpc, Happ.
pose proof (@alloc_ceiling_lt rc) as Hcl.
destruct (RtPgMem.rtm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (q_pp e) Layout.PP_SIZE (q_pp e) 0x4d20 HAR Hin ltac:(lia)
  ltac:(rewrite Hrq; lia)) as (HRA & _).
unfold T_SEG_STK, ASTACK in HRstk.
(* the record's three fields the set-up reads *)
assert (Hb : Z.of_nat (length (buf rec)) <= Layout.POD_BUF_MAX).
{ unfold buf. unfold corrupt in Hcorr. destruct (p_corr rec); [discriminate Hcorr|].
  destruct Hwf as (_ & _ & _ & _ & H5440 & _). unfold Layout.POD_BUF_MAX. lia. }
pose proof (rk_nent_le rec Hwf) as Hn32.
assert (Hs : Forall (fun en => (length (e_body en) <= 96)%nat) (ents rec)).
{ eapply Forall_impl; [|exact (rk_ents_wf rec Hwf)]. intros en (_ & Hl & Hz). lia. }
pose proof (RtPgMem.rtm_pp_is_props rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec)
  (corrupt rec) Hb Hn32 Hs (w_H W2) mem2 (q_pp e) Hpp) as Vip.
pose proof (RtPgMem.rtm_pp_params_struct rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec)
  (corrupt rec) Hb Hn32 Hs (w_H W2) mem2 (q_pp e) Hpp) as Vps.
pose proof (RtPgMem.rtm_pp_n_ent rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec)
  (corrupt rec) Hb Hn32 Hs (w_H W2) mem2 (q_pp e) Hpp) as Vn.
(* the registers and the real-frame cells at E *)
unfold rs_at_cx in Hat.
pose proof (sk_at_get _ _ _ _ _ 9 (q_R e) Hat ltac:(su_in)) as R9.
pose proof (sk_at_get _ _ _ _ _ 18 SHADOW_OFF Hat ltac:(su_in)) as R18.
pose proof (sk_at_get _ _ _ _ _ 27 (q_pp e) Hat ltac:(su_in)) as R27.
pose proof (sk_at_get _ _ _ _ _ 23 (q_pp e + 0x4000) Hat ltac:(su_in)) as R23.
pose proof (sk_at_cell _ _ _ _ _ XR 0xa8 (Z.shiftr (q_pp e + 0x4d14) 3) Hat ltac:(su_in)) as Va8.
pose proof (sk_at_cell _ _ _ _ _ XR 0xb8 (q_pp e + 0x4d14) Hat ltac:(su_in)) as Vb8.
pose proof (sk_at_cell _ _ _ _ _ XR 0xc0 (q_pp e) Hat ltac:(su_in)) as Vc0.
cbn [rt_xv] in Va8, Vb8, Vc0.
assert (Hsh : 0 <= Z.shiftr (q_pp e + 0x4d14) 3 < 2 ^ 64)
  by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.mod_small in Va8 by exact Hsh. rewrite Z.mod_small in Vb8, Vc0 by lia.
(* the facts every exit keeps: rs_L_chk and the registers and cells the exits name *)
assert (Hchk : rs_at rsegs (w_H W2) mem2 regs2 e (rs_L_chk rsegs cx)).
{ apply (sk_at_sub _ _ _ _ _ _ Hat). intros x Hx. apply in_or_app. left. exact Hx. }
pose proof (sk_at_get _ _ _ _ _ 24 (snd (rs_PA rsegs cx rec)) Hat ltac:(su_in)) as R24.
pose proof (sk_at_get _ _ _ _ _ 22 (q_F e) Hat ltac:(su_in)) as R22.
pose proof (sk_at_get _ _ _ _ _ 26 (q_fl e) Hat ltac:(su_in)) as R26.
assert (C78 : rt_at rsegs (w_H W2) mem2 regs2 e (LCell XR 0x78) (q_F e))
  by (unfold rs_at in Hat; rewrite Forall_forall in Hat; apply (Hat (LCell XR 0x78, _)); su_in).
assert (CC0 : rt_at rsegs (w_H W2) mem2 regs2 e (LCell XR 0xc0) (q_pp e))
  by (unfold rs_at in Hat; rewrite Forall_forall in Hat; apply (Hat (LCell XR 0xc0, _)); su_in).
(* the parse's answer is the scan's: the flags bit is 0 and the record is not corrupted *)
assert (HPA : rs_PA rsegs cx rec = rs_E0 rec) by (unfold rs_PA; fold e; rewrite Hfl; apply rk_parse_expect; assumption).
eapply SRr_bind.
{ exact (su_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R e) (q_pp e) (Z.of_nat (length (ents rec)))
    (is_props rec) (params_struct rec) HJ R9 R18 R27 R23 Va8 Vb8 Vc0 Vip Vps Vn ltac:(lia) HRA Happ H4096
    ltac:(lia) ltac:(lia) ltac:(lia)). }
intros W3 c3 _ Hpost. revert Hpost.
destruct (is_props rec) eqn:Eip; [destruct (params_struct rec) eqn:Eps|]; cbv beta iota;
intros (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk & HR);
pose proof (sk_at_keep _ _ regs2 regs3 _ (rs_L_chk rsegs cx) _ Hk ltac:(vm_compute; reflexivity) Hchk) as Hchk3;
pose proof (sk_chk_base B MT cx fx2 rec rs_PZ ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
  ltac:(intros r Hr; apply Hk; destruct Hr as [->|[->| ->]]; su_kin)) as Hbase3.
- (* O: the scan starts at at = 0 *)
  destruct HR as (Q27 & Q25 & Q28 & Q19 & Q7 & Q26 & Q31 & Q29 & Q30 & Q11 & Q14).
  apply (HO fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at, rs_L_scan. apply Forall_app. split; [apply Forall_app; split; [exact Hchk3|]|].
    - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
      + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
      + exact Q27.
      + exact Q25.
      + exact Q28.
      + exact Q19.
      + exact Q7.
      + exact Q26.
      + exact Q31.
      + exact Q29.
      + exact Q30.
      + exact C78.
      + exact CC0.
    - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
      + exact Q11.
      + exact Q14. }
  split; [exact Hhz|]. split; [exact (rk_inv_start rec Eip Eps)|].
  unfold rs_chk_rec. rewrite HPA. auto.
- (* ABS: the params property's value is not a Struct, the answer is (None, 0) *)
  apply (HA fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  rewrite HPA, (rk_expect_no_struct rec Eip Eps) in *. cbn [fst snd] in *.
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hchk3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
    + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
    + exact C78.
    + exact CC0. }
  split; [exact Hhz|]. rewrite HPA. split; reflexivity.
- (* MAL: not an Object of Props, the answer is (None, -1) *)
  apply (HM fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  rewrite HPA, (rk_expect_not_props rec Eip) in *. cbn [fst snd] in *.
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hchk3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rt_at fst snd].
    + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
    + rewrite (Hk (Z_to_bv 5 22)) by su_kin. exact R22.
    + rewrite (Hk (Z_to_bv 5 26)) by su_kin. exact R26.
    + exact C78.
    + exact CC0. }
  split; [exact Hhz|]. rewrite HPA. split; reflexivity.
Qed.
End e.
End c.

Print Assumptions rk_setup_A.
