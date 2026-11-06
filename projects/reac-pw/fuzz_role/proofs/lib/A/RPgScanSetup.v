(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v; 305 of its 341 lines of code are new or changed and 978 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the set-up of the inlined expect_role
   (fuzz_role.c:43-47) inside LLVMFuzzerTestOneInput (0x7ff88), from the cut E 0x8212c to the outer scan head
   O 0x821bc, the malformed check MAL 0x823fc or the absent check ABS 0x82380. Proves no function (kind: segment
   lemma): lib/A/RPgSeg.v's piece statement rs_piece_W11a_setup_stmt at image A's segments (rk_setup_A).

   THE CODE (s5 = pp + 0x4000, s1 = R, s7 = the runtime's shadow offset K)
     0x8212c .. 0x82138  a0 := pp + 0x4008; the instrumented check of a0 (srli, add s7, lb); 0x8213c bnez -> 0x82740
     0x82140  lw a0,0(a0)       pp->is_props; 0x82144 beqz -> MAL
     0x82148 .. 0x82154  a0 := pp + 0x4010; its instrumented check; 0x82158 bnez -> 0x82764
     0x8215c  lw a0,0(a0)       pp->params_struct; 0x82160 beqz -> ABS
     0x82164 .. 0x8216c  ld a0,0x68(s1) (the shadow index (pp + 0x4d14) >> 3 the preheader stored), add s7, lb;
                         0x82170 bnez -> 0x8278c
     0x82174 .. 0x821b8  a1 := 0, t2 := pp->n_ent (through R+0x78 = pp + 0x4d14), a4 := 0x68, s10 := 8, s11 and
                         t3 := pp + 0x4014, t4 := pp + 0x401c (pp from R+0x80), t5 := s11 + 8, t6 := s11 + 4,
                         s4 := n_ent - 1, ra := -1; falls through to O.
   No store, no call, no float instruction.

   HOW. su_blk is the piece as a block lemma, stated for any float state and applied at the run's own fx2. Its
   entry state holds the registers as atoms, with s5 written as the atom of s11 (pp) plus 0x4000, the three
   real-frame cells as one region at R (the cell R+0x68 holding the shift of pp + 0x4d14 by 3, so the third check
   reads a shadow address of the same form as the first two) and the three fields as one region at pp; is_props and
   params_struct are split before the run, so each run is straight-line. The engine's shadow tokens use s7 as the
   shadow base and one shadow entry over the whole first block (atom pp, [0, 0x4d20)), paid by RPgMem.rm_blk_ra:
   every byte of the block is marked usable, so each of the three `lb` reads 0 and no `bnez` is taken. The region
   list has no write window, so the memory at each exit is the memory at E. rk_setup_A reads E's cut, runs su_blk
   and rebuilds MAL's cut (answer (None, -1), RPgScanF.rk_expect_not_props), ABS's (None, 0, rk_expect_no_struct)
   or O's at at = 0 (rk_inv_start), the parse's answer being the scan's by rk_parse_expect. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgMem RPgScanF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges RPgCheck RPgScanOuter.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code: the 36 words 0x8212c .. 0x821b8 ---- *)
Definition su_tbl : ctable := build_table rsegs RS_E 36 TEmpty.
Lemma su_tbl_ok : table_ok rsegs su_tbl.
Proof. apply build_table_ok0. unfold RS_E. lia. Qed.

(* ---- the shadow base of the instrumented checks: s7 holds the runtime's shadow offset (atom 23) ---- *)
Definition su_Bx : sv := SOff 23 0.
Definition su_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the first block [pp, pp + 0x4d20), pp the atom of s11 (x27) *)
Definition su_SH : list shent := [mkSHE 27 0 0x4d20].

(* ---- the entry state ----
   s5 (x21) = pp + 0x4000 is written as the atom of s11 plus 0x4000; the real frame's cells R+0x68, R+0x78,
   R+0x80 (R = s1, atom 9) and the first block's fields is_props (pp + 0x4008), params_struct (pp + 0x4010) and
   n_ent (pp + 0x4d14) are chunks; n_ent is the extra atom 32. *)
Definition su_ov : list (bv 5 * sv) := [((21%bv : bv 5), SOff 27 0x4000)].
Definition su_regions (ipz psz : Z) : smem :=
[ YP09.mkRegion (Some 9%nat) 0x68 0x88 0 0
  [ YP09.mkChunk 0x68 (CVal 8 (SAlu ALU_SRL (SOff 27 0x4d14) (SLit 3)));
    YP09.mkChunk 0x78 (CVal 8 (SOff 27 0x4d14));
    YP09.mkChunk 0x80 (CVal 8 (SOff 27 0)) ];
  YP09.mkRegion (Some 27%nat) 0x4008 0x4d18 0 0
  [ YP09.mkChunk 0x4008 (CVal 4 (SLit ipz));
    YP09.mkChunk 0x4010 (CVal 4 (SLit psz));
    YP09.mkChunk 0x4d14 (CVal 4 (SOff 32 0)) ] ].
Definition su_facts : facts :=
mkFacts [ (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF 4096 (2 ^ 47 - 0x4d20) 0); (32%nat, mkAF 0 32 0) ]
[] [].
Definition su_ss (ipz psz : Z) : sstate := mkSS RS_E (RPgCheck.ck_sr su_ov) (su_regions ipz psz) None su_facts.

(* the extra atoms: slot 32 is n_ent *)
Definition su_extra (nent : Z) : list word := [Z_to_bv 64 nent].

(* ---- the value of an atom plus an offset ---- *)
Lemma su_soff : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* ---- the registers the cuts after the set-up read and the set-up does not write ---- *)
Definition SU_KEPT_O : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24].
Definition SU_KEPT_X : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 27].

(* ---- the walk's plumbing ---- *)
Ltac su_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok su_tbl_ok HS HJ SHOK su_Bspan stop; [awr_ok_tac | ] end.
Ltac su_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac su_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
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

(* what the run to O computes: ra = -1, t2 = n_ent, a1 = 0 (at), a4 = 104, s4 = n_ent - 1, s10 = 8 (POD_STRING),
   s11 = t3 = pp + 0x4014, t4 = t5 = pp + 0x401c, t6 = pp + 0x4018 *)
Definition su_RO (pp nent : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 1) = w64 (-1) /\ getr regs2 (Z_to_bv 5 7) = w64 nent /\
getr regs2 (Z_to_bv 5 11) = w64 0 /\ getr regs2 (Z_to_bv 5 14) = w64 104 /\
getr regs2 (Z_to_bv 5 20) = w64 (nent - 1) /\ getr regs2 (Z_to_bv 5 26) = w64 8 /\
getr regs2 (Z_to_bv 5 27) = w64 (pp + 0x4014) /\ getr regs2 (Z_to_bv 5 28) = w64 (pp + 0x4014) /\
getr regs2 (Z_to_bv 5 29) = w64 (pp + 0x401c) /\ getr regs2 (Z_to_bv 5 30) = w64 (pp + 0x401c) /\
getr regs2 (Z_to_bv 5 31) = w64 (pp + 0x4018).

(* THE BLOCK. From E with s1 = R, s7 = K, s11 = pp, s5 = pp + 0x4000, the three real-frame cells and the three
   fields of the first block: is_props = 0 goes to MAL, params_struct = 0 to ABS, else the set-up runs to O. *)
Lemma su_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R pp nent : Z) (ip ps : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
getr regs (Z_to_bv 5 27) = w64 pp -> getr regs (Z_to_bv 5 21) = w64 (pp + 0x4000) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x68) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 (Z.b2z ip) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 (Z.b2z ps) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 nent -> 0 <= nent <= 32 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF pp 0x4d20 ->
in_app pp 0x4d20 -> 4096 <= pp -> pp + 0x4d20 <= 2 ^ 47 -> pp + 0x4d20 <= R -> R + 0x1a0 <= 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs RS_E regs memc mdc)
(if ip then
   if ps then su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_O SU_KEPT_O (su_RO pp nent)
   else su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_ABS SU_KEPT_X (fun _ => True)
 else su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_MAL SU_KEPT_X (fun _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp nent ip ps
HJ H9 H23 H27 H21 V68 V78 V80 Vip Vps Vn Hn HRA Happ Hpp0 Hpp1 HppR HR1.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
set (E := Ereg regs (su_extra nent)).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (exact (eq_trans (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
  by (exact (eq_trans (ew_Ereg_nat regs _ 23 (Z_to_bv 5 23) eq_refl) H23)).
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (exact (eq_trans (ew_Ereg_nat regs _ 27 (Z_to_bv 5 27) eq_refl) H27)).
assert (E32 : ew E 32 = Z_to_bv 64 nent) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (HE : forall ipz psz, (ipz = 0 \/ ipz = 1) -> (psz = 0 \/ psz = 1) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 ipz ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 psz ->
  st_ok rsegs E (su_ss ipz psz) (restrict (w_H W) (mkst regs (Z_to_bv 64 RS_E) memc (seg_rom rsegs)))).
{ intros ipz psz Hi Hp Vi Vp. rewrite restrict_mkst_fx. unfold su_ss. apply (entry_st_ok_full rsegs).
  - apply RPgCheck.ck_regs_ok. repeat constructor.
    + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    + cbn [fst snd]. exact (eq_trans (su_soff _ 27 pp 0x4000 E27) (eq_sym H21)).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0x68 8 _ (Z.shiftr (pp + 0x4d14) 3)); [| | lia | exact V68].
        -- rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U27. cbn [zalu_raw].
           unfold zcanon, M64. rewrite (Z.mod_small (pp + 0x4d14)) by lia. change (3 mod 2 ^ 64) with 3.
           change (Z.land 3 63) with 3. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia.
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        -- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
      * apply (chunk_ok_val rsegs E _ R 0x78 8 _ (pp + 0x4d14)); [apply su_soff; exact E27 | | lia | exact V78].
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * apply (chunk_ok_val rsegs E _ R 0x80 8 _ pp); [| | lia | exact V80].
        -- rewrite (su_soff E 27 pp 0 E27), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + apply (rm_ro_region rsegs E (w_H W) memc 27 pp); [exact U27 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ pp 0x4008 4 _ ipz); [reflexivity | | lia | exact Vi].
        change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * apply (chunk_ok_val rsegs E _ pp 0x4010 4 _ psz); [reflexivity | | lia | exact Vp].
        change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * apply (chunk_ok_val rsegs E _ pp 0x4d14 4 _ nent); [| | lia | exact Vn].
        -- rewrite (su_soff E 32 nent 0 E32), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  - apply pairwise_disjoint_of_extents. unfold su_regions. cbn [map zpairwise_disjoint zall_disjoint].
    unfold extent_of_region, zdisj. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite U9, U27. lia.
  - split; [|split; [exact I | exact I]]. cbn [su_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E23, E27, E32. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
(* the three instrumented checks read the first block, every byte of which is marked usable *)
assert (SHOK : sh_ok rsegs su_Bx su_SH E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc E su_Bx 27 pp 0x4d20 pp 0 0x4d20 HRA).
  - unfold su_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
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
      intros r Hr; exact (regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs (su_extra nent) kl HS HAE
        ltac:(vm_compute; reflexivity) r Hr) end
  | ];
  try exact I;
  unfold su_RO; rewrite !(st_ok_restrict_reg rsegs (w_H W) E' ss' ms _ HS)
end.
repeat split; su_sv;
first [ exact (su_soff E 27 pp _ E27)
      | rewrite (su_soff E 32 nent _ E32); unfold w64; f_equal; lia
      | reflexivity
      | cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity ].
Qed.
End blk.

(* ================================ the cuts ================================ *)
#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* membership in a concrete list of facts *)
Ltac su_in := unfold rs_L_chk; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac su_kin := first [unfold SU_KEPT_O | unfold SU_KEPT_X]; apply in_map; cbn [In]; lia.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* a cell fact of a list *)
Lemma su_at_cell : forall H mem regs e L b o v, rs_at rsegs H mem regs e L -> In (LCell b o, v) L ->
val_mem rsegs (mrestrict H mem) (rl_xv e b + o) 8 (v mod 2 ^ 64).
Proof.
intros H mem regs e L b o v HL Hin. unfold rs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin).
Qed.

(* the checks' base at a state that differs from a cut's only in registers other than sp, gp, tp, and in its
   I/O-equal model *)
Lemma su_chk_base : forall (cx : rs_scx rsegs) (fx2 : YK11.FPState) rec ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem2 md3 (x_k cx) ->
same_io md2 md3 ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 (Hcore & Hrest) HJ3 Hio3 Hk.
split; [|exact Hrest].
unfold rs_core, rs_mid in Hcore |- *.
destruct Hcore as (_ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|].
split; [intros r Hr; rewrite <- (H234 r Hr); apply Hk; exact Hr|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo | exact Hkeep].
Qed.

(* THE PIECE: rs_piece_W11a_setup_stmt at image A's segments *)
Theorem rk_setup_A : rs_piece_W11a_setup_stmt rsegs B MT.
Proof.
unfold rs_piece_W11a_setup_stmt. intros cx POST inp Hst HO HA HM.
unfold rs_from_E. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HE.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HE as (Hbase & Hat & Hrole & Hfl & Hcorr & _).
pose proof Hbase as (Hcore & _ & _ & _ & Hpp & Hwf & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
destruct Hst as (Hpre & _).
unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (_ & _ & _ & _ & _ & HeS & _ & HRsz & HRstk & _ & _ & _ & _ & Hppin & _).
cbn [hi_rsz role_himg_A] in HRsz.
set (e := x_e cx) in *.
(* the first block: live, marked usable, apart from the shadow map, below the real frame *)
assert (Hin : In (e_pp e, Layout.PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hppin).
assert (Hrq : req_size Layout.PP_SIZE = 0x4d20) by reflexivity.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_pp e) Layout.PP_SIZE HAR Hin) as (_ & H4096 & Hpc & Happ & _).
rewrite Hrq in Hpc, Happ.
pose proof (@alloc_ceiling_lt rc) as Hcl.
destruct (rm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp e) Layout.PP_SIZE (e_pp e) 0x4d20 HAR Hin ltac:(lia)
  ltac:(rewrite Hrq; lia)) as (HRA & _).
unfold T_SEG_STK, ASTACK in HRstk.
(* the record's three fields the set-up reads *)
assert (Hb : Z.of_nat (length (buf rec)) <= Layout.POD_BUF_MAX).
{ unfold buf. unfold corrupt in Hcorr. destruct (p_corr rec); [discriminate Hcorr|].
  destruct Hwf as (_ & _ & _ & _ & H5440 & _). unfold Layout.POD_BUF_MAX. lia. }
pose proof (rk_nent_le rec Hwf) as Hn32.
assert (Hs : Forall (fun en => (length (e_body en) <= 96)%nat) (ents rec)).
{ eapply Forall_impl; [|exact (rk_ents_wf rec Hwf)]. intros en (_ & Hl & Hz). lia. }
pose proof (rm_pp_is_props rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp e) Hpp) as Vip.
pose proof (rm_pp_params_struct rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp e) Hpp) as Vps.
pose proof (rm_pp_n_ent rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp e) Hpp) as Vn.
(* the registers and the real-frame cells at E *)
unfold rs_at_cx in Hat.
pose proof (RPgScanOuter.ro_at_get _ _ _ _ _ 9 (e_R e) Hat ltac:(su_in)) as R9.
pose proof (RPgScanOuter.ro_at_get _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(su_in)) as R23.
pose proof (RPgScanOuter.ro_at_get _ _ _ _ _ 27 (e_pp e) Hat ltac:(su_in)) as R27.
pose proof (RPgScanOuter.ro_at_get _ _ _ _ _ 21 (e_pp e + 0x4000) Hat ltac:(su_in)) as R21.
pose proof (su_at_cell _ _ _ _ _ XR 0x68 (Z.shiftr (e_pp e + 0x4d14) 3) Hat ltac:(su_in)) as V68.
pose proof (su_at_cell _ _ _ _ _ XR 0x78 (e_pp e + 0x4d14) Hat ltac:(su_in)) as V78.
pose proof (su_at_cell _ _ _ _ _ XR 0x80 (e_pp e) Hat ltac:(su_in)) as V80.
cbn [rl_xv] in V68, V78, V80.
assert (Hsh : 0 <= Z.shiftr (e_pp e + 0x4d14) 3 < 2 ^ 64)
  by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.mod_small in V68 by exact Hsh. rewrite Z.mod_small in V78, V80 by lia.
(* the facts every exit keeps: rs_L_chk and the registers and cells the exits name *)
assert (Hchk : rs_at rsegs (w_H W2) mem2 regs2 e (rs_L_chk rsegs cx)).
{ apply (RPgScanOuter.ro_at_sub _ _ _ _ _ _ Hat). intros x Hx. apply in_or_app. left. exact Hx. }
pose proof (RPgScanOuter.ro_at_get _ _ _ _ _ 24 (snd (rs_PA rsegs cx rec)) Hat ltac:(su_in)) as R24.
pose proof (RPgScanOuter.ro_at_get _ _ _ _ _ 25 (e_F e) Hat ltac:(su_in)) as R25.
assert (C28 : rl_at rsegs (w_H W2) mem2 regs2 e (LCell XR 0x28) (e_F e))
  by (unfold rs_at in Hat; rewrite Forall_forall in Hat; apply (Hat (LCell XR 0x28, _)); su_in).
assert (C80 : rl_at rsegs (w_H W2) mem2 regs2 e (LCell XR 0x80) (e_pp e))
  by (unfold rs_at in Hat; rewrite Forall_forall in Hat; apply (Hat (LCell XR 0x80, _)); su_in).
(* the parse's answer is the scan's: the flags bit is 0 and the record is not corrupted *)
assert (HPA : rs_PA rsegs cx rec = rs_E0 rec) by (unfold rs_PA; fold e; rewrite Hfl; apply rk_parse_expect; assumption).
eapply SRr_bind.
{ exact (su_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R e) (e_pp e) (Z.of_nat (length (ents rec)))
    (is_props rec) (params_struct rec) HJ R9 R23 R27 R21 V68 V78 V80 Vip Vps Vn ltac:(lia) HRA Happ H4096
    ltac:(lia) ltac:(lia) ltac:(lia)). }
intros W3 c3 _ Hpost. revert Hpost.
destruct (is_props rec) eqn:Eip; [destruct (params_struct rec) eqn:Eps|]; cbv beta iota;
intros (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk & HR);
pose proof (RPgScanOuter.ro_at_keep _ _ regs2 regs3 _ (rs_L_chk rsegs cx) _ Hk ltac:(vm_compute; reflexivity) Hchk) as Hchk3;
pose proof (su_chk_base cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3
  ltac:(intros r Hr; apply Hk; destruct Hr as [->|[->| ->]]; su_kin)) as Hbase3.
- (* O: the scan starts at at = 0 *)
  destruct HR as (Q1 & Q7 & Q11 & Q14 & Q20 & Q26 & Q27 & Q28 & Q29 & Q30 & Q31).
  apply (HO fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at, rs_L_scan. apply Forall_app. split; [apply Forall_app; split; [exact Hchk3|]|].
    - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
      + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
      + exact Q1.
      + exact Q26.
      + exact Q7.
      + exact Q20.
      + exact Q28.
      + exact Q27.
      + exact Q31.
      + exact Q29.
      + exact Q30.
      + exact C28.
      + exact C80.
    - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
      + exact Q11.
      + exact Q14. }
  split; [exact Hrole|]. split; [exact (rk_inv_start rec Eip Eps)|].
  unfold rs_chk_rec. rewrite HPA. auto.
- (* ABS: the params property's value is not a Struct, the answer is (None, 0) *)
  apply (HA fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  rewrite HPA, (rk_expect_no_struct rec Eip Eps) in *. cbn [fst snd] in *.
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hchk3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
    + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
    + exact C28.
    + exact C80. }
  split; [exact Hrole|]. rewrite HPA. split; reflexivity.
- (* MAL: not an Object of Props, the answer is (None, -1) *)
  apply (HM fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  rewrite HPA, (rk_expect_not_props rec Eip) in *. cbn [fst snd] in *.
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hchk3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
    + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
    + rewrite (Hk (Z_to_bv 5 25)) by su_kin. exact R25.
    + rewrite (Hk (Z_to_bv 5 27)) by su_kin. exact R27. }
  split; [exact Hrole|]. rewrite HPA. split; reflexivity.
Qed.
End c.

Print Assumptions rk_setup_A.
