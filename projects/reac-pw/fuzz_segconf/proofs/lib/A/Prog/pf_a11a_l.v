(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the loop segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0):
   syntax_instantiate's loop from its head HEAD (0x8a670) to JOIN (0x8a734), an_head_ok : AN_JOIN_stmt ->
   AN_HEAD_stmt (lib/A/Prog/answer_s1.v), by strong induction on the bytes of the shape left, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (tcbb_loopX, a loop with inline checks, re-seeded at each iteration). The
   plain proof of the same loop is lib/Prog/answer.v:120-226 (an_loop). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_l.v, with its module paths, module names and numbers changed; 490 of its 561 lines of code are new or changed and 716 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the fold loop of segment A11a of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_a11a_k.v's cut LOOP 0x8829c), a11a_loop_ok : (forall j, A11_ZST_stmt B n j) ->
   forall li, A11_LOOP_stmt B n li. Part of segment A11a's proof (the fold loop), by the G3 walk owner, 2026-10-30. No Section hypothesis.
   One pass at index li (dis/reac_segconf_parse_file.fuzz_segconf.asan.s 0x8829c-0x882e0):
     0x8829c a3 = 23; 0x882a0 beq a0,a3 -> ZST          li = 23: the fold is full (ZST with a3 = 23)
     0x882a4 .. 0x882b0 a2 = lower(val[li])              the ASCII fold (a11l_fold_U, pf_a11a_f.v a11f_fold_byte)
     0x882b4 a3 = s4 + a0; 0x882b8 sb a2,0(a3)           low146[li], the store has no inline check
     0x882bc a2 = a1 + a0 = vp + 1 + li; check #19       load1, the obligation route (buf is in scope)
     0x882d0 a2 = val[li + 1]; a0 = a3 = li + 1
     0x882dc bnez a2 -> LOOP                             the next pass (li + 1)
     0x882e0 j ZST                                       val[li + 1] = 0: ZST with a3 = li + 1
   Each pass is re-seeded by pa_entry_st_ok_full (a11l_entry, trim_l.v tl_entry's shape) with two one-byte regions,
   low146[li] (written) and val[li + 1] (read, its value the extra atom 34), and two aliases that fold the code's
   sums s4 + a0 and a1 + a0 to the atoms 32 and 33 (RECIPE-state.md section 2.4; answer_l.v at 501c0d516c69).
   The cut's facts are carried across a pass by a11l_cx_move (the pass writes one byte of low146; the keep argument
   of pf_a6_k.v a6_base_move and pf_a5_k.v a5_keep_*, over that write set, with no SSPX / VRO); the loop closes by
   induction on 23 - li (trim_l.v tr_lead_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces pf_a5_k pf_a6_k pf_a11a_k pf_a11a_f.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- one pass of the loop, the seed at LOOP 0x8829c: every register its own atom; a0 = li (atom 10), a1 = vp + 1
   (11), a2 = val[li] (12), s4 = low146 (20), s6 = the shadow base SB (22); the extra atoms 32 = low146 + li (the fold
   store's cell, written), 33 = vp + 1 + li (the next byte's address, read), 34 = val[li + 1] (that byte). The two
   aliases fold the code's sums `add a3, s4, a0` and `add a2, a1, a0` to the single atoms 32 and 33. ---- *)
Definition a11l_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition a11l_facts : facts :=
  mkFacts [ (10%nat, mkAF 0 23 0); (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (12%nat, mkAF 0 255 0);
            (20%nat, mkAF 4096 (2 ^ 47 - 1) 0); (22%nat, mkAF SB SB 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 1) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0); (34%nat, mkAF 0 255 0) ]
          []
          [ (SAlu ALU_ADD (SOff 20 0) (SOff 10 0), SOff 32 0);
            (SAlu ALU_ADD (SOff 11 0) (SOff 10 0), SOff 33 0) ].
Definition a11l_ss : sstate := mkSS A11_LOOP sr_atoms a11l_regions None a11l_facts.
Definition a11l_Bx : sv := SOff 22 0.
(* the fold store's cell is in the frame: its app-memory entry (no inline check reads it) *)
Definition a11l_SH : list shent := [mkSHE 32 1 0].
(* the byte the run stores at 0x882b8: a2 + (((a2 - 'A') <u 26) << 5), over a2 = atom 12 *)
Definition a11l_FOLDV : sv :=
  SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 12 (-65)) (SLit 26)) (SLit 5)).
(* the registers no exit of a pass writes (a0, a2, a3, a4 are the pass's) *)
Definition A11L_KEPT : list Z := [2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 24; 25; 26; 27].
Lemma a11l_inK : forall r, existsb (Z.eqb r) A11L_KEPT = true -> In r A11L_KEPT.
Proof. intros r H. apply existsb_exists in H as (x & Hx & Hr). apply Z.eqb_eq in Hr. subst x. exact Hx. Qed.

(* the two branches of a pass: `beq a0, a3` (a3 = 23) and `bnez a2` *)
Lemma a11l_br_eq : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof. intros E n v z b H Hv Hz Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc. Qed.
Lemma a11l_br_ne0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> negb (v =? 0) = b.
Proof. intros E n v b H Hv Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc. Qed.
(* the byte the store writes is SegModel.lower of the byte the pass read (pf_a11a_f.v a11f_fold_byte) *)
Lemma a11l_fold_U : forall E C0, ew E 12 = Z_to_bv 64 C0 -> 0 <= C0 < 256 ->
  bv_unsigned (sv_denot E a11l_FOLDV) = lower C0.
Proof.
intros E C0 H HC. change (bv_unsigned (sv_denot E a11l_FOLDV)) with (U E a11l_FOLDV). unfold a11l_FOLDV.
rewrite !U_SAlu. rewrite (U_atom E 12 C0 H) by lia. rewrite U_SOff, H, unsigned_lit_small by lia.
rewrite !U_lit by lia. cbn [zalu_raw]. change (Z.land 5 63) with 5.
rewrite <- (a11f_fold_byte C0 HC). unfold zcanon, M64.
change (2 ^ 64) with 18446744073709551616.
destruct ((C0 + -65) mod 18446744073709551616 <? 26); cbn [Z.b2z].
- replace (Z.shiftl (1 mod 18446744073709551616) 5) with 32 by reflexivity.
  replace (Z.shiftl 1 5) with 32 by reflexivity. rewrite (Z.mod_small 32) by lia. apply Z.mod_small. lia.
- replace (Z.shiftl (0 mod 18446744073709551616) 5) with 0 by reflexivity.
  replace (Z.shiftl 0 5) with 0 by reflexivity. rewrite (Z.mod_small 0) by lia. apply Z.mod_small. lia.
Qed.
(* the environment after a run agrees with the seed's below 35 (trim_k.v tr_ag32 / tr_ag_ew, answer_l.v al_u32) *)
Lemma a11l_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma a11l_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma a11l_u32 : forall E0 E P, env_agree 35 E0 E -> ew E0 32 = Z_to_bv 64 P -> 0 <= P < 2 ^ 64 -> bv_unsigned (ew E 32) = P.
Proof. intros E0 E P H H0 HP. rewrite (proj1 H 32%nat ltac:(lia)), H0. apply unsigned_lit_small. exact HP. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition a11l_E (regs1 : bvmap 5 word) (P A C : Z) : env :=
  Eimg (Ereg regs1 [Z_to_bv 64 P; Z_to_bv 64 A; Z_to_bv 64 C]).

Lemma a11l_ew_reg : forall regs1 P A C n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (a11l_E regs1 P A C) n = getr regs1 r.
Proof. intros regs1 P A C n r Hn. unfold a11l_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma a11l_ew32 : forall regs1 P A C, ew (a11l_E regs1 P A C) 32 = Z_to_bv 64 P.
Proof. intros. unfold a11l_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). Qed.
Lemma a11l_ew33 : forall regs1 P A C, ew (a11l_E regs1 P A C) 33 = Z_to_bv 64 A.
Proof. intros. unfold a11l_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 1). Qed.
Lemma a11l_ew34 : forall regs1 P A C, ew (a11l_E regs1 P A C) 34 = Z_to_bv 64 C.
Proof. intros. unfold a11l_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 2). Qed.
Lemma a11l_env_agree : forall regs1 P A C,
  env_agree 32 (Ereg regs1 [Z_to_bv 64 P; Z_to_bv 64 A; Z_to_bv 64 C]) (a11l_E regs1 P A C).
Proof. intros. split; [intros n Hn; unfold a11l_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
(* a register list carried by registers a run left alone *)
Lemma a11l_rg_kept : forall (rX rX' : bvmap 5 word) (L : list (Z * Z)) (ks : list Z),
  (forall r, In r ks -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  Forall (fun rv => In (fst rv) ks) L -> pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L ks HK HL H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HK (fst rv) (HL rv Hin)). exact (H rv Hin).
Qed.

(* the seed of a pass (trim_l.v tl_entry, fuzz_command's answer_l.v al_entry) *)
Lemma a11l_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc (li : nat) L A1 C0 C1,
  getr regs1 (Z_to_bv 5 10) = w64 (Z.of_nat li) -> getr regs1 (Z_to_bv 5 11) = w64 A1 ->
  getr regs1 (Z_to_bv 5 12) = w64 C0 -> getr regs1 (Z_to_bv 5 20) = w64 L -> getr regs1 (Z_to_bv 5 22) = w64 SB ->
  (li <= 23)%nat -> 4096 <= L -> L + 24 <= 2 ^ 47 - 1 -> 4096 <= A1 -> A1 + 24 <= 2 ^ 47 - 1 ->
  0 <= C0 <= 255 -> 0 <= C1 <= 255 ->
  rdW W memc (A1 + Z.of_nat li) = Some C1 -> apresent (w_H W) memc (L + Z.of_nat li) ->
  (A1 + Z.of_nat li + 1 <= L + Z.of_nat li \/ L + Z.of_nat li + 1 <= A1 + Z.of_nat li) ->
  st_ok_pi SEGS VAL (a11l_E regs1 (L + Z.of_nat li) (A1 + Z.of_nat li) C1) a11l_ss
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A11_LOOP)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc li L A1 C0 C1 H10 H11 H12 H20 H22 Hli HL1 HL2 HA1 HA2 HC0 HC1 HrdC HpP Hdisj.
set (P := L + Z.of_nat li) in *. set (A := A1 + Z.of_nat li) in *.
set (E := a11l_E regs1 P A C1).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat li)) by (subst E; rewrite (a11l_ew_reg regs1 P A C1 10 (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 A1) by (subst E; rewrite (a11l_ew_reg regs1 P A C1 11 (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 C0) by (subst E; rewrite (a11l_ew_reg regs1 P A C1 12 (Z_to_bv 5 12) eq_refl); exact H12).
assert (E20 : ew E 20 = Z_to_bv 64 L) by (subst E; rewrite (a11l_ew_reg regs1 P A C1 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; rewrite (a11l_ew_reg regs1 P A C1 22 (Z_to_bv 5 22) eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; apply a11l_ew32).
assert (E33 : ew E 33 = Z_to_bv 64 A) by (subst E; apply a11l_ew33).
assert (E34 : ew E 34 = Z_to_bv 64 C1) by (subst E; apply a11l_ew34).
rewrite restrict_mkst_fx. unfold a11l_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold a11l_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact HpP.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E33, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc A C1 HrdC) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E34.
      rewrite !Z.add_0_r, (unsigned_lit_small C1), (unsigned_lit_small C1) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. subst C1. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
- unfold a11l_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E32, E33, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [a11l_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10, E11, E12, E20, E22, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [a11l_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom _ 20 L E20), (U_atom _ 10 _ E10), (U_atom _ 32 P E32) by lia.
      subst P. apply zcanon_id. unfold M64. lia.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom _ 11 A1 E11), (U_atom _ 10 _ E10), (U_atom _ 33 A E33) by lia.
      subst A. apply zcanon_id. unfold M64. lia.
Qed.

(* the byte a run wrote into a one-byte written region (trim_t.v tr_wbyte, fuzz_command's answer_l.v al_wbyte) *)
Lemma a11l_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.
(* a run of a pass writes at most the fold store's cell Pz (answer_l.v al_keep_step, this pass's regions) *)
Lemma a11l_keep_step : forall E cs0 cs1 (m0 m m' : word -> option byte) (H : word -> bool) Pz,
  frame_of E [YP09.mkRegion (Some 32%nat) 0 1 0 1 cs0; YP09.mkRegion (Some 33%nat) 0 1 0 0 cs1]
    (mrestrict H m) (mrestrict H m') ->
  bv_unsigned (ew E 32) = Pz ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> a <> Pz -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E cs0 cs1 m0 m m' H Pz HFr H32 KM a Ha Hn.
assert (HW : forall b wlo whi a', In (b, wlo, whi) (windows [YP09.mkRegion (Some 32%nat) 0 1 0 1 cs0;
    YP09.mkRegion (Some 33%nat) 0 1 0 0 cs1]) -> base_val E b + wlo <= a' < base_val E b + whi -> a' = Pz).
{ intros b wlo whi a' Hin Hr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia. }
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun a' => a' = Pz) HFr HW a Ha Hn). exact (KM a Ha Hn).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the cut's facts across a pass. A pass writes one byte of low146; every fact of a11_cx reads elsewhere: the
   stack from s1 up, the image and its low range [0x10000, kImgEnd) (the literals, the catalogue, the read-only
   window, the stack-protector cells), the live heap blocks, the shadow band, and in the frame cur_name, buf and
   the flag word. The keep argument of pf_a6_k.v a6_base_move and pf_a5_k.v a5_move0 / a5_keep_*, over this write
   set; heap shadow re-derived from AR at the new state (pf_a6_k.v a6_heap_addr). No Section hypothesis. ---- *)
Lemma a11l_keeps : forall v pos lyc Sc Wc rX memc mdc sc (rd' : reader),
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_F v pos + PF_O_L146 <= a < pf_F v pos + PF_O_L146 + 24) -> rd' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> a < pf_F v pos \/ pf_F v pos + 2048 <= a -> rd' a = rdW Wc memc a) /\
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rd' a = rdW Wc memc a) /\
  (forall a, in_img SEGS a -> rd' a = rdW Wc memc a) /\
  (forall a, 0x10000 <= a < 0x601000 -> rd' a = rdW Wc memc a) /\
  (forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> rd' a = rdW Wc memc a) /\
  (forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> rd' a = rdW Wc memc a).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rd' HB K.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hfin & G & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof alloc_ceiling_lt as Hac.
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (HO : PF_O_L146 = 736) by reflexivity.
assert (HFE : frame_addr (p_ly v) 5 pos = pf_F v pos) by reflexivity.
assert (HFB : fs_frame_bytes 5 = 2048) by reflexivity.
subst lyc.
assert (KO : forall a, 0 <= a < 2 ^ 64 -> a < pf_F v pos \/ pf_F v pos + 2048 <= a -> rd' a = rdW Wc memc a)
  by (intros a Ha Ho; apply K; [exact Ha | lia]).
split; [exact KO|].
split; [intros a Ha; apply KO; lia|].
split.
{ intros a Ha. pose proof (pa_img_range _ Ha) as Hr. unfold kImgEnd in Hr.
  pose proof (frm_img SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos a HAR Hfin) as Hf. rewrite HFE, HFB in Hf.
  apply KO; [lia|]. destruct (Z_lt_le_dec a (pf_F v pos)) as [h|h]; [left; exact h|right].
  destruct (Z_lt_le_dec a (pf_F v pos + 2048)) as [h2|h2]; [exfalso; exact (Hf ltac:(lia) Ha) | exact h2]. }
split.
{ intros a Ha. pose proof (frm_off_imgP B (p_ly v) Sc Wc memc mdc 5 pos HAR Hfin) as Hoff. unfold off_img in Hoff.
  rewrite HFE, HFB in Hoff. apply KO; lia. }
split.
{ intros b m a Hb Ha. pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE, HFB in Hd.
  destruct (al_blocks _ _ LAWS (p_ly v) Sc Wc memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  apply KO; lia. }
intros a Ha. pose proof (a6_band_not_app (pf_F v pos) 2048 a G9 Ha) as Hn.
apply KO; [unfold SHADOW_OFF in Ha; lia | lia].
Qed.

Lemma a11l_cx_move : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rX' memc' mdc',
  a11_cx B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_F v pos + PF_O_L146 <= a < pf_F v pos + PF_O_L146 + 24) ->
     rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (a5_FI B v) ->
  a11_cx B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val rX' memc' mdc' (HB & HMID & HST & HSTR & HINB & HSL) HJ2 K HRG2.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (HAR & Hly & Hfin & G & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
destruct (a11l_keeps v pos lyc Sc Wc rX memc mdc PF_SC_L146 _ HB K) as (KO & KS1 & KI & KLOW & KH & KB).
pose proof alloc_ceiling_lt as Hac.
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (HO : PF_O_L146 = 736) by reflexivity.
pose proof HB as (CX & FI & OBJ & SL & FSH).
pose proof FI as (HJ & HlyF & HSf & HPerm & HSV & HFLW & HFRM & HRG).
pose proof OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2.
assert (HB2 : pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_L146).
{ split; [exact CX|].
  split.
  { split; [exact HJ2|]. split; [exact HlyF|]. split; [exact HSf|]. split; [exact HPerm|].
    split.
    { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
      pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
      unfold PF_SAVED in Hj13. cbn [length] in Hj13. apply KS1. lia. }
    split.
    { rewrite <- HFLW. apply rdword_ext. intros k Hk. change (fs_frame_bytes 5) with 2048. apply K; lia. }
    split; [exact HFRM | exact HRG2]. }
  split.
  { destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
      as (bt & mt & Hint & Hbt1 & Hbt2 & _).
    split.
    { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
      - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
        rewrite (KH bt mt) by (first [exact Hint | lia]). exact (Hz i Hi).
      - intros x Hx.
        apply (AR_block_word_vis SEGS B lyc Sc Wc memc' mdc' bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2 Hint); lia. }
    split; [exact (a6_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR2 HT ltac:(unfold pf_len; lia))|].
    split; [exact HT|].
    split; [exact (a6_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR2 HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
    split; [exact HC|].
    split; [exact (a6_cat_move B _ Wc memc' CAT (fun x Hx _ _ => KI x Hx))|].
    split; [intros x Hx; exact (a6_lit_move B _ Wc memc' _ _ (LITS x Hx) (fun y Hy _ _ => KI y Hy))|].
    split.
    { intros a Hro Ho He. rewrite <- (ROD a Hro Ho He). destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
      - apply KI. exists sg. split; [exact Hsg | exact Hr].
      - apply KLOW. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
    destruct SSP as (S1 & g & S2). split.
    - rewrite <- S1. apply rdword_ext. intros k Hk. apply KLOW. unfold gotwA. lia.
    - exists g. rewrite <- S2. apply rdword_ext. intros k Hk. apply KLOW. unfold guardA. lia. }
  split.
  { apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (a6_PF_SL_offs v pos)); [lia | lia | exact KS1]. }
  intros i Hi. rewrite KB; [exact (FSH i Hi)|]. rewrite G10.
  pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)). unfold SHADOW_OFF in *. lia. }
split; [exact HB2|]. split; [exact HMID|].
split.
{ destruct HST as ((bs & Hbs & Henc) & HCO & (f & Hf & Hfe) & HN).
  destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
    as (bc & mc & Hinc & Hc1 & Hc2 & _).
  split; [|split; [exact HCO | split; [|exact HN]]].
  - exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
    rewrite (KH bc mc) by (first [exact Hinc | unfold seg_spec.SEG_C_SIZE in *; lia]). exact (Hbs i Hi).
  - exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as (Hl & _). rewrite Hl in Hi.
    rewrite K; [exact (Hf i ltac:(lia)) | unfold PF_O_CN; lia | unfold PF_O_CN; lia]. }
split.
{ destruct HSTR as ((Hz & Hn) & Ht). destruct HINB as [Hb1 Hb2]. unfold PF_O_BUF in Hb1, Hb2.
  split; [split; [|exact Hn]|].
  - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
    rewrite K; [exact (Hz i Hi) | lia | lia].
  - intros x Hx. pose proof (Z.mod_pos_bound (vp + Z.of_nat (length val)) 8 ltac:(lia)) as M8.
    rewrite K; [exact (Ht x Hx) | lia | lia]. }
split; [exact HINB|].
apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _ HSL); [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia | exact KS1].
Qed.

(* the writes of a pass: the fold store's cell P, in the class-5 frame (answer_l.v al_awr) *)
Lemma a11l_awr : forall E P STK sp0 FP bl0 blc fr0 ly pos cs0 cs1,
  bv_unsigned (ew E 32) = P -> frame_addr ly 5 pos <= P -> P + 1 <= frame_addr ly 5 pos + fs_frame_bytes 5 ->
  awr_ok SEGS B E [YP09.mkRegion (Some 32%nat) 0 1 0 1 cs0; YP09.mkRegion (Some 33%nat) 0 1 0 0 cs1]
    STK sp0 FP bl0 blc fr0 ly [(5, pos)].
Proof.
intros E P STK sp0 FP bl0 blc fr0 ly pos cs0 cs1 HP H1 H2.
eapply awr_ok_cons_gen with (n := 32%nat) (b := P); [reflexivity | exact HP | |].
- cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. left.
  exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. lia.
- apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
Qed.

Ltac a11l_awr_tac HAE E32 :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  eapply a11l_awr; [apply (a11l_u32 _ _ _ HAE E32); lia | lia | lia].
(* after a run: the environment agrees with the seed's E0 below 35 (HAE), the memory with memc off P (KM) *)
Ltac a11l_after E0 P E32 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let U := fresh "U32" in
    assert (U : bv_unsigned (ew Eo 32) = P) by (apply (a11l_u32 _ _ _ HAE E32); lia);
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 35 E0 En) by (env_agree_chain HAE);
    pose proof (a11l_keep_step Eo _ _ _ _ _ _ P HFr U KM) as KMn;
    clear U HFr HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
(* the registers a run left alone, as a Z list *)
Ltac a11l_kept HS rX HA0 HAE HK :=
  let HK0 := fresh "HK0" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) A11L_KEPT) HS (a11l_ag32 _ _ _ _ 35 ltac:(lia) HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK0;
  cbn [ms_regs restrict] in HK0;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (HK : forall r, In r A11L_KEPT -> getr (ms_regs msn) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
      by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; apply HK0; apply in_map; exact Hr) end;
  clear HK0.

(* ---- one pass, with the next one as a premise (trim_l.v tr_lead_ok's ITER) ---- *)
Lemma a11l_pass : forall n, (forall j, A11_ZST_stmt B n j) ->
  forall li, ((li < 23)%nat -> A11_LOOP_stmt B n (S li)) -> A11_LOOP_stmt B n li.
Proof.
intros n HZST li NEXT. unfold A11_LOOP_stmt.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (HCX & Hcap & Hlen & HLOW & HRG).
unfold A11_CAP in Hcap.
pose proof HCX as (HB & HMID & HST & HSTR & HINB & HSLB).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (HAR & Hly & Hfin & G & HFp & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof HB as (_ & (HJ & _ & _ & _ & _ & _ & _ & HRGF) & _ & _ & FSH).
pose proof alloc_ceiling_lt as Hac.
assert (HO : PF_O_L146 = 736) by reflexivity.
assert (HFE : frame_addr (p_ly v) 5 pos = pf_F v pos) by reflexivity.
assert (HFB : fs_frame_bytes 5 = 2048) by reflexivity.
subst lyc.
(* the registers at LOOP *)
pose proof (proj1 (a5_rg_app _ _ _) HRG) as (RL & HRG').
pose proof (proj1 (a5_rg_app _ _ _) HRG') as (RM & RN).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat li)) by (apply (a5_rg_get rX _ _ _ RN); cbn [In]; tauto).
assert (R11 : getr rX (Z_to_bv 5 11) = w64 (vp + 1)) by (apply (a5_rg_get rX _ _ _ RN); cbn [In]; tauto).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 (nth li val 0)) by (apply (a5_rg_get rX _ _ _ RN); cbn [In]; tauto).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 (pf_F v pos + PF_O_L146)) by (apply (a5_rg_get rX _ _ _ RN); cbn [In]; tauto).
assert (R25 : getr rX (Z_to_bv 5 25) = w64 vp) by (apply (a5_rg_get rX _ _ _ RN); cbn [In]; tauto).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SB) by (rewrite SB_SHADOW_OFF; apply (a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto).
assert (RLK : Forall (fun rv => In (fst rv) A11L_KEPT) (PF_RL v pos))
  by (unfold PF_RL; repeat (apply Forall_cons; [apply a11l_inK; reflexivity|]); apply Forall_nil).
assert (RMK : Forall (fun rv => In (fst rv) A11L_KEPT) (PF_RM v o ln))
  by (unfold PF_RM; repeat (apply Forall_cons; [apply a11l_inK; reflexivity|]); apply Forall_nil).
assert (FIK : Forall (fun rv => In (fst rv) A11L_KEPT) (a5_FI B v))
  by (unfold a5_FI; repeat (apply Forall_cons; [apply a11l_inK; reflexivity|]); apply Forall_nil).
(* the value in buf: val[li] and val[li + 1] (the NUL when li + 1 = |val|) *)
destruct HINB as [Hb1 Hb2]. unfold PF_O_BUF in Hb1, Hb2.
pose proof HSTR as ((HZ & HN0) & _).
assert (V0 : rdW Wc memc (vp + Z.of_nat li) = Some (nth li val 0)).
{ rewrite (HZ li ltac:(rewrite length_app; cbn [length]; lia)). rewrite app_nth1 by lia. reflexivity. }
assert (V1 : rdW Wc memc (vp + 1 + Z.of_nat li) = Some (nth (S li) val 0)).
{ replace (vp + 1 + Z.of_nat li) with (vp + Z.of_nat (S li)) by lia.
  rewrite (HZ (S li) ltac:(rewrite length_app; cbn [length]; lia)).
  destruct (Nat.lt_ge_cases (S li) (length val)) as [Hs|Hs].
  - rewrite app_nth1 by lia. reflexivity.
  - rewrite app_nth2 by lia. replace (S li - length val)%nat with 0%nat by lia. cbn [nth].
    rewrite nth_overflow by lia. reflexivity. }
remember (nth li val 0) as C0 eqn:HC0d. remember (nth (S li) val 0) as C1 eqn:HC1d.
destruct (aview_byte SEGS (w_H Wc) memc _ _ V0) as (_ & _ & _ & HC0).
destruct (aview_byte SEGS (w_H Wc) memc _ _ V1) as (_ & _ & _ & HC1).
assert (HpP : apresent (w_H Wc) memc (pf_F v pos + PF_O_L146 + Z.of_nat li)) by (apply HFp; lia).
pose proof (a11l_entry Wc rX memc li (pf_F v pos + PF_O_L146) (vp + 1) C0 C1 R10 R11 R12 R20 R22 Hcap
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) V1 HpP ltac:(lia)) as HS.
remember (pf_F v pos + PF_O_L146 + Z.of_nat li) as P eqn:HPd.
remember (vp + 1 + Z.of_nat li) as A eqn:HAd.
(* buf's shadow: buf is in scope (PF_SC_L146), so A is addressable *)
assert (HRAbuf : range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + 64) 512).
{ assert (DF : (pf_F v pos + 64) / 8 = pf_F v pos / 8 + 8).
  { replace (pf_F v pos + 64) with (pf_F v pos + 8 * 8) by lia. apply Z.div_add. lia. }
  assert (F8 : (pf_F v pos + 64) mod 8 = 0).
  { pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D32. rewrite G8 in D32.
    replace (pf_F v pos + 64) with ((4 * (pf_F v pos / 32) + 8) * 8) by lia. apply Z_mod_mult. }
  apply (zero_shadow_range _ _ (pf_F v pos + 64) 512 F8 eq_refl).
  intros i Hi. change (512 / 8) with 64 in Hi. unfold shadow_of_addr. rewrite DF.
  replace (SHADOW_OFF + (pf_F v pos / 8 + 8) + i) with (pf_SH v pos + (8 + i)) by (rewrite G10; lia).
  rewrite (FSH (8 + i) ltac:(lia)). rewrite a5_shb_in by lia. reflexivity. }
assert (HRA1 : range_addressable (rdW Wc memc) SHADOW_OFF A 1)
  by (apply (range_addressable_sub _ _ (pf_F v pos + 64) 512); [exact HRAbuf | lia | lia]).
(* A's shadow cell is not P, so a run that writes only P keeps it *)
assert (HSAP : 0 <= shadow_of_addr SHADOW_OFF A < 2 ^ 64 /\ shadow_of_addr SHADOW_OFF A <> P).
{ unfold shadow_of_addr. pose proof (Z.div_pos A 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound A 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (a6_band_not_app (pf_F v pos) 2048 (SHADOW_OFF + A / 8) G9 ltac:(unfold SHADOW_OFF in *; lia)) as Hn.
  split; [unfold SHADOW_OFF; lia | intros E; apply Hn; rewrite E; lia]. }
(* the transport of a11_cx to the end of the pass, and the folded prefix *)
assert (CXM : forall rg mm mdn,
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc mm mdn 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc mm a = rdW Wc memc a) ->
  (forall r, In r A11L_KEPT -> getr rg (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  a11_cx B n v pos (p_ly v) Sc Wc rg mm mdn cf nm o ln d gi vp val).
{ intros rg mm mdn HJ' KM' HK'.
  apply (a11l_cx_move n v pos (p_ly v) Sc Wc rX memc mdc cf nm o ln d gi vp val rg mm mdn HCX HJ').
  - intros a Ha Hw. apply KM'; [exact Ha|]. intros E. apply Hw. lia.
  - exact (a11l_rg_kept rX rg _ A11L_KEPT HK' FIK HRGF). }
assert (LOWK : forall mm k, (k <= li)%nat -> (k <= 23)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc mm a = rdW Wc memc a) ->
  (k < li \/ (k = li /\ rdW Wc mm P = Some (lower C0)))%nat \/ (k = 23%nat /\ li = 23%nat) ->
  a11_low (rdW Wc mm) v pos k val).
{ intros mm k Hk Hk23 KM' _ j Hj. rewrite KM'; [exact (HLOW j ltac:(lia)) | lia | lia]. }
assert (LOWW : forall mm, (forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc mm a = rdW Wc memc a) ->
  rdW Wc mm P = Some (lower C0) -> a11_low (rdW Wc mm) v pos (S li) val).
{ intros mm KM' HW j Hj. destruct (Nat.eq_dec j li) as [->|Hne].
  - rewrite <- HPd, <- HC0d. exact HW.
  - rewrite KM'; [exact (HLOW j ltac:(lia)) | lia | lia]. }
(* the environment of the pass *)
assert (HEI : img_env VAL A_LIM (a11l_E rX P A C1)) by (unfold a11l_E; apply Eimg_env).
pose proof (a11l_env_agree rX P A C1) as HA0.
assert (E10 : ew (a11l_E rX P A C1) 10 = Z_to_bv 64 (Z.of_nat li))
  by (rewrite (a11l_ew_reg rX P A C1 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E12 : ew (a11l_E rX P A C1) 12 = Z_to_bv 64 C0)
  by (rewrite (a11l_ew_reg rX P A C1 12 (Z_to_bv 5 12) eq_refl); exact R12).
assert (E22 : ew (a11l_E rX P A C1) 22 = Z_to_bv 64 SB)
  by (rewrite (a11l_ew_reg rX P A C1 22 (Z_to_bv 5 22) eq_refl); exact R22).
pose proof (a11l_ew32 rX P A C1) as E32. pose proof (a11l_ew33 rX P A C1) as E33.
pose proof (a11l_ew34 rX P A C1) as E34.
revert HS HEI HA0 E10 E12 E22 E32 E33 E34. generalize (a11l_E rX P A C1) as E0.
intros E0 HS HEI HA0 E10 E12 E22 E32 E33 E34.
pose proof (env_agree_refl 35 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (UB : U E0 a11l_Bx = SHADOW_OFF)
  by (unfold a11l_Bx; rewrite (U_atom E0 22 SB E22) by (unfold SB; lia); exact SB_SHADOW_OFF).
assert (U32 : U E0 (SOff 32 0) = P) by (apply U_atom; [exact E32 | lia]).
assert (SHOK : sh_ok SEGS a11l_Bx a11l_SH E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, a11l_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_app_of_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc E0 a11l_Bx 32%nat P 5 pos 0 1 _ HAR Hfin UB U32); lia. }
unfold cfg_at.
(* 0x8829c, 0x882a0: a3 = 23, `beq a0, a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ a11l_awr_tac HAE E32. }
a11l_after E0 P E32 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* li = 23: the fold is full, ZST with a3 = 23 *)
  pose proof (a11l_br_eq _ 10 _ 23 _ (a11l_ag_ew _ _ 35 10 _ HAE ltac:(lia) E10) ltac:(lia) ltac:(lia) Hc) as L23.
  apply Z.eqb_eq in L23. clear Hc. assert (Hl23 : li = 23%nat) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan A11_ZST. { a11l_awr_tac HAE E32. }
  a11l_after E0 P E32 HAE KM.
  a11l_kept HS rX HA0 HAE HK.
  prreg HS (Z_to_bv 5 13) N13.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (HZST 23%nat v pos (p_ly v) Sc Wc rg mm mdn cf nm o ln d gi vp val) end.
  split; [exact (CXM _ _ _ HJ KM HK)|].
  split; [rewrite (a11f_low_len val 24 HN0); lia|].
  split; [unfold A11_CAP; lia|].
  split; [exact (LOWK _ 23%nat ltac:(lia) ltac:(lia) KM ltac:(right; split; lia))|].
  apply (proj2 (a5_rg_app _ _ _)). split; [exact (a11l_rg_kept rX _ _ A11L_KEPT HK RLK RL)|].
  apply (proj2 (a5_rg_app _ _ _)). split; [exact (a11l_rg_kept rX _ _ A11L_KEPT HK RMK RM)|].
  apply Forall_cons; [cbn [fst snd]; rewrite N13; reflexivity|].
  apply Forall_cons; [cbn [fst snd]; rewrite (HK 20 ltac:(apply a11l_inK; reflexivity)); exact R20|].
  apply Forall_cons; [cbn [fst snd]; rewrite (HK 25 ltac:(apply a11l_inK; reflexivity)); exact R25|].
  apply Forall_nil.
- (* li < 23: fold val[li] into low146[li], check #19, read val[li + 1] *)
  pose proof (a11l_br_eq _ 10 _ 23 _ (a11l_ag_ew _ _ 35 10 _ HAE ltac:(lia) E10) ltac:(lia) ltac:(lia) Hc) as L23.
  apply Z.eqb_neq in L23. clear Hc. assert (Hlt : (li < 23)%nat) by lia.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m1) =>
    assert (HRA1' : range_addressable (rdW Wc (ms_mem m1)) SHADOW_OFF A 1)
      by (apply (range_addressable_agree (rdW Wc memc) _ SHADOW_OFF A 1); [|exact HRA1];
          intros x Hx; assert (x = A) as -> by lia; apply KM; [exact (proj1 HSAP) | exact (proj2 HSAP)]) end.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { unfold a11l_Bx. rewrite (U_atom _ 22 SB E22), (U_atom _ 33 A E33) by (unfold SB; lia).
    rewrite SB_SHADOW_OFF. exact HRA1'. }
  { a11l_awr_tac HAE E32. }
  a11l_after E0 P E32 HAE KM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* val[li + 1] <> 0: the next pass *)
    pose proof (a11l_br_ne0 _ 34 _ _ (a11l_ag_ew _ _ 35 34 _ HAE ltac:(lia) E34) ltac:(lia) Hc) as NZ.
    apply Bool.negb_true_iff, Z.eqb_neq in NZ. clear Hc.
    assert (HSl : (S li < length val)%nat).
    { destruct (Nat.lt_ge_cases (S li) (length val)) as [h|h]; [exact h|].
      exfalso. apply NZ. rewrite HC1d. apply nth_overflow. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A11_LOOP. { a11l_awr_tac HAE E32. }
    a11l_after E0 P E32 HAE KM.
    pose proof (a11l_wbyte _ _ _ _ 32%nat 0%nat P a11l_FOLDV HS ltac:(vm_compute; reflexivity)
      (a11l_u32 _ _ _ HAE E32 ltac:(lia))) as HWB.
    rewrite (a11l_fold_U _ C0 (a11l_ag_ew _ _ 35 12 _ HAE ltac:(lia) E12) ltac:(lia)) in HWB.
    rewrite Z.mod_small in HWB by (apply a11f_lower_range; lia).
    a11l_kept HS rX HA0 HAE HK.
    prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 12) N12.
    rewrite E10 in N10. rewrite unsigned_lit_small in N10 by lia. try rewrite E34 in N12.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (NEXT Hlt v pos (p_ly v) Sc Wc rg mm mdn cf nm o ln d gi vp val) end.
    split; [exact (CXM _ _ _ HJ KM HK)|].
    split; [unfold A11_CAP; lia|].
    split; [exact HSl|].
    split; [exact (LOWW _ KM HWB)|].
    apply (proj2 (a5_rg_app _ _ _)). split; [exact (a11l_rg_kept rX _ _ A11L_KEPT HK RLK RL)|].
    apply (proj2 (a5_rg_app _ _ _)). split; [exact (a11l_rg_kept rX _ _ A11L_KEPT HK RMK RM)|].
    apply Forall_cons; [cbn [fst snd]; rewrite N10; replace (Z.of_nat (S li)) with (Z.of_nat li + 1) by lia; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite (HK 11 ltac:(apply a11l_inK; reflexivity)); exact R11|].
    apply Forall_cons; [cbn [fst snd]; rewrite N12, <- HC1d; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite (HK 20 ltac:(apply a11l_inK; reflexivity)); exact R20|].
    apply Forall_cons; [cbn [fst snd]; rewrite (HK 25 ltac:(apply a11l_inK; reflexivity)); exact R25|].
    apply Forall_nil.
  + (* val[li + 1] = 0: the value ends, ZST with a3 = li + 1 *)
    pose proof (a11l_br_ne0 _ 34 _ _ (a11l_ag_ew _ _ 35 34 _ HAE ltac:(lia) E34) ltac:(lia) Hc) as NZ.
    apply Bool.negb_false_iff, Z.eqb_eq in NZ. clear Hc.
    assert (HSl : length val = S li).
    { destruct (Nat.lt_ge_cases (S li) (length val)) as [h|h]; [|lia].
      exfalso. apply HN0. rewrite <- NZ, HC1d. apply nth_In. exact h. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A11_ZST. { a11l_awr_tac HAE E32. }
    a11l_after E0 P E32 HAE KM.
    pose proof (a11l_wbyte _ _ _ _ 32%nat 0%nat P a11l_FOLDV HS ltac:(vm_compute; reflexivity)
      (a11l_u32 _ _ _ HAE E32 ltac:(lia))) as HWB.
    rewrite (a11l_fold_U _ C0 (a11l_ag_ew _ _ 35 12 _ HAE ltac:(lia) E12) ltac:(lia)) in HWB.
    rewrite Z.mod_small in HWB by (apply a11f_lower_range; lia).
    a11l_kept HS rX HA0 HAE HK.
    prreg HS (Z_to_bv 5 13) N13.
    rewrite E10 in N13. rewrite unsigned_lit_small in N13 by lia.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (HZST (S li) v pos (p_ly v) Sc Wc rg mm mdn cf nm o ln d gi vp val) end.
    split; [exact (CXM _ _ _ HJ KM HK)|].
    split; [rewrite (a11f_low_len val 24 HN0); lia|].
    split; [unfold A11_CAP; lia|].
    split; [exact (LOWW _ KM HWB)|].
    apply (proj2 (a5_rg_app _ _ _)). split; [exact (a11l_rg_kept rX _ _ A11L_KEPT HK RLK RL)|].
    apply (proj2 (a5_rg_app _ _ _)). split; [exact (a11l_rg_kept rX _ _ A11L_KEPT HK RMK RM)|].
    apply Forall_cons; [cbn [fst snd]; rewrite N13; replace (Z.of_nat (S li)) with (Z.of_nat li + 1) by lia; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite (HK 20 ltac:(apply a11l_inK; reflexivity)); exact R20|].
    apply Forall_cons; [cbn [fst snd]; rewrite (HK 25 ltac:(apply a11l_inK; reflexivity)); exact R25|].
    apply Forall_nil.
Qed.

(* ---- the loop: by induction on the passes left (trim_l.v tr_lead_ok); li > 23 is vacuous (A11_INV_LOOP's
   li <= A11_CAP) ---- *)
Theorem a11a_loop_ok : forall n : nat,
  (forall j : nat, A11_ZST_stmt B n j) -> forall li : nat, A11_LOOP_stmt B n li.
Proof.
intros n HZST.
assert (ALL : forall k li, (23 - li = k)%nat -> A11_LOOP_stmt B n li).
{ induction k as [|k IH]; intros li Hk; apply (a11l_pass n HZST li); intros Hlt.
  - lia.
  - apply (IH (S li)). lia. }
intros li. exact (ALL (23 - li)%nat li eq_refl).
Qed.

End e.
End f.
End d.
