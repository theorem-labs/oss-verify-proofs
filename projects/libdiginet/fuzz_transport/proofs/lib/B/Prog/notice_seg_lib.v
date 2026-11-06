(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_grant's program walk: the listing's names are gsym, PALib names fuzz_grant.asan's objects and the wrappers' 4-byte jumps, and fuzz_grant's image bound; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/GrantPaLib.v, file sha256 1750b9b228be; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodePaLib.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBPaLib.v (file sha256 73c9e12166f6; donor not released): the names are dbsym's (the wrappers' free and malloc entries are DB___interceptor_trampoline_free and DB___interceptor_trampoline_malloc); PALib names fuzz_decode.asan-ubsan's objects of lib/B/Prog/DecodeBAddr.v and lib/B/AsanCells.v: the shadow-base GOT word is object 1 (GOT_CELL_K 0x992e8) and its cell object 14 (CELL_K 0xa1338), the side-stack flag's GOT word object 0 (GOT_UAR 0x99340) and its cell object 15 (UAR 0xa1340); the two cells are one object later than image A's 13 and 14 because image B's slots load one more object (object 13, 0x103c8); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/DgnTransportBPaLib.v; 9 of its 34 lines of code are new or changed and 475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/TransportGRunB.v, with its module paths and module names changed; 398 of its 427 lines of code are new or changed and 5 lines of the source are left out. *)
(* notice_seg_lib: the region, fact and kept-memory lemmas and the tactics the segments of notice's walk share
   (lib/B/Prog/notice_seg_*.v, notice_cgW.v); the image-B twin of lib/A/Prog/notice_seg_lib.v. It also states
   paj_run_x, the image-B twin of lib/A/Prog/TransportGRunA.v paj_run_x (W_journalG.v SRr_run_pi_tok_AJX at image B's
   listing classes, lib/B/Prog/DgnTransportBPa.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBLeafb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The symbolic runs of lib/A/Prog/PaShadow.v taken over the G journal (W_journalG.v ajournal_gx G XO OUT), at image
   B's listing: TransportGRunA.v's paj_run_x at DgnTransportBPa.v's PAListing / PAImg (classes over tbsym). *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {L : ptable tbsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Definition paj_run_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
  SRr_run_pi_tok_AJX tbsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
  pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
Definition paj_run_to_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
  SRr_run_to_pi_tok_AJX tbsym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
  pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
End g.

(* ------------------------------------------------------------------ *)
(* Values                                                              *)
(* ------------------------------------------------------------------ *)

(* The sign-extended 4-byte load of an atom holding a u32: its signed value. *)
Lemma nt_sext32 : forall E (a : nat) u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
  intros E a u H R. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma nt_add_lit : forall x y, alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma nt_s32_range : forall NB k, -2 ^ 31 <= TW.s32_at NB k < 2 ^ 31.
Proof.
  intros NB k. unfold TW.s32_at. pose proof (bv_swrap_in_range 32 (TW.u_at NB k 4) ltac:(discriminate)) as R.
  change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* An int increment (`addiw r1, r0, 1`) of an int g, read back sign-extended: g + 1, or INT_MIN at INT_MAX. *)
Lemma nt_inc_z : forall g, -2 ^ 31 <= g < 2 ^ 31 ->
  bv_swrap 32 ((g mod 2 ^ 64) mod 2 ^ 32 + 1) = if g =? TC.INT_MAX then - 2 ^ 31 else g + 1.
Proof.
  intros g Hg.
  destruct (Z.eqb_spec g TC.INT_MAX) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - unfold TC.INT_MAX in E. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
    Z.div_mod_to_equations. lia.
Qed.

(* The value of a sign-extended 4-byte load of an atom holding a u32 u, and of its int increment. *)
Lemma nt_inc_U : forall E (a : nat) u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  U E (SExt true 32 (SOff a 0)) = bv_swrap 32 u mod 2 ^ 64 /\
  Sg E (SExt true 32 (SOff a 0)) = bv_swrap 32 u /\
  Sg E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1)) =
    (if bv_swrap 32 u =? TC.INT_MAX then - 2 ^ 31 else bv_swrap 32 u + 1).
Proof.
  intros E a u H R.
  pose proof (bv_swrap_in_range 32 u ltac:(discriminate)) as Rg. change (bv_half_modulus 32) with (2 ^ 31) in Rg.
  assert (HU : U E (SExt true 32 (SOff a 0)) = bv_swrap 32 u mod 2 ^ 64).
  { unfold U. rewrite (nt_sext32 E a u H R), Z_to_bv_unsigned. reflexivity. }
  split; [exact HU|]. split.
  - unfold Sg. rewrite (nt_sext32 E a u H R), Z_to_bv_signed.
    set (g := bv_swrap 32 u) in *. clearbody g.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
    rewrite Z.mod_small by lia. lia.
  - rewrite S_SAluw. cbn [zalu_raw]. rewrite HU, (U_lit E 1) by lia.
    rewrite (Z.mod_small 1) by lia. apply nt_inc_z. exact Rg.
Qed.

(* The UBSan overflow test after an increment (`blt r1, r0, trap`): taken exactly at INT_MAX. *)
Lemma nt_ovf_br : forall E (a : nat) u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1)))
    (sv_denot E (SExt true 32 (SOff a 0))) = (bv_swrap 32 u =? TC.INT_MAX).
Proof.
  intros E a u H R.
  pose proof (bv_swrap_in_range 32 u ltac:(discriminate)) as Rg. change (bv_half_modulus 32) with (2 ^ 31) in Rg.
  destruct (nt_inc_U E a u H R) as (_ & S1 & S2).
  cbn [branch_taken]. unfold bv_lts.
  change (bv_signed (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1))))
    with (Sg E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1))).
  change (bv_signed (sv_denot E (SExt true 32 (SOff a 0)))) with (Sg E (SExt true 32 (SOff a 0))).
  rewrite S1, S2.
  destruct (Z.eqb_spec (bv_swrap 32 u) TC.INT_MAX) as [E1|E1]; unfold TC.INT_MAX in *.
  - apply Z.ltb_lt. lia.
  - apply Z.ltb_ge. lia.
Qed.

(* The bytes of the stored increment: byte j < 4 of the 64-bit word is byte j of the int g + 1. *)
Lemma nt_inc_bytes : forall E (a : nat) u (j : nat), ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  bv_swrap 32 u <> TC.INT_MAX -> (j < 4)%nat ->
  bv_unsigned (YP09.byte_of_word (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1))) (Z.of_nat j)) =
  YO0f.le_byte (bv_swrap 32 u + 1) 4 j.
Proof.
  intros E a u j H R Hne Hj.
  destruct (nt_inc_U E a u H R) as (_ & _ & S2).
  rewrite (proj2 (Z.eqb_neq _ _) Hne) in S2.
  unfold YP09.byte_of_word. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  change (bv_unsigned (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1))))
    with (U E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit 1))).
  rewrite U_of_S, S2. unfold bv_wrap, bv_modulus, YO0f.le_byte. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (8 * Z.of_nat 4) with 32.
  rewrite (DgnTransportBLeafb.decode_leafb_byte_mod (bv_swrap 32 u + 1) 64 (8 * Z.of_nat j)) by lia.
  rewrite (DgnTransportBLeafb.decode_leafb_byte_mod (bv_swrap 32 u + 1) 32 (8 * Z.of_nat j)) by lia.
  reflexivity.
Qed.

(* The kind test at 0x83458 (bltu a2, a0 with a2 = 5, a0 = kind - 1): taken exactly for a kind outside 1 .. 6. *)
Lemma nt_br_kind : forall E (NB : list byte) k, ew E 33 = Z_to_bv 64 (TW.u_at NB 0 4) -> TW.s32_at NB 0 = k ->
  branch_taken BC_LTU (sv_denot E (SLit 5)) (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))))
  = negb ((1 <=? k) && (k <=? 6)).
Proof.
  intros E NB k H33 Hk.
  pose proof (TWL.u_at_range NB 0 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  pose proof (nt_s32_range NB 0) as Rk. rewrite Hk in Rk.
  change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit (-1))))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff 33 0))) (Z_to_bv 64 (-1))).
  rewrite (nt_sext32 E 33 _ H33 R). change (bv_swrap 32 (TW.u_at NB 0 4)) with (TW.s32_at NB 0). rewrite Hk.
  rewrite nt_add_lit. cbn [branch_taken sv_denot]. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small 5) by lia.
  destruct (Z_lt_le_dec (k + -1) 0) as [Hn|Hn].
  - rewrite <- (Z.mod_add (k + -1) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
    replace ((1 <=? k) && (k <=? 6))%bool with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    apply Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia.
    destruct (Z_le_gt_dec k 6) as [H6|H6].
    + replace ((1 <=? k) && (k <=? 6))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
      apply Z.ltb_ge. lia.
    + replace ((1 <=? k) && (k <=? 6))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
      apply Z.ltb_lt. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Facts and regions                                                   *)
(* ------------------------------------------------------------------ *)

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The facts replaced by others that hold. *)
Lemma nt_facts_set : forall E ss ms G,
  st_ok_pi segs VAL E ss ms -> facts_ok E G ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) G) ms.
Proof.
  intros E ss ms G HS HG. unfold st_ok_pi, abs_ss, setpc, st_ok in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 HG)))))))).
Qed.

Lemma nt_facts_ok : forall E sp p,
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 11) = p -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 4096 <= p <= 2 ^ 47 - 72 -> p mod 8 = 0 ->
  facts_ok E nt_facts.
Proof.
  intros E sp p U2 U11 E32 Hsp Hsp16 Hp Hp8.
  unfold nt_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U11, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* The facts with one more atom: an object holding the 4-aligned address v (the base of a writable region of G, so
   the run's static check can place its window away from the shadow band). *)
Definition nt_facts_g (obj : nat) (v : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 72) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_OBJ obj, mkAF v v 2)] [] [].

Lemma nt_facts_g_ok : forall E sp p obj v,
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 11) = p -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E (A_OBJ obj)) = v ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 4096 <= p <= 2 ^ 47 - 72 -> p mod 8 = 0 -> v mod 4 = 0 ->
  facts_ok E (nt_facts_g obj v).
Proof.
  intros E sp p obj v U2 U11 E32 Uo Hsp Hsp16 Hp Hp8 Hv4.
  unfold nt_facts_g, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U11, Uo, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* The notice's first 16 bytes, from its garr8 array at the current memory. *)
Lemma nt_preg_ok : forall E (mm : word -> option byte) p (NB : list byte),
  ew E 11 = Z_to_bv 64 p -> 0 <= p -> p + 72 <= 2 ^ 47 ->
  ew E 33 = Z_to_bv 64 (TW.u_at NB 0 4) -> ew E 34 = Z_to_bv 64 (TW.u_at NB 4 4) ->
  ew E 35 = Z_to_bv 64 (TW.u_at NB 8 4) -> ew E 36 = Z_to_bv 64 (TW.u_at NB 12 4) ->
  garr8 segs mm p (map DSpec.bz NB) -> length NB = 72%nat ->
  region_ok segs E mm nt_reg_p.
Proof.
  intros E mm p NB E11 Hp0 Hp47 E33 E34 E35 E36 HG HL.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n0 v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (R : forall k, 0 <= TW.u_at NB k 4 < 2 ^ 32)
    by (intros k; pose proof (TWL.u_at_range NB k 4) as R; change (8 * Z.of_nat 4) with 32 in R; exact R).
  unfold nt_reg_p, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E11, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val segs E _ p 0 4 (SOff 33 0) (TW.u_at NB 0 4));
      [apply DEN; [exact E33 | pose proof (R 0); lia] | exact (R 0) | lia | exact (nt_val4 mm p NB 0 HG HL ltac:(lia) ltac:(lia))].
  - apply (chunk_ok_val segs E _ p 4 4 (SOff 34 0) (TW.u_at NB 4 4));
      [apply DEN; [exact E34 | pose proof (R 4); lia] | exact (R 4) | lia | exact (nt_val4 mm p NB 4 HG HL ltac:(lia) ltac:(lia))].
  - apply (chunk_ok_val segs E _ p 8 4 (SOff 35 0) (TW.u_at NB 8 4));
      [apply DEN; [exact E35 | pose proof (R 8); lia] | exact (R 8) | lia | exact (nt_val4 mm p NB 8 HG HL ltac:(lia) ltac:(lia))].
  - apply (chunk_ok_val segs E _ p 12 4 (SOff 36 0) (TW.u_at NB 12 4));
      [apply DEN; [exact E36 | pose proof (R 12); lia] | exact (R 12) | lia | exact (nt_val4 mm p NB 12 HG HL ltac:(lia) ltac:(lia))].
Qed.

(* A byte of TRANS_RO_RD read through trans_rom_view_rd. *)
Lemma nt_rom_mbyte : forall (W : world segs) m a v,
  trans_rom_view_rd W m -> trans_in_ro_rd a ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)) = Some v -> 0 <= v < 256 ->
  mbyte segs (mrestrict (w_H W) m) a = Some (Z_to_bv 8 v).
Proof.
  intros W m a v HRO Ha Hv Hr. pose proof (HRO a Ha) as H. rewrite Hv in H. unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) m) a) as [b|]; [|discriminate H].
  cbn [option_map] in H. injection H as H. f_equal. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The jump table's 24 bytes. *)
Definition nt_tbl_bytes : list Z :=
  [252; 36; 6; 0; 120; 37; 6; 0; 52; 37; 6; 0; 84; 37; 6; 0; 32; 37; 6; 0; 116; 38; 6; 0].
Lemma nt_tbl_rom : forall j, (j < 24)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (TRANS_JT_NOTICE + Z.of_nat j))) =
  Some (nth j nt_tbl_bytes 0).
Proof. intros j Hj. do 24 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. Qed.

Lemma nt_tbl_in : forall a, TRANS_JT_NOTICE <= a < TRANS_JT_NOTICE + 24 -> trans_in_ro_rd a.
Proof.
  intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_JT_NOTICE, 24).
  split; [unfold TRANS_RO_RD; cbn [app In]; right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

(* The table's 4-byte entry i, little-endian. *)
Lemma nt_tbl_val : forall (W : world segs) m (i : nat) e, (i < 6)%nat -> nth i NT_TBL 0 = e ->
  trans_rom_view_rd W m -> val_mem segs (mrestrict (w_H W) m) (TRANS_JT_NOTICE + 4 * Z.of_nat i) 4 e.
Proof.
  intros W m i e Hi He HRO j Hj.
  replace (TRANS_JT_NOTICE + 4 * Z.of_nat i + Z.of_nat j) with (TRANS_JT_NOTICE + Z.of_nat (4 * i + j)) by lia.
  apply (nt_rom_mbyte W m _ (le_byte e 4 j) HRO).
  - apply nt_tbl_in. unfold TRANS_JT_NOTICE. lia.
  - rewrite (nt_tbl_rom (4 * i + j) ltac:(lia)). f_equal. subst e.
    do 6 (destruct i as [|i]; [do 4 (destruct j as [|j]; [vm_compute; reflexivity|]); lia|]). lia.
  - unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma nt_tbl_ok : forall (W : world segs) m E,
  bv_unsigned (ew E (A_OBJ 36)) = TRANS_JT_NOTICE -> trans_rom_view_rd W m ->
  region_ok segs E (mrestrict (w_H W) m) nt_reg_tbl.
Proof.
  intros W m E U36 HRO.
  unfold nt_reg_tbl, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U36. split; [unfold TRANS_JT_NOTICE; lia|]. split; [unfold TRANS_JT_NOTICE; lia|].
  split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val segs E _ _ 0 4 (SLit 0x624fc) 0x624fc); [reflexivity | lia | lia |].
    exact (nt_tbl_val W m 0 _ ltac:(lia) eq_refl HRO).
  - apply (chunk_ok_val segs E _ _ 4 4 (SLit 0x62578) 0x62578); [reflexivity | lia | lia |].
    exact (nt_tbl_val W m 1 _ ltac:(lia) eq_refl HRO).
  - apply (chunk_ok_val segs E _ _ 8 4 (SLit 0x62534) 0x62534); [reflexivity | lia | lia |].
    exact (nt_tbl_val W m 2 _ ltac:(lia) eq_refl HRO).
  - apply (chunk_ok_val segs E _ _ 12 4 (SLit 0x62554) 0x62554); [reflexivity | lia | lia |].
    exact (nt_tbl_val W m 3 _ ltac:(lia) eq_refl HRO).
  - apply (chunk_ok_val segs E _ _ 16 4 (SLit 0x62520) 0x62520); [reflexivity | lia | lia |].
    exact (nt_tbl_val W m 4 _ ltac:(lia) eq_refl HRO).
  - apply (chunk_ok_val segs E _ _ 20 4 (SLit 0x62674) 0x62674); [reflexivity | lia | lia |].
    exact (nt_tbl_val W m 5 _ ltac:(lia) eq_refl HRO).
Qed.

(* A 4-byte field of GOT at offset off (a GOT field region based at its object), its value the world's u32. *)
Lemma nt_fld_ok : forall (W : world segs) m E Bw (obj atom : nat) off,
  bv_unsigned (ew E (A_OBJ obj)) = TB_GOT + off -> 0 <= off -> off + 4 <= TW.SZ_GOT ->
  ew E atom = Z_to_bv 64 (TW.u_at Bw (TW.OFF_GOT + off) 4) ->
  tw_at TMAP_B (aview segs (w_H W) m) Bw ->
  region_ok segs E (mrestrict (w_H W) m) (nt_reg_fld obj atom).
Proof.
  intros W m E Bw obj atom off Uo Ho Ho4 Ea Htw.
  pose proof (TWL.u_at_range Bw (TW.OFF_GOT + off) 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold nt_reg_fld, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Uo. unfold TW.SZ_GOT in Ho4. split; [unfold TB_GOT; lia|]. split; [unfold TB_GOT; lia|].
  split.
  { intros o Hoo. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_GOT + off + o) G_HARNESS_B_rw).
    apply nt_inG_GOT. lia. }
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ (TB_GOT + off) 0 4 (SOff atom 0) (TW.u_at Bw (TW.OFF_GOT + off) 4));
    [cbn [sv_denot]; rewrite Ea, unsigned_lit_small, Z.add_0_r by lia; reflexivity | exact R | lia |].
  rewrite Z.add_0_r.
  exact (tw_read_val segs _ TMAP_B Bw TW.OFF_GOT TB_GOT TW.SZ_GOT off 4 TMAP_B_ok Htw TMAP_B_GOT ltac:(lia)
    ltac:(unfold TW.SZ_GOT; lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* Kept memory                                                         *)
(* ------------------------------------------------------------------ *)

(* The world relation kept, when no byte of the table is in the changed set. *)
Lemma nt_tw_keep : forall (W : world segs) memc m Bw (Zs : Z -> Prop),
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> nt_KA W memc m Zs -> (forall x, tw_in TMAP_B x -> ~ Zs x) ->
  tw_at TMAP_B (aview segs (w_H W) m) Bw.
Proof.
  intros W memc m Bw Zs H [KA _] HZ. apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact H|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KA; [lia | exact (HZ x Hx)].
Qed.

(* range_addressable kept when the changed set misses the range's shadow bytes. *)
Lemma nt_ra_kept : forall (W : world segs) memc m q n (Zs : Z -> Prop),
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n -> nt_KA W memc m Zs ->
  (forall x, q <= x < q + n -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ Zs (SHADOW_OFF + x / 8)) ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF q n.
Proof.
  intros W memc m q n Zs HRA [KA _] HZ x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. destruct (HZ x Hx) as [H1 H2]. rewrite (KA _ H1 H2). exact Hs.
Qed.

(* The walk's changed set misses the shadow band and the image's read-only bytes. *)
Lemma nt_Zs_far : forall regs Bw n a, alloc_ceiling <= spZ regs - NOTICE_STK ->
  nt_Zs regs Bw n a -> (alloc_ceiling <= a) \/ (TB_M <= a < TB_GOT + 224).
Proof.
  intros regs Bw n a Hce [Hw | Hw]; [left; lia|].
  right. destruct (nt_wr_range Bw n a Hw) as [H|H]; unfold TB_M, TB_GOT in *; lia.
Qed.

(* An array of bytes kept, when the changed set misses its range. *)
Lemma nt_garr8_keep : forall (W : world segs) memc m (Zs : Z -> Prop) q (l : list Z),
  nt_KA W memc m Zs -> garr8 segs (mrestrict (w_H W) memc) q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
  garr8 segs (mrestrict (w_H W) m) q l.
Proof.
  intros W memc m Zs q l [KA _] HG HZ.
  apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) m) q l HG).
  intros a Ha. apply (mbyte_of_aview segs). destruct (HZ a Ha) as [H1 H2]. exact (KA a H1 H2).
Qed.

(* The read-only bytes of the image are kept: each lies below 0xa4000, and the walk changes only the stack window
   (above alloc_ceiling) and bytes of M and GOT. *)
Lemma nt_ro_keep : forall (W : world segs) memc m regs Bw n,
  alloc_ceiling <= spZ regs - NOTICE_STK -> nt_KA W memc m (nt_Zs regs Bw n) ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W m.
Proof.
  intros W memc m regs Bw n Hce [KA _] HRO a Ha.
  pose proof (trans_ro_rd_bounds a Ha) as Hb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite (KA a ltac:(lia)); [exact (HRO a Ha)|].
  intros Hz. destruct (nt_Zs_far regs Bw n a Hce Hz) as [H|H]; unfold TB_M, TB_GOT in *; lia.
Qed.

(* A byte of a stored chunk, read through the view. *)
Lemma nt_chunk_aview : forall (W : world segs) m E base off (w : N) e i,
  YP09.chunk_ok segs E (mrestrict (w_H W) m) base (YP09.mkChunk off (YP09.CVal w e)) -> 0 <= i < Z.of_N w ->
  aview segs (w_H W) m (base + off + i) = Some (bv_unsigned (YP09.byte_of_word (sv_denot E e) i)).
Proof.
  intros W m E base off w e i Hc Hi.
  destruct (Hc i ltac:(unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. injection Hb as <-.
  unfold aview. rewrite Hm. reflexivity.
Qed.

(* The world after a 4-byte store into one payload: the model's upd .. (put 4 v). *)
Lemma nt_tw_set4 : forall (W : world segs) memc m Bw o b n k v,
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) m (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (b + k <= x < b + k + 4) -> aview segs (w_H W) m x = aview segs (w_H W) memc x) ->
  tw_at TMAP_B (aview segs (w_H W) m) (TW.upd Bw (o + k) (TW.put 4 v)).
Proof.
  intros W memc m Bw o b n k v Htw Hin Hk Hkn Hnew Hfr.
  apply (tw_write TMAP_B (aview segs (w_H W) memc) (aview segs (w_H W) m) Bw o b n k 4 v TMAP_B_ok Htw Hin Hk);
    [lia | exact Hnew |].
  intros x Hx Hn. apply Hfr; [exact Hx | lia].
Qed.
End r.

(* ------------------------------------------------------------------ *)
(* The statement of one arm of the kind switch                         *)
(* ------------------------------------------------------------------ *)

(* The walk from the jump `jr a0` (0x83474) with a0 the arm's code pointer, for a notice of kind kd: the symbolic
   state is the entry state after the prologue, the kind load and the switch (its one region is the 16-byte frame),
   the journal is the caller's at the current memory, and the walk has changed only bytes of its stack window
   (nt_Wn: no byte of the world yet, so an arm reads the world at the current memory). *)
Definition nt_Wn (regs : bvmap 5 word) (a : Z) : Prop := spZ regs - NOTICE_STK <= a < spZ regs.

Lemma nt_KA_mono : forall (W : world tfibsegs) memc m (Zs Zs' : Z -> Prop),
  (forall a, Zs a -> Zs' a) -> nt_KA W memc m Zs -> nt_KA W memc m Zs'.
Proof.
  intros W memc m Zs Zs' HZ [KA GA]. split; [|exact GA].
  intros a Ha Hn. apply KA; [exact Ha|]. intros Hz. exact (Hn (HZ a Hz)).
Qed.

Lemma nt_Wn_Zs : forall regs Bw n a, nt_Wn regs a -> nt_Zs regs Bw n a.
Proof. intros regs Bw n a H. left. exact H. Qed.

Lemma nt_tw_Wn : forall (W : world tfibsegs) memc m regs Bw,
  TG.G_HARNESS_B_HI <= spZ regs - NOTICE_STK ->
  tw_at TMAP_B (aview tfibsegs (w_H W) memc) Bw -> nt_KA W memc m (nt_Wn regs) ->
  tw_at TMAP_B (aview tfibsegs (w_H W) m) Bw.
Proof.
  intros W memc m regs Bw Hce H HK. apply (nt_tw_keep W memc m Bw (nt_Wn regs) H HK).
  intros x Hx Hz. pose proof (TMAP_B_hull x Hx) as Hh. unfold nt_Wn in Hz. lia.
Qed.

Section path. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Variable B : asyms.
Variable MT : ameter_ops.

Definition nt_path (kd off : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p n Fr Bw Bw' NB
         (E : env) (ms : machine_state) (md : Model),
    @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
    TI.n_kind n = kd ->
    st_ok_pi segs VAL E (nt_ss_jr (SOff A_TEXT off)) (restrict (w_H W) ms) ->
    img_env VAL A_LIM E ->
    (forall j, (j < 43)%nat -> ew E j = ew (nt_E regs NB Bw) j) ->
    ed E = ed (nt_E regs NB Bw) ->
    sh_ok segs NT_Bx NT_SH E (mrestrict (w_H W) (ms_mem ms)) ->
    @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
      (ms_mem ms) md k ->
    nt_KA W memc (ms_mem ms) (nt_Wn regs) ->
    SRr segs W (mkCfg ms md)
      (@transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw').
End path.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac nt_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "nt_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac nt_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The regions of HS's state, computed. *)
Ltac nt_norm HS := lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss ?ms => let v := eval vm_compute in ss in change (st_ok_pi sg vl Ex v ms) in HS end.
