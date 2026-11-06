(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 344 of its 380 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the two token runs w5i_head / w5i_tail become the runs B and C0 of the walk piece W8 (lib/A/RtPgW8Kit.v);
   the pcs, registers, start regions, atoms and facts are rate's; the post is RtPgSteps.rts_post (the statements
   rw8_runB_stmt and rw8_runC0_stmt) instead of a local one; the pad count of pod_pad is new. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): two engine runs of the walk piece
   "write + record" of LLVMFuzzerTestOneInput (0x80714). Proves no function (kind: segment lemma).

   RUN B, 0x81f44 -> __asan_memset 0x51cfc (pod.h:180 and pod_pad, pod.h:186-192):
     the check of pp->len (s6 = its shadow byte, s7 = pp + 0x4000), len += e->size (s8), the check again,
     s8 = (-len) & 7 (negw / andi), the capacity test `bltu 0x4000, s8 + len` (not taken: the atoms' ranges decide
     it), a0 = pp + len, a1 = 0, a2 = s8, `jal` __asan_memset (the engine steps it, so ra = 0x81f90).
     The start state names the start's pp->len L1 by the extra atom 33 (read unsigned, so L1 mod 2^64: the
     statement bounds only L1 + sz from below), e->size by atom 34 (s8) and L1 + sz by atom 35 (an alias of the
     sum). The engine's pad term (0 - (L1 + sz)) & 7 is Model.pad8 (L1 + sz) by w8b_pad.
   RUN C0, 0x81f90 -> 0x81ffc, `first` (R+0x110) clear:
     the check of pp->len, len += s8 (the pad), s8 = s10, s10 = R+0x118, a0 = R+0x110 (= 0), a1 = R+0x128 (k),
     `beqz a0` taken. Atoms 33 = L0 (the start's pp->len), 34 = the pad (s8), 35 = k.
   Every check is on pp's bytes and is covered by the shadow entry (27, 0x4000, 0x4008) of rw8_shent_blk; both runs
   reach their stop pc with no fresh atom and no shadow obligation. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- run B, the start state at 0x81f44: atoms 32 = K, 33 = L1 mod 2^64, 34 = sz, 35 = L1 + sz ---- *)
Definition w8b_extraB (L1 sz : Z) : list word := [w64 RW8_SB; w64 (L1 mod 2 ^ 64); w64 sz; w64 (L1 + sz)].
Definition w8b_ovB : list (bv 5 * sv) :=
  [((18%bv : bv 5), rw8_Bx); ((22%bv : bv 5), rw8_sh 27 0x4000);
   ((23%bv : bv 5), SOff 27 0x4000); ((24%bv : bv 5), SOff 34 0)].
Definition w8b_lenB : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 33 0))].
Definition w8b_factsB : facts :=
  mkFacts [(27%nat, mkAF 4096 140737479966720 4);
           (32%nat, mkAF RW8_SB RW8_SB 0);
           (34%nat, mkAF 0 45 0);
           (35%nat, mkAF 40 15993 0)]
   [] [(SAlu ALU_ADD (SOff 33 0) (SOff 34 0), SOff 35 0)].
Definition w8b_ssB : sstate := mkSS 0x81f44 (rw8_sr w8b_ovB) [w8b_lenB] None w8b_factsB.
Definition w8b_SH : list shent := [mkSHE 27 0x4000 0x4008].

(* ---- run C0, the start state at 0x81f90: atoms 32 = K, 33 = L0, 34 = p, 35 = k ---- *)
Definition w8b_extraC (L0 p kk : Z) : list word := [w64 RW8_SB; w64 L0; w64 p; w64 kk].
Definition w8b_ovC : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((18%bv : bv 5), rw8_Bx); ((22%bv : bv 5), rw8_sh 27 0x4000);
   ((23%bv : bv 5), SOff 27 0x4000); ((24%bv : bv 5), SOff 34 0)].
Definition w8b_slotsC : YP09.region :=            (* the real frame's cells, read only; `first` = 0 *)
  YP09.mkRegion (Some 9%nat) 0x110 0x130 0 0
   [YP09.mkChunk 0x110 (CVal 8 (SLit 0));
    YP09.mkChunk 0x118 (CVal 8 (SLit 18446744073709535231));
    YP09.mkChunk 0x128 (CVal 8 (SOff 35 0))].
Definition w8b_lenC : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 33 0))].
Definition w8b_factsC : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (27%nat, mkAF 4096 140737479966720 4);
           (32%nat, mkAF RW8_SB RW8_SB 0);
           (33%nat, mkAF 40 5440 0);
           (34%nat, mkAF 0 7 0);
           (35%nat, mkAF 0 31 0)] [] [].
Definition w8b_ssC : sstate := mkSS 0x81f90 (rw8_sr w8b_ovC) [w8b_slotsC; w8b_lenC] None w8b_factsC.

(* ======================================== the pad count ======================================== *)
(* the 64-bit (0 - x) & 7 of the code is pod_pad's (8 - x mod 8) mod 8 *)
Lemma w8b_pad : forall x, zcanon (Z.land (zcanon (0 - x)) 7) = pad8 x.
Proof.
intros x. unfold pad8, zcanon, M64.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
change (2 ^ 64) with 18446744073709551616.
pose proof (Z.div_mod (0 - x) 18446744073709551616 ltac:(lia)) as D1.
pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
assert (A : (0 - x) mod 18446744073709551616 mod 8 = (8 - x mod 8) mod 8).
{ replace ((0 - x) mod 18446744073709551616)
    with ((8 - x mod 8) + (- 2305843009213693952 * ((0 - x) / 18446744073709551616) - 1 - x / 8) * 8) by lia.
  apply Z_mod_plus_full. }
rewrite A. apply Z.mod_small. pose proof (Z.mod_pos_bound (8 - x mod 8) 8 ltac:(lia)). lia.
Qed.
Lemma w8b_den_pad : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff n 0)) (SLit 7)) = w64 (pad8 v).
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom E n v Hn Hv).
change (zcanon 0) with 0. change (zcanon 7) with 7. apply w8b_pad.
Qed.
Lemma w8b_den_pad0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff n 0)) (SLit 7)) (SLit 0)) = w64 (pad8 v).
Proof.
intros E n v Hn Hv. pose proof (pad8_bound v) as Hp. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
unfold U. rewrite (w8b_den_pad E n v Hn Hv). unfold w64. rewrite unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* a word's bytes name its value modulo 2^64 too *)
Lemma w8b_val_mod : forall m a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v V k Hk. rewrite (V k Hk). unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================================== run B: 0x81f44 -> __asan_memset ======================================== *)
Lemma rw8_runB : rw8_runB_stmt B MT.
Proof using MTL LAWS.
unfold rw8_runB_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos L1 sz
  HJ Hgeo Hpp Hfresh H2 H18 H22 H23 H24 H27 Vlen Hs1 Hs2 Hsz.
pose proof rw8_wx as Hwx. pose proof rw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
assert (HL1u : 0 <= L1 mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (E := Ereg regs (w8b_extraB L1 sz)).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 RW8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (L1 mod 2 ^ 64)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 sz) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (L1 + sz)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (w8b_extraB L1 sz)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs rw8_Bx w8b_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (rw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4008 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = RW8_SB) by (rewrite E32; apply unsigned_lit_small; unfold RW8_SB; lia).
assert (U34 : bv_unsigned (ew E 34) = sz) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = L1 + sz) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (rw8_sr w8b_ovB) regs).
{ apply (rw8_regs_ok E regs (w8b_extraB L1 sz)); [exact HE|]. unfold w8b_ovB.
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold rw8_Bx. rewrite (rw8_den_off E 32 RW8_SB 0 E32) by (unfold RW8_SB; lia).
    rewrite Z.add_0_r, H18. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_sh E 27 pp 0x4000 E27 E32) by lia. rewrite H22. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 27 pp 0x4000 E27) by lia. rewrite H23. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 34 sz 0 E34) by lia. rewrite Z.add_0_r, H24. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E w8b_factsB).
{ split; [| split].
  - cbn [w8b_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U27, U32, U34, U35.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                        | (change (2 ^ 4) with 16; assumption) ].
  - cbn [w8b_factsB f_conds conds_ok]. exact I.
  - cbn [w8b_factsB f_alias alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 33 (L1 mod 2 ^ 64) E33 HL1u), (U_atom E 34 sz E34), (U_atom E 35 (L1 + sz) E35) by lia.
    unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia. apply Z.mod_small. lia. }
assert (HS : st_ok rsegs E w8b_ssB (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81f44) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w8b_ssB. apply (rw8_entry _ _ regs (w8b_extraB L1 sz) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold w8b_lenB. apply Forall_cons; [|apply Forall_nil].
    apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
      [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 33 0) (L1 mod 2 ^ 64));
      [ rewrite (rw8_den_off E 33 (L1 mod 2 ^ 64) 0 E33) by lia; rewrite Z.add_0_r; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | lia | exact (w8b_val_mod _ _ _ Vlen) ].
  - cbn. tauto.
  - exact HFK. }
unfold cfg_at; change (w64 RW8_RA1) with (Z_to_bv 64 0x81f44).
aj_run_to_tok rw8_tbl_ok HS HJ Hsh rw8_Bspan 0x51cfc.
(* the write window: pp->len *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp);
    [ reflexivity | exact U27
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the state at the callee's entry *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 36 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  red; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (rw8_regs_kept E Ef 36 (rw8_sr w8b_ovB) (ss_regs ssf) regs (ms_regs msf) rw8_clobB HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply rw8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (rw8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U27 in Hb; lia | ]);
    destruct Hr
  |];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 1%bv (SLit 532368) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 10%bv (SAlu ALU_ADD (SOff 27 0) (SOff 35 0)) HRf HA
                     ltac:(vm_compute; reflexivity) eq_refl);
          rewrite denot_lit_U; unfold w64; f_equal; rewrite U_SAlu; cbn [zalu_raw];
          rewrite (U_atom E 27 pp E27), (U_atom E 35 (L1 + sz) E35) by lia;
          apply zcanon_id; unfold M64; lia|];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 11%bv (SLit 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 12%bv
                     (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 35 0)) (SLit 7)) (SLit 0)) HRf HA
                     ltac:(vm_compute; reflexivity) eq_refl);
          exact (w8b_den_pad0 E 35 (L1 + sz) E35 ltac:(lia))|];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 24%bv
                     (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 35 0)) (SLit 7)) HRf HA
                     ltac:(vm_compute; reflexivity) eq_refl);
          exact (w8b_den_pad E 35 (L1 + sz) E35 ltac:(lia))|];
  assert (F27 : ew Ef 27 = ew E 27) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rf := fresh "Rf" in
  apply Forall_cons_iff in HM as [Rf _];
  let Cf := fresh "Cf" in
  destruct Rf as (_ & _ & _ & Cf);
  cbn [r_chunks r_base base_val] in Cf; try rewrite F27 in Cf; rewrite U27 in Cf;
  apply (val_of_chunk_ok rsegs Ef _ pp 0x4000 8 (SOff 35 0) (L1 + sz));
  [ rewrite Forall_forall in Cf; apply Cf; cbn [In]; repeat (first [left; reflexivity | right])
  | try rewrite (sv_denot_agree 36 E Ef (SOff 35 0) HA eq_refl);
    rewrite (rw8_den_off E 35 (L1 + sz) 0 E35) by lia; rewrite Z.add_0_r; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | lia ]
  end.
Qed.

(* ======================================== run C0: 0x81f90 -> 0x81ffc, `first` clear ======================================== *)
Lemma rw8_runC0 : rw8_runC0_stmt B MT.
Proof using MTL LAWS.
unfold rw8_runC0_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos L0 p kk rl
  HJ Hgeo Hpp Hfresh H2 H9 H18 H22 H23 H24 H26 H27 V110 V118 V128 Vlen HL0 HL0p Hp Hkk Hrl.
pose proof rw8_wx as Hwx. pose proof rw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (HR16 & HRlo & HRhi & HRhm & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hm1 : (- 0x4001) mod 2 ^ 64 = 18446744073709535231) by reflexivity.
rewrite Hm1 in V118.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
set (E := Ereg regs (w8b_extraC L0 p kk)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = w64 rl) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 RW8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 L0) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 p) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 kk) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (w8b_extraC L0 p kk)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs rw8_Bx w8b_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (rw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4008 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = RW8_SB) by (rewrite E32; apply unsigned_lit_small; unfold RW8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = L0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = p) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = kk) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (rw8_sr w8b_ovC) regs).
{ apply (rw8_regs_ok E regs (w8b_extraC L0 p kk)); [exact HE|]. unfold w8b_ovC.
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold rw8_Bx. rewrite (rw8_den_off E 32 RW8_SB 0 E32) by (unfold RW8_SB; lia).
    rewrite Z.add_0_r, H18. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_sh E 27 pp 0x4000 E27 E32) by lia. rewrite H22. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 27 pp 0x4000 E27) by lia. rewrite H23. reflexivity. }
  apply Forall_cons; [split; [apply rw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rw8_den_off E 34 p 0 E34) by lia. rewrite Z.add_0_r, H24. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E w8b_factsC).
{ split; [| split; [exact I | exact I]].
  cbn [w8b_factsC f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U27, U32, U33, U34, U35.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) ]. }
assert (HS : st_ok rsegs E w8b_ssC (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81f90) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w8b_ssC. apply (rw8_entry _ _ regs (w8b_extraC L0 p kk) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold w8b_slotsC, w8b_lenC. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0x110 8 (SLit 0) 0);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V110 ].
      * apply (chunk_ok_val rsegs E _ R 0x118 8 (SLit 18446744073709535231) 18446744073709535231);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V118 ].
      * apply (chunk_ok_val rsegs E _ R 0x128 8 (SOff 35 0) kk);
          [ rewrite (rw8_den_off E 35 kk 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V128 ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 33 0) L0);
        [ rewrite (rw8_den_off E 33 L0 0 E33) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
  - unfold w8b_slotsC, w8b_lenC; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U27; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 RW8_RA2) with (Z_to_bv 64 0x81f90).
aj_run_to_tok rw8_tbl_ok HS HJ Hsh rw8_Bspan 0x81ffc.
(* the write window: pp->len *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp);
    [ reflexivity | exact U27
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the end state at 0x81ffc *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 36 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  red; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (rw8_regs_kept E Ef 36 (rw8_sr w8b_ovC) (ss_regs ssf) regs (ms_regs msf) rw8_clobC HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply rw8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (rw8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U27 in Hb; lia | ]);
    destruct Hr
  |];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 11%bv (SOff 35 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 35 kk 0 E35) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 24%bv (SOff 26 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 26 rl 0 E26) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 36 _ _ 26%bv (SLit 18446744073709535231) HRf HA
                     ltac:(vm_compute; reflexivity) eq_refl);
          rewrite Hm1; reflexivity|];
  assert (F27 : ew Ef 27 = ew E 27) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rf := fresh "Rf" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rf _];
  let Cf := fresh "Cf" in
  destruct Rf as (_ & _ & _ & Cf);
  cbn [r_chunks r_base base_val] in Cf; try rewrite F27 in Cf; rewrite U27 in Cf;
  apply (val_of_chunk_ok rsegs Ef _ pp 0x4000 8 (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (L0 + p));
  [ rewrite Forall_forall in Cf; apply Cf; cbn [In]; repeat (first [left; reflexivity | right])
  | try rewrite (sv_denot_agree 36 E Ef (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) HA eq_refl);
    rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw];
    rewrite (U_atom E 33 L0 E33), (U_atom E 34 p E34) by lia;
    apply zcanon_id; unfold M64; lia
  | change (8 * Z.of_N 8) with 64; lia | lia ]
  end.
Qed.
End r.

Print Assumptions rw8_runB.
Print Assumptions rw8_runC0.
