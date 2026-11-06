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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 242 of its 276 lines of code are new or changed and 256 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd (w5i_head), with the post
   of proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v at a1de917d2c21; rate's run C1 of the walk piece W8 (0x81f90 ->
   __asan_memcpy 0x51860) replaces role's Int-7 pod: the start state, the record copy's arguments and the n_ent
   update are new, the post is RtPgSteps.rts_post, the engine helpers are RtPgW8Kit's rw8_ ones. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): run C1 of the walk piece "write + record" of
   LLVMFuzzerTestOneInput, 0x81f90 -> __asan_memcpy 0x51860 on the path where `first` (R+0x110) is 1 (pod.h:180 the
   end of pod_pad, pod.h:432 `pp->ent[pp->n_ent++] = e`). Proves no function (kind: segment lemma).

   THE CODE
     0x81f90-0x81f98  the check of the 8-byte load of pp->len (s6 = (pp+0x4000)>>3 + K)
     0x81f9c-0x81fa4  pp->len += s8 (the pad)
     0x81fa8-0x81fb4  s8 := s10 (the rest of the input); s10 := R+0x118 (-0x4001); a0 := `first` (R+0x110);
                      a1 := R+0x128 (overwritten below, its value is not used)
     0x81fb8          beqz a0 -> 0x81ffc, not taken (first = 1)
     0x81fbc-0x81fc8  the check of the 4-byte access at pp+0x4d14 (pp->n_ent): R+0xa8 holds (pp+0x4d14)>>3; the
                      shadow byte is loaded with `lb` and the `bnez` to the slow block 0x82118 is decided by the
                      full zero granule rule (0x4d14 rounds down to 0x4d10; the shadow entry reaches 0x4d18)
     0x81fcc-0x81fe0  n_ent := n_ent + 1 at pp+0x4d14 (a2 = R+0xb8 = pp+0x4d14), a0 := 104 * n_ent
     0x81fe4-0x81ff4  a0 := pp+0x4014 + 104 * n_ent (R+0xa0 = &pp->ent[0]), a2 := 104, a1 := R+0x138 (= &e = F+0xf0),
                      jal __asan_memcpy (ra = 0x81ff8)
   The cell R+0x128 has no hypothesis in the statement: the run reads it, so its eight bytes get a value from the
   journal's stack presence (c1_word); the value goes to a1 and is overwritten before the call. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the start state at 0x81f90: atoms 32 = K, 33 = L0 (pp->len), 34 = p (the pad, s8), 35 = kk (pp->n_ent),
   36 = the word at R+0x128 ---- *)
Definition c1_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((18%bv : bv 5), rw8_Bx); ((22%bv : bv 5), rw8_sh 27 0x4000);
   ((23%bv : bv 5), SOff 27 0x4000); ((24%bv : bv 5), SOff 34 0)].
Definition c1_rR : YP09.region :=            (* the real frame's cells, read only; `first` = 1 *)
  YP09.mkRegion (Some 9%nat) 0xa0 0x140 0 0
   [YP09.mkChunk 0xa0 (CVal 8 (SOff 27 0x4014));
    YP09.mkChunk 0xa8 (CVal 8 (rw8_shr 27 0x4d14));
    YP09.mkChunk 0xb8 (CVal 8 (SOff 27 0x4d14));
    YP09.mkChunk 0x110 (CVal 8 (SLit 1));
    YP09.mkChunk 0x118 (CVal 8 (SLit 18446744073709535231));
    YP09.mkChunk 0x128 (CVal 8 (SOff 36 0));
    YP09.mkChunk 0x138 (CVal 8 (SOff 19 0x10))].
Definition c1_rLen : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 33 0))].
Definition c1_rNent : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4d14 0x4d18 0x4d14 0x4d18 [YP09.mkChunk 0x4d14 (CVal 4 (SOff 35 0))].
Definition c1_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (27%nat, mkAF 4096 140737479966720 4);
           (32%nat, mkAF RW8_SB RW8_SB 0);
           (33%nat, mkAF 40 5440 0);
           (34%nat, mkAF 0 7 0);
           (35%nat, mkAF 0 31 0)] [] [].
Definition c1_ss : sstate := mkSS 0x81f90 (rw8_sr c1_ov) [c1_rR; c1_rLen; c1_rNent] None c1_facts.
(* the shadow entry over pp->len .. pp->n_ent: the n_ent check needs the whole granule [0x4d10, 0x4d18) *)
Definition c1_SH : list shent := [mkSHE 27 0x4000 0x4d18].
Definition c1_extra (L0 p kk w : Z) : list word := [w64 RW8_SB; w64 L0; w64 p; w64 kk; w64 w].

(* ======================================== helpers ======================================== *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* eight present bytes hold some word *)
Lemma c1_word : forall (H : word -> bool) (mem : word -> option byte) (a : Z),
(forall j, 0 <= j < 8 -> apresent H mem (a + j)) ->
exists v, 0 <= v < 2 ^ 64 /\ val_mem rsegs (mrestrict H mem) a 8 v.
Proof.
intros H mem a Hp.
assert (A : forall j, 0 <= j < 8 -> exists b, aview rsegs H mem (a + j) = Some b /\ 0 <= b < 256).
{ intros j Hj. destruct (Hp j Hj) as [Hh [b Hb]]. exists (bv_unsigned b). split; [|apply rtm_byte_range].
  unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
destruct (A 0 ltac:(lia)) as (b0 & A0 & R0). rewrite Z.add_0_r in A0.
destruct (A 1 ltac:(lia)) as (b1 & A1 & R1). destruct (A 2 ltac:(lia)) as (b2 & A2 & R2).
destruct (A 3 ltac:(lia)) as (b3 & A3 & R3). destruct (A 4 ltac:(lia)) as (b4 & A4 & R4).
destruct (A 5 ltac:(lia)) as (b5 & A5 & R5). destruct (A 6 ltac:(lia)) as (b6 & A6 & R6).
destruct (A 7 ltac:(lia)) as (b7 & A7 & R7).
exists (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))).
split; [lia|].
apply val_mem_of_rdword. unfold rdword. rewrite A0, A1, A2, A3, A4, A5, A6, A7. reflexivity.
Qed.
Lemma c1_den_add : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the record copy's destination as the engine builds it: pp + 0x4014 + 104 * kk *)
Lemma c1_den_dst : forall E pp kk, ew E 27 = Z_to_bv 64 pp -> ew E 35 = Z_to_bv 64 kk ->
0 <= pp -> pp + 0x4014 + 104 * 31 < 2 ^ 64 -> 0 <= kk <= 31 ->
sv_denot E (SAlu ALU_ADD (SOff 27 16404) (SMd M_MUL (SOff 35 0) (SLit 104))) = w64 (pp + 0x4014 + 104 * kk).
Proof.
intros E pp kk H27 H35 Hp Hb Hk. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom_off E 27 pp 16404 H27) by lia. rewrite (U_atom E 35 kk H35) by lia. rewrite U_SLit.
rewrite (zcanon_id 104) by (unfold M64; lia).
rewrite (zcanon_id (kk * 104)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End h.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================================== run C1: 0x81f90 -> __asan_memcpy, first = 1 ======================================== *)
Lemma rw8_runC1 : rw8_runC1_stmt B MT.
Proof using MTL LAWS.
unfold rw8_runC1_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos L0 p kk rl
  HJ Hgeo Hpp Hfresh H2 H9 H18 H19 H22 H23 H24 H26 H27 Va0 Va8 Vb8 V110 V118 V138 Vlen Vnent
  HL0 HL0p Hp Hkk Hrl.
destruct Hgeo as (HR16 & HRlo & HRhi & HRhb & Hown & HF & HFapp & HF32).
pose proof rw8_wx as Hwx. pose proof rw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rts_fbounds F HF32 HFapp) as (HF4096 & HFceil & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
assert (Hm1 : (- 0x4001) mod 2 ^ 64 = 18446744073709535231) by reflexivity.
rewrite Hm1 in V118.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
(* the word at R+0x128, which the run reads and drops *)
destruct (c1_word (w_H W) memc (R + 0x128)) as (w & Hw & Vw).
{ intros j Hj. apply Hpres. lia. }
set (E := Ereg regs (c1_extra L0 p kk w)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = w64 (F + 0xe0)) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E26 : ew E 26 = w64 rl) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 RW8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 L0) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 p) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 kk) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 w) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (HE : E = Ereg regs (c1_extra L0 p kk w)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs rw8_Bx c1_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (rw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4d18 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = RW8_SB) by (rewrite E32; apply unsigned_lit_small; unfold RW8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = L0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = p) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = kk) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (rw8_sr c1_ov) regs).
{ apply (rw8_regs_ok E regs (c1_extra L0 p kk w)); [exact HE|]. unfold c1_ov.
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
assert (HFK : facts_ok E c1_facts).
{ split; [| split; [exact I | exact I]].
  cbn [c1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U27, U32, U33, U34, U35.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ]. }
assert (HSR : 0 <= Z.shiftr (pp + 0x4d14) 3 < 2 ^ 64).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (HS : st_ok rsegs E c1_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81f90) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold c1_ss. apply (rw8_entry _ _ regs (c1_extra L0 p kk w) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold c1_rR, c1_rLen, c1_rNent.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0xa0 8 (SOff 27 0x4014) (pp + 0x4014));
          [ rewrite (rw8_den_off E 27 pp 0x4014 E27) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Va0 ].
      * apply (chunk_ok_val rsegs E _ R 0xa8 8 (rw8_shr 27 0x4d14) (Z.shiftr (pp + 0x4d14) 3));
          [ rewrite (rw8_den_shr E 27 pp 0x4d14 E27) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Va8 ].
      * apply (chunk_ok_val rsegs E _ R 0xb8 8 (SOff 27 0x4d14) (pp + 0x4d14));
          [ rewrite (rw8_den_off E 27 pp 0x4d14 E27) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vb8 ].
      * apply (chunk_ok_val rsegs E _ R 0x110 8 (SLit 1) 1);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V110 ].
      * apply (chunk_ok_val rsegs E _ R 0x118 8 (SLit 18446744073709535231) 18446744073709535231);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V118 ].
      * apply (chunk_ok_val rsegs E _ R 0x128 8 (SOff 36 0) w);
          [ rewrite (rw8_den_off E 36 w 0 E36) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vw ].
      * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 19 0x10) (F + 0xf0));
          [ rewrite (rw8_den_off E 19 (F + 0xe0) 0x10 E19) by lia; unfold w64; f_equal; lia
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V138 ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 33 0) L0);
        [ rewrite (rw8_den_off E 33 L0 0 E33) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4d14 4 (SOff 35 0) kk);
        [ rewrite (rw8_den_off E 35 kk 0 E35) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 4) with 32; lia | lia | exact Vnent ].
  - unfold c1_rR, c1_rLen, c1_rNent; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U27; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at, RW8_RA2; change (w64 0x81f90) with (Z_to_bv 64 0x81f90).
aj_run_to_tok rw8_tbl_ok HS HJ Hsh rw8_Bspan 0x51860.
(* the write windows: pp->len and pp->n_ent, both in the fresh first block *)
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
all: apply SRr_ret; unfold rts_post.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 37 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (rw8_regs_kept E Ef 37 (rw8_sr c1_ov) (ss_regs ssf) regs (ms_regs msf) rw8_clobC HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply rw8_same_io_wvb]|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (rw8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U27 in Hb; apply Hn; cbv beta; lia | ]);
    destruct Hr
  |];
  assert (F27 : ew Ef 27 = ew E 27) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rl := fresh "Rl" in let Rn := fresh "Rn" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rl HM];
  apply Forall_cons_iff in HM as [Rn _];
  let Cl := fresh "Cl" in let Cn := fresh "Cn" in
  destruct Rl as (_ & _ & _ & Cl); destruct Rn as (_ & _ & _ & Cn);
  cbn [r_chunks r_base base_val] in Cl, Cn; rewrite F27, U27 in Cl, Cn;
  rewrite Forall_forall in Cl, Cn;
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 1%bv (SLit 532472) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 10%bv (SAlu ALU_ADD (SOff 27 16404) (SMd M_MUL (SOff 35 0) (SLit 104)))
                     HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (c1_den_dst E pp kk E27 E35 ltac:(lia) ltac:(lia) ltac:(lia))|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 11%bv (SOff 19 16) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 19 (F + 0xe0) 16 E19) by lia; unfold w64; f_equal; lia|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 12%bv (SLit 104) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 24%bv (SOff 26 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rw8_den_off E 26 rl 0 E26) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rw8_reg_val E Ef 37 _ _ 26%bv (SLit 18446744073709535231) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite Hm1; reflexivity|];
  split;
  [ apply (val_of_chunk_ok rsegs Ef _ pp 0x4000 8 (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) (L0 + p));
    [ apply Cl; cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite (sv_denot_agree 37 E Ef (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) HA eq_refl); exact (c1_den_add E 33 34 L0 p E33 E34 ltac:(lia) ltac:(lia) ltac:(lia))
    | change (8 * Z.of_N 8) with 64; lia | lia ]
  | apply (val_of_chunk_ok rsegs Ef _ pp 0x4d14 4 (SOff 35 1) (kk + 1));
    [ apply Cn; cbn [In]; repeat (first [left; reflexivity | right])
    | rewrite (sv_denot_agree 37 E Ef (SOff 35 1) HA eq_refl); exact (rw8_den_off E 35 kk 1 E35 ltac:(lia) ltac:(lia))
    | change (8 * Z.of_N 4) with 32; lia | lia ] ]
  end.
Qed.
End c.

Print Assumptions rw8_runC1.
