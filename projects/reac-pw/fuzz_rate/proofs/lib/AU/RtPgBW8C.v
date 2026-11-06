(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 269 of its 297 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd (w5i_head), with the post
   of proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Close.v at a1de917d2c21; rate's run C1 of the walk piece W8 (0x81f90 ->
   __asan_memcpy 0x51860) replaces role's Int-7 pod: the start state, the record copy's arguments and the n_ent
   update are new, the post is RtPgSteps.rts_post, the engine helpers are RtPgW8Kit's rw8_ ones. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the two token runs w5i_head / w5i_tail become the runs B and C0 of the walk piece W8 (lib/A/RtPgW8Kit.v);
   the pcs, registers, start regions, atoms and facts are rate's; the post is RtPgSteps.rts_post (the statements
   rw8_runB_stmt and rw8_runC0_stmt) instead of a local one; the pad count of pod_pad is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8C.v (run C1) and
   proofs/reac-pw/fuzz_rate/lib/A/RtPgW8B.v (run C0) at 8f1d7a0a9084 for the same unit's image B
   (fuzz_rate.asan-ubsan): both runs start at 0x8210c after the call of pod_write_ent; run C1's code has image B's
   three UBSan trap branches and two n_ent checks, its start state names pp, n_ent and the trap bound by extra atoms
   (no register holds pp); run C0 is three instructions on the plain engine; the post is RtPgStepsB.rtsb_post and
   the helpers are RtPgBW8Kit's rbw8_ ones; image A's run B and its pad lemmas are dropped. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the runs C1 and C0 of the walk piece
   "write + record" of LLVMFuzzerTestOneInput (0x8076c), from 0x8210c (after pod_write_ent) on the two values of
   `first` (R+0x160) (pod.h:432 `pp->ent[pp->n_ent++] = e`). Proves no function (kind: segment lemma).

   RUN C1, 0x8210c -> __asan_memcpy 0x518b8, `first` = 1:
     0x8210c-0x82114  a0 := `first` (R+0x160), a1 := k (R+0x178, overwritten below), `beqz a0` not taken
     0x82118-0x82124  the check of the 4-byte access at pp+0x4d14 (pp->n_ent): R+0xf8 holds (pp+0x4d14)>>3, a1 :=
                      its shadow address; the `bnez` to the slow block 0x82228 is decided by the full zero granule
                      rule (0x4d14 rounds down to 0x4d10; the shadow entry reaches 0x4d18)
     0x82128-0x82134  a0 := n_ent (lw from R+0x138 = pp+0x4d14), a2 := n_ent + 1 (addiw), the UBSan trap
                      `blt a2,a0` -> 0x83098 not taken (the same atom at offsets 1 and 0, both below 2^63)
     0x82138-0x8213c  the store check, the same shadow byte, `bnez` to 0x8223c not taken
     0x82140-0x82144  n_ent := n_ent + 1
     0x82148-0x8215c  the traps `bgeu a0,33` (n_ent <= 31) and `bltu ~(pp+0x4014), 104 n_ent` (the cell R+0xf0,
                      at least 2^63 since pp + 0x4014 < 2^63, against 104 n_ent <= 3224): neither is taken
     0x82160-0x82170  a0 := pp+0x4014 + 104 n_ent (R+0xe8 = &pp->ent[0]), a2 := 104, a1 := s6 (= &e62 = F+0x210),
                      jal __asan_memcpy (ra = 0x82174)
     Atoms 32 = K, 33 = pp, 34 = kk (both the n_ent word and the cell R+0x178 hold it), 35 = the cell R+0xf0, read
     as 2^64 - 1 - (pp + 0x4014). The engine loads two shadow bytes (two fresh atoms) and reaches the stop pc with
     no shadow obligation.
   RUN C0, 0x8210c -> 0x82178, `first` = 0: a0 := R+0x160 (= 0), a1 := R+0x178 (k), `beqz a0` taken. Atom 32 = k;
     no check, so the plain engine. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMemB RtPgStepsB RtPgBW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ---- run C1, the start state at 0x8210c: atoms 32 = K, 33 = pp, 34 = kk, 35 = the cell R+0xf0 ---- *)
Definition c1_ov : list (bv 5 * sv) := [((2%bv : bv 5), SOff 9 0); ((20%bv : bv 5), rbw8_Bx)].
Definition c1_rR : YP09.region :=            (* the real frame's cells, read only; `first` = 1 *)
  YP09.mkRegion (Some 9%nat) 0xe8 0x180 0 0
   [YP09.mkChunk 0xe8 (CVal 8 (SOff 33 0x4014));
    YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
    YP09.mkChunk 0xf8 (CVal 8 (rbw8_shr 33 0x4d14));
    YP09.mkChunk 0x138 (CVal 8 (SOff 33 0x4d14));
    YP09.mkChunk 0x160 (CVal 8 (SLit 1));
    YP09.mkChunk 0x178 (CVal 8 (SOff 34 0))].
Definition c1_rNent : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4d14 0x4d18 0x4d14 0x4d18 [YP09.mkChunk 0x4d14 (CVal 4 (SOff 34 0))].
Definition c1_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (32%nat, mkAF RBW8_SB RBW8_SB 0);
           (33%nat, mkAF 4096 140737479966720 4);
           (34%nat, mkAF 0 31 0);
           (35%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] [].
Definition c1_ss : sstate := mkSS 0x8210c (rbw8_sr c1_ov) [c1_rR; c1_rNent] None c1_facts.
(* the shadow entry over pp->len .. pp->n_ent: the n_ent check needs the whole granule [0x4d10, 0x4d18) *)
Definition c1_SH : list shent := [mkSHE 33 0x4000 0x4d18].
Definition c1_extra (pp kk : Z) : list word :=
  [w64 RBW8_SB; w64 pp; w64 kk; w64 (18446744073709551615 - (pp + 0x4014))].

(* ---- run C0, the start state at 0x8210c: atom 32 = k ---- *)
Definition c0_rR : YP09.region :=            (* the real frame's cells, read only; `first` = 0 *)
  YP09.mkRegion (Some 9%nat) 0x160 0x180 0 0
   [YP09.mkChunk 0x160 (CVal 8 (SLit 0)); YP09.mkChunk 0x178 (CVal 8 (SOff 32 0))].
Definition c0_facts : facts := mkFacts [(32%nat, mkAF 0 31 0)] [] [].
Definition c0_ss : sstate := mkSS 0x8210c sr_atoms [c0_rR] None c0_facts.
Definition c0_extra (kk : Z) : list word := [w64 kk].

(* ======================================== helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
(* the 64-bit complement of a value below 2^63, as the cell R+0xf0 holds it *)
Lemma c1_lnot : forall x, 0 <= x < 2 ^ 63 -> Z.lnot x mod 2 ^ 64 = 18446744073709551615 - x.
Proof.
intros x Hx. unfold Z.lnot. change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808 in Hx.
symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
Qed.
(* the record copy's destination as the engine builds it: pp + 0x4014 + 104 * kk *)
Lemma c1_den_dst : forall E pp kk, ew E 33 = Z_to_bv 64 pp -> ew E 34 = Z_to_bv 64 kk ->
0 <= pp -> pp + 0x4014 + 104 * 31 < 2 ^ 64 -> 0 <= kk <= 31 ->
sv_denot E (SAlu ALU_ADD (SOff 33 16404) (SMd M_MUL (SOff 34 0) (SLit 104))) = w64 (pp + 0x4014 + 104 * kk).
Proof.
intros E pp kk H33 H34 Hp Hb Hk. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom_off E 33 pp 16404 H33) by lia. rewrite (U_atom E 34 kk H34) by lia. rewrite U_SLit.
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

(* ======================================== run C1: 0x8210c -> __asan_memcpy, first = 1 ======================================== *)
Lemma rbw8_runC1 : rbw8_runC1_stmt B MT.
Proof using MTL LAWS.
unfold rbw8_runC1_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos kk
  HJ Hgeo Hpp Hfresh H2 H9 H20 H22 Ve8 Vf0 Vf8 V138 V160 V178 Vnent Hkk.
destruct Hgeo as (HR16 & HRlo & HRhi & HRhb & Hown & HF & HFapp & HF32).
pose proof rbw8_wx as Hwx. pose proof rbw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rtsb_fbounds F HF32 HFapp) as (HF4096 & HFceil & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
rewrite (c1_lnot (pp + 0x4014)) in Vf0 by (change (2 ^ 63) with 9223372036854775808; lia).
set (E := Ereg regs (c1_extra pp kk)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = w64 (F + 0x210)) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 RBW8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 kk) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (18446744073709551615 - (pp + 0x4014))) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (c1_extra pp kk)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs rbw8_Bx c1_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (rbw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4d18 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = RBW8_SB) by (rewrite E32; apply unsigned_lit_small; unfold RBW8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = kk) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = 18446744073709551615 - (pp + 0x4014))
  by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (rbw8_sr c1_ov) regs).
{ apply (rbw8_regs_ok E regs (c1_extra pp kk)); [exact HE|]. unfold c1_ov.
  apply Forall_cons; [split; [apply rbw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rbw8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply rbw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold rbw8_Bx. rewrite (rbw8_den_off E 32 RBW8_SB 0 E32) by (unfold RBW8_SB; lia).
    rewrite Z.add_0_r, H20. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E c1_facts).
{ split; [| split; [exact I | exact I]].
  cbn [c1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34, U35.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ]. }
assert (HSR : 0 <= Z.shiftr (pp + 0x4d14) 3 < 2 ^ 64).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (HS : st_ok rsegs E c1_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8210c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold c1_ss. apply (rbw8_entry _ _ regs (c1_extra pp kk) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold c1_rR, c1_rNent.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0xe8 8 (SOff 33 0x4014) (pp + 0x4014));
          [ rewrite (rbw8_den_off E 33 pp 0x4014 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Ve8 ].
      * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 35 0) (18446744073709551615 - (pp + 0x4014)));
          [ rewrite (rbw8_den_off E 35 (18446744073709551615 - (pp + 0x4014)) 0 E35) by lia;
            rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf0 ].
      * apply (chunk_ok_val rsegs E _ R 0xf8 8 (rbw8_shr 33 0x4d14) (Z.shiftr (pp + 0x4d14) 3));
          [ rewrite (rbw8_den_shr E 33 pp 0x4d14 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf8 ].
      * apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 33 0x4d14) (pp + 0x4d14));
          [ rewrite (rbw8_den_off E 33 pp 0x4d14 E33) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V138 ].
      * apply (chunk_ok_val rsegs E _ R 0x160 8 (SLit 1) 1);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V160 ].
      * apply (chunk_ok_val rsegs E _ R 0x178 8 (SOff 34 0) kk);
          [ rewrite (rbw8_den_off E 34 kk 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V178 ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4d14 4 (SOff 34 0) kk);
        [ rewrite (rbw8_den_off E 34 kk 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 4) with 32; lia | lia | exact Vnent ].
  - unfold c1_rR, c1_rNent; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 RBW8_RA1) with (Z_to_bv 64 0x8210c).
aj_run_to_tok rbw8_tbl_ok HS HJ Hsh rbw8_Bspan 0x518b8.
(* the write window: pp->n_ent, in the fresh first block *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat pp);
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the state at the callee's entry *)
all: apply SRr_ret; unfold rtsb_post.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 36 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & (_ & HM & _) & _);
  cbn [ms_regs restrict] in HRf;
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (rbw8_regs_kept E Ef 36 (rbw8_sr c1_ov) (ss_regs ssf) regs (ms_regs msf) rbw8_clobC HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply rbw8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (rbw8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33 in Hb; apply Hn; cbv beta; lia | ]);
    destruct Hr
  |];
  assert (F33 : ew Ef 33 = ew E 33) by (apply (proj1 HA); lia);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rn := fresh "Rn" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rn _];
  let Cn := fresh "Cn" in
  destruct Rn as (_ & _ & _ & Cn);
  cbn [r_chunks r_base base_val] in Cn; rewrite F33, U33 in Cn;
  rewrite Forall_forall in Cn;
  split; [rewrite (rbw8_reg_val E Ef 36 _ _ 1%bv (SLit 532852) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rbw8_reg_val E Ef 36 _ _ 10%bv (SAlu ALU_ADD (SOff 33 16404) (SMd M_MUL (SOff 34 0) (SLit 104)))
                     HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          exact (c1_den_dst E pp kk E33 E34 ltac:(lia) ltac:(lia) ltac:(lia))|];
  split; [rewrite (rbw8_reg_val E Ef 36 _ _ 11%bv (SOff 22 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rbw8_den_off E 22 (F + 0x210) 0 E22) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rbw8_reg_val E Ef 36 _ _ 12%bv (SLit 104) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  apply (val_of_chunk_ok rsegs Ef _ pp 0x4d14 4 (SOff 34 1) (kk + 1));
  [ apply Cn; cbn [In]; repeat (first [left; reflexivity | right])
  | rewrite (sv_denot_agree 36 E Ef (SOff 34 1) HA eq_refl); exact (rbw8_den_off E 34 kk 1 E34 ltac:(lia) ltac:(lia))
  | change (8 * Z.of_N 4) with 32; lia | lia ]
  end.
Qed.

(* ======================================== run C0: 0x8210c -> 0x82178, `first` clear ======================================== *)
Lemma rbw8_runC0 : rbw8_runC0_stmt B MT.
Proof using MTL LAWS.
unfold rbw8_runC0_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pos kk HJ Hgeo H2 H9 V160 V178 Hkk.
pose proof rbw8_wx as Hwx. pose proof rbw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgeo as (HR16 & HRlo & HRhi & HRhb & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
set (E := Ereg regs (c0_extra kk)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 kk) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (HE : E = Ereg regs (c0_extra kk)) by reflexivity. clearbody E.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = kk) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (c0_extra kk)) E) by (rewrite HE; apply env_agree_refl).
assert (HS : st_ok rsegs E c0_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8210c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold c0_ss. apply (rbw8_entry _ _ regs (c0_extra kk) E); [exact HE| | | | |].
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold c0_rR. apply Forall_cons; [|apply Forall_nil].
    apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs E _ R 0x160 8 (SLit 0) 0);
        [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V160 ].
    + apply (chunk_ok_val rsegs E _ R 0x178 8 (SOff 32 0) kk);
        [ exact (rtsb_den_atom E 32 kk E32 ltac:(lia)) | change (8 * Z.of_N 8) with 64; lia | lia | exact V178 ].
  - cbn. tauto.
  - split; [| split; [exact I | exact I]].
    cbn [c0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) ]. }
unfold cfg_at; change (w64 RBW8_RA1) with (Z_to_bv 64 0x8210c).
aj_run_to rbw8_tbl_ok HS HJ 0x82178.
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ =>
  (* the one start region is read only *)
  change (ss_mem c0_ss) with [c0_rR];
  apply awr_ok_cons_ro; [unfold c0_rR; cbn [YP09.r_wlo YP09.r_whi]; lia|]; apply awr_ok_nil
| |- _ =>
  apply SRr_ret; red;
  exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (RtPgStepsB.regs_kept_of_st_ok rsegs _ _ ms regs (c0_extra kk) (w_H W) _ HS HAE);
          vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply rbw8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ (* the run writes nothing *)
    let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (rbw8_kept_run E _ (w_H W) memc (ms_mem ms) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    change (ss_mem c0_ss) with [c0_rR] in Hr;
    destruct Hr as [<- | []]; unfold c0_rR in Hb; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia
  | (* a1 = k *)
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms (11%bv : bv 5) HS);
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e end;
    exact (rtsb_den_atom E 32 kk E32 ltac:(lia)) ]
end.
Qed.
End c.

Print Assumptions rbw8_runC1.
Print Assumptions rbw8_runC0.
