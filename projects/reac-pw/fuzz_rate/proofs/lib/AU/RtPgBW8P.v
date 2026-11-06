(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 147 of its 171 lines of code are new or changed and 302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Int.v at 3e85ad4cf5dd for reac-pw/fuzz_rate's
   image A: the run is the first run of the piece "write + record" (J 0x81e00 -> __asan_memcpy 0x51860) and its
   statement is lib/A/RtPgW8Kit.v's rw8_runA_stmt (post RtPgSteps.rts_post); the start state adds the frame for
   locals (e's type and size at F + 0xf0 / F + 0xf4, read through s3 = F + 0xe0) and two capacity conditions; the
   eight bytes written are read back as e->size and e->type (the second word carries the engine's sign extension). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8A.v and lib/A/RtPgW8B.v at 8f1d7a0a9084 for
   the same unit's image B (fuzz_rate.asan-ubsan): the run is lib/AU/RtPgBW8Kit.v's run P (J 0x820dc -> pod_write_ent
   0x83cc4, statement rbw8_runP_stmt, post RtPgStepsB.rtsb_post); the prefix rw8_ becomes rbw8_, RtPgMem's rtm_ becomes
   RtPgMemB's rtmb_ and RtPgSteps' rts_ becomes RtPgStepsB's rtsb_; the start state is image B's (the shadow address of
   pp->len is the frame cell R+0x170, no byte is written, the capacity guard reads len + 112). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): run P of the walk piece "write + record" of
   LLVMFuzzerTestOneInput (0x8076c), J 0x820dc -> pod_write_ent 0x83cc4 (pod.h:428-429: the capacity guard and the
   arguments of the call pod_write_ent(pp, e62)). Proves no function (kind: segment lemma).

   THE RUN. One token-engine run (lib/Reusable/YCbn.v) from 0x820dc to the entry of pod_write_ent; the engine steps
   the `jal`, so ra = 0x8210c.
     0x820dc .. 0x820e8  `ld a0,0x170(s1); lbu a0,0(a0); beqz a0; j 0x832cc`: the check of the 8-byte load of
                         pp->len. The cell R+0x170 holds the shadow address of pp + 0x4000 in the form the code
                         computes it (RtPgBW8Kit.rbw8_sh 33 0x4000); the shadow entry (33, 0x4000, 0x4008) of
                         RtPgBW8Kit.rbw8_shent_blk covers the eight bytes, so the shadow byte reads 0 and the run
                         leaves no shadow obligation and no fresh atom.
     0x820ec             `mv s9,t1`
     0x820f0 .. 0x820fc  `ld a0,0(s2); addi a0,a0,112; lui a1,4; bltu a1,a0,0x82484`: not taken, since the atom of
                         len lies in [0, 5440] and so len + 112 < 0x4000.
     0x82100 .. 0x82108  `ld a0,0x168(s1); mv a1,s6; jal 0x83cc4`
   Atoms: 9 = R (s1), 32 = the shadow offset K, 33 = pp, 34 = len. Every start region is read only (the run writes
   no byte), so every byte is kept. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec RtPgMemB RtPgStepsB RtPgBW8Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the start state at J 0x820dc ======================================== *)
(* atoms 32 = the shadow offset, 33 = pp, 34 = len *)
Definition rbw8p_extra (pp len : Z) : list word := [w64 RBW8_SB; w64 pp; w64 len].
(* sp = s1 = R, s2 = &pp->len, s4 = the shadow offset *)
Definition rbw8p_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((18%bv : bv 5), SOff 33 0x4000); ((20%bv : bv 5), rbw8_Bx)].
(* the real frame's cells, read only: pp (R+0x168) and the shadow address of &pp->len (R+0x170) *)
Definition rbw8p_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x168 0x178 0 0
   [YP09.mkChunk 0x168 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x170 (CVal 8 (rbw8_sh 33 0x4000))].
(* pp->len, read only *)
Definition rbw8p_rLen : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4000 0x4008 0 0 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0))].
Definition rbw8p_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (32%nat, mkAF RBW8_SB RBW8_SB 0);
           (33%nat, mkAF 4096 140737479966720 4);
           (34%nat, mkAF 0 5440 0)] [] [].
Definition rbw8p_ss : sstate := mkSS 0x820dc (rbw8_sr rbw8p_ov) [rbw8p_rR; rbw8p_rLen] None rbw8p_facts.
Definition rbw8p_SH : list shent := [mkSHE 33 0x4000 0x4008].

(* ======================================== run P ======================================== *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma rbw8_runP : rbw8_runP_stmt B MT.
Proof using MTL LAWS.
unfold rbw8_runP_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len
  HJ HG Hpp H2 H9 H18 H20 H22 V168 V170 Vlen Hlen.
pose proof rbw8_wx as Hwx. pose proof rbw8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rbw8_geo in HG. destruct HG as (HR16 & HRlo & HRhi & HRhb & Hown & HF & HFapp & HF32).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp.
destruct (rtsb_fbounds F HF32 HFapp) as (HF0 & HFc & _).
set (E := Ereg regs (rbw8p_extra pp len)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = w64 (F + 0x210)) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 RBW8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 len) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HE : E = Ereg regs (rbw8p_extra pp len)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs rbw8_Bx rbw8p_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (rbw8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = RBW8_SB) by (rewrite E32; apply unsigned_lit_small; unfold RBW8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (rbw8_sr rbw8p_ov) regs).
{ apply (rbw8_regs_ok E regs (rbw8p_extra pp len)); [exact HE|]. unfold rbw8p_ov.
  apply Forall_cons; [split; [apply rbw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rbw8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply rbw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (rbw8_den_off E 33 pp 0x4000 E33) by lia. rewrite H18. reflexivity. }
  apply Forall_cons; [split; [apply rbw8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold rbw8_Bx. rewrite (rbw8_den_off E 32 RBW8_SB 0 E32) by (unfold RBW8_SB; lia).
    rewrite Z.add_0_r, H20. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E rbw8p_facts).
{ split; [| split; [exact I | exact I]].
  cbn [rbw8p_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) ]. }
(* the shadow address the cell R+0x170 holds is a 64-bit value *)
assert (Hsa : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (pp + 0x4000) / 8 <= pp + 0x4000)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  lia. }
assert (HS : st_ok rsegs E rbw8p_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x820dc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold rbw8p_ss. apply (rbw8_entry _ _ regs (rbw8p_extra pp len) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold rbw8p_rR, rbw8p_rLen.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 33 0) pp);
          [ rewrite (rbw8_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V168 ].
      * apply (chunk_ok_val rsegs E _ R 0x170 8 (rbw8_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (rbw8_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; exact Hsa | lia | exact V170 ].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 33 pp); [exact U33 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) len);
        [ rewrite (rbw8_den_off E 34 len 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
  - unfold rbw8p_rR, rbw8p_rLen; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 RBW8_J) with (Z_to_bv 64 0x820dc).
aj_run_to_tok rbw8_tbl_ok HS HJ Hsh rbw8_Bspan 0x83cc4.
(* no write window: every start region is read only *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
(* the state at the entry of pod_write_ent *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 35 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
  cbn [ms_regs restrict] in HRf;
  unfold rtsb_post; cbv beta; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (rbw8_regs_kept E Ef 35 (rbw8_sr rbw8p_ov) (ss_regs ssf) regs (ms_regs msf) rbw8_clobP HR0 HRf HA
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
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33 in Hb; lia | ]);
    destruct Hr
  |];
  split; [rewrite (rbw8_reg_val E Ef 35 _ _ 1%bv (SLit 532748) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (rbw8_reg_val E Ef 35 _ _ 10%bv (SOff 33 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rbw8_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (rbw8_reg_val E Ef 35 _ _ 11%bv (SOff 22 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (rbw8_den_off E 22 (F + 0x210) 0 E22) by lia; rewrite Z.add_0_r; reflexivity|];
  rewrite (rbw8_reg_val E Ef 35 _ _ 25%bv (SOff 6 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
  first [ exact (eq_sym (HR0 (6%bv : bv 5)))
        | (rewrite (HR0 (6%bv : bv 5)); f_equal; vm_compute; reflexivity) ]
  end.
Qed.
End p.

Print Assumptions rbw8_runP.
