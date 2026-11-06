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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8P.v, with its module paths, module names and addresses changed; 71 of its 173 lines of code are new or changed and 69 lines of the source are left out. *)
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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgBW8P.v at 6c65f5a5cf5c for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the prefix
   rbw8_ becomes w8_, RtPgMemB's rtmb_ becomes RPgMem's rm_ and RtPgStepsB's rtsb_ becomes RPgSteps' rl_; the run is
   role B's (J 0x818d8 -> pod_write_ent 0x82bac): the check's branch is one `bnez` to the error path 0x827f4, the
   shadow address of pp->len is the cell R+0x148, pp is in a5 and &pp->len in s6, &e62 is read from the cell R+0x158
   (a fourth atom), the two moves s8 := a3 and s2 := t1 and `li s4,1` are new and named in the post. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): run P of the walk piece "write + record" of
   LLVMFuzzerTestOneInput (0x80020), J 0x818d8 -> pod_write_ent 0x82bac (pod.h:428-429: the capacity guard and the
   arguments of the call pod_write_ent(pp, e62)). Proves no function (kind: segment lemma).

   THE RUN. One token-engine run (lib/Reusable/YCbn.v) from 0x818d8 to the entry of pod_write_ent; the engine steps
   the `jal`, so ra = 0x8190c.
     0x818d8 .. 0x818e0  `ld a0,0x148(s1); lbu a0,0(a0); bnez a0,0x827f4`: the instrumented check of the 8-byte load
                         of pp->len. The cell R+0x148 holds the shadow address of pp + 0x4000 in the form the code
                         computes it (RPgW8Kit.w8_sh 33 0x4000); the shadow entry (33, 0x4000, 0x4008) of
                         RPgW8Kit.w8_shent_blk covers the eight bytes, so the shadow byte reads 0, the error path is
                         not reached, and the run leaves no shadow obligation.
     0x818e4 .. 0x818e8  `mv s8,a3; mv s2,t1`
     0x818ec .. 0x818fc  `ld a0,0(s6); addi a0,a0,112; lui a1,4; li s4,1; bltu a1,a0,0x81c90`: not taken, since the
                         atom of len lies in [0, 5440] and so len + 112 < 0x4000.
     0x81900 .. 0x81908  `mv a0,a5; ld a1,0x158(s1); jal 0x82bac`
   Atoms: 9 = R (s1), 32 = the shadow offset K, 33 = pp, 34 = len, 35 = &e62 = F + 0x210. Every start region is read
   only (the run writes no byte), so every byte is kept. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 PweSpec RPgMem RPgSteps RPgStepsU RPgW8Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the start state at J 0x818d8 ======================================== *)
(* atoms 32 = the shadow offset, 33 = pp, 34 = len, 35 = &e62 *)
Definition w8p_extra (pp len FE : Z) : list word := [w64 W8_SB; w64 pp; w64 len; w64 FE].
(* sp = s1 = R, s6 = &pp->len, a5 = pp *)
Definition w8p_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((22%bv : bv 5), SOff 33 0x4000); ((15%bv : bv 5), SOff 33 0)].
(* the real frame's cells, read only: the shadow address of &pp->len (R+0x148) and &e62 (R+0x158) *)
Definition w8p_rR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x148 0x160 0 0
   [YP09.mkChunk 0x148 (CVal 8 (w8_sh 33 0x4000));
    YP09.mkChunk 0x158 (CVal 8 (SOff 35 0))].
(* pp->len, read only *)
Definition w8p_rLen : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4000 0x4008 0 0 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0))].
Definition w8p_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 4);
           (32%nat, mkAF W8_SB W8_SB 0);
           (33%nat, mkAF 4096 140737479966720 4);
           (34%nat, mkAF 0 5440 0)] [] [].
Definition w8p_ss : sstate := mkSS 0x818d8 (w8_sr w8p_ov) [w8p_rR; w8p_rLen] None w8p_facts.
Definition w8p_SH : list shent := [mkSHE 33 0x4000 0x4008].

(* ======================================== run P ======================================== *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w8_runP : w8_runP_stmt B MT.
Proof using MTL LAWS.
unfold w8_runP_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp F pos len
  HJ HG Hpp H2 H9 H15 H22 V148 V158 Vlen Hlen.
pose proof w8_wx as Hwx. pose proof w8_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hcl.
unfold w8_geo in HG. destruct HG as (HR16 & HRlo & HRhi & HRhb & Hown & HF & HFapp & HF32).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp.
destruct (rl_fbounds F HF32 HFapp) as (HF0 & HFc & _).
set (E := Ereg regs (w8p_extra pp len (F + 0x210))).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 W8_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 len) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (F + 0x210)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (w8p_extra pp len (F + 0x210))) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w8_Bx w8p_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor].
  apply (w8_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
  try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W8_SB) by (rewrite E32; apply unsigned_lit_small; unfold W8_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w8_sr w8p_ov) regs).
{ apply (w8_regs_ok E regs (w8p_extra pp len (F + 0x210))); [exact HE|]. unfold w8p_ov.
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 33 pp 0x4000 E33) by lia. rewrite H22. reflexivity. }
  apply Forall_cons; [split; [apply w8_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (w8_den_off E 33 pp 0 E33) by lia. rewrite Z.add_0_r, H15. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E w8p_facts).
{ split; [| split; [exact I | exact I]].
  cbn [w8p_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) ]. }
(* the shadow address the cell R+0x148 holds is a 64-bit value *)
assert (Hsa : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (pp + 0x4000) / 8 <= pp + 0x4000)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  lia. }
assert (HS : st_ok rsegs E w8p_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x818d8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w8p_ss. apply (w8_entry _ _ regs (w8p_extra pp len (F + 0x210)) E); [exact HE| | | | |].
  - exact HR0.
  - vm_compute. reflexivity.
  - unfold w8p_rR, w8p_rLen.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x148 8 (w8_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (w8_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; exact Hsa | lia | exact V148 ].
      * apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 35 0) (F + 0x210));
          [ rewrite (w8_den_off E 35 (F + 0x210) 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V158 ].
    + apply (rm_ro_region rsegs E (w_H W) memc 33 pp); [exact U33 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) len);
        [ rewrite (w8_den_off E 34 len 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
  - unfold w8p_rR, w8p_rLen; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U33; repeat split; try exact I; lia.
  - exact HFK. }
unfold cfg_at; change (w64 W8_J) with (Z_to_bv 64 0x818d8).
aj_run_to_tok w8_tbl_ok HS HJ Hsh w8_Bspan 0x82bac.
(* no write window: every start region is read only *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
(* the state at the entry of pod_write_ent *)
all: apply SRr_ret.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  assert (HA : env_agree 36 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2 | apply env_agree_ewset]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
  cbn [ms_regs restrict] in HRf;
  unfold rl_wpost; cbv beta; exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    exact (w8_regs_kept E Ef 36 (w8_sr w8p_ov) (ss_regs ssf) regs (ms_regs msf) w8_clobP HR0 HRf HA
             ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w8_same_io_wvb]|];
  split; [exact (mle_start MT Sc MTL)|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w8_kept_run E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33 in Hb; lia | ]);
    destruct Hr
  |];
  split; [rewrite (w8_reg_val E Ef 36 _ _ 1%bv (SLit 530700) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          reflexivity|];
  split; [rewrite (w8_reg_val E Ef 36 _ _ 10%bv (SOff 33 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (w8_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (w8_reg_val E Ef 36 _ _ 11%bv (SOff 35 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          rewrite (w8_den_off E 35 (F + 0x210) 0 E35) by lia; rewrite Z.add_0_r; reflexivity|];
  split; [rewrite (w8_reg_val E Ef 36 _ _ 24%bv (SOff 13 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          first [ exact (eq_sym (HR0 (13%bv : bv 5)))
                | (rewrite (HR0 (13%bv : bv 5)); f_equal; vm_compute; reflexivity) ]|];
  split; [rewrite (w8_reg_val E Ef 36 _ _ 18%bv (SOff 6 0) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
          first [ exact (eq_sym (HR0 (6%bv : bv 5)))
                | (rewrite (HR0 (6%bv : bv 5)); f_equal; vm_compute; reflexivity) ]|];
  rewrite (w8_reg_val E Ef 36 _ _ 20%bv (SLit 1) HRf HA ltac:(vm_compute; reflexivity) eq_refl);
  reflexivity
  end.
Qed.
End p.
