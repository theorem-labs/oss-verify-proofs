(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc; L_ANS_cs as tl_L4_cs and
   ch_L_cs) for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02: the tail and the two checks, proved
   against lib/A/RPgSeg.v's rs_piece_W11b_tail_stmt and rs_piece_W11b_checks_stmt on lib/A/Img0.v rsegs. *)
(* reac-pw/fuzz_role, image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes). Proves no function
   (kind: segment lemma): the pieces W11b-tail and W11b-checks of LLVMFuzzerTestOneInput's segment M02, whose
   statements are lib/A/RPgSeg.v's (rs_piece_W11b_tail_stmt, rs_piece_W11b_checks_stmt); nothing here
   restates a cut.

   THE TAIL (rs_cut_T at T 0x82408 -> rs_cut_C4 at C4 0x82478; the code is listed in lib/A/RPgM02Base.v):
   - tl_head: one run 0x82408 .. 0x82428 from an entry state with two regions, the real frame's flags cell R+0x30
     (env slot 33 = the flags byte fl) and the role cell (the literal value), and s8 overridden by the literal rc.
     The engine decides `bne s8,a1` (0x82418) itself on each of the four cases of the parse's answer
     (RPgScanF.rk_parse_cases: (-1, None), (0, None), (1, MASTER), (1, SLAVE)): rc = 1 reads req from the role cell
     (0x8241c), else req = cur xor 1 (0x82424). cur = bit 1 of fl and 1 - cur are the values of the two ALU chains
     the run leaves in s5 / s6, checked over the 256 byte values (tl_bits).
   - tl_s1 .. tl_s6: the six calls cfg_changes 0x82ec8, apply_state 0x82ed4, check_answer 0x82c30, refuse_code
     0x82e6c (a0 = 0, then a0 = 1) and check_code 0x82c80. Each stage is a fresh entry state with no region (the
     code between two calls only moves registers), a run to the callee's entry, the callee's theorem (RPgCfgChanges,
     RPgCfgApply, RPgCheckStr, RPgRefuse) through SRr_bind with RPgM02Base.m2_pre_call for its rl_pre, and
     m2_core_call for rs_core at the return pc. apply_state's result is the string check_answer is called with;
     refuse_code's results 0x21500 / 0x21520 are the strings check_code is called with; RPgM02Base.m2_strs gives
     every string, the table and its shadow at the call's memory.
   - What C4 reads (hi_L4: s2 = pod, s0 = S, s1 = R, s3, s9 = F, s11 = pp and R+0x8 = F) is carried from the T cut:
     the six registers are callee-saved and not written by the tail (tl_L4), and no byte outside the callees' stack
     [R - T_SEG_STK, R) is written (tl_cut_C4).
   THE CHECKS (rs_cut_ABS at 0x82380, rs_cut_MAL at 0x823fc -> rs_cut_T at 0x82408):
   - ch_mal: one run (the role cell as the one region: `lw a1,0(s6)` reads 0x5a, the parse having written no role)
     to check_malformed (a0 = s8 = -1), whose return address is T itself.
   - ch_abs: one run to check_absent (a0 = s8 = 0, a1 = 0x5a), then a run from its return 0x8238c with the real
     frame's cells R+0x28 / R+0x80 as the region (`ld s9` / `ld s11`) to T.
   - ch_cut_T restates RPgSeg's rs_cut_T at the state reached from the check cut's facts.
   Every callee returns at the float state it was called at, so every state of the half is at the cut's own float
   state fx2; the walk lemmas are stated at the configurations' float state (Section w) and used at fx2.

   SECTION HYPOTHESES of the two theorems (Section m): MTL : ameter_laws MT and LAWS : AR_laws rsegs B (both);
   for the tail also ASTRCMP : the strcmp wrapper's contract astrcmp_realizes rsegs B 0x41ad0 at every float state
   (check_answer and check_code call the wrapper at the cut's float state), and HGOT / HSC (as_got_shadow B = 0x9a830,
   as_shadow_cell B = 0xa33f8, which lib/A/RPgRefuse.v's rl_refuse_code_A takes). Nothing else is assumed. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSiteA RPgSeg RPgMem RPgScanF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgCheck RPgCheckStr RPgRefuse RPgCfgChanges RPgCfgApply.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= registers ======================================= *)
(* the registers the C4 cut reads (RPgImgA's hi_L4): all callee-saved, none written by the tail or the checks *)
Definition tl_L4 : list (bv 5) := [8; 9; 18; 19; 25; 27]%bv.
Lemma tl_L4_cs : forall r, In r tl_L4 -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [tl_L4 In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Lemma tl_r234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Proof.
intros r1 r2 H r Hr; destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma tl_sp_of_cs : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. unfold spZ. rewrite (H 2%bv); [reflexivity | cbv [In]; left; reflexivity]. Qed.
Lemma tl_sp_pres : forall r1 r2, aregs_preserved r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. unfold spZ. f_equal. exact (H 2 ltac:(unfold acallee_saved; lia)). Qed.
Lemma tl_ereg : forall regs extra (n : nat), (n < 32)%nat -> ew (Ereg regs extra) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

(* the enter step of a run that starts at a cut with no memory access before its next call: the registers as
   atoms, no region, no fact *)
Ltac tl_enter :=
lazymatch goal with |- SRr rsegs ?W (cfg_at rsegs ?pc ?regs ?mem ?md) _ =>
let HS := fresh "HS" in
pose proof (m2_entry pc [] [] (mkFacts [] [] []) W regs [] mem (Forall_nil _) eq_refl (Forall_nil _) I
  ltac:(repeat split)) as HS;
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs []) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W) mem)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem a)
by (intros; reflexivity);
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.

(* ======================================= the flags byte's bit 1 =======================================
   0x82408 ld a0,0x30(s1); slli a0,a0,0x3e; srli s5,a0,0x3f: s5 = bit 1 of the flags byte fl (cur); 0x82424
   xori s6,s5,1: s6 = 1 - cur. Checked over the 256 values of the byte. *)
Lemma tl_bits_all : forallb (fun n => andb
  (bv_eqb (alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 62)) (Z_to_bv 64 63))
    (Z_to_bv 64 (Z.b2z (Z.testbit (Z.of_nat n) 1))))
  (bv_eqb (alu64 ALU_XOR (alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 62)) (Z_to_bv 64 63))
    (Z_to_bv 64 1)) (Z_to_bv 64 (1 - Z.b2z (Z.testbit (Z.of_nat n) 1))))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tl_bits : forall fl, 0 <= fl < 256 ->
alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 fl) (Z_to_bv 64 62)) (Z_to_bv 64 63) = Z_to_bv 64 (Z.b2z (Z.testbit fl 1)) /\
alu64 ALU_XOR (alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 fl) (Z_to_bv 64 62)) (Z_to_bv 64 63)) (Z_to_bv 64 1) =
  Z_to_bv 64 (1 - Z.b2z (Z.testbit fl 1)).
Proof.
intros fl Hfl. pose proof tl_bits_all as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat fl) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. split; assumption.
Qed.
Lemma tl_cur_range : forall fl, 0 <= Z.b2z (Z.testbit fl 1) < 2 ^ 64 /\ 0 <= 1 - Z.b2z (Z.testbit fl 1) < 2 ^ 64.
Proof. intros fl. destruct (Z.testbit fl 1); cbn; lia. Qed.

(* the registers ABS / MAL keep for the T cut (RPgSeg's rs_L_chk and s8) *)
Definition ch_L : list (bv 5) := [8; 9; 18; 19; 22; 23; 24]%bv.
Lemma ch_L_cs : forall r, In r ch_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [ch_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
(* a register of a kept list, read through the list *)
Ltac cs_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [tl_L4 ch_L In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
Lemma w64_mod : forall x, w64 (x mod 2 ^ 64) = w64 x.
Proof.
intros x. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ======================================= the tail's six calls =======================================
   Stated at the float state fx of the configurations (the cut's own fx2 when used): every callee returns at the
   float state it was called at. regs0 / W0 / mem0 are the registers, world and memory of the T cut: what C4 reads
   from them is carried as "the six registers of tl_L4 as in regs0" and "every byte outside [R - T_SEG_STK, R) as in
   (W0, mem0)". *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis ASTRCMP : astrcmp_realizes rsegs B A_STRCMP.
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.

(* what reaching C4 from the tail means *)
Definition tl_K (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word) (W0 : world rsegs)
(mem0 : word -> option byte) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq tl_L4 regs0 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs 0x82478 regs3 mem3 md3) POST.

(* 0x8246c: a0 = codes[1], s5 = codes[0]; mv a1,a0; mv a0,s5; jal check_code -> C4 *)
Lemma tl_s6 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 0x21520 -> getr regs2 (Z_to_bv 5 21) = w64 0x21500 ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x8246c regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 H21 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (proj1 Hcore) as HJ.
tl_enter.
m2_run m2_awr. ck_keep kwr_stk.
let R10 := fresh "R10" in rreg HS (10%bv : bv 5) R10.
let R11 := fresh "R11" in rreg HS (11%bv : bv 5) R11.
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1.
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ tl_L4 HS HAE ltac:(vm_compute; reflexivity)) as CL4;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
rewrite (st_ok_restrict_mkst rsegs (w_H W2) E ss ms HS eq_refl);
replace (ss_pc ss) with A_CHECK_CODE by (vm_compute; reflexivity)
end.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82478) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E21 : ew E 21 = getr regs2 (Z_to_bv 5 21)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (HspT : spZ (ms_regs ms) = e_R (x_e rsegs cx)) by (rewrite (tl_sp_of_cs _ _ C234); exact Hsp).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdT) _ =>
assert (HcoreT : rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
      (tl_r234 _ _ C234) eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |];
    intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (_ & _ & _ & _ & SN & SM & S0 & S1 & _).
eapply SRr_bind.
{ apply (rl_check_code_A B MT MTL LAWS ASTRCMP (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) 0x21500 0x21520).
  - apply (m2_pre_call B MT cx (rs_E2 rsegs cx) ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ T_cmp_STK Hpre HcoreT);
    [ rewrite R1'; vm_compute; reflexivity
    | unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | exact HspT | unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK; lia ].
  - etransitivity; [exact R10|]. rewrite E21. exact H21.
  - etransitivity; [exact R11|]. rewrite E10. exact H10.
  - exact S0.
  - exact S1.
  - exact SN.
  - exact SM. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_cmp_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK in *; lia) (fun x => x)).
  rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
Qed.

(* the common steps of a stage: the stack facts, the entry, the run to the callee, the kept registers, the goal
   in the mkCfg form at the callee's entry pc *)
Ltac tl_stage regs2 pcC :=
pose proof m2_wx as Hwx; pose proof m2_segs_low as Hsegs;
let HJ := fresh "HJ" in
lazymatch goal with Hcore : rs_core _ _ _ _ _ _ _ _ regs2 _ _ |- _ => pose proof (proj1 Hcore) as HJ end;
tl_enter;
m2_run m2_awr; ck_keep kwr_stk;
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
let CL4 := fresh "CL4" in let C234 := fresh "C234" in
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ tl_L4 HS HAE ltac:(vm_compute; reflexivity)) as CL4;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
replace (ss_pc ss) with pcC by (vm_compute; reflexivity)
end.
(* rs_core and sp at the callee's entry *)
Ltac tl_coreT regs2 :=
lazymatch goal with
| Hcore : rs_core _ _ _ ?cx ?E2 ?ly2 ?S2 ?W2 regs2 ?mem2 ?md2, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _,
  C234 : cs_eq _ regs2 (ms_regs ?ms), KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?ms) a = _,
  Hsp : spZ regs2 = _ |- _ =>
  let HcoreT := fresh "HcoreT" in let HspT := fresh "HspT" in
  assert (HspT : spZ (ms_regs ms) = e_R (x_e rsegs cx)) by (rewrite (tl_sp_of_cs _ _ C234); exact Hsp);
  assert (HcoreT : rs_core rsegs B MT cx E2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
        (tl_r234 _ _ C234) eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |];
      intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
Ltac tl_pre T :=
lazymatch goal with HcoreT : rs_core _ _ _ ?cx _ _ _ _ _ _ _, Hpre : rs_pre _ _ ?cx, R1' : getr _ 1 = w64 _,
  HspT : spZ _ = _ |- _ =>
apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T Hpre HcoreT);
[ rewrite R1'; vm_compute; reflexivity
| unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
| exact HspT | unfold T_cmp_STK, T_check_STK, T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia ]
end.
Ltac tl_kept Hkept3 KE Hkept :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
intros a Ha Hs; rewrite (Hkept3 a Ha ltac:(unfold T_cmp_STK, T_check_STK, T_leaf_STK, T_SEG_STK, ASTACK, ESTACK in *; lia)
  (fun x => x));
rewrite (KE a Ha (fun x => x)); exact (Hkept a Ha Hs).

(* 0x82460: a0 = codes[0]; mv s5,a0; li a0,1; jal reac_role_refuse_code (a0 = 1) -> 0x8246c *)
Lemma tl_s5 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 0x21500 ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82460 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_REFUSE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x8246c) by exact R1.
assert (R10' : getr (ms_regs ms) 10 = w64 1) by exact R10.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & T1 & TR).
eapply SRr_bind.
{ apply (rl_refuse_code_A B MT MTL LAWS HGOT HSC (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - tl_pre T_check_STK.
  - lia.
  - lia.
  - lia.
  - exact m2_tbl_img.
  - exact T0.
  - exact T1.
  - exact TR. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s6 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3).
- rewrite (tl_sp_pres _ _ Hpres3). exact HspT.
- etransitivity; [exact HR3|]. rewrite R10'. reflexivity.
- etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R21|].
  rewrite E10. exact H10.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x82458: li a0,0; jal reac_role_refuse_code (a0 = 0) -> 0x82460 *)
Lemma tl_s4 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82458 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_REFUSE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82460) by exact R1.
assert (R10' : getr (ms_regs ms) 10 = w64 0) by exact R10.
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & T1 & TR).
eapply SRr_bind.
{ apply (rl_refuse_code_A B MT MTL LAWS HGOT HSC (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - tl_pre T_check_STK.
  - lia.
  - lia.
  - lia.
  - exact m2_tbl_img.
  - exact T0.
  - exact T1.
  - exact TR. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s5 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (tl_sp_pres _ _ Hpres3); exact HspT)).
- etransitivity; [exact HR3|]. rewrite R10'. reflexivity.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x82444: a0 = the state string, s7 = changes, s5 = cur, s6 = req; mv a1,a0; mv a0,s7; mv a2,s5; mv a3,s6;
   jal check_answer -> 0x82458 *)
Lemma tl_s3 : forall (cx : rs_scx rsegs) POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
getr regs2 (Z_to_bv 5 10) = w64 (if cur =? req then 0x21580 else 0x21540) ->
getr regs2 (Z_to_bv 5 23) = w64 (rl_changes cur req) ->
getr regs2 (Z_to_bv 5 21) = w64 cur -> getr regs2 (Z_to_bv 5 22) = w64 req ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82444 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp Hcur Hreq H10 H23 H21 H22 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CHECK_ANSWER.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R12" in rreg HS (12%bv : bv 5) R.
let R := fresh "R13" in rreg HS (13%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82458) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E21 : ew E 21 = getr regs2 (Z_to_bv 5 21)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E22 : ew E 22 = getr regs2 (Z_to_bv 5 22)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E23 : ew E 23 = getr regs2 (Z_to_bv 5 23)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (SA & SP & SA' & SP' & _).
eapply SRr_bind.
{ apply (rl_check_answer_A B MT MTL LAWS ASTRCMP (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) cur req (if cur =? req then 0x21580 else 0x21540)).
  - tl_pre T_cmp_STK.
  - etransitivity; [exact R10|]. rewrite E23. exact H23.
  - etransitivity; [exact R11|]. rewrite E10. exact H10.
  - etransitivity; [exact R12|]. rewrite E21. exact H21.
  - exact Hcur.
  - etransitivity; [exact R13|]. rewrite E22. exact H22.
  - exact Hreq.
  - destruct (cur =? req); [exact SA' | exact SP'].
  - exact SA.
  - exact SP. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_cmp_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s4 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (tl_sp_pres _ _ Hpres3); exact HspT)).
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x82434: a0 = changes, s5 = cur, s6 = req; mv s7,a0; mv a0,s5; mv a1,s6; jal reac_role_cfg_apply_state -> 0x82444 *)
Lemma tl_s2 : forall (cx : rs_scx rsegs) POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
getr regs2 (Z_to_bv 5 10) = w64 (rl_changes cur req) ->
getr regs2 (Z_to_bv 5 21) = w64 cur -> getr regs2 (Z_to_bv 5 22) = w64 req ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82434 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp Hcur Hreq H10 H21 H22 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CFG_APPLY.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82444) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E21 : ew E 21 = getr regs2 (Z_to_bv 5 21)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E22 : ew E 22 = getr regs2 (Z_to_bv 5 22)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_cfg_apply_state_A B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) cur req).
  - tl_pre T_leaf_STK.
  - etransitivity; [exact R10|]. rewrite E21. exact H21.
  - exact Hcur.
  - etransitivity; [exact R11|]. rewrite E22. exact H22.
  - exact Hreq. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_leaf_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s3 cx POST cur req regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (tl_sp_pres _ _ Hpres3); exact HspT)).
- exact Hcur.
- exact Hreq.
- etransitivity; [exact HR3|]. unfold A_STR_APPLIED, A_STR_PENDING. reflexivity.
- etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R23|].
  rewrite E10. exact H10.
- etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R21|].
  rewrite E21. exact H21.
- etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R22|].
  rewrite E22. exact H22.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x82428: s5 = cur, s6 = req; mv a0,s5; mv a1,s6; jal reac_role_cfg_changes -> 0x82434 *)
Lemma tl_s1 : forall (cx : rs_scx rsegs) POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
getr regs2 (Z_to_bv 5 21) = w64 cur -> getr regs2 (Z_to_bv 5 22) = w64 req ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82428 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp Hcur Hreq H21 H22 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CFG_CHANGES.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82434) by exact R1.
assert (E21 : ew E 21 = getr regs2 (Z_to_bv 5 21)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E22 : ew E 22 = getr regs2 (Z_to_bv 5 22)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_cfg_changes_A B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) cur req).
  - tl_pre T_leaf_STK.
  - etransitivity; [exact R10|]. rewrite E21. exact H21.
  - exact Hcur.
  - etransitivity; [exact R11|]. rewrite E22. exact H22.
  - exact Hreq. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_leaf_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s2 cx POST cur req regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (tl_sp_pres _ _ Hpres3); exact HspT)).
- exact Hcur.
- exact Hreq.
- exact HR3.
- etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R21|].
  rewrite E21. exact H21.
- etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R22|].
  rewrite E22. exact H22.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* ======================================= the tail's head, 0x82408 .. 0x82428 =======================================
   One run with two regions: the real frame's flags cell R+0x30 (env slot 33 = fl) and the role cell (the literal
   cell). s8 is the literal rc, so the engine decides `bne s8,a1` (0x82418) itself: rc = 1 reads req from the role
   cell (0x8241c), rc = -1 or 0 takes req = cur xor 1 (0x82424). *)
Ltac tl_head_run :=
lazymatch goal with
| Hpre : rs_pre _ _ ?cx, Hcore : rs_core _ _ _ ?cx _ ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2,
  H24 : getr ?regs2 (Z_to_bv 5 24) = w64 ?v, Hcell : val_mem _ _ (_ + 0x180) 4 ?c,
  Hfl : val_mem _ _ (_ + 0x30) 8 ?fl, E9 : bv_unsigned (ew _ 9) = ?R, E22 : bv_unsigned (ew _ 22) = ?F22,
  E33 : ew _ 33 = _, Hpres : forall a, _ -> apresent _ _ a |- _ =>
let HS := fresh "HS" in
pose proof (m2_entry 0x82408 [((24%bv : bv 5), SLit v)]
  [m2_frame 0 0x138 0 0 [YP09.mkChunk 0x30 (CVal 8 (SOff 33 0))]; m2_rcell (SLit c)] m2_facts W2 regs2
  [Z_to_bv 64 M2_SB; Z_to_bv 64 fl] mem2) as HS;
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
  [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | rewrite ck_lit; symmetry; exact H24]));
specialize (HS ltac:(vm_compute; reflexivity));
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (m2_frame_ok _ W2 mem2 R (x_STK rsegs cx) (x_sp0 rsegs cx)); [exact E9 | lia | lia | exact Hpres | lia |];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val rsegs _ _ R 0x30 8 (SOff 33 0) fl); [| cbn; lia | cbn; lia | exact Hfl];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r, E33; rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | apply (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SLit c) c); [exact E22 | lia | lia | reflexivity | lia | exact Hcell] ]));
specialize (HS ltac:(cbn [pairwise_disjoint all_disjoint]; split; [split; [|exact I] | split; exact I];
  unfold extent_disjoint; cbn [m2_frame m2_rcell YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E9, E22;
  right; unfold T_SEG_STK, ASTACK in *; lia));
specialize (HS (m2_facts_ok _ R E9 ltac:(lia) ltac:(assumption)));
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs2 [Z_to_bv 64 M2_SB; Z_to_bv 64 fl]) as E eqn:HE;
let HAE := fresh "HAE" in
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 M2_SB; Z_to_bv 64 fl]) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity);
let HJ := fresh "HJ" in pose proof (proj1 Hcore) as HJ;
unfold cfg_at; change (w64 0x82408) with (Z_to_bv 64 0x82408);
m2_run_to m2_awr 0x82428; ck_keep kwr_stk
end.

Lemma tl_head : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 (fl rcv cell : Z),
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 22) = w64 (e_F (x_e rsegs cx) + 0x180) ->
getr regs2 (Z_to_bv 5 24) = w64 rcv ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x30) 8 fl -> 0 <= fl < 256 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x180) 4 cell ->
(rcv = -1 /\ cell = 0x5a \/ rcv = 0 /\ cell = 0x5a \/ rcv = 1 /\ (cell = 0 \/ cell = 1)) ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82408 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 fl rcv cell Hpre Hpod Hcore Hsp H9 H22 H24 Hfl Hfl8 Hcell
Hcase HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (proj1 Hcore) as HJ0.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). clear HJ0.
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (tl_bits fl Hfl8) as (Bcur & Breq).
pose proof (tl_cur_range fl) as (Rcur & Rreq).
assert (E9 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 M2_SB; Z_to_bv 64 fl]) 9) = e_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); assert (G : getr regs2 9%bv = w64 (e_R (x_e rsegs cx))) by exact H9;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
assert (E22 : bv_unsigned (ew (Ereg regs2 [Z_to_bv 64 M2_SB; Z_to_bv 64 fl]) 22) = e_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl);
    assert (G : getr regs2 22%bv = w64 (e_F (x_e rsegs cx) + 0x180)) by exact H22;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew (Ereg regs2 [Z_to_bv 64 M2_SB; Z_to_bv 64 fl]) 33 = Z_to_bv 64 fl)
by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
destruct Hcase as [[Hr Hc]|[[Hr Hc]|[Hr [Hc|Hc]]]]; subst rcv cell.
all: tl_head_run.
all: let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
all: let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
all: lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ tl_L4 HS HAE ltac:(vm_compute; reflexivity)) as CL4;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with 0x82428 by (vm_compute; reflexivity)
  end.
all: tl_coreT regs2.
all: assert (H21' : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (Z.b2z (Z.testbit fl 1)))
  by (etransitivity; [exact R21|]; rewrite E33; exact Bcur).
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) (1 - Z.b2z (Z.testbit fl 1)) regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur Rreq H21').
  + etransitivity; [exact R22|]. rewrite E33. exact Breq.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) (1 - Z.b2z (Z.testbit fl 1)) regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur Rreq H21').
  + etransitivity; [exact R22|]. rewrite E33. exact Breq.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) 0 regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur ltac:(lia) H21').
  + exact R22.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) 1 regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur ltac:(lia) H21').
  + exact R22.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
Qed.

(* ======================================= the two checks ======================================= *)
(* what reaching T from a check means: rs_core, the registers of ch_L as at the check's cut, s9 = vF, s11 = vP, every
   byte outside the callees' stack as at the cut *)
Definition ch_K (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word) (W0 : world rsegs)
(mem0 : word -> option byte) (vF vP : Z) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq ch_L regs0 regs3 ->
getr regs3 (Z_to_bv 5 25) = w64 vF -> getr regs3 (Z_to_bv 5 27) = w64 vP ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs 0x82408 regs3 mem3 md3) POST.

(* the enter step at a check's cut: the role cell as the one region (s6 = F + 0x180, value 0x5a) *)
Ltac ch_enter :=
lazymatch goal with
| Hpre : rs_pre _ _ ?cx, Hcore : rs_core _ _ _ ?cx _ ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2,
  Hcell : val_mem _ _ (_ + 0x180) 4 0x5a, E22 : bv_unsigned (ew _ 22) = _
  |- SRr rsegs ?W2 (cfg_at rsegs ?pc ?regs2 ?mem2 ?md2) _ =>
let HS := fresh "HS" in
pose proof (m2_entry pc [] [m2_rcell (SLit 0x5a)] (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl) as HS;
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SLit 0x5a) 0x5a); [exact E22 | lia | lia | reflexivity | lia | exact Hcell])
  ltac:(cbn; tauto) ltac:(repeat split));
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs2 []) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity);
let HJ := fresh "HJ" in pose proof (proj1 Hcore) as HJ;
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.

(* MAL 0x823fc: lw a1,0(s6) (0x5a); mv a0,s8 (-1); jal check_malformed, ra = 0x82408 *)
Lemma ch_mal : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vF vP,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 22) = w64 (e_F (x_e rsegs cx) + 0x180) -> getr regs2 (Z_to_bv 5 24) = w64 (-1) ->
getr regs2 (Z_to_bv 5 25) = w64 vF -> getr regs2 (Z_to_bv 5 27) = w64 vP ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x180) 4 0x5a ->
ch_K cx POST regs2 W2 mem2 vF vP ->
SRr rsegs W2 (cfg_at rsegs 0x823fc regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vF vP Hpre Hcore Hsp H22 H24 H25 H27 Hcell HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E22 : bv_unsigned (ew (Ereg regs2 []) 22) = e_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl);
    assert (G : getr regs2 22%bv = w64 (e_F (x_e rsegs cx) + 0x180)) by exact H22;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
ch_enter.
m2_run m2_awr. ck_keep kwr_stk.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82408) by exact R1.
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [25; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2527;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_MALFORMED by (vm_compute; reflexivity)
end.
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_check_malformed_A B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - tl_pre T_check_STK.
  - etransitivity; [exact R10|]. rewrite E24. exact H24.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
- etransitivity; [exact (Hpres3 25 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2527 25%bv ltac:(cbv [In]; left; reflexivity))|]. exact H25.
- etransitivity; [exact (Hpres3 27 ltac:(unfold acallee_saved; lia))|].
  etransitivity; [exact (C2527 27%bv ltac:(cbv [In]; right; left; reflexivity))|]. exact H27.
- intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)).
Qed.

(* ABS 0x82380: lw a1,0(s6) (0x5a); mv a0,s8 (0); jal check_absent, ra = 0x8238c; then 0x8238c ld s9,0x28(s1);
   ld s11,0x80(s1); j 0x82408 (the real frame's two cells as the one region, env slots 32 / 33 = vF / vP) *)
Lemma ch_abs : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vF vP,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 22) = w64 (e_F (x_e rsegs cx) + 0x180) -> getr regs2 (Z_to_bv 5 24) = w64 0 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x180) 4 0x5a ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x28) 8 vF -> 0 <= vF < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x80) 8 vP -> 0 <= vP < 2 ^ 64 ->
ch_K cx POST regs2 W2 mem2 vF vP ->
SRr rsegs W2 (cfg_at rsegs 0x82380 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vF vP Hpre Hcore Hsp H9 H22 H24 Hcell H28 HvF H80 HvP HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E22 : bv_unsigned (ew (Ereg regs2 []) 22) = e_F (x_e rsegs cx) + 0x180)
by (rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl);
    assert (G : getr regs2 22%bv = w64 (e_F (x_e rsegs cx) + 0x180)) by exact H22;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
ch_enter.
m2_run m2_awr. ck_keep kwr_stk.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x8238c) by exact R1.
assert (E24 : ew E 24 = getr regs2 (Z_to_bv 5 24)) by (subst E; apply ew_Ereg_nat; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_ABSENT by (vm_compute; reflexivity)
end.
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_check_absent_A B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - tl_pre T_check_STK.
  - etransitivity; [exact R10|]. rewrite E24. exact H24.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
(* the state at 0x8238c *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)). }
assert (CL3 : cs_eq ch_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
assert (Hsp3 : spZ regs3 = e_R (x_e rsegs cx)) by (rewrite (tl_sp_pres _ _ Hpres3); exact HspT).
assert (H93 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx))) by (cs_get CL3 (9%bv : bv 5); exact H9).
assert (H283 : val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x28) 8 vF).
{ eapply (val_mem_kept rsegs); [|exact H28]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
assert (H803 : val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x80) 8 vP).
{ eapply (val_mem_kept rsegs); [|exact H80]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
clear dependent ms. clear dependent E.
pose proof (proj1 Hcore3) as HJ3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (E9 : bv_unsigned (ew (Ereg regs3 [Z_to_bv 64 vF; Z_to_bv 64 vP]) 9) = e_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); assert (G : getr regs3 9%bv = w64 (e_R (x_e rsegs cx))) by exact H93;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
pose proof (m2_entry 0x8238c []
  [m2_frame 0 0x138 0 0 [YP09.mkChunk 0x28 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x80 (CVal 8 (SOff 33 0))]]
  (mkFacts [] [] []) W3 regs3 [Z_to_bv 64 vF; Z_to_bv 64 vP] mem3 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_frame_ok _ W3 mem3 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx)); [exact E9 | lia | lia | exact Hpres | lia |];
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (chunk_ok_val rsegs _ _ _ 0x28 8 (SOff 32 0) vF); [| cbn; lia | cbn; lia | exact H283];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | apply (chunk_ok_val rsegs _ _ _ 0x80 8 (SOff 33 0) vP); [| cbn; lia | cbn; lia | exact H803];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia ])
  ltac:(cbn; tauto) ltac:(repeat split)).
remember (Ereg regs3 [Z_to_bv 64 vF; Z_to_bv 64 vP]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 vF; Z_to_bv 64 vP]) E) by (subst E; apply env_agree_refl).
assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W3) mem3 a)
by (intros; reflexivity).
change (cfg_at rsegs 0x8238c regs3 mem3 md3) with (mkCfg (mkst regs3 (Z_to_bv 64 0x8238c) mem3 (seg_rom rsegs)) md3).
m2_run_to m2_awr 0x82408. ck_keep kwr_stk.
let R := fresh "R25" in rreg HS (25%bv : bv 5) R.
let R := fresh "R27" in rreg HS (27%bv : bv 5) R.
assert (E32 : ew E 32 = Z_to_bv 64 vF) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 vP) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with 0x82408 by (vm_compute; reflexivity)
end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
end.
- apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ Hcore3
    ltac:(eassumption) (tl_r234 _ _ C234) eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (KE a Ha (fun x => x)).
- exact (cs_eq_trans _ _ _ _ CL3 CL').
- etransitivity; [exact R25|]. exact E32.
- etransitivity; [exact R27|]. exact E33.
- intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (K3 a Ha Hs).
Qed.
End w.

(* ======================================= the two piece statements ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the strcmp wrapper's contract at every float state: the tail's cut T holds at any float state fx2 the walk
   reached, and check_answer / check_code call the wrapper there *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, @astrcmp_realizes fy rc rsegs B A_STRCMP.
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.

(* the bytes a cut of this half names and no call or run of the half writes: below the allocator's ceiling, or
   in the real frame at R and above *)
Lemma m2t_far : forall cx : rs_scx rsegs, rs_pre rsegs B cx -> forall a,
(0 <= a < alloc_ceiling) \/ (e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x1a0) ->
0 <= a < 2 ^ 64 /\ ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)).
Proof.
intros cx Hpre a Ha. pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in *. lia.
Qed.
(* the first block: below the allocator's ceiling *)
Lemma m2t_pp : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling.
Proof.
intros cx Hpre. pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hpp) as (_ & H4096 & Hceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hceil. lia.
Qed.
Lemma m2t_garr8_kept : forall H H' (m m' : word -> option byte) a l,
garr8 rsegs (mrestrict H m) a l ->
(forall j, (j < length l)%nat -> aview rsegs H' m' (a + Z.of_nat j) = aview rsegs H m (a + Z.of_nat j)) ->
garr8 rsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l G K j Hj. destruct (G j Hj) as (Hv & Hr). split; [|exact Hr].
eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 1) with 1 in Hk.
replace k with 0 by lia. rewrite Z.add_0_r. exact (K j Hj).
Qed.

(* the cut facts of a check cut (or T) that the T cut restates, carried to a state whose memory agrees outside the
   callees' stack and whose registers of ch_L agree *)
Lemma ch_cut_T : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx) -> rs_role_at rsegs cx rec W2 mem2 ->
getr regs2 (Z_to_bv 5 24) = w64 (snd (rs_PA rsegs cx rec)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq ch_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 25) = w64 (e_F (x_e rsegs cx)) -> getr regs3 (Z_to_bv 5 27) = w64 (e_pp (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_T (fx := fx) rsegs B MT cx fx2 rec ly3 S3 W3 regs3 mem3 md3.
Proof using LAWS.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1) Hat Hrole H24 Hcore3 HL H25 H27 K3.
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2t_pp cx Hpre) as (P4096 & Pceil).
pose proof (m2t_far cx Hpre) as Far.
pose proof m2_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
unfold rs_at_cx, rs_at, rs_L_chk in Hat. rewrite !Forall_cons_iff in Hat.
destruct Hat as (A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _).
cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, AC8, AC30.
split; [|split].
- (* rs_chk_base *)
  split; [exact Hcore3|]. split; [exact Hfxk|].
  split; [apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh); intros i Hi;
    apply K3; apply Far; left; unfold shadow_addr, SHADOW_OFF; change (Z.of_nat (length rs_PB)) with 52 in Hi;
    assert (e_F (x_e rsegs cx) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia);
    assert (0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia); lia|].
  split; [eapply (rm_rom_kept rsegs); [exact Hrom|]; intros a (sg & Hsg & _ & Hr);
    apply K3; apply Far; left; pose proof (Hsegs a ltac:(exists sg; split; [exact Hsg | exact Hr])); unfold kLowMemEnd in *; lia|].
  split; [unfold rs_pp_at in *; apply (m2t_garr8_kept _ _ _ _ _ _ Hpp); intros j Hj;
    unfold rs_u8s in Hj; rewrite length_map in Hj; pose proof (Layout.length_pp_bytes rec Hwf) as HL0;
    apply K3; apply Far; left; lia|].
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
- (* the registers and cells *)
  unfold rs_at_cx, rs_at, rs_L_chk. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [rl_at rl_xv fst snd].
  + cs_get HL (8%bv : bv 5). exact A8.
  + cs_get HL (9%bv : bv 5). exact A9.
  + cs_get HL (19%bv : bv 5). exact A19.
  + cs_get HL (23%bv : bv 5). exact A23.
  + cs_get HL (18%bv : bv 5). exact A18.
  + cs_get HL (22%bv : bv 5). exact A22.
  + eapply (val_mem_kept rsegs); [|exact AC8]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    apply K3; apply Far; right; lia.
  + eapply (val_mem_kept rsegs); [|exact AC30]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    apply K3; apply Far; right; lia.
  + cs_get HL (24%bv : bv 5). exact H24.
  + exact H25.
  + exact H27.
- (* the role cell *)
  unfold rs_role_at in *. eapply (val_mem_kept rsegs); [|exact Hrole]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
  apply K3; apply Far; left; lia.
Qed.

(* the C4 cut from the T cut's facts, carried to a state whose memory agrees outside the callees' stack and whose
   six registers of tl_L4 agree *)
Lemma tl_cut_C4 : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
  (LReg 27, e_pp (x_e rsegs cx))]) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq tl_L4 regs2 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_C4 (fx := fx) rsegs B MT cx fx2 ly3 S3 W3 regs3 mem3 md3.
Proof using LAWS.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & _) Hat Hcore3 HL K3.
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2t_far cx Hpre) as Far.
pose proof asan_consts as (C1 & _).
unfold rs_at_cx, rs_at, rs_L_chk in Hat. rewrite Forall_app, !Forall_cons_iff in Hat.
destruct Hat as ((A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _) & A24 & A25 & A27 & _).
cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, AC8, AC30, A24, A25, A27.
split; [exact Hcore3|]. split; [exact Hfxk|]. split.
- unfold rl_cut. cbn [hi_L4 role_himg_A]. repeat apply Forall_cons; try apply Forall_nil; cbn [rl_at rl_xv fst snd].
  + cs_get HL (18%bv : bv 5). exact A18.
  + cs_get HL (8%bv : bv 5). exact A8.
  + cs_get HL (9%bv : bv 5). exact A9.
  + cs_get HL (19%bv : bv 5). exact A19.
  + cs_get HL (25%bv : bv 5). exact A25.
  + cs_get HL (27%bv : bv 5). rewrite Z.add_0_r. exact A27.
  + eapply (val_mem_kept rsegs); [|exact AC8]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    apply K3; apply Far; right; lia.
- apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh). intros i Hi.
  change (Z.of_nat (length rs_PB)) with 52 in Hi.
  assert (e_F (x_e rsegs cx) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
  apply K3; apply Far; left; unfold shadow_addr, SHADOW_OFF; lia.
Qed.

(* ---- W11b TAIL: T 0x82408 -> C4 0x82478 ---- *)
Theorem rl_m02_tail_A : rs_piece_W11b_tail_stmt rsegs B MT.
Proof using MTL LAWS ASTRCMP HGOT HSC.
unfold rs_piece_W11b_tail_stmt. intros cx POST inp Hst HC4.
unfold rs_from_T. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HT.
destruct Hst as (Hpre & _).
destruct HT as (Hbase & Hat & Hrole).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfl & _).
pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'. rewrite Forall_app, !Forall_cons_iff in Hat'.
destruct Hat' as ((A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _) & A24 & A25 & A27 & _).
cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, AC8, AC30, A24, A25, A27.
rewrite Z.mod_small in AC30 by lia.
assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
assert (Hcase : (snd (rs_PA rsegs cx rec) = -1 /\ rs_rcell (fst (rs_PA rsegs cx rec)) = 0x5a) \/
  (snd (rs_PA rsegs cx rec) = 0 /\ rs_rcell (fst (rs_PA rsegs cx rec)) = 0x5a) \/
  (snd (rs_PA rsegs cx rec) = 1 /\ (rs_rcell (fst (rs_PA rsegs cx rec)) = 0 \/ rs_rcell (fst (rs_PA rsegs cx rec)) = 1))).
{ unfold rs_PA. destruct (rk_parse_cases (Z.testbit (e_fl (x_e rsegs cx)) 0) (buf rec))
  as [(H1 & H2)|[(H1 & H2)|(H1 & w & H2)]]; rewrite H1, H2.
  - left. split; reflexivity.
  - right. left. split; reflexivity.
  - right. right. split; [reflexivity|]. destruct w; cbn; [left | right]; reflexivity. }
apply (tl_head (fx := fx2) B MT MTL LAWS (ASTRCMP fx2) HGOT HSC cx POST regs2 W2 mem2 ly2 S2 W2 regs2 mem2 md2
  (e_fl (x_e rsegs cx)) (snd (rs_PA rsegs cx rec)) (rs_rcell (fst (rs_PA rsegs cx rec))) Hpre Hpod Hcore Hsp A9 A22 A24
  AC30 Hfl Hrole Hcase).
- intros r Hr. reflexivity.
- intros a _ _. reflexivity.
- intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL K3.
  apply (HC4 fx2 ly3 S3 W3 regs3 mem3 md3).
  exact (tl_cut_C4 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hat Hcore3 HL K3).
Qed.

(* ---- W11b CHECKS: ABS 0x82380 -> T, MAL 0x823fc -> T ---- *)
Theorem rl_m02_checks_A : rs_piece_W11b_checks_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W11b_checks_stmt. intros cx POST inp Hst HT.
destruct Hst as (Hpre & _).
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
split.
- unfold rs_from_ABS. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HA.
  destruct HA as (Hbase & Hat & Hrole & Hn & H0).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'. rewrite Forall_app, !Forall_cons_iff in Hat'.
  destruct Hat' as ((A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _) & A24 & AC28 & AC80 & _).
  cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, AC8, AC30, A24, AC28, AC80.
  assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  unfold rs_role_at in Hrole. rewrite Hn in Hrole. cbn [rs_rcell] in Hrole.
  apply (ch_abs (fx := fx2) B MT MTL LAWS cx POST ly2 S2 W2 regs2 mem2 md2 _ _ Hpre Hcore Hsp A9 A22 A24 Hrole AC28
    ltac:(apply Z.mod_pos_bound; lia) AC80 ltac:(apply Z.mod_pos_bound; lia)).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H25 H27 K3.
  apply (HT fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (ch_cut_T cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + unfold rs_at_cx, rs_at, rs_L_chk. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + unfold rs_role_at. rewrite Hn. exact Hrole.
  + rewrite H0. exact A24.
  + exact Hcore3.
  + exact HL.
  + rewrite H25. apply w64_mod.
  + rewrite H27. apply w64_mod.
  + exact K3.
- unfold rs_from_MAL. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HM.
  destruct HM as (Hbase & Hat & Hrole & Hn & H1).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rs_at_cx, rs_at, rs_L_chk in Hat'. rewrite Forall_app, !Forall_cons_iff in Hat'.
  destruct Hat' as ((A8 & A9 & A19 & A23 & A18 & A22 & AC8 & AC30 & _) & A24 & A25 & A27 & _).
  cbn [rl_at rl_xv fst snd] in A8, A9, A19, A23, A18, A22, AC8, AC30, A24, A25, A27.
  assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  unfold rs_role_at in Hrole. rewrite Hn in Hrole. cbn [rs_rcell] in Hrole.
  apply (ch_mal (fx := fx2) B MT MTL LAWS cx POST ly2 S2 W2 regs2 mem2 md2 _ _ Hpre Hcore Hsp A22 A24 A25 A27 Hrole).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H25 H27 K3.
  apply (HT fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (ch_cut_T cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + unfold rs_at_cx, rs_at, rs_L_chk. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + unfold rs_role_at. rewrite Hn. exact Hrole.
  + rewrite H1. exact A24.
  + exact Hcore3.
  + exact HL.
  + exact H25.
  + exact H27.
  + exact K3.
Qed.
End m.

Print Assumptions rl_m02_tail_A.
Print Assumptions rl_m02_checks_A.
