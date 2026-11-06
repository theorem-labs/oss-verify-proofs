(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc; L_ANS_cs as tl_L4_cs and
   ch_L_cs) for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02: the tail and the two checks, proved
   against lib/A/RPgSeg.v's rs_piece_W11b_tail_stmt and rs_piece_W11b_checks_stmt on lib/A/Img0.v rsegs. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v at 1d255703e88, with
   proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02ChkB.v at b419fd3eb4f as the template of the absent arm at image B's form,
   for image B (fuzz_role.asan-ubsan): image B's pcs and callees; the tail reads the flags byte from s8 (no frame
   read) and keeps cur / req / changes / codes[0] in s7 / s4 / s5 / s4 (image A: s5 / s6 / s7 / s5); the role cell
   is at F+0x2a0 in s4 and the answer in s9; the absent arm reads the answer from the real-frame cell R+0x158 and its
   second run reloads F (R+0x38), pp (R+0x140) and the flags byte (R+0x40) into s10 / s6 / s8; what C4 reads is
   lib/AU/RPgImgA.v's hi_L4; the cuts are lib/AU/RPgSeg.v's, the half's kit is lib/AU/RPgM02Base.v and the callee
   theorems are lib/AU's rl_*_B; the tail's code has its own table (the kit's covers the key compare and the two
   checks, not the tail); the cut lemmas read a cut's list by location, not by position. *)
(* reac-pw/fuzz_role, image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes). Proves no function
   (kind: segment lemma): the pieces W11b-tail and W11b-checks of LLVMFuzzerTestOneInput's segment M02, whose
   statements are lib/AU/RPgSeg.v's (rs_piece_W11b_tail_stmt, rs_piece_W11b_checks_stmt); nothing here restates a
   cut.

   THE CODE (the listing of image B's entry function):
     ABS 0x8245c lw a1,0(s4) (the role cell, 0x5a); 0x82460 ld s9,0x158(s1) (the answer, 0); 0x82464 mv a0,s9;
         0x82468 jal check_absent 0x82a80, ra = 0x8246c; 0x8246c ld s10,0x38(s1) (F); 0x82470 ld s6,0x140(s1) (pp);
         0x82474 ld s8,0x40(s1) (the flags byte); 0x82478 j T
     MAL 0x824f8 lw a1,0(s4) (0x5a); 0x824fc mv a0,s9 (-1); 0x82500 jal check_malformed 0x82ad8, ra = T
     T   0x82504 slli a0,s8,0x3e; 0x82508 li a1,1; 0x8250c srli s7,a0,0x3f (cur = bit 1 of the flags byte);
         0x82510 bne s9,a1 -> 0x8251c; 0x82514 lw s4,0(s4) (req = the role cell); 0x82518 j 0x82520;
         0x8251c xori s4,s7,1 (req = cur xor 1);
         0x82520 mv a0,s7; mv a1,s4; 0x82528 jal reac_role_cfg_changes 0x83108, ra = 0x8252c;
         0x8252c mv s5,a0; mv a0,s7; mv a1,s4; 0x82538 jal reac_role_cfg_apply_state 0x83114, ra = 0x8253c;
         0x8253c mv a1,a0; mv a0,s5; mv a2,s7; mv a3,s4; 0x8254c jal check_answer 0x82b08, ra = 0x82550;
         0x82550 li a0,0; 0x82554 jal reac_role_refuse_code 0x8309c, ra = 0x82558;
         0x82558 mv s4,a0; li a0,1; 0x82560 jal reac_role_refuse_code, ra = 0x82564;
         0x82564 mv a1,a0; mv a0,s4; 0x8256c jal check_code 0x82b5c, ra = C4 0x82570.
   No instrumented check and no trap branch lies in this code: the reads of the role cell (0x8245c, 0x824f8,
   0x82514) are a constant offset in the frame for locals and the real-frame reloads (0x82460, 0x8246c .. 0x82474)
   are in the real frame; none carries a check. The one branch, `bne s9,a1` 0x82510, is decided by the engine on
   each of the parse's four answers. The error paths of the pieces are the callees' aborts (check_absent's and
   check_malformed's `bnez` / `bne` to their abort calls, check_answer's and check_code's strcmp tests): each is
   refuted by the callee's theorem (lib/AU/RPgCheck.v rl_check_absent_B, rl_check_malformed_B; lib/AU/RPgCheckStr.v
   rl_check_answer_B, rl_check_code_B) at the arguments the walk passes; reac_role_refuse_code's own trap branch is
   refuted by lib/AU/RPgRefuse.v rl_refuse_code_B (a0 = 0 and a0 = 1).

   THE TAIL (rs_cut_T at T 0x82504 -> rs_cut_C4 at C4 0x82570):
   - tl_head: one run 0x82504 .. 0x82520 from an entry state with the role cell as its one region and s9 overridden
     by the literal answer, on each of the four cases of the parse's answer (RPgScanF.rk_parse_cases: (-1, None),
     (0, None), (1, MASTER), (1, SLAVE)): rc = 1 reads req from the role cell, else req = cur xor 1. cur = bit 1 of
     fl and 1 - cur are the values of the two ALU chains the run leaves in s7 / s4, checked over the 256 byte values
     (tl_bits).
   - tl_s1 .. tl_s6: the six calls. Each stage is a fresh entry state with no region (the code between two calls
     only moves registers), a run to the callee's entry, the callee's theorem through SRr_bind with
     RPgM02Base.m2_pre_call for its rl_pre, and m2_core_call for rs_core at the return pc. apply_state's result
     (0x215c0 / 0x21580) is the string check_answer is called with; refuse_code's results 0x21540 / 0x21560 are the
     strings check_code is called with; RPgM02Base.m2_strs gives every string, the table and its shadow.
   - What C4 reads (hi_L4: s2 = pod, s0 = S, s1 = R, s3, s6 = pp, s10 = F and R+0x20 = F) is carried from the T cut:
     the six registers are callee-saved and not written by the tail (tl_L4), and no byte outside the callees' stack
     [R - T_SEG_STK, R) is written (tl_cut_C4).
   THE CHECKS (rs_cut_ABS at 0x8245c, rs_cut_MAL at 0x824f8 -> rs_cut_T at 0x82504):
   - ch_mal: one run (the role cell as the one region: `lw a1,0(s4)` reads 0x5a, the parse having written no role)
     to check_malformed (a0 = s9 = -1), whose return address is T itself.
   - ch_abs: one run (the role cell and the real-frame cell R+0x158 as its regions) to check_absent (a0 = s9 = 0,
     a1 = 0x5a), then a run from its return 0x8246c with the real frame's cells R+0x38 / R+0x40 / R+0x140 as the
     region (env slots 32 / 33 / 34) to T.
   - ch_cut_T builds RPgSeg's rs_cut_T at the state reached from the check cut's facts.
   Every callee returns at the float state it was called at, so every state of the half is at the cut's own float
   state fx2; the walk lemmas are stated at the configurations' float state (Section w) and used at fx2.

   SECTION HYPOTHESES of the two theorems (Section m): MTL : ameter_laws MT and LAWS : AR_laws rsegs B (both); for
   the tail also ASTRCMP : the strcmp wrapper's contract astrcmp_realizes rsegs B 0x41b68 at every float state
   (check_answer and check_code call the wrapper at the cut's float state), and HGOT / HSC (as_got_shadow B =
   0x9aad0, as_shadow_cell B = 0xa3678, which lib/AU/RPgRefuse.v's rl_refuse_code_B takes). Nothing else is
   assumed. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgMem RPgScanF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgCheck RPgCheckStr RPgRefuse RPgCfgChanges RPgCfgApply.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgM02Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the tail's code ======================================= *)
(* the 27 4-byte words 0x82504 .. 0x8256c (RPgM02Base.m2_tbl covers 0x82370 .. 0x82500, the key compare and the
   two checks); C4 0x82570 lies outside it, as the engine's stop pcs may *)
Definition tl_tbl : ctable := Eval vm_compute in (build_table rsegs M2_T 27 TEmpty).
Lemma tl_tbl_eq : tl_tbl = build_table rsegs M2_T 27 TEmpty.
Proof. vm_cast_no_check (eq_refl tl_tbl). Qed.
Lemma tl_tbl_ok : table_ok rsegs tl_tbl.
Proof. rewrite tl_tbl_eq. apply build_table_ok0. unfold M2_T. lia. Qed.
Ltac tl_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tl_tbl_ok HS HJ SHOK M2_Bspan; [awr | ] end.
Ltac tl_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tl_tbl_ok HS HJ SHOK M2_Bspan stop; [awr | ] end.

(* ======================================= registers ======================================= *)
(* the registers the C4 cut reads (RPgImgA's hi_L4): all callee-saved, none written by the tail or the checks *)
Definition tl_L4 : list (bv 5) := [8; 9; 18; 19; 22; 26]%bv.
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

(* the registers both checks keep for the T cut (RPgSeg's rs_L_chk registers): all callee-saved *)
Definition ch_L : list (bv 5) := [8; 9; 18; 19; 20; 27]%bv.
Lemma ch_L_cs : forall r, In r ch_L -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [ch_L In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
(* membership of a register in a kept list *)
Ltac tl_in := cbv [tl_L4 ch_L In]; repeat (first [left; apply bv_eq; reflexivity | right]).
(* a register of a kept list, read through the list *)
Ltac cs_get Hcs r := etransitivity; [exact (Hcs r ltac:(tl_in))|].

(* ---- a cut's list read by location (the cut lemmas do not depend on the list's order) ---- *)
(* membership of a (location, value) pair in a cut's list *)
Ltac in_list := try unfold rs_L_chk; cbn [app In]; repeat (first [left; reflexivity | right]).
(* Hat : the unfolded list of a cut (Forall (fun f => rl_at ...) L); H := the fact at (l, v) *)
Ltac at_get Hat l v H :=
pose proof (proj1 (Forall_forall _ _) Hat (l, v) ltac:(in_list)) as H; cbn [fst snd rl_at rl_xv] in H.
(* a register goal of a cut's list at regs3, from the fact at regs2 through the kept list HL *)
Ltac at_reg Hat HL :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = w64 ?v =>
etransitivity; [exact (HL (Z_to_bv 5 r) ltac:(tl_in))|];
let X := fresh "X" in at_get Hat (LReg r) v X; exact X
end.
(* a real-frame cell goal of a cut's list at mem3, from the fact at mem2 through the kept memory K3 and Far *)
Ltac at_cell Hat K3 Far :=
lazymatch goal with |- val_mem _ _ (e_R ?e + ?o) 8 (?v mod 2 ^ 64) =>
let X := fresh "X" in at_get Hat (LCell XR o) v X;
eapply (val_mem_kept rsegs); [|exact X];
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; change (Z.of_nat 8) with 8 in Hk; apply K3; apply Far; right; lia
end.
(* a cut's list, from the unfolded list Hat of another cut that holds each of its pairs *)
Ltac at_sub Hat :=
unfold rs_at_cx, rs_at; apply (proj2 (Forall_forall _ _));
let f := fresh "f" in let Hf := fresh "Hf" in
intros f Hf; apply (proj1 (Forall_forall _ _) Hat);
unfold rs_L_chk in Hf |- *; cbn [app In] in Hf |- *;
repeat (destruct Hf as [<- | Hf]; [repeat (first [left; reflexivity | right]) |]); destruct Hf.

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
(* the same after the entry state HS of a run with regions: the env, the shadow seam, the kept memory, the journal *)
Ltac ch_env Hcore W2 regs2 extra mem2 pc :=
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs2 extra) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs2 extra) E) by (subst E; apply env_agree_refl);
let SHOK := fresh "SHOK" in assert (SHOK : sh_ok rsegs M2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor;
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a)
by (intros; reflexivity);
let HJ := fresh "HJ" in pose proof (proj1 Hcore) as HJ;
try unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc).

(* ======================================= the flags byte's bit 1 =======================================
   0x82504 slli a0,s8,0x3e; 0x8250c srli s7,a0,0x3f: s7 = bit 1 of the flags byte fl (cur); 0x8251c xori s4,s7,1:
   s4 = 1 - cur. Checked over the 256 values of the byte. *)
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
Hypothesis HGOT : as_got_shadow B = 0x9aad0.
Hypothesis HSC : as_shadow_cell B = 0xa3678.

(* what reaching C4 from the tail means *)
Definition tl_K (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word) (W0 : world rsegs)
(mem0 : word -> option byte) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq tl_L4 regs0 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs 0x82570 regs3 mem3 md3) POST.

(* the common steps of a stage: the stack facts, the entry, the run to the callee, the kept registers, the goal
   in the mkCfg form at the callee's entry pc *)
Ltac tl_stage regs2 pcC :=
pose proof m2_wx as Hwx; pose proof m2_segs_low as Hsegs;
let HJ := fresh "HJ" in
lazymatch goal with Hcore : rs_core _ _ _ _ _ _ _ _ regs2 _ _ |- _ => pose proof (proj1 Hcore) as HJ end;
tl_enter;
tl_run m2_awr; ck_keep kwr_stk;
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
  assert (HspT : spZ (ms_regs ms) = e_R (x_e rsegs cx))
  by (rewrite (m2_sp_of_cs [2; 3; 4]%bv _ _ ltac:(cbv [In]; left; reflexivity) C234); exact Hsp);
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

(* 0x82564: a0 = codes[1], s4 = codes[0]; mv a1,a0; mv a0,s4; jal check_code -> C4 *)
Lemma tl_s6 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 0x21560 -> getr regs2 (Z_to_bv 5 20) = w64 0x21540 ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82564 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 H20 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CHECK_CODE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82570) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = getr regs2 (Z_to_bv 5 20)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (_ & _ & _ & _ & SN & SM & S0 & S1 & _).
eapply SRr_bind.
{ apply (rl_check_code_B B MT MTL LAWS ASTRCMP (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) 0x21540 0x21560).
  - tl_pre T_cmp_STK.
  - etransitivity; [exact R10|]. rewrite E20. exact H20.
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
- tl_kept Hkept3 KE Hkept.
Qed.

(* 0x82558: a0 = codes[0]; mv s4,a0; li a0,1; jal reac_role_refuse_code (a0 = 1) -> 0x82564 *)
Lemma tl_s5 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 0x21540 ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82558 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_REFUSE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R20" in rreg HS (20%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82564) by exact R1.
assert (R10' : getr (ms_regs ms) 10 = w64 1) by exact R10.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & T1 & TR).
eapply SRr_bind.
{ apply (rl_refuse_code_B B MT MTL LAWS HGOT HSC (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
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
- rewrite (m2_sp_pres _ _ Hpres3). exact HspT.
- etransitivity; [exact HR3|]. rewrite R10'. reflexivity.
- etransitivity; [exact (Hpres3 20 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R20|].
  rewrite E10. exact H10.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x82550: li a0,0; jal reac_role_refuse_code (a0 = 0) -> 0x82558 *)
Lemma tl_s4 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82550 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_REFUSE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82558) by exact R1.
assert (R10' : getr (ms_regs ms) 10 = w64 0) by exact R10.
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & T1 & TR).
eapply SRr_bind.
{ apply (rl_refuse_code_B B MT MTL LAWS HGOT HSC (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
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
apply (tl_s5 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (m2_sp_pres _ _ Hpres3); exact HspT)).
- etransitivity; [exact HR3|]. rewrite R10'. reflexivity.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x8253c: a0 = the state string, s5 = changes, s7 = cur, s4 = req; mv a1,a0; mv a0,s5; mv a2,s7; mv a3,s4;
   jal check_answer -> 0x82550 *)
Lemma tl_s3 : forall (cx : rs_scx rsegs) POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
getr regs2 (Z_to_bv 5 10) = w64 (if cur =? req then 0x215c0 else 0x21580) ->
getr regs2 (Z_to_bv 5 21) = w64 (rl_changes cur req) ->
getr regs2 (Z_to_bv 5 23) = w64 cur -> getr regs2 (Z_to_bv 5 20) = w64 req ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x8253c regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp Hcur Hreq H10 H21 H23 H20 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CHECK_ANSWER.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R12" in rreg HS (12%bv : bv 5) R.
let R := fresh "R13" in rreg HS (13%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82550) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E21 : ew E 21 = getr regs2 (Z_to_bv 5 21)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E23 : ew E 23 = getr regs2 (Z_to_bv 5 23)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = getr regs2 (Z_to_bv 5 20)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
destruct (m2_strs B MT LAWS cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT)
as (SA & SP & SA' & SP' & _).
eapply SRr_bind.
{ apply (rl_check_answer_B B MT MTL LAWS ASTRCMP (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) cur req (if cur =? req then 0x215c0 else 0x21580)).
  - tl_pre T_cmp_STK.
  - etransitivity; [exact R10|]. rewrite E21. exact H21.
  - etransitivity; [exact R11|]. rewrite E10. exact H10.
  - etransitivity; [exact R12|]. rewrite E23. exact H23.
  - exact Hcur.
  - etransitivity; [exact R13|]. rewrite E20. exact H20.
  - exact Hreq.
  - destruct (cur =? req); [exact SA' | exact SP'].
  - exact SA.
  - exact SP. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_cmp_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s4 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (m2_sp_pres _ _ Hpres3); exact HspT)).
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x8252c: a0 = changes, s7 = cur, s4 = req; mv s5,a0; mv a0,s7; mv a1,s4; jal reac_role_cfg_apply_state
   -> 0x8253c *)
Lemma tl_s2 : forall (cx : rs_scx rsegs) POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
getr regs2 (Z_to_bv 5 10) = w64 (rl_changes cur req) ->
getr regs2 (Z_to_bv 5 23) = w64 cur -> getr regs2 (Z_to_bv 5 20) = w64 req ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x8252c regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp Hcur Hreq H10 H23 H20 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CFG_APPLY.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
let R := fresh "R20" in rreg HS (20%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x8253c) by exact R1.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E23 : ew E 23 = getr regs2 (Z_to_bv 5 23)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = getr regs2 (Z_to_bv 5 20)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_cfg_apply_state_B B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) cur req).
  - tl_pre T_leaf_STK.
  - etransitivity; [exact R10|]. rewrite E23. exact H23.
  - exact Hcur.
  - etransitivity; [exact R11|]. rewrite E20. exact H20.
  - exact Hreq. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_leaf_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s3 cx POST cur req regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (m2_sp_pres _ _ Hpres3); exact HspT)).
- exact Hcur.
- exact Hreq.
- etransitivity; [exact HR3|]. unfold A_STR_APPLIED, A_STR_PENDING. reflexivity.
- etransitivity; [exact (Hpres3 21 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R21|].
  rewrite E10. exact H10.
- etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R23|].
  rewrite E23. exact H23.
- etransitivity; [exact (Hpres3 20 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R20|].
  rewrite E20. exact H20.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* 0x82520: s7 = cur, s4 = req; mv a0,s7; mv a1,s4; jal reac_role_cfg_changes -> 0x8252c *)
Lemma tl_s1 : forall (cx : rs_scx rsegs) POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
0 <= cur < 2 ^ 64 -> 0 <= req < 2 ^ 64 ->
getr regs2 (Z_to_bv 5 23) = w64 cur -> getr regs2 (Z_to_bv 5 20) = w64 req ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82520 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST cur req regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp Hcur Hreq H23 H20 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
tl_stage regs2 A_CFG_CHANGES.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
let R := fresh "R20" in rreg HS (20%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x8252c) by exact R1.
assert (E23 : ew E 23 = getr regs2 (Z_to_bv 5 23)) by (subst E; apply ew_Ereg_nat; reflexivity).
assert (E20 : ew E 20 = getr regs2 (Z_to_bv 5 20)) by (subst E; apply ew_Ereg_nat; reflexivity).
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_cfg_changes_B B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) cur req).
  - tl_pre T_leaf_STK.
  - etransitivity; [exact R10|]. rewrite E23. exact H23.
  - exact Hcur.
  - etransitivity; [exact R11|]. rewrite E20. exact H20.
  - exact Hreq. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_leaf_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_leaf_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (tl_s2 cx POST cur req regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3 ltac:(rewrite (m2_sp_pres _ _ Hpres3); exact HspT)).
- exact Hcur.
- exact Hreq.
- exact HR3.
- etransitivity; [exact (Hpres3 23 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R23|].
  rewrite E23. exact H23.
- etransitivity; [exact (Hpres3 20 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact R20|].
  rewrite E20. exact H20.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres tl_L4 _ _ tl_L4_cs Hpres3)).
- tl_kept Hkept3 KE Hkept.
- exact HK.
Qed.

(* ======================================= the tail's head, 0x82504 .. 0x82520 =======================================
   One run with the role cell (atom 20 = s4, the literal cell) as its one region; s9 is the literal rc, so the
   engine decides `bne s9,a1` (0x82510) itself: rc = 1 reads req from the role cell (0x82514), rc = -1 or 0 takes
   req = cur xor 1 (0x8251c). The flags byte is s8 (atom 24): no memory read for it. *)
Ltac tl_head_run :=
lazymatch goal with
| Hpre : rs_pre _ _ ?cx, Hcore : rs_core _ _ _ ?cx _ ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2,
  H25 : getr ?regs2 (Z_to_bv 5 25) = w64 ?v, Hcell : val_mem _ _ (_ + 0x2a0) 4 ?c,
  E20 : bv_unsigned (ew _ 20) = _ |- _ =>
let HS := fresh "HS" in
pose proof (m2_entry 0x82504 [((25%bv : bv 5), SLit v)] [m2_rcell (SLit c)] (mkFacts [] [] []) W2 regs2 []
  mem2) as HS;
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
  [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | rewrite ck_lit; symmetry; exact H25]));
specialize (HS ltac:(vm_compute; reflexivity));
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SLit c) c); [exact E20 | lia | lia | reflexivity | lia | exact Hcell]));
specialize (HS ltac:(cbn; tauto));
specialize (HS ltac:(repeat split));
ch_env Hcore W2 regs2 constr:(@nil word) mem2 0x82504;
tl_run_to m2_awr 0x82520; ck_keep kwr_stk
end.

Lemma tl_head : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 (fl rcv cell : Z),
rs_pre rsegs B cx -> In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 20) = w64 (e_F (x_e rsegs cx) + 0x2a0) ->
getr regs2 (Z_to_bv 5 24) = w64 fl -> 0 <= fl < 256 ->
getr regs2 (Z_to_bv 5 25) = w64 rcv ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2a0) 4 cell ->
(rcv = -1 /\ cell = 0x5a \/ rcv = 0 /\ cell = 0x5a \/ rcv = 1 /\ (cell = 0 \/ cell = 1)) ->
cs_eq tl_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
tl_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs 0x82504 regs2 mem2 md2) POST.
Proof using MTL LAWS ASTRCMP HGOT HSC.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 fl rcv cell Hpre Hpod Hcore Hsp H20 H24 Hfl8 H25 Hcell
Hcase HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
pose proof (tl_bits fl Hfl8) as (Bcur & Breq).
pose proof (tl_cur_range fl) as (Rcur & Rreq).
assert (E20 : bv_unsigned (ew (Ereg regs2 []) 20) = e_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl);
    assert (G : getr regs2 20%bv = w64 (e_F (x_e rsegs cx) + 0x2a0)) by exact H20;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (E24 : ew (Ereg regs2 []) 24 = Z_to_bv 64 fl)
by (rewrite (ew_Ereg_nat regs2 _ 24 24%bv eq_refl); exact H24).
destruct Hcase as [[Hr Hc]|[[Hr Hc]|[Hr [Hc|Hc]]]]; subst rcv cell.
all: tl_head_run.
all: let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
all: let R := fresh "R20" in rreg HS (20%bv : bv 5) R.
all: lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ tl_L4 HS HAE ltac:(vm_compute; reflexivity)) as CL4;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with 0x82520 by (vm_compute; reflexivity)
  end.
all: tl_coreT regs2.
all: assert (H23' : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (Z.b2z (Z.testbit fl 1)))
  by (etransitivity; [exact R23|]; rewrite E24; exact Bcur).
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) (1 - Z.b2z (Z.testbit fl 1)) regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur Rreq H23').
  + etransitivity; [exact R20|]. rewrite E24. exact Breq.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) (1 - Z.b2z (Z.testbit fl 1)) regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur Rreq H23').
  + etransitivity; [exact R20|]. rewrite E24. exact Breq.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) 0 regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur ltac:(lia) H23').
  + exact R20.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
- apply (tl_s1 cx POST (Z.b2z (Z.testbit fl 1)) 1 regs0 W0 mem0 ly2 S2 W2 (ms_regs ms)
    (ms_mem ms) _ Hpre Hpod HcoreT HspT Rcur ltac:(lia) H23').
  + exact R20.
  + exact (cs_eq_trans _ _ _ _ HL4 CL4).
  + intros a Ha Hs. rewrite (KE a Ha (fun x => x)). exact (Hkept a Ha Hs).
  + exact HK.
Qed.

(* ======================================= the two checks ======================================= *)
(* what reaching T from a check means: rs_core, the registers of ch_L as at the check's cut, s9 = vC, s6 = vP,
   s8 = vL and s10 = vF, and every byte outside the callees' stack as at the cut *)
Definition ch_K (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word) (W0 : world rsegs)
(mem0 : word -> option byte) (vC vP vL vF : Z) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq ch_L regs0 regs3 ->
getr regs3 (Z_to_bv 5 25) = w64 vC -> getr regs3 (Z_to_bv 5 22) = w64 vP ->
getr regs3 (Z_to_bv 5 24) = w64 vL -> getr regs3 (Z_to_bv 5 26) = w64 vF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs 0x82504 regs3 mem3 md3) POST.

(* MAL 0x824f8: lw a1,0(s4) (0x5a); mv a0,s9 (-1); jal check_malformed, ra = T 0x82504 *)
Lemma ch_mal : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vP vL vF,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 20) = w64 (e_F (x_e rsegs cx) + 0x2a0) -> getr regs2 (Z_to_bv 5 25) = w64 (-1) ->
getr regs2 (Z_to_bv 5 22) = w64 vP -> getr regs2 (Z_to_bv 5 24) = w64 vL -> getr regs2 (Z_to_bv 5 26) = w64 vF ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2a0) 4 0x5a ->
ch_K cx POST regs2 W2 mem2 (-1) vP vL vF ->
SRr rsegs W2 (cfg_at rsegs 0x824f8 regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vP vL vF Hpre Hcore Hsp H20 H25 H22 H24 H26 Hcell HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E20 : bv_unsigned (ew (Ereg regs2 []) 20) = e_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl);
    assert (G : getr regs2 20%bv = w64 (e_F (x_e rsegs cx) + 0x2a0)) by exact H20;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
(* the run's start: the role cell (s4 = F + 0x2a0, atom 20) as its one region *)
pose proof (m2_entry 0x824f8 [] [m2_rcell (SLit 0x5a)] (mkFacts [] [] []) W2 regs2 [] mem2
  (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SLit 0x5a) 0x5a);
  [exact E20 | lia | lia | reflexivity | lia | exact Hcell])
  ltac:(cbn; tauto) ltac:(repeat split)).
ch_env Hcore W2 regs2 constr:(@nil word) mem2 0x824f8.
m2_run m2_awr. ck_keep kwr_stk.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82504) by exact R1.
assert (E25 : ew E 25 = getr regs2 (Z_to_bv 5 25)) by (subst E; apply ew_Ereg_nat; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [22; 24; 25; 26]%bv HS HAE ltac:(vm_compute; reflexivity)) as C2;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_MALFORMED by (vm_compute; reflexivity)
end.
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_check_malformed_B B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - tl_pre T_check_STK.
  - etransitivity; [exact R10|]. rewrite E25. exact H25.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
- etransitivity; [exact (Hpres3 25 ltac:(unfold acallee_saved; lia))|]. cs_get C2 (25%bv : bv 5). exact H25.
- etransitivity; [exact (Hpres3 22 ltac:(unfold acallee_saved; lia))|]. cs_get C2 (22%bv : bv 5). exact H22.
- etransitivity; [exact (Hpres3 24 ltac:(unfold acallee_saved; lia))|]. cs_get C2 (24%bv : bv 5). exact H24.
- etransitivity; [exact (Hpres3 26 ltac:(unfold acallee_saved; lia))|]. cs_get C2 (26%bv : bv 5). exact H26.
- intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)).
Qed.

(* ABS 0x8245c: lw a1,0(s4) (0x5a); ld s9,0x158(s1) (0); mv a0,s9; jal check_absent, ra = 0x8246c; then 0x8246c
   ld s10,0x38(s1); ld s6,0x140(s1); ld s8,0x40(s1); j T (the real frame's three cells as the one region, env slots
   32 / 33 / 34 = vF / vL / vP) *)
Lemma ch_abs : forall (cx : rs_scx rsegs) POST ly2 S2 W2 regs2 mem2 md2 vF vL vP,
rs_pre rsegs B cx -> rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = e_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)) ->
getr regs2 (Z_to_bv 5 20) = w64 (e_F (x_e rsegs cx) + 0x2a0) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2a0) 4 0x5a ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x158) 8 0 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x38) 8 vF -> 0 <= vF < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x40) 8 vL -> 0 <= vL < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x140) 8 vP -> 0 <= vP < 2 ^ 64 ->
ch_K cx POST regs2 W2 mem2 0 vP vL vF ->
SRr rsegs W2 (cfg_at rsegs 0x8245c regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST ly2 S2 W2 regs2 mem2 md2 vF vL vP Hpre Hcore Hsp H9 H20 Hcell H158 H38 HvF H40 HvL H140 HvP HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof asan_consts as (C1 & _).
pose proof m2_wx as Hwx. pose proof m2_segs_low as Hsegs.
assert (E20 : bv_unsigned (ew (Ereg regs2 []) 20) = e_F (x_e rsegs cx) + 0x2a0)
by (rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl);
    assert (G : getr regs2 20%bv = w64 (e_F (x_e rsegs cx) + 0x2a0)) by exact H20;
    rewrite G; unfold w64; apply unsigned_lit_small; lia).
assert (E9 : bv_unsigned (ew (Ereg regs2 []) 9) = e_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl);
    assert (G : getr regs2 9%bv = w64 (e_R (x_e rsegs cx))) by exact H9;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
pose proof (proj1 Hcore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
(* the first run's start: the role cell (atom 20) and the real-frame cell R+0x158 (atom 9 = R), read only *)
pose proof (m2_entry 0x8245c []
  [m2_rcell (SLit 0x5a); m2_frame 0x158 0x160 0 0 [YP09.mkChunk 0x158 (CVal 8 (SLit 0))]]
  (mkFacts [] [] []) W2 regs2 [] mem2 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ apply (m2_rcell_ok _ W2 mem2 (e_F (x_e rsegs cx)) (SLit 0x5a) 0x5a);
    [exact E20 | lia | lia | reflexivity | lia | exact Hcell]
  | apply (m2_frame_ok _ W2 mem2 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres0 | lia |];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val rsegs _ _ _ 0x158 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact H158] ])
  ltac:(change (((bv_unsigned (ew (Ereg regs2 []) 20) + 4 <= bv_unsigned (ew (Ereg regs2 []) 9) + 0x158 \/
                  bv_unsigned (ew (Ereg regs2 []) 9) + 0x160 <= bv_unsigned (ew (Ereg regs2 []) 20) + 0) /\ True) /\
                (True /\ True));
        rewrite E20, E9; refine (conj (conj _ I) (conj I I)); left; unfold T_SEG_STK, ASTACK in *; lia)
  ltac:(repeat split)).
ch_env Hcore W2 regs2 constr:(@nil word) mem2 0x8245c.
m2_run m2_awr. ck_keep kwr_stk.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R25" in rreg HS (25%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x8246c) by exact R1.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with A_CHECK_ABSENT by (vm_compute; reflexivity)
end.
tl_coreT regs2.
eapply SRr_bind.
{ apply (rl_check_absent_B B MT MTL LAWS (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - tl_pre T_check_STK.
  - exact R10.
  - exact R11. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ _ W3 c3
  Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf) Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
(* the state at 0x8246c *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (Hkept3 a Ha ltac:(unfold T_check_STK, T_SEG_STK, ASTACK in *; lia) (fun x => x)).
  exact (KE a Ha (fun x => x)). }
assert (CL3 : cs_eq ch_L regs2 regs3) by exact (cs_eq_trans _ _ _ _ CL (cs_eq_of_pres ch_L _ _ ch_L_cs Hpres3)).
assert (H93 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx))) by (cs_get CL3 (9%bv : bv 5); exact H9).
assert (R253 : getr regs3 (Z_to_bv 5 25) = w64 0)
by (etransitivity; [exact (Hpres3 25 ltac:(unfold acallee_saved; lia))|]; exact R25).
assert (H383 : val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x38) 8 vF).
{ eapply (val_mem_kept rsegs); [|exact H38]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
assert (H403 : val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x40) 8 vL).
{ eapply (val_mem_kept rsegs); [|exact H40]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
assert (H1403 : val_mem rsegs (mrestrict (w_H W3) mem3) (e_R (x_e rsegs cx) + 0x140) 8 vP).
{ eapply (val_mem_kept rsegs); [|exact H140]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia | unfold T_SEG_STK, ASTACK; lia]. }
clear dependent ms. clear dependent E.
pose proof (proj1 Hcore3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (E9 : bv_unsigned (ew (Ereg regs3 [Z_to_bv 64 vF; Z_to_bv 64 vL; Z_to_bv 64 vP]) 9) = e_R (x_e rsegs cx))
by (rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); assert (G : getr regs3 9%bv = w64 (e_R (x_e rsegs cx))) by exact H93;
    rewrite G; unfold w64; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
pose proof (m2_entry 0x8246c []
  [m2_frame 0 0x148 0 0 [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 33 0));
                         YP09.mkChunk 0x140 (CVal 8 (SOff 34 0))]]
  (mkFacts [] [] []) W3 regs3 [Z_to_bv 64 vF; Z_to_bv 64 vL; Z_to_bv 64 vP] mem3 (Forall_nil _) eq_refl) as HS.
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil];
  apply (m2_frame_ok _ W3 mem3 (e_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx)); [exact E9 | lia | lia | exact Hpres | lia |];
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  [ apply (chunk_ok_val rsegs _ _ _ 0x38 8 (SOff 32 0) vF); [| cbn; lia | cbn; lia | exact H383];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | apply (chunk_ok_val rsegs _ _ _ 0x40 8 (SOff 33 0) vL); [| cbn; lia | cbn; lia | exact H403];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
  | apply (chunk_ok_val rsegs _ _ _ 0x140 8 (SOff 34 0) vP); [| cbn; lia | cbn; lia | exact H1403];
    apply bv_eq; rewrite denot_SOff, Z.add_0_r; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth];
    rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia ])
  ltac:(cbn; tauto) ltac:(repeat split)).
ch_env Hcore3 W3 regs3 constr:([Z_to_bv 64 vF; Z_to_bv 64 vL; Z_to_bv 64 vP]) mem3 0x8246c.
m2_run m2_awr. ck_keep kwr_stk.
let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
let R := fresh "R22" in rreg HS (22%bv : bv 5) R.
let R := fresh "R24" in rreg HS (24%bv : bv 5) R.
assert (E32 : ew E 32 = Z_to_bv 64 vF) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 vL) by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 vP) by (subst E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ ch_L HS HAE ltac:(vm_compute; reflexivity)) as CL';
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [25]%bv HS HAE ltac:(vm_compute; reflexivity)) as C25;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs3 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with 0x82504 by (vm_compute; reflexivity)
end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdT)
end.
- apply (m2_core_step B MT MTL cx _ ly3 S3 W3 regs3 mem3 md3 ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ Hcore3
    ltac:(eassumption) (tl_r234 _ _ C234) eq_refl (Permutation_refl _)); [kio | apply (mo_le_refl MT MTL) |].
  intros a Ha _ _. exact (KE a Ha (fun x => x)).
- exact (cs_eq_trans _ _ _ _ CL3 CL').
- etransitivity; [exact (C25 25%bv ltac:(cbv [In]; left; reflexivity))|]. exact R253.
- etransitivity; [exact R22|]. exact E34.
- etransitivity; [exact R24|]. exact E33.
- etransitivity; [exact R26|]. exact E32.
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
Hypothesis HGOT : as_got_shadow B = 0x9aad0.
Hypothesis HSC : as_shadow_cell B = 0xa3678.

(* the bytes a cut of this half names and no call or run of the half writes: below the allocator's ceiling, or
   in the real frame at R and above *)
Lemma m2t_far : forall cx : rs_scx rsegs, rs_pre rsegs B cx -> forall a,
(0 <= a < alloc_ceiling) \/ (e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x200) ->
0 <= a < 2 ^ 64 /\ ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)).
Proof.
intros cx Hpre a Ha. pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof asan_consts as (C1 & _). unfold T_SEG_STK, ASTACK in *. lia.
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
(* rs_chk_base at a state whose memory agrees with the cut's outside the callees' stack *)
Lemma m2t_base_kept : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_chk_base (fx := fx) rsegs B MT cx fx2 rec ly3 S3 W3 regs3 mem3 md3.
Proof using LAWS.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1) Hcore3 K3.
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2_pp B LAWS cx Hpre) as (P4096 & Pceil & _).
pose proof (m2t_far cx Hpre) as Far.
pose proof m2_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
split; [exact Hcore3|]. split; [exact Hfxk|].
split; [apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh); intros i Hi;
  lazymatch type of Hi with context [Z.of_nat (length ?p)] =>
    let n := eval vm_compute in (Z.of_nat (length p)) in change (Z.of_nat (length p)) with n in Hi end;
  apply K3; apply Far; left; unfold shadow_addr, SHADOW_OFF;
  assert (e_F (x_e rsegs cx) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia);
  assert (0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia); lia|].
split; [eapply (rm_rom_kept rsegs); [exact Hrom|]; intros a (sg & Hsg & _ & Hr);
  apply K3; apply Far; left; pose proof (Hsegs a ltac:(exists sg; split; [exact Hsg | exact Hr])); unfold kLowMemEnd in *; lia|].
split; [unfold rs_pp_at in *; apply (m2t_garr8_kept _ _ _ _ _ _ Hpp); intros j Hj;
  unfold rs_u8s in Hj; rewrite length_map in Hj; pose proof (Layout.length_pp_bytes rec Hwf) as HL0;
  apply K3; apply Far; left; lia|].
split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
Qed.

(* the T cut, built at a state whose memory agrees with a check cut's outside the callees' stack and whose
   registers of ch_L agree, from the check cut's facts (its list holds rs_L_chk and the cells R+0x38 = F,
   R+0x140 = pp) and the four registers s9 = rc, s6 = pp, s8 = fl, s10 = F *)
Lemma ch_cut_T : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LCell XR 0x38, e_F (x_e rsegs cx)); (LCell XR 0x140, e_pp (x_e rsegs cx))]) ->
rs_role_at rsegs cx rec W2 mem2 ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq ch_L regs2 regs3 ->
getr regs3 (Z_to_bv 5 25) = w64 (snd (rs_PA rsegs cx rec)) ->
getr regs3 (Z_to_bv 5 22) = w64 (e_pp (x_e rsegs cx)) ->
getr regs3 (Z_to_bv 5 24) = w64 (e_fl (x_e rsegs cx)) ->
getr regs3 (Z_to_bv 5 26) = w64 (e_F (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_T (fx := fx) rsegs B MT cx fx2 rec ly3 S3 W3 regs3 mem3 md3.
Proof using LAWS.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hat Hrole Hcore3 HL H25 H22 H24 H26 K3.
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2t_far cx Hpre) as Far.
pose proof asan_consts as (C1 & _).
unfold rs_at_cx, rs_at in Hat.
split; [|split].
- exact (m2t_base_kept cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hcore3 K3).
- unfold rs_at_cx, rs_at, rs_L_chk. cbn [app]. repeat apply Forall_cons; try apply Forall_nil;
  cbn [rl_at rl_xv fst snd];
  first [ exact H25 | exact H22 | exact H24 | exact H26 | at_reg Hat HL | at_cell Hat K3 Far ].
- unfold rs_role_at in *. eapply (val_mem_kept rsegs); [|exact Hrole]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
  apply K3; apply Far; left; lia.
Qed.

(* the C4 cut from the T cut, carried to a state whose memory agrees outside the callees' stack and whose six
   registers of tl_L4 agree *)
Lemma tl_cut_C4 : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_cut_T (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq tl_L4 regs2 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_C4 (fx := fx) rsegs B MT cx fx2 ly3 S3 W3 regs3 mem3 md3.
Proof using LAWS.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre (Hbase & Hat & _) Hcore3 HL K3.
pose proof (m2t_base_kept cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hcore3 K3)
as (_ & Hfxk & Hfsh & _).
pose proof (m2_frameF B LAWS cx Hpre) as (F32 & F4096 & Fceil & _).
pose proof (m2t_far cx Hpre) as Far.
pose proof asan_consts as (C1 & _).
unfold rs_at_cx, rs_at in Hat.
split; [exact Hcore3|]. split; [exact Hfxk|]. split; [|exact Hfsh].
unfold rl_cut. cbn [hi_L4 role_himg_B]. repeat apply Forall_cons; try apply Forall_nil; cbn [rl_at rl_xv fst snd];
rewrite ?Z.add_0_r; first [ at_reg Hat HL | at_cell Hat K3 Far ].
Qed.

(* ---- W11b TAIL: T 0x82504 -> C4 0x82570 ---- *)
Theorem rl_m02_tail_B : rs_piece_W11b_tail_stmt rsegs B MT.
Proof using MTL LAWS ASTRCMP HGOT HSC.
unfold rs_piece_W11b_tail_stmt. intros cx POST inp Hst HC4.
unfold rs_from_T. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HT.
destruct Hst as (Hpre & _).
pose proof HT as (Hbase & Hat & Hrole).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (m2_stack B cx Hpre) as (HR & _).
pose proof Hpre as Hp. unfold rs_pre, rl_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfl & _).
unfold rs_at_cx, rs_at in Hat.
at_get Hat (LReg 20) (e_F (x_e rsegs cx) + 0x2a0) A20.
at_get Hat (LReg 24) (e_fl (x_e rsegs cx)) A24.
at_get Hat (LReg 25) (snd (rs_PA rsegs cx rec)) A25.
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
  (e_fl (x_e rsegs cx)) (snd (rs_PA rsegs cx rec)) (rs_rcell (fst (rs_PA rsegs cx rec))) Hpre Hpod Hcore Hsp A20 A24
  Hfl A25 Hrole Hcase).
- intros r Hr. reflexivity.
- intros a _ _. reflexivity.
- intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL K3.
  apply (HC4 fx2 ly3 S3 W3 regs3 mem3 md3).
  exact (tl_cut_C4 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre HT Hcore3 HL K3).
Qed.

(* ---- W11b CHECKS: ABS 0x8245c -> T, MAL 0x824f8 -> T ---- *)
Theorem rl_m02_checks_B : rs_piece_W11b_checks_stmt rsegs B MT.
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
  pose proof Hat as Hat'. unfold rs_at_cx, rs_at in Hat'.
  at_get Hat' (LReg 9) (e_R (x_e rsegs cx)) A9.
  at_get Hat' (LReg 20) (e_F (x_e rsegs cx) + 0x2a0) A20.
  at_get Hat' (LCell XR 0x158) 0 AC158.
  at_get Hat' (LCell XR 0x38) (e_F (x_e rsegs cx)) AC38.
  at_get Hat' (LCell XR 0x40) (e_fl (x_e rsegs cx)) AC40.
  at_get Hat' (LCell XR 0x140) (e_pp (x_e rsegs cx)) AC140.
  assert (AC158' : val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x158) 8 0) by exact AC158.
  assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  pose proof Hrole as Hcell. unfold rs_role_at in Hcell. rewrite Hn in Hcell. cbn [rs_rcell] in Hcell.
  apply (ch_abs (fx := fx2) B MT MTL LAWS cx POST ly2 S2 W2 regs2 mem2 md2 _ _ _ Hpre Hcore Hsp A9 A20 Hcell AC158'
    AC38 ltac:(apply Z.mod_pos_bound; lia) AC40 ltac:(apply Z.mod_pos_bound; lia)
    AC140 ltac:(apply Z.mod_pos_bound; lia)).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H25 H22 H24 H26 K3.
  apply (HT fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (ch_cut_T cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + at_sub Hat'.
  + exact Hrole.
  + exact Hcore3.
  + exact HL.
  + rewrite H0. exact H25.
  + rewrite H22. apply m2_w64_mod.
  + rewrite H24. apply m2_w64_mod.
  + rewrite H26. apply m2_w64_mod.
  + exact K3.
- unfold rs_from_MAL. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HM.
  destruct HM as (Hbase & Hat & Hrole & Hn & H1).
  pose proof Hbase as (Hcore & _).
  pose proof Hat as Hat'. unfold rs_at_cx, rs_at in Hat'.
  at_get Hat' (LReg 20) (e_F (x_e rsegs cx) + 0x2a0) A20.
  at_get Hat' (LReg 25) (-1) A25.
  at_get Hat' (LReg 22) (e_pp (x_e rsegs cx)) A22.
  at_get Hat' (LReg 24) (e_fl (x_e rsegs cx)) A24.
  at_get Hat' (LReg 26) (e_F (x_e rsegs cx)) A26.
  assert (Hsp : spZ regs2 = e_R (x_e rsegs cx)).
  { rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
  pose proof Hrole as Hcell. unfold rs_role_at in Hcell. rewrite Hn in Hcell. cbn [rs_rcell] in Hcell.
  apply (ch_mal (fx := fx2) B MT MTL LAWS cx POST ly2 S2 W2 regs2 mem2 md2 _ _ _ Hpre Hcore Hsp A20 A25 A22 A24 A26
    Hcell).
  intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL H25 H22 H24 H26 K3.
  apply (HT fx2 ly3 S3 W3 regs3 mem3 md3 rec).
  apply (ch_cut_T cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase).
  + at_sub Hat'.
  + exact Hrole.
  + exact Hcore3.
  + exact HL.
  + rewrite H1. exact H25.
  + exact H22.
  + exact H24.
  + exact H26.
  + exact K3.
Qed.
End m.
