(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 246 of its 275 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkB.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the registers (n in s9, the part string in s8, t in s5, the part pointer in s6), the frame slots (parts[1..3] at R+0x160.., e.body at R+0x108) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkB.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the registers (n in s9, the part string in s10, t in s11, the part pointer in s2, the part's length in s6), the frame slots (parts[1..3] at R+0x1a0.., e62.body at R+0x130) and the frame bound (R + 0x220 <= 2^47) are image B's; E1 is image B's 0x816fc .. 0x81714: the reloads of R+0x158 and R+0x150 and the UBSan test of e62.body + n against the cell R+0x100 (~(F + 0x218)), decided by the engine from the cell's atom range, before the NUL's address; lib/A/RtPgW7bBase.v is lib/AU/RtPgW7bBaseB.v; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): blocks B, C, D and E1 of the walk of
   LLVMFuzzerTestOneInput from 0x8160c (lib/AU/RtPgW7bBaseB.v). Proves no function (kind: segment lemma).

   No block holds an instrumented check, so each is one run of the plain engine (aj_run_to); every branch is
   decided by the start state's atom facts or by literal offsets of one atom.
   B,  0x816a8 .. 0x816c8 (pod.h:256-258, one turn's clamp and memcpy(t + n, parts[i], l)):
     mv s6,a0; add a0,a0,s9; addi a1,zero,0x5f; bgeu a1,a0 -> 0x816bc (taken: l <= 21, n <= 40)
     add a0,s11,s9; mv a1,s10; mv a2,s6; jal __asan_memcpy
   C,  0x816cc .. 0x816a4 (i = 0 .. 2: n += l, the next part, strlen(parts[i+1])):
     addi s2,s2,8; add s9,s6,s9; addi a0,s1,0x1b8; bne s2,a0 -> 0x8169c (taken: s2 = R + 0x1a0 + 8 i)
     ld s10,0(s2); mv a0,s10; jal strlen
   D,  0x816cc .. 0x816f8 (i = 3: n += l, the 95 clamp of ent_text, memcpy(e62.body, t, n)):
     addi s2,s2,8; add s9,s6,s9; addi a0,s1,0x1b8; bne s2,a0 (not taken: s2 = R + 0x1b8)
     addi a0,zero,0x5f; bltu s9,a0 -> 0x816e8 (taken: n + l <= 61); ld s10,0x130(s1); mv a0,s10; mv a1,s11;
     mv a2,s9; jal __asan_memcpy
   E1, 0x816fc .. 0x81714 (the reloads, the UBSan test, the NUL's address):
     ld s2,0x158(s1); ld s6,0x150(s1); ld a0,0x100(s1); bgeu a0,s9 -> 0x81710 (taken; the other arm `j` 0x83098)
     add a0,s10,s9; addi s9,s9,1
   A frame slot the block reads (parts[i+1] at R + 0x1a0 + 8 i, e62.body at R + 0x130) is a read-only region of
   atom 9 (s1 = R) whose one chunk holds the extra atom 32, the slot's value; E1's three cells are the extra atoms
   32 .. 34 of one such region, and the cell R+0x100 (which holds ~(F + 0x218)) carries the closed range
   [2^63, 2^64 - 1], so that `bgeu a0,s9` against n in [0, 95] is decided by computation. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Lemma w7b_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
rewrite zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.

(* the register r of the engine's last state: its symbolic value, computed *)
Ltac w7b_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.

(* a read-only 8-byte slot of the frame at R + lo whose chunk holds the extra atom 32 *)
Definition w7b_slot (lo : Z) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo (lo + 8) lo lo [YP09.mkChunk lo (CVal 8 (SOff 32 0))].
(* the start state of C and D: s2 = R + c, the slot at R + so, the facts on R, n and l *)
Definition ssb_CD (c so : Z) : sstate :=
mkSS W7B_AFTER_MEMCPY (sr_set sr_atoms 18%bv (SOff 9 c)) [w7b_slot so] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x220) 4); (25%nat, mkAF 0 40 0); (22%nat, mkAF 0 21 0)] [] []).
Lemma w7b_CD_nowr : forall E c so a, ~ in_wrange E (ss_mem (ssb_CD c so)) a.
Proof. intros E c so a (r & [<-|[]] & Hb). cbn [w7b_slot YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.
Lemma w7b_slot_wf : forall so, regions_wf [w7b_slot so] = true.
Proof.
intros so. cbn [regions_wf]. unfold region_wf, chunk_inside, YP09.c_len, cv_len, w7b_slot.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_val forallb].
repeat match goal with |- context [?a <=? ?b] =>
  let H := fresh in assert (H : (a <=? b) = true) by (apply Z.leb_le; lia); rewrite H; clear H end.
reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w7b_CD_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) R n l v c so,
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + c) -> 0 <= c <= 0x220 ->
getr regs 25 = w64 n -> getr regs 22 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
0 <= so -> so + 8 <= 0x220 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + so) 8 v -> 0 <= v < 2 ^ 64 ->
st_ok rsegs (Ereg regs [Z_to_bv 64 v]) (ssb_CD c so)
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_AFTER_MEMCPY) memc (seg_rom rsegs))).
Proof.
intros W memc regs R n l v c so H9 HR1 HR2 HR3 H18 Hc H25 H22 Hn Hl Hso1 Hso2 Hval Hv.
assert (E9 : ew (Ereg regs [Z_to_bv 64 v]) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E25 : ew (Ereg regs [Z_to_bv 64 v]) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E22 : ew (Ereg regs [Z_to_bv 64 v]) 22 = w64 l) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
rewrite restrict_mkst_fx. unfold ssb_CD. apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
  rewrite H18, denot_lit_U, (U_atom_off _ 9 R c E9) by lia. reflexivity.
- apply w7b_slot_wf.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, w7b_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R so 8 (SOff 32 0) v); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hval].
  rewrite w7b_den0. exact (ew_Ereg_extra regs [Z_to_bv 64 v] 0).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E9, E25, E22. unfold w64. rewrite !unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
  repeat split; first [exact HR3 | lia].
Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================== B: 0x816a8 -> 0x518b8 ======================== *)
Definition ssb_B : sstate :=
mkSS W7B_AFTER_STRLEN sr_atoms [] None (mkFacts [(10%nat, mkAF 0 21 0); (25%nat, mkAF 0 40 0)] [] []).

Lemma w7b_B : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) l n x t,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 l -> 0 <= l <= 21 -> getr regs 25 = w64 n -> 0 <= n <= 40 ->
getr regs 26 = w64 x -> getr regs 27 = w64 t -> 0 <= t -> t + 0x80 <= 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_STRLEN) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_MEMCPY regs memc mdc [1; 10; 11; 12; 22]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7B_AFTER_MEMCPY /\ getr regs2 10 = w64 (t + n) /\ getr regs2 11 = w64 x /\
 getr regs2 12 = w64 l /\ getr regs2 22 = w64 l)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs l n x t HJ H10 Hl H25 Hn H26 H27 Ht Ht2.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 10 = w64 l) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E25 : ew (Ereg regs []) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E26 : ew (Ereg regs []) 26 = w64 x) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew (Ereg regs []) 27 = w64 t) by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (HS : st_ok rsegs (Ereg regs []) ssb_B (restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_AFTER_STRLEN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ssb_B f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E10, E25. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
aj_run_to w7b_tbl_ok HS HJ W7B_MEMCPY.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + cbv beta.
    split; [w7b_reg HS; reflexivity|].
    split; [w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 27 t E27) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E26|].
    split; w7b_reg HS; rewrite w7b_den0; exact E10.
Qed.

(* ======================== C: 0x816cc -> 0x421ec (i = 0 .. 2) ======================== *)
Lemma w7b_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i : nat) R n l x',
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> (i < 3)%nat ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + 0x198 + 8 * Z.of_nat i) -> getr regs 25 = w64 n -> getr regs 22 = w64 l ->
0 <= n <= 40 -> 0 <= l <= 21 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x1a0 + 8 * Z.of_nat i) 8 x' -> 0 <= x' < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_STRLEN regs memc mdc [1; 10; 18; 25; 26]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7B_AFTER_STRLEN /\ getr regs2 10 = w64 x' /\ getr regs2 26 = w64 x' /\
 getr regs2 18 = w64 (R + 0x1a0 + 8 * Z.of_nat i) /\ getr regs2 25 = w64 (n + l))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i R n l x' HJ Hi H9 HR1 HR2 HR3 H18 H25 H22 Hn Hl Hval Hx.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (Ho : 8 * Z.of_nat i = 0 \/ 8 * Z.of_nat i = 8 \/ 8 * Z.of_nat i = 16) by lia.
remember (8 * Z.of_nat i) as o eqn:Hoi. clear Hoi Hi i.
assert (E9 : ew (Ereg regs [Z_to_bv 64 x']) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E25 : ew (Ereg regs [Z_to_bv 64 x']) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E22 : ew (Ereg regs [Z_to_bv 64 x']) 22 = w64 l) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew (Ereg regs [Z_to_bv 64 x']) 32 = w64 x') by exact (ew_Ereg_extra regs [Z_to_bv 64 x'] 0).
assert (H18' : getr regs 18 = w64 (R + (0x198 + o))) by (rewrite H18; unfold w64; f_equal; lia).
assert (Hval' : val_mem rsegs (mrestrict (w_H W) memc) (R + (0x1a0 + o)) 8 x')
  by (replace (R + (0x1a0 + o)) with (R + 0x1a0 + o) by lia; exact Hval).
pose proof (w7b_CD_entry W memc regs R n l x' (0x198 + o) (0x1a0 + o) H9 HR1 HR2 HR3 H18' ltac:(lia) H25 H22 Hn Hl
  ltac:(lia) ltac:(lia) Hval' Hx) as HS.
clear H18 Hval H18' Hval'.
destruct Ho as [-> | [-> | ->]].
all: aj_run_to w7b_tbl_ok HS HJ W7B_STRLEN; [awr_ok_tac |
  eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ];
  [ eapply (w7b_regs_kept _ _ ms regs [Z_to_bv 64 x'] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity]
  | intros a Ha Hz;
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7b_CD_nowr _ _ _ a Hw) a Ha Hz)
  | cbv beta;
    split; [w7b_reg HS; reflexivity|];
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|];
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|];
    split; [w7b_reg HS; rewrite denot_lit_U, (U_atom_off _ 9 R _ E9) by lia; unfold w64; f_equal; lia|];
    w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 22 l E22) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia ] ].
Qed.

(* ======================== D: 0x816cc -> 0x518b8 (i = 3) ======================== *)
Lemma w7b_D : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R n l t eb,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 (R + 0x1b0) -> getr regs 25 = w64 n -> getr regs 22 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
getr regs 27 = w64 t ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 eb -> 0 <= eb < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_MEMCPY regs memc mdc [1; 10; 11; 12; 18; 25; 26]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7B_AFTER_TEXT /\ getr regs2 10 = w64 eb /\ getr regs2 11 = w64 t /\
 getr regs2 12 = w64 (n + l) /\ getr regs2 26 = w64 eb /\ getr regs2 25 = w64 (n + l))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R n l t eb HJ H9 HR1 HR2 HR3 H18 H25 H22 Hn Hl H27 Hval Heb.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E25 : ew (Ereg regs [Z_to_bv 64 eb]) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E27 : ew (Ereg regs [Z_to_bv 64 eb]) 27 = w64 t) by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E22 : ew (Ereg regs [Z_to_bv 64 eb]) 22 = w64 l) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew (Ereg regs [Z_to_bv 64 eb]) 32 = w64 eb) by exact (ew_Ereg_extra regs [Z_to_bv 64 eb] 0).
pose proof (w7b_CD_entry W memc regs R n l eb 0x1b0 0x130 H9 HR1 HR2 HR3 H18 ltac:(lia) H25 H22 Hn Hl
  ltac:(lia) ltac:(lia) Hval Heb) as HS.
aj_run_to w7b_tbl_ok HS HJ W7B_MEMCPY.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [Z_to_bv 64 eb] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7b_CD_nowr _ _ _ a Hw) a Ha Hz).
  + cbv beta.
    split; [w7b_reg HS; reflexivity|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E27|].
    split; [w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 22 l E22) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7b_reg HS; rewrite w7b_den0; exact E32|].
    w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 22 l E22) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia.
Qed.

(* ======================== E1: 0x816fc -> 0x81718 ======================== *)
(* the three cells E1 reads, R+0x158 (&pp->len), R+0x150 (&e62) and R+0x100 (~(F + 0x218)), as the extra atoms
   32, 33, 34 of one read-only region based on s1 (atom 9); the closed range of atom 34 decides the UBSan test *)
Definition e1b_extra (v158 v150 v100 : Z) : list word := [w64 v158; w64 v150; w64 v100].
Definition ssb_E1 : sstate :=
mkSS W7B_AFTER_TEXT sr_atoms
[YP09.mkRegion (Some 9%nat) 0x100 0x160 0x100 0x100
   [YP09.mkChunk 0x100 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x150 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))]] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x220) 4); (25%nat, mkAF 0 95 0);
          (34%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] []).
Lemma w7b_E1_nowr : forall E a, ~ in_wrange E (ss_mem ssb_E1) a.
Proof. intros E a (r & [<-|[]] & Hb). cbn [YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.

Lemma w7b_E1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R eb n v158 v150 v100,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 26 = w64 eb -> getr regs 25 = w64 n -> 0 <= eb -> 0 <= n <= 95 -> eb + n + 1 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 v158 -> 0 <= v158 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 v150 -> 0 <= v150 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 v100 -> 2 ^ 63 <= v100 < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_AFTER_TEXT) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_E2 regs memc mdc [10; 18; 22; 25]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (eb + n) /\ getr regs2 25 = w64 (n + 1) /\
 getr regs2 18 = w64 v158 /\ getr regs2 22 = w64 v150)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R eb n v158 v150 v100
HJ H9 HR1 HR2 HR3 H26 H25 Heb Hn Hsum V158 H158 V150 H150 V100 H100.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
set (X := e1b_extra v158 v150 v100).
assert (E9 : ew (Ereg regs X) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew (Ereg regs X) 26 = w64 eb) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E25 : ew (Ereg regs X) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (X32 : ew (Ereg regs X) 32 = w64 v158) by exact (ew_Ereg_extra regs X 0).
assert (X33 : ew (Ereg regs X) 33 = w64 v150) by exact (ew_Ereg_extra regs X 1).
assert (X34 : ew (Ereg regs X) 34 = w64 v100) by exact (ew_Ereg_extra regs X 2).
assert (B9 : bv_unsigned (ew (Ereg regs X) 9) = R) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs X) ssb_E1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_AFTER_TEXT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssb_E1. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val rsegs _ _ R 0x100 8 (SOff 34 0) v100);
      [ apply (RtPgStepsB.rtsb_den_atom _ 34 v100 X34 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V100 ].
    + apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 33 0) v150);
      [ apply (RtPgStepsB.rtsb_den_atom _ 33 v150 X33 H150) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V150 ].
    + apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 32 0) v158);
      [ apply (RtPgStepsB.rtsb_den_atom _ 32 v158 X32 H158) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V158 ].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E9, E25, X34. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
    repeat split; first [exact HR3 | lia]. }
aj_run_to w7b_tbl_ok HS HJ W7B_E2.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs X (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7b_E1_nowr _ a Hw) a Ha Hz).
  + cbv beta.
    split; [w7b_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 26 eb E26), (U_atom _ 25 n E25) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7b_reg HS; rewrite denot_lit_U, (U_atom_off _ 25 n 1 E25) by lia; reflexivity|].
    split; [w7b_reg HS; rewrite w7b_den0; exact X32|].
    w7b_reg HS; rewrite w7b_den0; exact X33.
Qed.
End d.
End b.

Print Assumptions w7b_B.
Print Assumptions w7b_C.
Print Assumptions w7b_D.
Print Assumptions w7b_E1.
