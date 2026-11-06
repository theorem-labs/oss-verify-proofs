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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 203 of its 237 lines of code are new or changed and 256 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkB.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the registers (n in s9, the part string in s8, t in s5, the part pointer in s6), the frame slots (parts[1..3] at R+0x160.., e.body at R+0x108) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): blocks B, C, D and E1 of the walk of
   LLVMFuzzerTestOneInput from 0x8150c (lib/A/RtPgW7bBase.v). Proves no function (kind: segment lemma).

   No block holds an instrumented check, so each is one run of the plain engine (aj_run_to); every branch is
   decided by the start state's atom facts or by literal offsets of one atom.
   B,  0x8159c .. 0x815bc (pod.h:256-258, one turn's clamp and memcpy(t + n, parts[i], l)):
     mv s11,a0; add a0,a0,s9; addi a1,zero,0x5f; bgeu a1,a0 -> 0x815b0 (taken: l <= 21, n <= 40)
     add a0,s5,s9; mv a1,s8; mv a2,s11; jal __asan_memcpy
   C,  0x815c0 .. 0x81598 (i = 0 .. 2: n += l, the next part, strlen(parts[i+1])):
     addi s6,s6,8; add s9,s11,s9; addi a0,s1,0x178; bne s6,a0 -> 0x81590 (taken: s6 = R + 0x160 + 8 i)
     ld s8,0(s6); mv a0,s8; jal strlen
   D,  0x815c0 .. 0x815ec (i = 3: n += l, the 95 clamp of ent_text, memcpy(e.body, t, n)):
     addi s6,s6,8; add s9,s11,s9; addi a0,s1,0x178; bne s6,a0 (not taken: s6 = R + 0x178)
     addi a0,zero,0x5f; bltu s9,a0 -> 0x815dc (taken: n + l <= 61); ld s6,0x108(s1); mv a0,s6; mv a1,s5; mv a2,s9;
     jal __asan_memcpy
   E1, 0x815f0 .. 0x815f4 (the NUL's address): add a0,s6,s9; addi s9,s9,1.
   A frame slot the block reads (parts[i+1] at R + 0x160 + 8 i, e.body at R + 0x108) is a read-only region of atom 9
   (s1 = R) whose one chunk holds the extra atom 32, the slot's value. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgW7bBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Lemma w7_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
rewrite zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.

(* the register r of the engine's last state: its symbolic value, computed *)
Ltac w7_reg HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
lazymatch type of HS with st_ok ?sg ?Ev ?ssv (restrict ?H _) =>
rewrite (st_ok_restrict_reg sg H Ev ssv m r HS);
let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end end.

(* a read-only 8-byte slot of the frame at R + lo whose chunk holds the extra atom 32 *)
Definition w7_slot (lo : Z) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo (lo + 8) lo lo [YP09.mkChunk lo (CVal 8 (SOff 32 0))].
(* the start state of C and D: s6 = R + c, the slot at R + so, the facts on R, n and l *)
Definition ss_CD (c so : Z) : sstate :=
mkSS W7_AFTER_MEMCPY (sr_set sr_atoms 22%bv (SOff 9 c)) [w7_slot so] None
(mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x1e0) 4); (25%nat, mkAF 0 40 0); (27%nat, mkAF 0 21 0)] [] []).
Lemma w7_CD_nowr : forall E c so a, ~ in_wrange E (ss_mem (ss_CD c so)) a.
Proof. intros E c so a (r & [<-|[]] & Hb). cbn [w7_slot YP09.r_wlo YP09.r_whi] in Hb. lia. Qed.
Lemma w7_slot_wf : forall so, regions_wf [w7_slot so] = true.
Proof.
intros so. cbn [regions_wf]. unfold region_wf, chunk_inside, YP09.c_len, cv_len, w7_slot.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_val forallb].
repeat match goal with |- context [?a <=? ?b] =>
  let H := fresh in assert (H : (a <=? b) = true) by (apply Z.leb_le; lia); rewrite H; clear H end.
reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w7_CD_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) R n l v c so,
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 22 = w64 (R + c) -> 0 <= c <= 0x1e0 ->
getr regs 25 = w64 n -> getr regs 27 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
0 <= so -> so + 8 <= 0x1e0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + so) 8 v -> 0 <= v < 2 ^ 64 ->
st_ok rsegs (Ereg regs [Z_to_bv 64 v]) (ss_CD c so)
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7_AFTER_MEMCPY) memc (seg_rom rsegs))).
Proof.
intros W memc regs R n l v c so H9 HR1 HR2 HR3 H22 Hc H25 H27 Hn Hl Hso1 Hso2 Hval Hv.
assert (E9 : ew (Ereg regs [Z_to_bv 64 v]) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E25 : ew (Ereg regs [Z_to_bv 64 v]) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E27 : ew (Ereg regs [Z_to_bv 64 v]) 27 = w64 l) by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
rewrite restrict_mkst_fx. unfold ss_CD. apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
  rewrite H22, denot_lit_U, (U_atom_off _ 9 R c E9) by lia. reflexivity.
- apply w7_slot_wf.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, w7_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R so 8 (SOff 32 0) v); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hval].
  rewrite w7_den0. exact (ew_Ereg_extra regs [Z_to_bv 64 v] 0).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite E9, E25, E27. unfold w64. rewrite !unsigned_lit_small by lia.
  change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
  repeat split; first [exact HR3 | lia].
Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================== B: 0x8159c -> 0x51860 ======================== *)
Definition ss_B : sstate :=
mkSS W7_AFTER_STRLEN sr_atoms [] None (mkFacts [(10%nat, mkAF 0 21 0); (25%nat, mkAF 0 40 0)] [] []).

Lemma w7_B : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) l n x t,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 l -> 0 <= l <= 21 -> getr regs 25 = w64 n -> 0 <= n <= 40 ->
getr regs 24 = w64 x -> getr regs 21 = w64 t -> 0 <= t -> t + 0x80 <= 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_AFTER_STRLEN) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_MEMCPY regs memc mdc [1; 10; 11; 12; 27]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7_AFTER_MEMCPY /\ getr regs2 10 = w64 (t + n) /\ getr regs2 11 = w64 x /\
 getr regs2 12 = w64 l /\ getr regs2 27 = w64 l)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs l n x t HJ H10 Hl H25 Hn H24 H21 Ht Ht2.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 10 = w64 l) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E25 : ew (Ereg regs []) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E24 : ew (Ereg regs []) 24 = w64 x) by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E21 : ew (Ereg regs []) 21 = w64 t) by (rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (HS : st_ok rsegs (Ereg regs []) ss_B (restrict (w_H W) (mkst regs (Z_to_bv 64 W7_AFTER_STRLEN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_B f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E10, E25. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
aj_run_to w7_tbl_ok HS HJ W7_MEMCPY.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + cbv beta.
    split; [w7_reg HS; reflexivity|].
    split; [w7_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 21 t E21) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7_reg HS; rewrite w7_den0; exact E24|].
    split; w7_reg HS; rewrite w7_den0; exact E10.
Qed.

(* ======================== C: 0x815c0 -> 0x42194 (i = 0 .. 2) ======================== *)
Lemma w7_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i : nat) R n l x',
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> (i < 3)%nat ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 22 = w64 (R + 0x158 + 8 * Z.of_nat i) -> getr regs 25 = w64 n -> getr regs 27 = w64 l ->
0 <= n <= 40 -> 0 <= l <= 21 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x160 + 8 * Z.of_nat i) 8 x' -> 0 <= x' < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_STRLEN regs memc mdc [1; 10; 22; 24; 25]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7_AFTER_STRLEN /\ getr regs2 10 = w64 x' /\ getr regs2 24 = w64 x' /\
 getr regs2 22 = w64 (R + 0x160 + 8 * Z.of_nat i) /\ getr regs2 25 = w64 (n + l))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i R n l x' HJ Hi H9 HR1 HR2 HR3 H22 H25 H27 Hn Hl Hval Hx.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (Ho : 8 * Z.of_nat i = 0 \/ 8 * Z.of_nat i = 8 \/ 8 * Z.of_nat i = 16) by lia.
remember (8 * Z.of_nat i) as o eqn:Hoi. clear Hoi Hi i.
assert (E9 : ew (Ereg regs [Z_to_bv 64 x']) 9 = w64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E25 : ew (Ereg regs [Z_to_bv 64 x']) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E27 : ew (Ereg regs [Z_to_bv 64 x']) 27 = w64 l) by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew (Ereg regs [Z_to_bv 64 x']) 32 = w64 x') by exact (ew_Ereg_extra regs [Z_to_bv 64 x'] 0).
assert (H22' : getr regs 22 = w64 (R + (0x158 + o))) by (rewrite H22; unfold w64; f_equal; lia).
assert (Hval' : val_mem rsegs (mrestrict (w_H W) memc) (R + (0x160 + o)) 8 x')
  by (replace (R + (0x160 + o)) with (R + 0x160 + o) by lia; exact Hval).
pose proof (w7_CD_entry W memc regs R n l x' (0x158 + o) (0x160 + o) H9 HR1 HR2 HR3 H22' ltac:(lia) H25 H27 Hn Hl
  ltac:(lia) ltac:(lia) Hval' Hx) as HS.
clear H22 Hval H22' Hval'.
destruct Ho as [-> | [-> | ->]].
all: aj_run_to w7_tbl_ok HS HJ W7_STRLEN; [awr_ok_tac |
  eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ];
  [ eapply (w7_regs_kept _ _ ms regs [Z_to_bv 64 x'] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity]
  | intros a Ha Hz;
    exact (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7_CD_nowr _ _ _ a Hw) a Ha Hz)
  | cbv beta;
    split; [w7_reg HS; reflexivity|];
    split; [w7_reg HS; rewrite w7_den0; exact E32|];
    split; [w7_reg HS; rewrite w7_den0; exact E32|];
    split; [w7_reg HS; rewrite denot_lit_U, (U_atom_off _ 9 R _ E9) by lia; unfold w64; f_equal; lia|];
    w7_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 27 l E27) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia ] ].
Qed.

(* ======================== D: 0x815c0 -> 0x51860 (i = 3) ======================== *)
Lemma w7_D : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R n l t eb,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 22 = w64 (R + 0x170) -> getr regs 25 = w64 n -> getr regs 27 = w64 l -> 0 <= n <= 40 -> 0 <= l <= 21 ->
getr regs 21 = w64 t ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 eb -> 0 <= eb < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_AFTER_MEMCPY) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_MEMCPY regs memc mdc [1; 10; 11; 12; 22; 25]%bv (fun _ => False)
(fun regs2 _ => getr regs2 1 = w64 W7_AFTER_TEXT /\ getr regs2 10 = w64 eb /\ getr regs2 11 = w64 t /\
 getr regs2 12 = w64 (n + l) /\ getr regs2 22 = w64 eb /\ getr regs2 25 = w64 (n + l))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R n l t eb HJ H9 HR1 HR2 HR3 H22 H25 H27 Hn Hl H21 Hval Heb.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E25 : ew (Ereg regs [Z_to_bv 64 eb]) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E21 : ew (Ereg regs [Z_to_bv 64 eb]) 21 = w64 t) by (rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E27 : ew (Ereg regs [Z_to_bv 64 eb]) 27 = w64 l) by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew (Ereg regs [Z_to_bv 64 eb]) 32 = w64 eb) by exact (ew_Ereg_extra regs [Z_to_bv 64 eb] 0).
pose proof (w7_CD_entry W memc regs R n l eb 0x170 0x108 H9 HR1 HR2 HR3 H22 ltac:(lia) H25 H27 Hn Hl
  ltac:(lia) ltac:(lia) Hval Heb) as HS.
aj_run_to w7_tbl_ok HS HJ W7_MEMCPY.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [Z_to_bv 64 eb] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => w7_CD_nowr _ _ _ a Hw) a Ha Hz).
  + cbv beta.
    split; [w7_reg HS; reflexivity|].
    split; [w7_reg HS; rewrite w7_den0; exact E32|].
    split; [w7_reg HS; rewrite w7_den0; exact E21|].
    split; [w7_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 27 l E27) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    split; [w7_reg HS; rewrite w7_den0; exact E32|].
    w7_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 25 n E25), (U_atom _ 27 l E27) by lia; cbn [zalu_raw];
    rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia.
Qed.

(* ======================== E1: 0x815f0 -> 0x815f8 ======================== *)
Definition ss_E1 : sstate := mkSS W7_AFTER_TEXT sr_atoms [] None (mkFacts [] [] []).

Lemma w7_E1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) eb n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 22 = w64 eb -> getr regs 25 = w64 n -> 0 <= eb -> 0 <= n -> eb + n + 1 < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_AFTER_TEXT) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_E2 regs memc mdc [10; 25]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (eb + n) /\ getr regs2 25 = w64 (n + 1))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs eb n HJ H22 H25 Heb Hn Hsum.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E22 : ew (Ereg regs []) 22 = w64 eb) by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E25 : ew (Ereg regs []) 25 = w64 n) by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (HS : st_ok rsegs (Ereg regs []) ss_E1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W7_AFTER_TEXT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [exact I|split; exact I]. }
aj_run_to w7_tbl_ok HS HJ W7_E2.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + cbv beta.
    split; [w7_reg HS; rewrite denot_lit_U, U_SAlu, (U_atom _ 22 eb E22), (U_atom _ 25 n E25) by lia; cbn [zalu_raw];
      rewrite zcanon_id by (unfold M64; lia); unfold w64; f_equal; lia|].
    w7_reg HS; rewrite denot_lit_U, (U_atom_off _ 25 n 1 E25) by lia. reflexivity.
Qed.
End d.
End b.

Print Assumptions w7_B.
Print Assumptions w7_C.
Print Assumptions w7_D.
Print Assumptions w7_E1.
