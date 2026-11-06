(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 155 of its 177 lines of code are new or changed and 304 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkA2.v at 1227c8ba2a69 for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the param table (0x9bbe0), HPFX (0x20fe0), the separators, the registers (the shadow offset in s2, the part pointer in s6, the saved cursor in s7, the part string in s8, n in s9), the frame window (R+0x158 .. R+0x178, the store check of R+0x160) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkA2.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the param table (0x9bee0), the registers (p in s9, the shadow offset in s4, the part pointer in s2, the saved input left in s8 from t1, the part string in s10, n in s9), the frame window (R+0x198 .. R+0x1b8, the store check of R+0x1a0) and the frame bound (R + 0x220 <= 2^47) are image B's; lib/A/RtPgW7bBase.v is lib/AU/RtPgW7bBaseB.v; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): block A2 of the walk of
   LLVMFuzzerTestOneInput from 0x8160c (lib/AU/RtPgW7bBaseB.v). Proves no function (kind: segment lemma).

   A2, 0x81640 .. 0x816a4 (pod.h:251-255, sep and parts[0..3]):
     slli s9,s9,0x38; bgez s9 -> 0x81654; a1 = 0x212e0 (""); j 0x8165c; 0x81654: a1 = 0x21500 (".")
     a2 = 0x20fe0; sd a2,0x198(s1); addi a2,s1,0x1a0; srli a2,a2,3; add a2,a2,s4; lbu a2,0(a2)
     ld a0,0(a0); beqz a2 -> 0x81684; j report
     0x81684: mv s8,t1; mv s9,zero; sd s2,0x1a0(s1); sd a1,0x1a8(s1); sd a0,0x1b0(s1)
     addi s2,s1,0x198; ld s10,0(s2); mv a0,s10; jal strlen 0x421ec
   The engine starts with a0 pinned to an extra atom (32, the param table entry's address W7B_PTAB p) whose 8 bytes
   are a region with the entry's value (atom 33, pa), and the frame window [R+0x198, R+0x1b8) as a writable region
   based on s1 (atom 9). The `bgez` is decided by the fact on s9 (atom 25): [0, 127] or [128, 255] after a case
   split on bit 7 of p. The `lbu` / `beqz` / `j` triple is the instrumented check of the store to R+0x1a0; the
   token engine takes the fast arm on one shadow obligation, range_addressable of [R+0x1a0, R+0x1a8), which the
   lemma asks. A2 ends at the strlen entry with ra = 0x816a8 and the four slots of the window stored. *)
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
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* the param table entry's address, A1's a0 at 0x81640: 0x9bee0 + ((p & 7) << 3) *)
Definition W7B_PTAB (p : Z) : Z := 0x9bee0 + 8 * (p mod 8).

(* bit 7 of a byte *)
Lemma w7b_b7 : forall p, 0 <= p < 256 -> Z.testbit p 7 = (128 <=? p).
Proof.
intros p Hp. destruct (Z.leb_spec 128 p) as [H|H].
- apply (proj2 (Z.testbit_true p 7 ltac:(lia))). change (2 ^ 7) with 128.
  rewrite <- (Z.div_unique p 128 1 (p - 128)) by lia. reflexivity.
- apply (proj2 (Z.testbit_false p 7 ltac:(lia))). change (2 ^ 7) with 128.
  rewrite Z.div_small by lia. reflexivity.
Qed.

(* the engine's start state at 0x81640: a0 is the extra atom 32 (the entry's address), the entry's 8 bytes hold the
   extra atom 33 (its value pa), the frame window [R+0x198, R+0x1b8) is writable; b7 is bit 7 of p *)
Definition a2b_extra (p pa : Z) : list word := [w64 (W7B_PTAB p); w64 pa].
Definition ssb_A2 (b7 : bool) : sstate :=
mkSS W7B_A2 (sr_set sr_atoms 10%bv (SOff 32 0))
[YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
 YP09.mkRegion (Some 9%nat) 0x198 0x1b8 0x198 0x1b8 []] None
(mkFacts [(20%nat, mkAF W7B_SB W7B_SB 0); (25%nat, if b7 then mkAF 128 255 0 else mkAF 0 127 0);
 (9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x220) 4); (32%nat, mkAF 0x9bee0 0x9bf18 3)] [] []).

(* the leaf's helpers: a register's value, and a slot of the window (the region based on atom 9), out of the engine's
   last state *)
Ltac a2b_reg HS r :=
  rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
  lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end;
  cbn [sv_denot].
Ltac a2b_field RG F9 od e v :=
  refine (w7b_field _ _ 9%nat _ _ 408 440 408 440 od 8%N e v RG F9 _ _ _ _);
  [ cbv [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64)
  | lia ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w7b_A2_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p R pa b7,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 (W7B_PTAB p) -> getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 p -> 0 <= p < 256 ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (W7B_PTAB p) 8 pa -> 0 <= pa < 2 ^ 64 ->
(forall a, R + 0x198 <= a < R + 0x1b8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
Z.testbit p 7 = b7 ->
st_ok rsegs (Ereg regs (a2b_extra p pa)) (ssb_A2 b7)
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7B_A2) memc (seg_rom rsegs))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p R pa b7 HJ H10 H20 H25 Hp H9 HR0 HR1 HR16 HPA Hpa HWIN Hb7.
assert (E9 : ew (Ereg regs (a2b_extra p pa)) 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
assert (E20 : ew (Ereg regs (a2b_extra p pa)) 20 = getr regs 20) by exact (ew_Ereg_nat regs _ 20 20%bv eq_refl).
assert (E25 : ew (Ereg regs (a2b_extra p pa)) 25 = getr regs 25) by exact (ew_Ereg_nat regs _ 25 25%bv eq_refl).
assert (X32 : ew (Ereg regs (a2b_extra p pa)) 32 = w64 (W7B_PTAB p)) by exact (ew_Ereg_extra regs _ 0).
assert (X33 : ew (Ereg regs (a2b_extra p pa)) 33 = w64 pa) by exact (ew_Ereg_extra regs _ 1).
assert (HPT : 0x9bee0 <= W7B_PTAB p <= 0x9bf18) by (unfold W7B_PTAB; pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
assert (B9 : bv_unsigned (ew (Ereg regs (a2b_extra p pa)) 9) = R) by (rewrite E9, H9; unfold w64; apply unsigned_lit_small; lia).
assert (B32 : bv_unsigned (ew (Ereg regs (a2b_extra p pa)) 32) = W7B_PTAB p)
by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ssb_A2. apply (entry_st_ok_full rsegs).
- apply YI04.regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite B32, Z.add_0_r. exact H10.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (W7B_PTAB p) 0 8 (SOff 33 0) pa).
    * cbn [sv_denot]. rewrite X33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * rewrite Z.add_0_r. exact HPA.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply apresent_writable.
    eapply proj1. eapply (awr_byte_present rsegs B LAWS); [exact HJ | apply HWIN; lia].
- cbn [pairwise_disjoint all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B32, B9.
  split; [split; [left; lia | exact I] | split; exact I].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok.
  rewrite B9, B32, E20, E25, H20, H25. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  assert (HM : W7B_PTAB p mod 8 = 0).
  { unfold W7B_PTAB. replace (0x9bee0 + 8 * (p mod 8)) with ((79836 + p mod 8) * 8) by ring. apply Z.mod_mul. lia. }
  rewrite w7b_b7 in Hb7 by exact Hp.
  destruct b7; cbn [af_lo af_hi af_al2];
  [apply Z.leb_le in Hb7 | apply Z.leb_gt in Hb7];
  change (2 ^ 0) with 1; change (2 ^ 4) with 16; change (2 ^ 3) with 8; rewrite !Z.mod_1_r, HM, HR16;
  unfold SHADOW_OFF, W7B_SB; repeat split; lia.
Qed.

Lemma w7b_A2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p R s2v left pa,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 (W7B_PTAB p) -> getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 p -> 0 <= p < 256 ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 18 = w64 s2v -> 0 <= s2v < 2 ^ 64 -> getr regs 6 = w64 left ->
val_mem rsegs (mrestrict (w_H W) memc) (W7B_PTAB p) 8 pa -> 0 <= pa < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (R + 0x1a0) 8 ->
(forall a, R + 0x198 <= a < R + 0x1b8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_A2) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_STRLEN regs memc mdc [1; 10; 11; 12; 18; 24; 25; 26]%bv
(fun a => R + 0x198 <= a < R + 0x1b8)
(fun regs2 mem2 => getr regs2 1 = w64 W7B_AFTER_STRLEN /\ getr regs2 10 = w64 0x20fe0 /\ getr regs2 26 = w64 0x20fe0 /\
 getr regs2 18 = w64 (R + 0x198) /\ getr regs2 24 = w64 left /\ getr regs2 25 = w64 0 /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x198) 8 0x20fe0 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x1a0) 8 s2v /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x1a8) 8 (w7b_sep p) /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x1b0) 8 pa)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p R s2v left pa
HJ H10 H20 H25 Hp H9 HR0 HR1 HR16 H18 Hs2 H6 HPA Hpa HRA HWIN.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E9 : ew (Ereg regs (a2b_extra p pa)) 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
assert (E18 : ew (Ereg regs (a2b_extra p pa)) 18 = getr regs 18) by exact (ew_Ereg_nat regs _ 18 18%bv eq_refl).
assert (E20 : ew (Ereg regs (a2b_extra p pa)) 20 = getr regs 20) by exact (ew_Ereg_nat regs _ 20 20%bv eq_refl).
assert (E6 : ew (Ereg regs (a2b_extra p pa)) 6 = getr regs 6) by exact (ew_Ereg_nat regs _ 6 6%bv eq_refl).
assert (X33 : ew (Ereg regs (a2b_extra p pa)) 33 = w64 pa) by exact (ew_Ereg_extra regs _ 1).
assert (B9 : bv_unsigned (ew (Ereg regs (a2b_extra p pa)) 9) = R) by (rewrite E9, H9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs (a2b_extra p pa)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (a2b_extra p pa)) (Ereg regs (a2b_extra p pa))) by apply env_agree_refl.
assert (HWR : forall b7 a, in_wrange (Ereg regs (a2b_extra p pa)) (ss_mem (ssb_A2 b7)) a -> R + 0x198 <= a < R + 0x1b8).
{ intros b7 a (r & Hin & Ha). cbn [ssb_A2 ss_mem In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | rewrite B9 in Ha; lia]. }
destruct (Z.testbit p 7) eqn:Hb7;
pose proof (w7b_A2_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p R pa _
  HJ H10 H20 H25 Hp H9 HR0 HR1 HR16 HPA Hpa HWIN Hb7) as HS;
aj_run_to_tok w7b_tbl_ok HS HJ SHOK W7B_span 0x421ec.
(* goals 1-3: bit 7 set (the `bgez` falls through, sep = "" at 0x212e0); 4-6: clear (taken, sep = "." at 0x21500).
   The shadow obligation of the store check, [R+0x1a0, R+0x1a8) *)
1,4: cbn [ms_mem mkst]; unfold W7B_Bx;
  rewrite (U_atom _ 20 SHADOW_OFF) by first [rewrite E20, H20; reflexivity | unfold SHADOW_OFF; lia];
  rewrite U_SOff, B9, zcanon_id by (unfold M64; lia); exact HRA.
(* the start state's regions: the entry (read only) and the window, writable by the hypothesis on it *)
1,3: unfold ssb_A2; cbn [ss_mem];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply (w7b_awr_cons _ _ _ _ _ _ _ _ _ _ 9%nat R);
  [reflexivity | exact B9 | cbn [YP09.r_wlo YP09.r_whi]; exact HWIN | apply awr_ok_nil].
(* the leaf: w7b_post from the engine's last state at the strlen entry *)
all: eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
1,4: eapply (w7b_regs_kept _ _ ms regs (a2b_extra p pa) (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
1,3: intros a Ha Hz;
  exact (w7b_kept_run (fun a => R + 0x198 <= a < R + 0x1b8) _ _ (w_H W) memc memc (ms_mem ms)
    (fun a _ _ => eq_refl) HFr (HWR _) a Ha Hz).
(* the result: ra, a0 = s10 = parts[0], s2 = &parts[0], s8 = the old t1, s9 = 0, and the four slots *)
all: cbv beta;
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  let sepv := eval vm_compute in (sr_get (ss_regs ssv) (11%bv : bv 5)) in
  let r9 := eval vm_compute in (nth 1 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
  assert (F9 : bv_unsigned (ew Ev 9) = R) by (rewrite ew_ewset_other by lia; exact B9);
  assert (F18 : ew Ev 18 = w64 s2v) by (rewrite ew_ewset_other by lia; rewrite E18; exact H18);
  assert (F6 : ew Ev 6 = w64 left) by (rewrite ew_ewset_other by lia; rewrite E6; exact H6);
  assert (F33 : ew Ev 33 = w64 pa) by (rewrite ew_ewset_other by lia; exact X33);
  assert (RG : region_ok rsegs Ev (mrestrict (w_H W) (ms_mem msv)) r9)
  by exact (w7b_region_nth Ev ssv (restrict (w_H W) msv) 1%nat r9 HS ltac:(vm_compute; reflexivity));
  split; [a2b_reg HS (1%bv : bv 5); reflexivity|];
  split; [a2b_reg HS (10%bv : bv 5); reflexivity|];
  split; [a2b_reg HS (26%bv : bv 5); reflexivity|];
  split; [a2b_reg HS (18%bv : bv 5); rewrite F9; reflexivity|];
  split; [a2b_reg HS (24%bv : bv 5); rewrite F6, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|];
  split; [a2b_reg HS (25%bv : bv 5); reflexivity|];
  split; [a2b_field RG F9 408 (SLit 135136) 135136; [reflexivity | lia]|];
  split; [a2b_field RG F9 416 (SOff 18 0) s2v; [rewrite F18, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | lia]|];
  split; [a2b_field RG F9 424 sepv (w7b_sep p); unfold w7b_sep; rewrite Hb7; cbn beta iota; [reflexivity | lia]|];
  a2b_field RG F9 432 (SOff 33 0) pa; [rewrite F33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | lia]
  end.
Qed.
End d.
End b.

Print Assumptions w7b_A2_entry.
Print Assumptions w7b_A2.
