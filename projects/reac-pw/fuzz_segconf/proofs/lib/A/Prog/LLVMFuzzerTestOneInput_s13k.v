(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s20.v, with its module paths, module names and numbers changed; 348 of its 449 lines of code are new or changed and 2793 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of file group _s13
   (segment S03 of the walk of the test harness's entry function LLVMFuzzerTestOneInput, K84f98 -> K85024 at turn 0;
   the segment lemma is lt_seg_S03 in LLVMFuzzerTestOneInput_s13.v). It holds the two symbolic seeds (0x84f98 and
   0x84ff0, after reac_segconf_init), the facts the cut readers carry (the frame and its shadow apart from the
   blocks, lt_img under an agreement on the image bytes, lt_frame under an agreement on its bytes), the call step
   of reac_segconf_init (s13_call, PaCall.v's cl_callS with the callee's contract), and the run tactics.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67 YG0q YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegPa SegPaLib PaCall PaDenot SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_init_c
LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic seeds of the two runs: every register its own atom, the s1 frame's write windows, the one byte
   read from the frame (cap at 40(s1), run 1) and the two words read (m at 168(s1), the shadow base at 176(s1),
   run 2) as read-only chunks; no instrumented check, so no shadow entry ---- *)
Definition s13_X : sv := SLit SHADOW_OFF.
Definition s13_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s13_rg1 : smem := [
  YP09.mkRegion (Some 9%nat) 8 16 8 16 [];
  YP09.mkRegion (Some 9%nat) 32 40 32 40 [];
  YP09.mkRegion (Some 9%nat) 40 41 40 40 [YP09.mkChunk 40 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 48 64 48 64 [];
  YP09.mkRegion (Some 9%nat) 80 88 80 88 [];
  YP09.mkRegion (Some 9%nat) 96 112 96 112 [];
  YP09.mkRegion (Some 9%nat) 160 176 160 176 [];
  YP09.mkRegion (Some 9%nat) 184 192 184 192 [] ].
Definition s13_fa1 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 4); (22%nat, mkAF 4096 (2 ^ 47) 4);
    (32%nat, mkAF 0 255 0) ] [] [].
Definition s13_ss1 : sstate := mkSS LO_K84f98 sr_atoms s13_rg1 None s13_fa1.
(* run 2 (0x84ff0 .. 0x85020): the three write windows, m at 168(s1) and the shadow base at 176(s1) read-only *)
Definition S13_RA : Z := 0x2bc.
Definition s13_rg2 : smem := [
  YP09.mkRegion (Some 9%nat) 64 80 64 80 [];
  YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
  YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
  YP09.mkRegion (Some 9%nat) 168 184 168 168
    [YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 176 (CVal 8 (SLit SHADOW_OFF))] ].
Definition s13_fa2 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47) 4) ] [] [].
Definition s13_ss2 : sstate := mkSS S13_RA sr_atoms s13_rg2 None s13_fa2.
(* the bytes each run may write: its windows above s1 *)
Definition s13_w1 (s1 a : Z) : Prop :=
  s1 + 8 <= a < s1 + 16 \/ s1 + 32 <= a < s1 + 40 \/ s1 + 48 <= a < s1 + 64 \/ s1 + 80 <= a < s1 + 88 \/
  s1 + 96 <= a < s1 + 112 \/ s1 + 160 <= a < s1 + 176 \/ s1 + 184 <= a < s1 + 192.
Definition s13_w2 (s1 a : Z) : Prop :=
  s1 + 64 <= a < s1 + 80 \/ s1 + 88 <= a < s1 + 96 \/ s1 + 144 <= a < s1 + 152.

(* a value occurring twice in a permutation's right side *)
Lemma s13_perm_dup : forall {A : Type} (o1 o2 l1 l2 : list A) x,
  Permutation (x :: x :: (o1 ++ o2 ++ l1 ++ l2)) ((o1 ++ x :: o2) ++ l1 ++ x :: l2).
Proof.
intros A o1 o2 l1 l2 x. rewrite <- app_assoc. cbn [app].
apply Permutation_cons_app.
replace (o1 ++ o2 ++ l1 ++ x :: l2) with ((o1 ++ o2 ++ l1) ++ x :: l2) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_cons_app. rewrite <- !app_assoc. reflexivity.
Qed.
(* the shadow byte of a side-stack frame byte is never a byte of the application's memory *)
Lemma s13_sh_app : forall {rc : YM05.RunCeil} fr b n i, 4096 <= fr -> fr + 512 <= alloc_ceiling -> in_app b n ->
  0 <= i < 64 -> ~ (b <= shadow_addr fr + i < b + n).
Proof.
intros rc fr b n i H1 H2 (Hb & Hb2) Hi Hx. pose proof asan_consts as (HAC & _).
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
destruct Hb2 as [Hb2 | (Hb2 & Hb3)]; lia.
Qed.
(* an image byte's address under a reader agreement *)
Definition s13_imgeq (rd rd' : reader) : Prop := forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a.
Lemma s13_rdword_img : forall rd rd' a, s13_imgeq rd rd' -> 0x10000 <= a -> a + 8 <= kImgEnd ->
  rdword rd' a = rdword rd a.
Proof. intros rd rd' a HE H0 H1. apply rdword_ext. intros k Hk. apply HE. lia. Qed.


(* cap is the first payload byte mod 40 (SegModel.decode) *)
Lemma s13_cap_range : forall pl, 0 <= seg_spec.seg_cap pl < 40.
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s13_E (regs : bvmap 5 word) (x : Z) : env := Eimg (Ereg regs [Z_to_bv 64 x]).

(* val_mem (lib/Reusable/YI04.v) reads its bytes through YO0f's le_byte *)
Lemma s13_le_byte_1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 8 0 = YO0f.le_byte v 1 0.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* the seed at 0x84f98 *)
Lemma s13_seed1 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 m c cap,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 192 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  getr regs 10 = w64 m -> 4096 <= m <= 2 ^ 47 -> m mod 16 = 0 ->
  getr regs 22 = w64 c -> 4096 <= c <= 2 ^ 47 -> c mod 16 = 0 ->
  0 <= cap < 256 -> rdword (rdW W mem) (s1 + 40) = Some cap ->
  (forall a, s1 + 8 <= a < s1 + 192 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (s13_E regs cap) s13_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K84f98)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m c cap R9 Hs1a Hs1b Hs1c R10 Hm Hm16 R22 Hc Hc16 Hcap Hw40 Hpres.
set (E := s13_E regs cap).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 cap]) n)
  by (intros n Hn; subst E; unfold s13_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = Z_to_bv 64 m)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E22 : ew E 22 = Z_to_bv 64 c)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 40) cap Hw40) as HV8.
assert (HV1 : val_mem SEGS (mrestrict (w_H W) mem) (s1 + 40) 1 cap).
{ intros k0 Hk0. assert (k0 = 0%nat) by lia. subst k0.
  rewrite (HV8 0%nat ltac:(lia)). rewrite (s13_le_byte_1 cap Hcap). reflexivity. }
unfold s13_ss1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s13_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s13_rg1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite VB;
    (split; [lia|]); (split; [lia|]).
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 40 1 (SOff 32 0) cap);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact HV1].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
- apply pairwise_disjoint_of_extents. unfold s13_rg1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s13_fa1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E10, E22, E32, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the seed at 0x84ff0, after reac_segconf_init returned *)
Lemma s13_seed2 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 m,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 192 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= m <= 2 ^ 47 -> m mod 16 = 0 ->
  rdword (rdW W mem) (s1 + 168) = Some m -> rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  (forall a, s1 + 8 <= a < s1 + 192 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (s13_E regs m) s13_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S13_RA)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m R9 Hs1a Hs1b Hs1c Hm Hm16 Hw168 Hw176 Hpres.
set (E := s13_E regs m).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 m]) n)
  by (intros n Hn; subst E; unfold s13_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 m) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 168) m Hw168) as HV168.
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 176) SHADOW_OFF Hw176) as HV176.
unfold s13_ss2. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s13_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s13_rg2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite VB;
    (split; [lia|]); (split; [lia|]).
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
  + split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ s1 168 8 (SOff 32 0) m);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact HV168].
    * apply (chunk_ok_val SEGS E _ s1 176 8 (SLit SHADOW_OFF) SHADOW_OFF);
        [reflexivity | unfold SHADOW_OFF; cbn; lia | lia | exact HV176].
- apply pairwise_disjoint_of_extents. unfold s13_rg2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s13_fa2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E32, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the value of an atom with an offset *)
Lemma s13_U_atom : forall E n x v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof.
intros E n x v H Hv Hvx. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* a word of a chunk of the symbolic state, read through the reader *)
Lemma s13_chunk_word : forall (W : world SEGS) E ss ms i rg p off e a v,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  U E e = v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W (ms_mem ms)) (a + off) = Some v.
Proof.
intros W E ss ms i rg p off e a v HS Hi Hb Hc Ha HU Hv.
assert (He : sv_denot E e = Z_to_bv 64 v).
{ apply bv_eq. rewrite unsigned_lit_small by lia. exact HU. }
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) i rg p off 8 e a v HS Hi Hb Hc Ha He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as HV.
cbn [ms_mem restrict] in HV.
exact (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms) (a + off) v HV Hv).
Qed.
(* the registers a call keeps *)
Lemma s13_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

Lemma s13_nth_repeat : forall {A : Type} (x d : A) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof.
intros A x d n. induction n as [|n IH]; intros [|i] Hi; cbn [repeat nth]; first [lia | reflexivity | apply IH; lia].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the callee's contract, at every FP state, at the listing's entry of reac_segconf_init and its window *)
Hypothesis HINIT : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_init) STK_reac_segconf_init.
(* the walk's hypotheses: the call targets of the program functions, the meter across a set_fs state change *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis MTFL : ameter_fs_laws MT.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* the entry sp, the realigned base s1 = (SP0 - 320) & ~31 and the window bounds *)
Lemma s13_sp : forall cx, lt_base B MT cx ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  x_sp0 cx - 351 <= x_s1 cx <= x_sp0 cx - 320 /\ x_s1 cx mod 32 = 0 /\
  x_sp0 cx <= ly_top (x_ly cx).
Proof.
intros cx HBs. pose proof HBs as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
unfold x_s1, x_sp0, LT_FRAME in *.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - 320) 32 ltac:(lia)) as Hm.
split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [|exact Htop].
rewrite Zminus_mod. rewrite Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
Qed.

(* a block the harness made is not one of the entry's *)
Lemma s13_not_entry : forall ly S (W : world SEGS) mem md O x l, AR SEGS B ly S W mem md ->
  Permutation (ablocks B ly S) (O ++ l) -> In x O -> 0 < req_size (snd x) -> ~ In x l.
Proof.
intros ly S W mem md O x l HAR HP HO Hr Hl.
apply in_split in HO as (o1 & o2 & ->). apply in_split in Hl as (l1 & l2 & ->).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x _ HAR
  (Permutation_trans HP (Permutation_sym (s13_perm_dup o1 o2 l1 l2 x)))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a live block of the allocator is a harness block at any reader of its state *)
Lemma s13_hblk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) ->
  0 < n -> req_size n = n -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin Hn Hr.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4 & Hc & _).
pose proof asan_consts as (HAC & _).
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* lt_img reads only bytes of the image: a reader that keeps every image byte keeps lt_img *)
Lemma s13_lit_kept : forall rd H mem a s, s13_imgeq rd (aview SEGS H mem) ->
  sa_lit SEGS B rd a s -> sa_lit SEGS B (aview SEGS H mem) a s.
Proof.
intros rd H mem a s HE (Ha & ((Hzs & Hn0) & _) & Hp & Hr & Hi).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS H mem _ Hr)]|].
- intros i Hi'. rewrite HE; [exact (Hzs i Hi')|].
  rewrite length_app in Hi'. cbn [length] in Hi'.
  destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _). exact (pa_img_range _ Himg).
- split; [exact Hp|]. split; [exact Hr | exact Hi].
Qed.
Lemma s13_img_kept : forall cx rd H mem, s13_imgeq rd (aview SEGS H mem) ->
  lt_img B cx rd -> lt_img B cx (aview SEGS H mem).
Proof.
intros cx rd H mem HE (HRO & HHI & HGI).
assert (HW : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword (aview SEGS H mem) a = rdword rd a)
  by (intros a H0 H1; exact (s13_rdword_img rd _ a HE H0 H1)).
assert (HL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (aview SEGS H mem) a s)
  by (intros a s Hl; exact (s13_lit_kept rd H mem a s HE Hl)).
split; [|split].
- intros a Hro Ho He. rewrite HE; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(sg & Hs & _ & Hr) | Hr].
  + apply pa_img_range. exists sg. split; [exact Hs | exact Hr].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
- destruct HHI as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [intros kk Hk; rewrite HE; [exact (H1 kk Hk) | unfold mod40A, kImgEnd; lia]|].
  split; [exact H2|].
  split; [intros s Hs; destruct (H3 s Hs) as (Hl & Ha); split; [exact (HL _ _ Hl) | exact Ha]|].
  split; [intros s Hs; destruct (H4 s Hs) as (Hl & Ha); split; [exact (HL _ _ Hl) | exact Ha]|].
  split.
  { destruct H5 as (Hp & Hi & Hrow). split; [exact Hp|]. split; [exact Hi|].
    intros i Hi'. destruct (Hrow i Hi') as (tp & Htp & Hl). exists tp.
    split; [|exact (HL _ _ Hl)]. rewrite HW; [exact Htp | |];
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA, kImgEnd; unfold pin_spec.CAT_N in Hi'; lia. }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros i Hi'. destruct (Hw i Hi') as (wp & Hwp & Hl). exists wp.
    split; [|exact (HL _ _ Hl)]. rewrite HW; [exact Hwp | |]; unfold wordsA, kImgEnd; lia. }
  split.
  { destruct H8 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hi' kk Hk. rewrite HE; [exact (Hr i Hi' kk Hk) | unfold rolesA, kImgEnd; lia]. }
  split.
  { destruct H9 as (Hg & g & Hgd). split; [rewrite HW; [exact Hg | |]; unfold gotwA, kImgEnd; lia|].
    exists g. rewrite HW; [exact Hgd | |]; unfold guardA, kImgEnd; lia. }
  exact H10.
- intros i Hi. rewrite HE; [exact (HGI i Hi)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd. lia.
Qed.

(* the class-3 frame: in the allocator's range and apart from every live block *)
Lemma s13_fr : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  (forall b n, In (b, n) (ablocks B ly S) -> b + req_size n <= x_fr cx \/ x_fr cx + 512 <= b).
Proof.
intros cx ly S W mem md k HBs HJ.
pose proof HBs as (HPRE & _). pose proof HPRE as (HAR0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr. exact (proj1 (proj2 (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly)) LT_FCLS (x_fpos cx)). }
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HB512 : fs_frame_bytes LT_FCLS = 512) by reflexivity.
pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HFs).
rewrite Forall_forall in HFs. pose proof (HFs _ Hin) as (H1 & H2). cbn [fst snd] in H1, H2.
rewrite EF in H1, H2. rewrite HB512 in H2.
split; [lia|]. split; [lia|].
intros b n Hbn. pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n LT_FCLS (x_fpos cx) HAR Hbn Hin) as Hd.
rewrite EF, HB512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* lt_frame at a later state of the journal whose kept registers and frame bytes are the same *)
Lemma s13_frame_move : forall cx ly S (W : world SEGS) regs mem md k ly' S' (W' : world SEGS) regs' mem' md' k',
  lt_frame B cx ly S W regs mem md k LFO0 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly' S' W' mem' md' k' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx \/ x_fr cx <= a < x_fr cx + 24 \/
     x_fr cx + LT_FLAGW <= a < x_fr cx + LT_FLAGW + 8 \/ x_s1 cx + 176 <= a < x_s1 cx + 184 \/
     x_sh cx <= a < x_sh cx + 36 -> rdW W' mem' a = rdW W mem a) ->
  lt_frame B cx ly' S' W' regs' mem' md' k' LFO0.
Proof.
intros cx ly S W regs mem md k ly' S' W' regs' mem' md' k' HF HJ' E2 E3 E4 E8 E9 HK.
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFLW & H176 & HSH).
split; [exact HJ'|].
split; [rewrite E2; exact R2|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split.
{ intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
  change (length LT_SAVED) with 13%nat in Hi13.
  rewrite (rdword_ext (rdW W mem) (rdW W' mem')); [exact (HSV i r Hi)|].
  intros kk Hk. apply HK. left. lia. }
split; [rewrite (rdword_ext (rdW W mem) (rdW W' mem')); [exact HH0 | intros kk Hk; apply HK; right; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W' mem')); [exact HH8 | intros kk Hk; apply HK; right; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W' mem')); [exact HH16 | intros kk Hk; apply HK; right; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W' mem'));
  [exact HFLW | intros kk Hk; apply HK; right; right; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W' mem'));
  [exact H176 | intros kk Hk; apply HK; right; right; right; left; lia]|].
intros i Hi. rewrite HK; [exact (HSH i Hi)|]. right; right; right; right. rewrite lt_fsh_len in Hi. lia.
Qed.

(* 0x84fec: the call of reac_segconf_init(c) through PaCall.v's cl_callS, the callee's contract applied at the
   segment's FP state (its post is apost_base: the FP state is kept), to its return at 0x84ff0 *)
Lemma s13_call : forall cx ly S (W : world SEGS) regs mem md k c Q,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = w64 (x_s1 cx) -> getr regs 3 = getr (x_regs cx) 3 -> getr regs 4 = getr (x_regs cx) 4 ->
  getr regs 8 = w64 (x_sp0 cx) -> getr regs 1 = w64 (BASE + S13_RA) -> getr regs 10 = w64 c ->
  In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S) -> ~ In (c, seg_spec.SEG_C_SIZE) (x_bl0 B cx) ->
  sa_addr (rdW W mem) c seg_spec.SEG_C_SIZE -> st_nev S <= EV_MAX ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
       (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
     aregs_preserved regs regs2 ->
     sa_kept SEGS W mem W2 mem2 regs STK_reac_segconf_init (fun a => c <= a < c + seg_spec.SEG_C_SIZE) ->
     sa_bytes (rdW W2 mem2) c (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE)) ->
     sa_noalloc B ly S ly2 S2 ->
     SRr SEGS W2 (mkCfg (mkst regs2 (w64 (BASE + S13_RA)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_init)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k c Q HBs HJ R2 R3 R4 R8 R1 R10 HCin HCn HCad Hnev HK.
pose proof HBs as (HPRE0 & HAP0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (s13_sp cx HBs) as (Hsp0 & Hsp16 & Hs1 & Hs32 & Htop0).
pose proof HJ as (HAR & _).
pose proof asan_consts as (HAC & _ & _ & _ & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HSI : STK_reac_segconf_init = 4112) by reflexivity.
assert (HCS : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (Hc16 & Hc4 & Hcc & _).
assert (HRC : req_size seg_spec.SEG_C_SIZE = seg_spec.SEG_C_SIZE) by reflexivity.
(* the frame chain at the call's sp: s0 = SP0, the stack from the call's sp to the top is present *)
assert (HAP : astack_pres ly (w_H W) mem (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
{ apply (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAP0).
  intros a (r & Hr & Hlo & Hhi) Ha. unfold ltoi_PG in Hr. cbn [In] in Hr.
  destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold longlA, A_LONGL, LONGL_N in Hhi.
  exfalso. unfold x_sp0 in *. lia. }
pose proof (astack_rd_of_pres SEGS ly (w_H W) mem (x_s1 cx)
  (astack_pres_mono ly (w_H W) mem (x_sp0 cx - STK_LLVMFuzzerTestOneInput) (x_s1 cx) ltac:(lia) HAP)) as HRD.
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch1 & Hch).
assert (Hsp' : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hal : (x_s1 cx - x_sp0 cx) mod 16 = 0) by lia.
assert (Hch' : achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regs) ch1).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact Hch. }
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
assert (Hraw : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold w64; apply ret_ok_codeptr_v; [unfold S13_RA; lia | reflexivity]).
assert (Hra4 : 4096 <= bv_unsigned (getr regs 1)).
{ rewrite R1. unfold w64, S13_RA. rewrite unsigned_lit_small by lia. lia. }
assert (HPRE : reac_segconf_init_pre B ly S (rdW W mem) c).
{ split; [lia|]. split; [exact Hc16|]. split; [|exact HCad].
  exists c, seg_spec.SEG_C_SIZE. split; [exact HCin | lia]. }
eapply SRr_bind.
{ apply (cl_callS B LAWS W regs mem (Z_to_bv 64 (BASE + AF_reac_segconf_init)) STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k
    STK_reac_segconf_init [(c, c + seg_spec.SEG_C_SIZE)] EV_reac_segconf_init (x_s1 cx - x_sp0 cx) (getr regs 1) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       getr regs' 10 = w64 c /\
       sa_bytes (rdW W' mem') c (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE)) /\
       sa_rconf (rdW W' mem') c SegModel.rconf0 /\
       sa_kept SEGS W mem W' mem' regs STK_reac_segconf_init (fun a => c <= a < c + seg_spec.SEG_C_SIZE) /\
       sa_noalloc B ly S ly' S')
    HJ Hsp' Hal ltac:(lia) ltac:(rewrite HSI; lia) ltac:(rewrite HSI, HSTK; lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) eq_refl Hraw Hra4 Hch').
  - intros HPRE1. exact (HINIT fx ly S W regs mem md ch1 c HPRE1 R10 ltac:(lia) HPRE
      ltac:(unfold EV_reac_segconf_init; lia)).
  - intros a (r & Hr & Hlo & Hhi). cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi.
    right. exists c, seg_spec.SEG_C_SIZE. split; [exact HCin|]. split; [exact HCn|]. rewrite HRC. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & (_ & HZB & _ & HKP & HNA)).
replace (k + EV_reac_segconf_init) with k in HJ2 by (unfold EV_reac_segconf_init; lia).
rewrite R1. exact (HK ly2 S2 W2 regs2 mem2 md2 HJ2 HP HKP HZB HNA).
Qed.

End e.
End f.
End d.

(* the kept registers across a run and the call: each is the atom it was *)
Ltac s13_kr Q P EEo2 EEo HPr n r :=
  rewrite Q, (EEo2 n r eq_refl), (HPr r (Z.of_nat n) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
    P, (EEo n r eq_refl).
(* a word of chunk [off] of region [i] of the state HS (base atom 9) *)
Ltac s13_rd HS i off e :=
  lazymatch type of HS with
  | st_ok _ _ ?ss _ =>
    let l := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch l with Some ?rg =>
      apply (s13_chunk_word _ _ ss _ i rg 9%nat off e _ _ HS);
      [ vm_compute; reflexivity | reflexivity
      | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | | | ]
    end
  end.
