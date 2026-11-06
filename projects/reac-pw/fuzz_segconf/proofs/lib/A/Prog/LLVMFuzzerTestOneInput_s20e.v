(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s20.v, with its module paths, module names, addresses and numbers changed; 268 of its 611 lines of code are new or changed and 2551 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s20, piece e:
    s20_L0 (K856bc -> H 0 | N) and s20_L3 (Z i -> H (i + 1) | N) of the test harness's entry function
   LLVMFuzzerTestOneInput (0x84d34). No call: engine runs and branches only.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s44.v (origin/ossv/recipes 501c0d516c69: a seed of
   the state inside the function, paj_run_tok / paj_run_to_tok, psrr_branch_tok, the registers read back by prreg)
   and segconf's _s10 (LLVMFuzzerTestOneInput_s10.v: the class-3 frame's shadow as a region, its awr_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* beyond LLVMFuzzerTestOneInput_s20.v's Requires: the engine's kernel modules, as LLVMFuzzerTestOneInput_s10.v
   imports them (before the walk's own Reusable modules, so these never shadow them) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK0h YK0i YK1b YK1a YK18.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
  YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegPaLib SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s20k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc RtPFSeg RtString.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* beyond LLVMFuzzerTestOneInput_s20.v's Requires: the engine's Pa* modules, as LLVMFuzzerTestOneInput_s10.v
   imports them (the second Open Scope keeps Z_scope over what they open) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
  PaSym PaStep PaRun PaShadow PaJournal PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Local Open Scope Z_scope.

(* ---- the symbolic seeds (every register its own atom; the bytes the code reads as read-only chunks) ----
   K856bc (0x856bc): atoms 32 = FR + 192 (the probe), 33 = SH(FR), 34 = SH(m + 0x2000), 35 = m, 36 = m + 0x2000,
   37 = m->n; the s1 slots 104, 144, 152, 168, 184 (one region of s1), the shadow byte of m + 0x2000 (0) and the
   4 bytes of m->n. *)
Definition s20e_X : sv := SLit SHADOW_OFF.
Definition s20e_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s20e_rgA : smem := [
  YP09.mkRegion (Some 9%nat) 104 192 104 104
    [YP09.mkChunk 104 (CVal 8 (SOff 32 0)); YP09.mkChunk 144 (CVal 8 (SOff 33 0));
     YP09.mkChunk 152 (CVal 8 (SOff 34 0)); YP09.mkChunk 168 (CVal 8 (SOff 35 0));
     YP09.mkChunk 184 (CVal 8 (SOff 36 0))];
  YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
  YP09.mkRegion (Some 36%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))] ].
Definition s20e_faA : facts := mkFacts [(37%nat, mkAF 0 32 0)] [] [].
Definition s20e_ssA : sstate := mkSS LO_K856bc sr_atoms s20e_rgA None s20e_faA.

(* Z i (0x85748): extras 32 = m + 0x2000, 33 = m->n; the probe's three shadow bytes SH(FR) + 24 .. 26 (written), the
   shadow byte of m + 0x2000 (0), the slot 184(s1) and the 4 bytes of m->n; s2 = i <= 31 and m->n <= 32 *)
Definition s20e_rgZ : smem := [
  YP09.mkRegion (Some 21%nat) 24 27 24 27 [];
  YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
  YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 32%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))] ].
(* the token runner's shadow band for Z i: empty (no shadow entry, no token check), so that the run's write window
   SH(FR) + 24 .. 26 passes sh_static_ok's cells_safe_b *)
Definition s20e_spanZ : Z * Z := (0, 0).
Definition s20e_faZ : facts :=
  mkFacts [(18%nat, mkAF 0 31 0); (21%nat, mkAF SHADOW_OFF 0x10007fff8000 0); (33%nat, mkAF 0 32 0)] [] [].
Definition s20e_ssZ : sstate := mkSS LO_Z sr_atoms s20e_rgZ None s20e_faZ.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* image numbers of the runtime rows (instantiated by the close) *)
Variables (cstk snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
(* the runtime entries and callees S11 / S12 reach, at every FP state *)
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (SIG SS___interceptor_trampoline_calloc) cstk.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
(* row 4's image numbers (_s15's text, shared by both harness snprintf sites): the harness's formats lie in
   [snp_lo, gotwA) (FR_seg), the read-only ranges inside [snp_lo, snp_hi), and [snp_lo, snp_hi) below the
   allocator ceiling and the fake stack (dest_off_globals for a destination in the class-3 frame); at image A
   snp_lo := 0x10000, snp_hi := YG0f.kImgEnd, each a computation *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
(* the walk hypotheses (the close discharges them at image A) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).


(* the environment of the seed at K856bc *)
Definition s20e_EA (regs : bvmap 5 word) (pr sh shm m n : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [pr; sh; shm; m; m + seg_spec.MC_N; n])).

(* the entry sp, the realigned base s1 = (SP0 - 320) & ~31 (_s13's s13_sp) *)
Lemma s20e_sp : forall cx, lt_base B MT cx ->
  alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
  x_sp0 cx - 351 <= x_s1 cx <= x_sp0 cx - 320 /\ x_s1 cx mod 32 = 0.
Proof.
intros cx HBs. pose proof HBs as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME in *.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - 320) 32 ltac:(lia)) as Hm.
split; [lia|]. split; [exact Hal|]. split; [lia|].
rewrite Zminus_mod. rewrite Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
Qed.

(* the class-3 frame of a point: live in the state, 32-aligned, in the application memory, its 64 shadow bytes
   present, apart from every block *)
Lemma s20e_fr : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_frame B cx ly S W regs mem md k o ->
  x_fr cx = frame_addr ly 3 (x_fpos cx) /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ x_fr cx mod 32 = 0 /\ in_app (x_fr cx) 512 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)) /\
  (forall b n, In (b, n) (ablocks B ly S) -> b + req_size n <= x_fr cx \/ x_fr cx + 512 <= b).
Proof.
intros cx ly S W regs mem md k o HF.
destruct HF as (HJ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : x_fr cx = frame_addr ly 3 (x_fpos cx)).
{ unfold x_fr, frame_addr, LT_FCLS. destruct Hly as (_ & _ & _ & _ & _ & HlF & _). rewrite HlF. reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos cx) HAR Hin) as (Hal & Happ & HFp & HSp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos cx) HAR Hin) as (H4096 & Hceil & _).
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HSp.
rewrite <- EF in *.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Happ|]. split.
- intros i Hi. exact (proj1 (HSp i Hi)).
- intros b n Hbn. pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n 3 (x_fpos cx) HAR Hbn Hin) as Hd.
  rewrite <- EF in Hd. change (fs_frame_bytes 3) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the seed at K856bc *)
Lemma s20e_seedA : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 pr sh shm m n,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 192 <= 2 ^ 64 ->
  0 <= pr < 2 ^ 64 -> 0 <= sh < 2 ^ 64 -> 0 <= shm -> shm + 1 <= 2 ^ 64 ->
  0 <= m -> m + seg_spec.MC_N + 4 <= 2 ^ 64 -> 0 <= n <= 32 ->
  rdword (rdW W mem) (s1 + 104) = Some pr -> rdword (rdW W mem) (s1 + 144) = Some sh ->
  rdword (rdW W mem) (s1 + 152) = Some shm -> rdword (rdW W mem) (s1 + 168) = Some m ->
  rdword (rdW W mem) (s1 + 184) = Some (m + seg_spec.MC_N) ->
  rdW W mem shm = Some 0 -> sa_val (rdW W mem) (m + seg_spec.MC_N) 4 n ->
  (s1 + 192 <= shm \/ shm + 1 <= s1 + 104) ->
  (s1 + 192 <= m + seg_spec.MC_N \/ m + seg_spec.MC_N + 4 <= s1 + 104) ->
  (shm + 1 <= m + seg_spec.MC_N \/ m + seg_spec.MC_N + 4 <= shm) ->
  st_ok_pi SEGS VAL (s20e_EA regs pr sh shm m n) s20e_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K856bc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 pr sh shm m n R9 H1 H2 Hpr Hsh Hshm1 Hshm2 Hm1 Hm2 Hn W104 W144 W152 W168 W184 Hz Hv D1 D2 D3.
assert (HMN : seg_spec.MC_N = 0x2000) by reflexivity.
set (E := s20e_EA regs pr sh shm m n).
set (X := map (Z_to_bv 64) [pr; sh; shm; m; m + seg_spec.MC_N; n]).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs X) k)
  by (intros k Hk; subst E X; unfold s20e_EA; apply Eimg_low; exact Hk).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j X (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
subst X. cbn [Nat.add nth map] in E32, E33, E34, E35, E36, E37. clear EX.
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv0. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv0. }
pose proof (VB 9%nat s1 E9 ltac:(lia)) as V9.
pose proof (VB 34%nat shm E34 ltac:(lia)) as V34.
pose proof (VB 36%nat (m + seg_spec.MC_N) E36 ltac:(lia)) as V36.
destruct (aview_byte SEGS _ _ _ _ Hz) as (bz & Ebz & Ez & _).
assert (HVz : val_mem SEGS (mrestrict (w_H W) mem) (shm + 0) (N.to_nat 1) 0).
{ intros k0 Hk0. assert (k0 = 0%nat) by (cbn in Hk0; lia). subst k0. change (Z.of_nat 0) with 0.
  rewrite !Z.add_0_r. rewrite Ebz. f_equal. apply bv_eq. rewrite <- Ez. reflexivity. }
unfold s20e_ssA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s20e_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s20e_rgA. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 104 8 (SOff 32 0) pr);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W104)].
    * apply (chunk_ok_val SEGS E _ s1 144 8 (SOff 33 0) sh);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W144)].
    * apply (chunk_ok_val SEGS E _ s1 152 8 (SOff 34 0) shm);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W152)].
    * apply (chunk_ok_val SEGS E _ s1 168 8 (SOff 35 0) m);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W168)].
    * apply (chunk_ok_val SEGS E _ s1 184 8 (SOff 36 0) (m + seg_spec.MC_N));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W184)].
  + rewrite V34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ shm 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HVz].
  + rewrite V36. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (m + seg_spec.MC_N) 0 4 (SOff 37 0) n);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | cbn; lia | rewrite Z.add_0_r; exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hv)].
- apply pairwise_disjoint_of_extents. unfold s20e_rgA, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V9, V34, V36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s20e_faA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E37, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the probe's three shadow bytes (offsets 24 .. 26 of the frame's 36) *)
Lemma s20e_zs_probe : forall rd sh o, sa_zs rd sh (lt_fsh o) ->
  sa_zs rd (sh + 24) (if fo_probe o then [0; 0; 2] else [0xf8; 0xf8; 0xf8]).
Proof.
intros rd sh o H i Hi.
replace (sh + 24 + Z.of_nat i) with (sh + Z.of_nat (24 + i)) by lia.
assert (Hi3 : (i < 3)%nat) by (destruct (fo_probe o); cbn [length] in Hi; lia).
rewrite (H (24 + i)%nat) by (rewrite lt_fsh_len; lia).
f_equal. destruct o as [[] [] [] [] []]; cbn [fo_probe];
  (do 3 (destruct i as [|i]; [reflexivity|])); lia.
Qed.

(* memory kept by a run whose regions have no write window *)
Ltac s20e_keep0 K :=
  lazymatch goal with Hfr : frame_of ?E0 _ (mrestrict (w_H ?W0) ?m0) (mrestrict _ (ms_mem ?ms0)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> rdW W0 (ms_mem ms0) a = rdW W0 m0 a);
  [ intros a Ha; apply (kept_of_frame E0 _ (w_H W0) m0 (ms_mem ms0) (fun _ => False) Hfr); [| exact Ha | tauto];
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; lia |]);
    destruct Hin
  | clear Hfr; try lazymatch goal with HF0 : frame_of E0 _ m0 (ms_mem ms0) |- _ => clear HF0 end;
    try lazymatch goal with HG0 : mem_grows (mrestrict _ m0) _ |- _ => clear HG0 end ] end.

(* memory kept by a run whose only write window is [lo, hi) (the base rewritten by U) *)
Ltac s20e_keepZ K U lo hi :=
  lazymatch goal with Hfr : frame_of ?E0 _ (mrestrict (w_H ?W0) ?m0) (mrestrict _ (ms_mem ?ms0)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W0 (ms_mem ms0) a = rdW W0 m0 a);
  [ intros a Ha Hna; apply (kept_of_frame E0 _ (w_H W0) m0 (ms_mem ms0) (fun x => lo <= x < hi) Hfr);
      [| exact Ha | exact Hna];
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hx; rewrite ?U in Hx; cbv beta; lia |]);
    destruct Hin
  | clear Hfr; try lazymatch goal with HF0 : frame_of E0 _ m0 (ms_mem ms0) |- _ => clear HF0 end;
    try lazymatch goal with HG0 : mem_grows (mrestrict _ m0) _ |- _ => clear HG0 end ] end.

Lemma s20_L0 : S20A_H B MT 0 -> S20A_N B MT -> LT_K856bc_stmt B MT.
Proof.
intros HH HN. unfold LT_K856bc_stmt.
intros cx ly S W regs mem md k acc c m HBs Hfrm HCORE HC HM HSL HCM.
assert (HCTX : s20_ctx B MT cx ly S W regs mem md k acc LFO0 c m)
  by (split; [exact HCORE | split; [exact HC | split; [exact HM | split; [exact HSL | exact HCM]]]]).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFLW & H176 & HSH).
pose proof (s20e_sp cx HBs) as (Hsp0 & Hsp16 & Hs1 & Hs32).
pose proof (s20e_fr cx ly S W regs mem md k LFO0 HFR) as (EFR & HF4 & HFc & HF32 & HFapp & HFsh & HFsep).
pose proof HJ as (HAR & _).
pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & Hmapp & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
rewrite HRM in Hmc, Hmapp.
pose proof asan_consts as (HAC & _ & _ & _ & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HMN : seg_spec.MC_N = 0x2000) by reflexivity.
assert (W104 : rdword (rdW W mem) (x_s1 cx + 104) = Some (x_fr cx + FO_PROBE))
  by (apply HSL; apply in_or_app; left; cbn [LT_L In]; repeat (first [left; reflexivity | right])).
assert (W144 : rdword (rdW W mem) (x_s1 cx + 144) = Some (x_sh cx))
  by (apply HSL; apply in_or_app; left; cbn [LT_L In]; repeat (first [left; reflexivity | right])).
assert (W152 : rdword (rdW W mem) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N)))
  by (apply HSL; apply in_or_app; right; left; reflexivity).
assert (W168 : rdword (rdW W mem) (x_s1 cx + 168) = Some m)
  by (apply HSL; apply in_or_app; left; cbn [LT_L In]; repeat (first [left; reflexivity | right])).
assert (W184 : rdword (rdW W mem) (x_s1 cx + 184) = Some (m + seg_spec.MC_N))
  by (apply HSL; apply in_or_app; left; cbn [LT_L In]; repeat (first [left; reflexivity | right])).
pose proof HCM as (_ & HMC).
assert (HN0 : sa_val (rdW W mem) (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) /\
  (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply s20_mconf_n; eauto).
destruct HN0 as (Hnv & Hn32).
assert (Hz : rdW W mem (shadow_addr (m + seg_spec.MC_N)) = Some 0) by (eapply s20_mn_shadow; eauto).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (subst n; lia).
(* the shadow addresses of m + 0x2000 and of FR, without division *)
pose proof (Z.div_mod (m + seg_spec.MC_N) 8 ltac:(lia)) as Dm.
pose proof (Z.mod_pos_bound (m + seg_spec.MC_N) 8 ltac:(lia)) as Mm.
assert (Hshm : shadow_addr (m + seg_spec.MC_N) = SHADOW_OFF + (m + seg_spec.MC_N) / 8) by reflexivity.
set (qm := (m + seg_spec.MC_N) / 8) in *.
pose proof (Z.div_mod (x_fr cx) 8 ltac:(lia)) as DF.
assert (HF8 : x_fr cx mod 8 = 0).
{ destruct (Z.mod_divide (x_fr cx) 32 ltac:(lia)) as [Hd _]. destruct (Hd HF32) as [q Hq].
  rewrite Hq. replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (Hxsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
set (qF := x_fr cx / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
unfold FO_PROBE in W104.
pose proof (s20e_seedA W regs mem (x_s1 cx) (x_fr cx + 192) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) m n
  R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hn
  W104 W144 W152 W168 W184 Hz Hnv ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (SHOK : sh_ok SEGS s20e_X [] (s20e_EA regs (x_fr cx + 192) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) m n)
  (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20e_EA regs (x_fr cx + 192) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) m n))
  by (unfold s20e_EA; apply Eimg_env).
remember (s20e_EA regs (x_fr cx + 192) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) m n) as E eqn:HE.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs r)
  by (intros k0 r Hk; rewrite HE; unfold s20e_EA; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [x_fr cx + 192; x_sh cx; shadow_addr (m + seg_spec.MC_N); m; m + seg_spec.MC_N; n])
    (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; unfold s20e_EA; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth map] in E32, E33, E34, E35, E36, E37. clear EX HE.
unfold cfg_at. change (w64 (BASE + LO_K856bc)) with (Z_to_bv 64 (BASE + LO_K856bc)).
(* 0x856bc .. 0x856d0: s10 := SH(m + 0x2000), check 25 (its shadow byte 0: bnez falls through), a0 := m->n;
   the run stops at blez a0 *)
paj_run_tok RUN HS HJ SHOK s20e_span.
{ awr_ok_tac. }
s20e_keep0 K1.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
assert (HZ0 : sa_zs (rdW W mem) (x_sh cx + 24) [0xf8; 0xf8; 0xf8]) by exact (s20e_zs_probe _ _ LFO0 HSH).
psrr_branch_tok RUN BR HS SHOK s20e_span.
- (* blez taken: m->n = 0, no turn; 0x856d0 jumps to 0x85780 (N) *)
  assert (Hn0 : n <= 0).
  { cbn [branch_taken sv_denot] in Hc. rewrite E37, Z.add_0_r, (unsigned_lit_small n) in Hc by lia.
    rewrite bv_lts_small in Hc by lia. destruct (Z.ltb_spec 0 n); [discriminate Hc | lia]. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20e_span LO_N.
  { awr_ok_tac. }
  s20e_keep0 K2.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (26%bv : bv 5) P26.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha _; rewrite K2, K1 by exact Ha; reflexivity).
  assert (HZ1 : sa_zs (rdW W (ms_mem ms)) (x_sh cx + 24) [0xf8; 0xf8; 0xf8]).
  { intros i Hi. cbn [length] in Hi. rewrite K2, K1 by lia. exact (HZ0 i Hi). }
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  apply (HN fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm HCTX2).
  rewrite P26, E34. reflexivity.
- (* blez not taken: 0 < m->n; 0x856d4 .. 0x856fc, the loop's registers, to H 0 at 0x85700 *)
  assert (Hn0 : 0 < n).
  { cbn [branch_taken sv_denot] in Hc. rewrite E37, Z.add_0_r, (unsigned_lit_small n) in Hc by lia.
    rewrite bv_lts_small in Hc by lia. destruct (Z.ltb_spec 0 n); [lia | discriminate Hc]. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20e_span LO_H.
  { awr_ok_tac. }
  s20e_keep0 K2.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha _; rewrite K2, K1 by exact Ha; reflexivity).
  assert (HZ1 : sa_zs (rdW W (ms_mem ms)) (x_sh cx + 24) [0xf8; 0xf8; 0xf8]).
  { intros i Hi. cbn [length] in Hi. rewrite K2, K1 by lia. exact (HZ0 i Hi). }
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  assert (Hlt : (0 < length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold n in Hn0; lia).
  assert (HLR : s20_lregs cx (ms_regs ms) m 0).
  { unfold s20_lregs.
    split; [rewrite P18; reflexivity|].
    split; [rewrite P19; change (ew E 248) with (ew E (A_OBJ 7)); apply bv_eq;
      rewrite (HEI (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); unfold w64;
      rewrite unsigned_lit_small by exact (pa_val_range (A_OBJ 7)); reflexivity|].
    split; [rewrite P20, E35; unfold w64, seg_spec.mseg_addr; change (Z.of_nat 0) with 0;
      rewrite Z.mul_0_r, Z.add_0_r; reflexivity|].
    split; [rewrite P21, E33; reflexivity|].
    split; [rewrite P22; reflexivity|].
    split; [rewrite P23; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite P25, E32; reflexivity|].
    rewrite P26, E34; reflexivity. }
  exact (HH fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm Hlt HCTX2 HLR).
Qed.

(* the environment of the seed at Z i *)
Definition s20e_EZ (regs : bvmap 5 word) (mn n : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [mn; n])).

(* the seed at Z i *)
Lemma s20e_seedZ : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 sh shm mn n i,
  getr regs 9 = w64 s1 -> getr regs 21 = w64 sh -> getr regs 26 = w64 shm -> getr regs 18 = w64 i ->
  0 <= s1 -> s1 + 192 <= 2 ^ 64 -> SHADOW_OFF <= sh <= 0x10007fff8000 -> 0 <= shm -> shm + 1 <= 2 ^ 64 ->
  0 <= mn -> mn + 4 <= 2 ^ 64 -> 0 <= n <= 32 -> 0 <= i <= 31 ->
  (forall o, 24 <= o < 27 -> apresent (w_H W) mem (sh + o)) ->
  rdW W mem shm = Some 0 -> rdword (rdW W mem) (s1 + 184) = Some mn -> sa_val (rdW W mem) mn 4 n ->
  (sh + 27 <= shm \/ shm + 1 <= sh + 24) -> (sh + 27 <= s1 + 184 \/ s1 + 192 <= sh + 24) ->
  (sh + 27 <= mn \/ mn + 4 <= sh + 24) -> (shm + 1 <= s1 + 184 \/ s1 + 192 <= shm) ->
  (shm + 1 <= mn \/ mn + 4 <= shm) -> (s1 + 192 <= mn \/ mn + 4 <= s1 + 184) ->
  st_ok_pi SEGS VAL (s20e_EZ regs mn n) s20e_ssZ
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_Z)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 sh shm mn n i R9 R21 R26 R18 H1 H2 Hsh Hshm1 Hshm2 Hmn1 Hmn2 Hn Hi Hpres Hz W184 Hv
  D1 D2 D3 D4 D5 D6.
unfold SHADOW_OFF in Hsh.
set (E := s20e_EZ regs mn n).
set (X := map (Z_to_bv 64) [mn; n]).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs X) k)
  by (intros k Hk; subst E X; unfold s20e_EZ; apply Eimg_low; exact Hk).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 i)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E21 : ew E 21 = Z_to_bv 64 sh)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E26 : ew E 26 = Z_to_bv 64 shm)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j X (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
subst X. cbn [Nat.add nth map] in E32, E33. clear EX.
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv0. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv0. }
pose proof (VB 9%nat s1 E9 ltac:(lia)) as V9.
pose proof (VB 21%nat sh E21 ltac:(lia)) as V21.
pose proof (VB 26%nat shm E26 ltac:(lia)) as V26.
pose proof (VB 32%nat mn E32 ltac:(lia)) as V32.
destruct (aview_byte SEGS _ _ _ _ Hz) as (bz & Ebz & Ez & _).
assert (HVz : val_mem SEGS (mrestrict (w_H W) mem) (shm + 0) (N.to_nat 1) 0).
{ intros k0 Hk0. assert (k0 = 0%nat) by (cbn in Hk0; lia). subst k0. change (Z.of_nat 0) with 0.
  rewrite !Z.add_0_r. rewrite Ebz. f_equal. apply bv_eq. rewrite <- Ez. reflexivity. }
unfold s20e_ssZ. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s20e_EZ. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s20e_rgZ. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite V21. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite V26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ shm 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact HVz].
  + rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 184 8 (SOff 32 0) mn);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ W184)].
  + rewrite V32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mn 0 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 4) with 32; lia | cbn; lia | rewrite Z.add_0_r; exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hv)].
- apply pairwise_disjoint_of_extents. unfold s20e_rgZ, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V9, V21, V26, V32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s20e_faZ f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, E21, E33, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Lemma s20_L3 : forall i, S20A_H B MT (Datatypes.S i) -> S20A_N B MT -> S20_Z_stmt B MT i.
Proof.
intros i HH HN. unfold S20_Z_stmt.
intros cx ly S W regs mem md k acc c m HBs Hfrm Hlt HCTX HLR HPZ.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFLW & H176 & HSH).
pose proof HLR as (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
pose proof (s20e_sp cx HBs) as (Hsp0 & Hsp16 & Hs1 & Hs32).
pose proof (s20e_fr cx ly S W regs mem md k LFO_P HFR) as (EFR & HF4 & HFc & HF32 & HFapp & HFsh & HFsep).
pose proof HJ as (HAR & _).
pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & Hmapp & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
rewrite HRM in Hmc, Hmapp.
pose proof (HFsep m seg_spec.SEG_M_SIZE HMin) as HmF. rewrite HRM in HmF.
pose proof asan_consts as (HAC & _ & _ & _ & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HMN : seg_spec.MC_N = 0x2000) by reflexivity.
assert (W184 : rdword (rdW W mem) (x_s1 cx + 184) = Some (m + seg_spec.MC_N))
  by (apply HSL; apply in_or_app; left; cbn [LT_L In]; repeat (first [left; reflexivity | right])).
pose proof HCM as (_ & HMC).
assert (HN0 : sa_val (rdW W mem) (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) /\
  (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply s20_mconf_n; eauto).
destruct HN0 as (Hnv & Hn32).
assert (Hz : rdW W mem (shadow_addr (m + seg_spec.MC_N)) = Some 0) by (eapply s20_mn_shadow; eauto).
set (n := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hn : 0 <= n <= 32) by (subst n; lia).
assert (Hilt : Z.of_nat i < n) by (subst n; lia).
(* the shadow addresses of m + 0x2000 and of FR, without division *)
pose proof (Z.div_mod (m + seg_spec.MC_N) 8 ltac:(lia)) as Dm.
pose proof (Z.mod_pos_bound (m + seg_spec.MC_N) 8 ltac:(lia)) as Mm.
assert (Hshm : shadow_addr (m + seg_spec.MC_N) = SHADOW_OFF + (m + seg_spec.MC_N) / 8) by reflexivity.
set (qm := (m + seg_spec.MC_N) / 8) in *.
pose proof (Z.div_mod (x_fr cx) 8 ltac:(lia)) as DF.
assert (HF8 : x_fr cx mod 8 = 0).
{ destruct (Z.mod_divide (x_fr cx) 32 ltac:(lia)) as [Hd _]. destruct (Hd HF32) as [q Hq].
  rewrite Hq. replace (q * 32) with ((q * 4) * 8) by ring. apply Z_mod_mult. }
assert (Hxsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
set (qF := x_fr cx / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
pose proof (s20e_seedZ W regs mem (x_s1 cx) (x_sh cx) (shadow_addr (m + seg_spec.MC_N)) (m + seg_spec.MC_N) n
  (Z.of_nat i) R9 R21 R26 R18 ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) Hn ltac:(lia) (fun o Ho => HFsh o ltac:(lia)) Hz W184 Hnv
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS0.
(* s7 = -8 as a literal, so that the three stores leave literal chunks *)
pose proof (st_ok_pi_pin_reg' _ _ _ 23%bv (-8) HS0 R23 eq_refl) as HS. clear HS0.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
assert (SHOK : sh_ok SEGS s20e_X [] (s20e_EZ regs (m + seg_spec.MC_N) n) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20e_EZ regs (m + seg_spec.MC_N) n)) by (unfold s20e_EZ; apply Eimg_env).
remember (s20e_EZ regs (m + seg_spec.MC_N) n) as E eqn:HE.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs r)
  by (intros k0 r Hk; rewrite HE; unfold s20e_EZ; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [m + seg_spec.MC_N; n]) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HE; unfold s20e_EZ; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth map] in E32, E33. clear EX HE.
assert (U21 : bv_unsigned (ew E 21) = x_sh cx)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + LO_Z)) with (Z_to_bv 64 (BASE + LO_Z)).
(* 0x85748 .. 0x8576c: the probe out of scope (three 0xf8 shadow bytes), check 26 (its shadow byte 0: bnez falls
   through), a0 := m->n, s2 := i + 1, s4 := &m->seg[i + 1]; the run stops at blt s2,a0 *)
paj_run_tok RUN HS HJ SHOK s20e_spanZ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact U21 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, (x_fpos cx).
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes 3 / 8) with 64. rewrite <- EFR.
    change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
s20e_keepZ K1 U21 (x_sh cx + 24) (x_sh cx + 27).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s20e_spanZ.
- (* blt taken: i + 1 < m->n, back to the head H (i + 1) at 0x85700 *)
  assert (Hi1 : Z.of_nat i + 1 < n).
  { cbn [branch_taken sv_denot] in Hc. rewrite (EE 18%nat 18%bv eq_refl), R18, E33 in Hc. unfold w64 in Hc.
    rewrite (unsigned_lit_small (Z.of_nat i)), (unsigned_lit_small n), Z.add_0_r in Hc by lia.
    rewrite bv_lts_small in Hc by lia. apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20e_spanZ LO_H.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact U21 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, (x_fpos cx).
      split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 3 / 8) with 64. rewrite <- EFR.
      change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
    repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
  s20e_keepZ K2 U21 (x_sh cx + 24) (x_sh cx + 27).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  (* the three 0xf8 bytes, from the chunks the stores left in the first region *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (RZ : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r0)
      by exact (st_ok_pi_region_nth E _ (restrict (w_H W) ms) 0%nat r0 HS ltac:(vm_compute; reflexivity)) end.
  destruct RZ as (_ & _ & _ & CZ). cbn [YP09.r_base YP09.r_chunks base_val] in CZ. rewrite U21 in CZ.
  pose proof (s10_zs_ok E (w_H W) (ms_mem ms) (x_sh cx) _ [0xf8; 0xf8; 0xf8] 24 CZ ltac:(vm_compute; reflexivity))
    as HZ1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha Hna; rewrite (K2 a Ha Hna), (K1 a Ha Hna); reflexivity).
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  assert (Hlt' : (Datatypes.S i < length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold n in Hi1; lia).
  assert (HLR' : s20_lregs cx (ms_regs ms) m (Datatypes.S i)).
  { unfold s20_lregs.
    split; [rewrite P18, (EE 18%nat 18%bv eq_refl), R18; unfold w64; rewrite unsigned_lit_small by lia;
      f_equal; lia|].
    split; [rewrite P19, (EE 19%nat 19%bv eq_refl), R19; reflexivity|].
    split; [rewrite P20, (EE 20%nat 20%bv eq_refl), R20; unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite P21, (EE 21%nat 21%bv eq_refl), R21; reflexivity|].
    split; [rewrite P22, (EE 22%nat 22%bv eq_refl), R22; reflexivity|].
    split; [rewrite P23; reflexivity|].
    split; [rewrite P25, (EE 25%nat 25%bv eq_refl), R25; reflexivity|].
    rewrite P26, (EE 26%nat 26%bv eq_refl), R26; reflexivity. }
  exact (HH fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm Hlt' HCTX2 HLR').
- (* blt not taken: m->n = i + 1, 0x85770 jumps to 0x85780 (N) *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK s20e_spanZ LO_N.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact U21 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, (x_fpos cx).
      split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 3 / 8) with 64. rewrite <- EFR.
      change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
    repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
  s20e_keepZ K2 U21 (x_sh cx + 24) (x_sh cx + 27).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  pmkst HS.
  (* the three 0xf8 bytes, from the chunks the stores left in the first region *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (RZ : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r0)
      by exact (st_ok_pi_region_nth E _ (restrict (w_H W) ms) 0%nat r0 HS ltac:(vm_compute; reflexivity)) end.
  destruct RZ as (_ & _ & _ & CZ). cbn [YP09.r_base YP09.r_chunks base_val] in CZ. rewrite U21 in CZ.
  pose proof (s10_zs_ok E (w_H W) (ms_mem ms) (x_sh cx) _ [0xf8; 0xf8; 0xf8] 24 CZ ltac:(vm_compute; reflexivity))
    as HZ1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (26%bv : bv 5) P26.
  assert (HRK : s20_rkept regs (ms_regs ms)).
  { unfold s20_rkept. rewrite P2, P3, P4, P8, P9.
    rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
      (EE 9%nat 9%bv eq_refl). repeat split; reflexivity. }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha Hna; rewrite (K2 a Ha Hna), (K1 a Ha Hna); reflexivity).
  assert (HCTX2 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc LFO0 c m)
    by (eapply s20_ctx_store; try eassumption; try reflexivity).
  apply (HN fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m HBs Hfrm HCTX2).
  rewrite P26, (EE 26%nat 26%bv eq_refl), R26. reflexivity.
Qed.

End e.
End f.
End d.
