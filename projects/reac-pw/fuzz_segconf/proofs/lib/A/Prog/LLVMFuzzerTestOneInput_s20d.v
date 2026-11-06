(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB_Base.v, with its module paths and module names changed; 985 of its 1076 lines of code are new or changed and 1922 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s20, piece d:
   the segment lemmas s20_L2 (A i -> Z i: strlen, m_find, check_absent on a miss) and s20_L4 (N -> NZ: m_find and
   check_absent of "nosuch0") of LLVMFuzzerTestOneInput_s20.v, proved against their statements as written.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s20k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c reac_segconf_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.
(* ---- the points of the two segments (offsets from BASE = 0x84d34) ----
   S20_A_stmt's code (0x85720 .. 0x85748): a0 = probe; jal strlen -> 0x85728; a2 = a0, a0 = m, a1 = probe;
   jal m_find -> 0x85738; bnez a0,0x85748; a0 = c, a1 = probe; jal check_absent -> 0x85748 = BASE + LO_Z.
   S20_N_stmt's code (0x85780 .. 0x857a8): a1 = "nosuch0", a2 = 7, a0 = m; jal m_find -> 0x85794;
   bnez a0,0x857a8; a1 = "nosuch0", a0 = c; jal check_absent -> 0x857a8 = BASE + LO_NZ. *)
Definition LO_SLRA : Z := 0x9f4.   (* 0x85728: strlen returned *)
Definition LO_MFRA : Z := 0xa04.   (* 0x85738: m_find returned (the probe) *)
Definition LO_CARA : Z := 0xa14.   (* 0x85748 = LO_Z: check_absent returned (the probe) *)
Definition LO_NMRA : Z := 0xa60.   (* 0x85794: m_find returned ("nosuch0") *)
Definition LO_NCRA : Z := 0xa74.   (* 0x857a8 = LO_NZ: check_absent returned ("nosuch0") *)

(* ---- the symbolic states ----
   Every register is its own atom; the three extra atoms are 32 = the probe (FR + 192), 33 = c, 34 = m. The one
   region is the s1 slot window [104, 176) read-only, with the three words 104(s1) = probe, 160(s1) = c and
   168(s1) = m as chunks. No instrumented check lies in either segment (the checks of m->n are segment S11's
   other pieces), so the shadow-entry list is empty and the shadow base is a literal. *)
Definition S20Dx : sv := SLit SHADOW_OFF.
Definition S20Dspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s20d_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 104 176 104 104
    [YP09.mkChunk 104 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0));
     YP09.mkChunk 168 (CVal 8 (SOff 34 0))].
(* the fact on s1 (the frame base, 32-aligned, in the stack band) and the fact a0 carries at a seed after a call *)
Definition s20d_facts (alo ahi : Z) : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (10%nat, mkAF alo ahi 0)] [] [].
Definition s20d_ss (pc alo ahi : Z) : sstate := mkSS pc sr_atoms [s20d_rg] None (s20d_facts alo ahi).

(* the callee-saved registers a straight-line run of either segment keeps: every one of them is still its own
   atom in the run's symbolic state, so prreg reads it back as the entry's register *)
Ltac s20d_preserved HS EEo :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia);
  repeat (destruct Hc as [-> | Hc]); try subst r;
  lazymatch goal with |- getr _ ?rr = getr _ ?rr =>
    let P := fresh "P" in prreg HS rr P; rewrite P; apply EEo; reflexivity end.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the environment of a seed: the registers, then the probe, c and m ---- *)
Definition s20d_E (regs : bvmap 5 word) (p c m : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [p; c; m])).
Lemma s20d_E_reg : forall regs p c m n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (s20d_E regs p c m) n = getr regs r.
Proof.
intros regs p c m n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s20d_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma s20d_E_extra : forall regs p c m j, (j < 3)%nat ->
  ew (s20d_E regs p c m) (32 + j) = Z_to_bv 64 (nth j [p; c; m] 0).
Proof.
intros regs p c m j Hj. unfold s20d_E. rewrite Eimg_low by (unfold A_TEXT; cbn; lia).
rewrite ew_Ereg_extra. apply (map_nth (Z_to_bv 64) [p; c; m] 0 j).
Qed.
(* an image atom, as a value rather than as its bv_unsigned *)
Lemma s20d_E_img : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = Z_to_bv 64 (VAL n).
Proof. intros E n HE Hn. rewrite <- (HE n Hn). rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* a word read through the reader is a 64-bit value (_s19's s19_rdword_rng) *)
Lemma s20d_rdword_rng : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v E. unfold rdword in E.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (sa_aview_rng _ _ _ _ _ E0). pose proof (sa_aview_rng _ _ _ _ _ E1).
pose proof (sa_aview_rng _ _ _ _ _ E2). pose proof (sa_aview_rng _ _ _ _ _ E3).
pose proof (sa_aview_rng _ _ _ _ _ E4). pose proof (sa_aview_rng _ _ _ _ _ E5).
pose proof (sa_aview_rng _ _ _ _ _ E6). pose proof (sa_aview_rng _ _ _ _ _ E7).
lia.
Qed.
(* an 8-byte chunk of a region, from the word the reader holds there (_s19's s19_chunk8) *)
Lemma s20d_chunk8 : forall (W : world SEGS) mem E base off (n : nat) x,
  ew E n = Z_to_bv 64 x -> rdword (rdW W mem) (base + off) = Some x ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E base off n x En Hrd.
pose proof (s20d_rdword_rng _ _ _ _ Hrd) as R.
apply (chunk_ok_val SEGS E _ base off 8 _ x);
  [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R | zside | exact (val_mem_of_rdword SEGS _ _ _ _ Hrd)].
cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- the seed at a point of either segment ---- *)
Lemma s20d_seed : forall pc alo ahi (W : world SEGS) (regs : bvmap 5 word) mem s1 p c m,
  getr regs 9 = w64 s1 -> 0x7fff7f800000 <= s1 -> s1 + 192 <= 2 ^ 47 ->
  alo <= bv_unsigned (getr regs 10) <= ahi ->
  rdword (rdW W mem) (s1 + 104) = Some p -> rdword (rdW W mem) (s1 + 160) = Some c ->
  rdword (rdW W mem) (s1 + 168) = Some m ->
  st_ok_pi SEGS VAL (s20d_E regs p c m) (s20d_ss pc alo ahi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S20Dx [] (s20d_E regs p c m) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (s20d_E regs p c m).
Proof.
intros pc alo ahi W regs mem s1 p c m R9 Hs1 Hs1' Ha0 Hp Hc Hm.
set (E := s20d_E regs p c m).
assert (E9 : ew E 9 = w64 s1) by exact (eq_trans (s20d_E_reg regs p c m 9 9%bv eq_refl) R9).
assert (E32 : ew E 32 = Z_to_bv 64 p) by exact (s20d_E_extra regs p c m 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by exact (s20d_E_extra regs p c m 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by exact (s20d_E_extra regs p c m 2 ltac:(lia)).
assert (E10 : ew E 10 = getr regs 10) by exact (s20d_E_reg regs p c m 10 10%bv eq_refl).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
split; [|split; [apply Forall_nil | unfold E, s20d_E; apply Eimg_env]].
unfold s20d_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, s20d_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, s20d_rg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + exact (s20d_chunk8 W mem E s1 104 32 p E32 Hp).
  + exact (s20d_chunk8 W mem E s1 160 33 c E33 Hc).
  + exact (s20d_chunk8 W mem E s1 168 34 m E34 Hm).
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [s20d_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, E10, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* a run whose only region has an empty write window changes no byte *)
Lemma s20d_nowin_kept : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [s20d_rg] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [s20d_rg] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin Hr. cbn [windows map In] in Hin.
destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* a callee-saved register a call keeps *)
Lemma s20d_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

(* ---- sub-range facts of SegABase's shadow and location forms ---- *)
Lemma s20d_addr_le : forall rd q n n', sa_addr rd q n -> 0 <= n' <= n -> sa_addr rd q n'.
Proof.
intros rd q n n' (H0 & H63 & Hm & Hra & Hv) Hn.
split; [exact H0|]. split; [lia|]. split.
- unfold amem_range in *. lia.
- split; [intros x Hx; exact (Hra x ltac:(lia))|].
  intros Hn' s Hs. apply Hv; [lia|]. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (q + n' - 1) (q + n - 1) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (2147450880 + (q + n' - 1) / 8) (2147450880 + (q + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF in *. lia.
Qed.
Lemma s20d_img_le : forall (Bs : asyms) q n n', sa_img SEGS Bs q n -> 0 <= n' <= n -> sa_img SEGS Bs q n'.
Proof. intros Bs q n n' H Hn x Hx. exact (H x ltac:(lia)). Qed.
Lemma s20d_bytes_app_l : forall rd a l1 l2, sa_bytes rd a (l1 ++ l2) -> sa_bytes rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite <- (app_nth1 l1 l2 ZB0 Hi).
apply H. rewrite length_app. lia.
Qed.
Lemma s20d_zs_app_l : forall rd a l1 l2, sa_zs rd a (l1 ++ l2) -> sa_zs rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite <- (app_nth1 l1 l2 0 Hi).
apply H. rewrite length_app. lia.
Qed.
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

Let RUNTO := paj_run_to B LAWS.
Let RUN := paj_run B LAWS.

(* the entry sp and the base register s1 (_s19's s19_bounds) *)
Lemma s20d_bounds : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 352 <= x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold STK_LLVMFuzzerTestOneInput in Hslo.
unfold x_s1, x_sp0, LT_FRAME. set (s := spZ (x_regs cx)) in *.
pose proof (Z.div_mod s 16 ltac:(lia)) as D1. pose proof (Z.div_mod (s - 320) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (s - 320) 32 ltac:(lia)) as M2.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split.
- replace (s - 320 - (s - 320) mod 32) with ((s - 320) / 32 * 32) by lia. apply Z.mod_mul. lia.
- lia.
Qed.

(* s20_ctx carried to a state that the journal reaches, that keeps every byte outside a window below s1 and
   whose registers the call preserved; the state allocates nothing (sa_noalloc) *)
Lemma s20d_carry : forall cx ly S (W : world SEGS) regs mem md k acc o c m
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 lo,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  aregs_preserved regs regs2 ->
  alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  (exists f, S2 = set_fs f S) ->
  s20_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 k acc o c m.
Proof.
intros cx ly S W regs mem md k acc o c m ly2 S2 W2 regs2 mem2 md2 lo HB HCTX HJ2 HP Hlo HK HPerm [f HS2].
assert (HRK : s20_rkept regs regs2).
{ unfold s20_rkept.
  split; [exact (s20d_pres regs regs2 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  split; [exact (s20d_pres regs regs2 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  split; [exact (s20d_pres regs regs2 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  split; [exact (s20d_pres regs regs2 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))|].
  exact (s20d_pres regs regs2 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). }
assert (HKP : s20_kept B cx c m W mem W2 mem2).
{ eapply s20_kept_of_win with (lo := lo); try eassumption.
  intros a Ha Hw _. exact (HK a Ha Hw). }
assert (HBUD : lt_bud MT cx S2 k acc 6).
{ pose proof HCTX as HC2. destruct HC2 as ((_ & _ & _ & Hb) & _).
  destruct Hb as (Hk0 & Hr0 & Hkr & Hmo & Hacc & Hxm).
  split; [exact Hk0|]. split; [exact Hr0|]. split; [exact Hkr|].
  split; [rewrite HS2; (eapply mo_le_set_fs_r; eassumption)|]. split; [exact Hacc | exact Hxm]. }
eapply s20_ctx_carry; try eassumption.
Qed.

(* a program call from a point of the segment (sp = s1) to a callee with no footprint and no allocator event
   whose post keeps every byte outside its window (m_find, check_absent), through PaCall's cl_callS; back at
   BASE + ret the walk's journal holds again and s20_ctx is carried (_s19's s19_call, with the callee's own
   answer X passed on) *)
Lemma s20d_call : forall cx ly S (W : world SEGS) regs mem md k acc o c m (STKF AF ret : Z)
  (X : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) Q,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  0 <= STKF <= ASTACK -> getr regs 1 = w64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall ch, afn_pre SEGS B STKF ly S W regs mem md ch ->
     SRr SEGS W (cfg_at SEGS AF regs mem md) (apost_base SEGS B STKF [] regs ly S W mem md 0 X)) ->
  (forall ly' S' (W' : world SEGS) regs' mem' md', X ly' S' W' regs' mem' md' ->
     sa_kept SEGS W mem W' mem' regs STKF (fun _ => False) /\ sa_noalloc B ly S ly' S') ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2, wle W W2 ->
     s20_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 k acc o c m ->
     aregs_preserved regs regs2 -> X ly2 S2 W2 regs2 mem2 md2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - STKF <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + ret) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 AF) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k acc o c m STKF AF ret X Q HBASE HCTX HSTK R1 Hret Hret2 HCALLEE HQX HK.
destruct (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof HBASE as (HPRE0 & HPRES0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HCTX as (HCORE & _).
destruct HCORE as (HFR & _ & _ & _).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & _).
assert (Hsp : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0 : s0Z regs = x_sp0 cx).
{ unfold s0Z. rewrite F8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* the frame chain at the call: the stack from s1 up is readable (the entry's astack_pres, kept by the journal) *)
assert (HRD : astack_rd ly (rdW W mem) (x_s1 cx)).
{ apply (astack_rd_of_pres SEGS). apply (astack_pres_mono _ _ _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
  - unfold STK_LLVMFuzzerTestOneInput. lia.
  - eapply (astack_pres_journal SEGS B pa_segs_low); [exact HJ | exact HPRES0 |].
    intros a (r & Hr & Ha) Ha2. exfalso. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch & Hch).
eapply SRr_bind.
{ apply (cl_callS B LAWS W regs mem (Z_to_bv 64 AF) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STKF [] 0
    (x_s1 cx - x_sp0 cx) (getr regs 1) ch
    X
    HJ Hsp).
  - pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D1.
    replace (x_s1 cx - x_sp0 cx) with ((x_s1 cx / 32 * 2 - x_sp0 cx / 16) * 16).
    + apply Z.mod_mul. lia.
    + pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D2. lia.
  - lia.
  - lia.
  - unfold STK_LLVMFuzzerTestOneInput, ASTACK in *. lia.
  - rewrite F3. exact Hgp0.
  - rewrite F4. exact Htp0.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hret2].
  - rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia. rewrite Hs0. exact Hch.
  - intros HPRE. exact (HCALLEE ch HPRE).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & HX).
destruct (HQX ly2 S2 W2 regs2 mem2 md2 HX) as (Hkp & Hna).
rewrite Z.add_0_r in HJ2. rewrite R1.
pose proof Hna as (HPerm & -> & Hfs).
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - STKF <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha Hw. apply (Hkp a Ha); [|tauto]. unfold spZ. rewrite F2. unfold w64.
  rewrite unsigned_lit_small by lia. exact Hw. }
apply (HK ly S2 W2 regs2 mem2 md2 Hle); [| exact HP | exact HX | exact HKEEP].
eapply (s20d_carry cx ly S W regs mem md k acc o c m ly S2 W2 regs2 mem2 md2 (x_s1 cx - STKF));
  [exact HBASE | exact HCTX | exact HJ2 | exact HP | unfold ASTACK in HSTK; lia | exact HKEEP | exact HPerm
  | exact Hfs].
Qed.

(* the strlen wrapper at a point of the segment, through PaArt's aj_art_at (window ESTACK, Eb = False), in the
   donor's aw_snl_art_loc / aw_strnlen_loc form (fuzz_command _s41.v:377-454) *)
Lemma s20d_strlen : forall cx ly S (W : world SEGS) regs mem md k acc o c m (ret : Z) (x : Z) (s : list byte) Q,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  getr regs 1 = w64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regs 10 = w64 x -> 0 < x ->
  astr_at SEGS W mem x s ->
  aread_ok SEGS ESTACK W regs mem x (astr_len s + 1) ->
  atail_vis SEGS W mem (x + astr_len s) ->
  (forall regs2 mem2 md2,
     s20_ctx B MT cx ly S W regs2 mem2 md2 k acc o c m ->
     aregs_preserved regs regs2 -> getr regs2 10 = w64 (astr_len s) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W mem a) ->
     SRr SEGS W (cfg_at SEGS (BASE + ret) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIG SS___interceptor_trampoline_strlen)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k acc o c m ret x s Q HBASE HCTX R1 Hret Hret2 R10 Hx Hstr Hrd Htl HK.
destruct (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof HBASE as (HPRE0 & HPRES0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HCTX as (HCORE & _).
destruct HCORE as (HFR & HIMG & _ & _).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Hsp : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hal : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D1.
  replace (x_s1 cx - x_sp0 cx) with ((x_s1 cx / 32 * 2 - x_sp0 cx / 16) * 16).
  - apply Z.mod_mul. lia.
  - pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D2. lia. }
assert (HraT : YK0s.ret_ok (getr regs 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | exact Hret2]).
(* the read-only image bytes the strlen interceptor reads, and the errno cell of the record *)
assert (HENV : api_env SEGS B)
  by (first [exact (pal_env B TL) | exact (pal_env TL) | exact (@pal_env _ _ _ B TL) | exact (@pal_env _ _ _ _ B TL)]).
assert (HROM : rt_rom_view SEGS B W mem).
{ destruct HIMG as (HRO & _ & _). intros a Hr Ho He. apply HRO; [left; exact Hr | exact Ho | exact He]. }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low HENV ESTACK (fun _ => False)
    (SIG SS___interceptor_trampoline_strlen) W regs mem STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k (x_s1 cx - x_sp0 cx)
    (getr regs 1) (fun regs' _ => getr regs' 10 = w64 (astr_len s))
    HJ Hsp Hal ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HLS; lia) eq_refl (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W regs mem md x s).
  - exact (ecall_pre_stk_at SEGS B ESTACK STK_LLVMFuzzerTestOneInput (x_sp0 cx)
      (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k
      regs (x_s1 cx - x_sp0 cx) HJ Hsp Hal ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HLS; lia) HraT
      ltac:(rewrite F3; exact Hgp0) ltac:(rewrite F4; exact Htp0)).
  - exact R10.
  - exact Hx.
  - exact Hstr.
  - exact Hrd.
  - exact Htl.
  - exact HROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & HK2).
rewrite R1.
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W mem a).
{ intros a Ha Hw. apply (HK2 a Ha); [|tauto]. replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  exact Hw. }
apply (HK regs2 mem2 md2); [| exact HP | exact HQ | exact HKEEP].
eapply (s20d_carry cx ly S W regs mem md k acc o c m ly S W regs2 mem2 md2 (x_s1 cx - ESTACK));
  [exact HBASE | exact HCTX | exact HJ2 | exact HP | rewrite Hes; lia | exact HKEEP | apply Permutation_refl
  | exists (st_fs S); destruct S; reflexivity].
Qed.

(* ---- the facts of the literal "nosuch0" (A_OBJ 8 = 0x21040) ---- *)
Lemma s20d_obj8 : VAL (A_OBJ 8) = seg_litA_fz LIT_NOSUCH.
Proof. rewrite (VOBJS 8%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma s20d_nosuch_lit : forall cx rd, lt_img B cx rd -> sa_lit SEGS B rd (VAL (A_OBJ 8)) LIT_NOSUCH.
Proof.
intros cx rd (_ & HH & _). destruct HH as (_ & _ & HLIT & _). rewrite s20d_obj8.
refine (proj1 (HLIT LIT_NOSUCH _)).
unfold LTOI_FZ_LITS. apply in_or_app. left. unfold LTOI_LITS. cbn [In].
repeat first [left; reflexivity | right].
Qed.

(* st_nev at a point of the segment: the entry's budget, less what the journal has spent *)
Lemma s20d_nev : forall cx ly S (W : world SEGS) regs mem md k acc o c m,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W regs mem md k acc o c m HBASE HCTX.
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & _).
pose proof HCTX as ((HFR & _ & _ & HBUD) & _).
pose proof (proj1 HFR) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn1 & Hk0 & _).
destruct HBUD as (Hb1 & Hb2 & Hb3 & _). lia.
Qed.

(* a seed at a point of either segment, from s20_ctx: the s1 slot window and the a0 fact *)
Lemma s20d_seed_at : forall pc alo ahi cx ly S (W : world SEGS) regs mem md k acc o c m,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  alo <= bv_unsigned (getr regs 10) <= ahi ->
  st_ok_pi SEGS VAL (s20d_E regs (x_fr cx + FO_PROBE) c m) (s20d_ss pc alo ahi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S20Dx [] (s20d_E regs (x_fr cx + FO_PROBE) c m) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (s20d_E regs (x_fr cx + FO_PROBE) c m).
Proof.
intros pc alo ahi cx ly S W regs mem md k acc o c m HBASE HCTX Ha0.
pose proof (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof HCTX as ((HFR & _ & _ & _) & _ & _ & HSL & _).
pose proof HFR as (_ & _ & _ & _ & _ & F9 & _).
assert (Hslot : forall off v, In (off, v) (LT_L cx c m) -> rdword (rdW W mem) (x_s1 cx + off) = Some v)
  by (intros off v Hin; apply HSL; apply in_or_app; left; exact Hin).
apply (s20d_seed pc alo ahi W regs mem (x_s1 cx) (x_fr cx + FO_PROBE) c m F9 ltac:(lia) ltac:(lia) Ha0);
  apply Hslot; unfold LT_L; cbn [In]; repeat first [left; reflexivity | right].
Qed.

(* a0 of a fresh seed when nothing is known of it *)
Lemma s20d_a0_any : forall (regs : bvmap 5 word), 0 <= bv_unsigned (getr regs 10) <= 2 ^ 64 - 1.
Proof.
intros regs. pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Hr.
change (bv_modulus 64) with (2 ^ 64) in Hr. lia.
Qed.

(* 0x85794, with m_find's answer a0: a miss (a0 = 0, and "nosuch0" is absent of the reader's state, so
   check_absent's pre holds and its call is taken) or a hit (a0 a pointer into m, so the bnez goes to
   0x857a8 = BASE + LO_NZ) *)
Lemma s20d_after_mfind : S20A_NZ B MT -> sa_frm0 ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m (a0 : Z),
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc LFO0 c m ->
  getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) -> getr regs 10 = w64 a0 ->
  (a0 = 0 /\ SegModel.absent (x_rcF cx) LIT_NOSUCH = true) \/ 4096 <= a0 <= 2 ^ 63 ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_NMRA) regs mem md) (lt_post B MT cx).
Proof.
intros HNZ Hfrm cx ly S W regs mem md k acc c m a0 HBASE HCTX R26 R10 Hcase.
pose proof (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HC as (HCin & Hc4 & Hc16 & HCad). pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (_ & _ & Hcc & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & _).
assert (HRC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (HRM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity.
rewrite HRC in Hcc. rewrite HRM in Hmc.
assert (HLN : Z.of_nat (length LIT_NOSUCH) = 7) by (vm_compute; reflexivity).
destruct HCM as (HRCF & HMCF).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20d_E regs (x_fr cx + FO_PROBE) c m) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs _ c m n rr Hn)).
assert (E33 : ew (s20d_E regs (x_fr cx + FO_PROBE) c m) 33%nat = Z_to_bv 64 c)
  by (apply (s20d_E_extra regs (x_fr cx + FO_PROBE) c m 1%nat); lia).
destruct Hcase as [(-> & HABS) | Hfound].
- (* the miss: the bnez is not taken, a1 := "nosuch0", a0 := c, jal check_absent *)
  destruct (s20d_seed_at LO_NMRA 0 (2 ^ 64 - 1) cx ly S W regs mem md k acc LFO0 c m HBASE HCTX
    (s20d_a0_any regs)) as (HS & SHOK & HEI).
  remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
  unfold cfg_at.
  pose proof (st_ok_pi_pin_reg' E _ _ 10%bv 0 HS
    ltac:(first [exact R10 | (cbn [ms_regs restrict mkst]; exact R10)]) eq_refl) as HS2.
  clear HS. rename HS2 into HS.
  paj_run_tok RUN HS HJ SHOK S20Dspan.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
  assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO0 c m).
  { eapply (s20d_carry cx ly S W regs mem md k acc LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
      [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
      | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  rewrite (SIGP SS_check_absent ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  replace (seg_af SS_check_absent) with AF_check_absent by (vm_compute; reflexivity).
  pose proof HCTX1 as (HCORE1 & HC1 & HM1 & HSL1 & HCM1).
  pose proof HCORE1 as (HFR1 & HIMG1 & HBL1 & HBUD1).
  pose proof HIMG1 as (HRO1 & _ & _).
  pose proof (proj1 (proj1 HFR1)) as HAR1.
  pose proof HC1 as (HCin1 & _ & _ & HCad1).
  destruct HCM1 as (HRCF1 & HMCF1).
  pose proof (s20d_nosuch_lit cx (rdW W (ms_mem ms)) HIMG1) as (HL0 & HLSTR & HLPIN & HLRT & HLIMG).
  assert (HADR8 : sa_addr (rdW W (ms_mem ms)) (VAL (A_OBJ 8)) (Z.of_nat (length LIT_NOSUCH) + 1))
    by exact (HLPIN ly S W (ms_mem ms) mdv HAR1).
  assert (HLOC8 : sa_loc SEGS B ly S (VAL (A_OBJ 8)) (Z.of_nat (length LIT_NOSUCH) + 1))
    by (right; right; exact HLIMG).
  assert (Hnrng : 0 <= VAL (A_OBJ 8) < 2 ^ 64).
  { destruct (HLIMG (VAL (A_OBJ 8)) ltac:(lia)) as (Hin & _ & _).
    pose proof (pa_segs_low _ Hin) as Hlo. unfold kLowMemEnd in Hlo. lia. }
  assert (E249 : ew E 249%nat = w64 (VAL (A_OBJ 8)))
    by (unfold w64; apply (s20d_E_img E 249%nat HEI ltac:(unfold A_TEXT, A_LIM; lia))).
  assert (R1' : getr (ms_regs ms) 1 = w64 (BASE + LO_NCRA)) by (rewrite P1; reflexivity).
  assert (R10' : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, E33; reflexivity).
  assert (R11' : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 8))) by (rewrite P11, E249; reflexivity).
  assert (R26' : getr (ms_regs ms) 26 = w64 (shadow_addr (m + seg_spec.MC_N))).
  { rewrite <- R26. exact (s20d_pres regs (ms_regs ms) 26%bv 26 HPR ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). }
  assert (Hnev : st_nev S <= EV_MAX) by (eapply s20d_nev; eassumption).
  assert (HSCA : STK_check_absent = 8288) by (vm_compute; reflexivity).
  assert (HCAPRE : check_absent_c.check_absent_pre SEGS B ly S (rdW W (ms_mem ms)) c (VAL (A_OBJ 8))
    (x_rcF cx) LIT_NOSUCH).
  { split; [|exact HABS].
    split; [lia|]. split; [exact Hc16|]. split; [exact HRCF1|].
    split; [exists c, seg_spec.SEG_C_SIZE; split; [exact HCin1 | lia]|].
    split; [exact HCad1|]. split; [lia|]. split; [exact HLSTR|]. split; [exact HLOC8|].
    split; [exact HADR8 | lia]. }
  eapply (s20d_call cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO0 c m STK_check_absent
    (VAL A_TEXT + AF_check_absent) LO_NCRA
    (fun ly' S' (W' : world SEGS) regs' mem' md' =>
       sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_check_absent (fun _ => False) /\
       sa_noalloc B ly S ly' S')
    (lt_post B MT cx) HBASE HCTX1 ltac:(rewrite HSCA; unfold ASTACK; lia) R1'
    ltac:(unfold LO_NCRA; lia) ltac:(reflexivity)).
  + intros ch HPRE1.
    exact (HCHECK_ABSENT fx ly S W (ms_regs ms) (ms_mem ms) mdv ch c (VAL (A_OBJ 8)) (x_rcF cx) LIT_NOSUCH
      HPRE1 HRO1 R10' ltac:(lia) R11' Hnrng HCAPRE
      ltac:(unfold check_absent_c.EV_check_absent; lia)).
  + intros ly' S' W' regs' mem' md' HQ. exact HQ.
  + intros ly2 S2 W2 regs2 mem2 md2 Hle HCTX2 HPR2 _ HKEEP2.
    assert (R26'' : getr regs2 26 = w64 (shadow_addr (m + seg_spec.MC_N))).
    { rewrite <- R26'. exact (s20d_pres (ms_regs ms) regs2 26%bv 26 HPR2 ltac:(unfold acallee_saved; lia)
        ltac:(apply bv_eq; reflexivity)). }
    exact (HNZ fx cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE Hfrm HCTX2 R26'').
- (* the hit: the bnez goes straight to 0x857a8 *)
  assert (Ha0 : 4096 <= bv_unsigned (getr regs 10) <= 2 ^ 63)
    by (rewrite R10; unfold w64; rewrite unsigned_lit_small by lia; lia).
  destruct (s20d_seed_at LO_NMRA 4096 (2 ^ 63) cx ly S W regs mem md k acc LFO0 c m HBASE HCTX Ha0)
    as (HS & SHOK & HEI).
  remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
  unfold cfg_at.
  paj_run_to_tok RUNTO HS HJ SHOK S20Dspan LO_NZ.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
  assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO0 c m).
  { eapply (s20d_carry cx ly S W regs mem md k acc LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
      [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
      | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
  assert (R26' : getr (ms_regs ms) 26 = w64 (shadow_addr (m + seg_spec.MC_N))).
  { rewrite <- R26. exact (s20d_pres regs (ms_regs ms) 26%bv 26 HPR ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). }
  pmkst HS.
  exact (HNZ fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HBASE Hfrm HCTX1 R26').
Qed.
Lemma s20_L4 : S20A_NZ B MT -> S20_N_stmt B MT.
Proof.
intros HNZ cx ly S W regs mem md k acc c m HBASE Hfrm HCTX R26.
pose proof (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HC as (HCin & Hc4 & Hc16 & HCad). pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (_ & _ & Hcc & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & _).
assert (HRC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (HRM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity.
rewrite HRC in Hcc. rewrite HRM in Hmc.
assert (HCS : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
(* the model: at most 32 segments, and the "nosuch0" query is checked of the run *)
destruct HCM as (HRCF & HMCF).
assert (Hmn : sa_val (rdW W mem) (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) /\
              (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply s20_mconf_n; eassumption).
destruct Hmn as (_ & Hn32).
pose proof (s20_probe_ok_all (x_pl cx)) as (_ & HPOK).
(* the bytes of "nosuch0" and its length *)
assert (HZB : seg_spec.zs (seg_spec.zb LIT_NOSUCH) = LIT_NOSUCH) by (vm_compute; reflexivity).
assert (HLB : Z.of_nat (length (seg_spec.zb LIT_NOSUCH)) = 7) by (vm_compute; reflexivity).
assert (HLN : Z.of_nat (length LIT_NOSUCH) = 7) by (vm_compute; reflexivity).
(* ---- the seed at 0x85780 ---- *)
destruct (s20d_seed_at LO_N 0 (2 ^ 64 - 1) cx ly S W regs mem md k acc LFO0 c m HBASE HCTX
  (s20d_a0_any regs)) as (HS & SHOK & HEI).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20d_E regs (x_fr cx + FO_PROBE) c m) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs _ c m n rr Hn)).
assert (E34 : ew (s20d_E regs (x_fr cx + FO_PROBE) c m) 34%nat = Z_to_bv 64 m)
  by (apply (s20d_E_extra regs (x_fr cx + FO_PROBE) c m 2%nat); lia).
remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
unfold cfg_at.
(* 0x85780 .. 0x8578c: a1 := "nosuch0", a2 := 7, a0 := m; jal m_find *)
paj_run_tok RUN HS HJ SHOK S20Dspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO0 c m).
{ eapply (s20d_carry cx ly S W regs mem md k acc LFO0 c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
    [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
    | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
rewrite (SIGP SS_m_find ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
replace (seg_af SS_m_find) with AF_m_find by (vm_compute; reflexivity).
(* the facts of the literal at the call's reader *)
pose proof HCTX1 as (HCORE1 & HC1 & HM1 & HSL1 & HCM1).
pose proof HCORE1 as (HFR1 & HIMG1 & HBL1 & HBUD1).
pose proof HIMG1 as (HRO1 & _ & _).
pose proof (proj1 (proj1 HFR1)) as HAR1.
pose proof HM1 as (HMin1 & _ & _ & HMad1).
destruct HCM1 as (HRCF1 & HMCF1).
pose proof (s20d_nosuch_lit cx (rdW W (ms_mem ms)) HIMG1) as (HL0 & HLSTR & HLPIN & HLRT & HLIMG).
assert (HADR8 : sa_addr (rdW W (ms_mem ms)) (VAL (A_OBJ 8)) (Z.of_nat (length LIT_NOSUCH) + 1))
  by exact (HLPIN ly S W (ms_mem ms) mdv HAR1).
assert (HADR7 : sa_addr (rdW W (ms_mem ms)) (VAL (A_OBJ 8)) 7)
  by (apply (s20d_addr_le _ _ (Z.of_nat (length LIT_NOSUCH) + 1)); [exact HADR8 | lia]).
assert (HLOC7 : sa_loc SEGS B ly S (VAL (A_OBJ 8)) 7)
  by (right; right; apply (s20d_img_le B _ (Z.of_nat (length LIT_NOSUCH) + 1)); [exact HLIMG | lia]).
assert (Hnrng : 0 <= VAL (A_OBJ 8) < 2 ^ 64).
{ destruct (HLIMG (VAL (A_OBJ 8)) ltac:(lia)) as (Hin & _ & _).
  pose proof (pa_segs_low _ Hin) as Hlo. unfold kLowMemEnd in Hlo. lia. }
assert (HBYT : sa_bytes (rdW W (ms_mem ms)) (VAL (A_OBJ 8)) (seg_spec.zb LIT_NOSUCH)).
{ destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms) (VAL (A_OBJ 8)) LIT_NOSUCH (proj1 HLSTR)) as (HB1 & _ & _).
  exact (s20d_bytes_app_l _ _ _ _ HB1). }
assert (E249 : ew E 249%nat = w64 (VAL (A_OBJ 8)))
  by (unfold w64; apply (s20d_E_img E 249%nat HEI ltac:(unfold A_TEXT, A_LIM; lia))).
assert (R1' : getr (ms_regs ms) 1 = w64 (BASE + LO_NMRA)) by (rewrite P1; reflexivity).
assert (R10' : getr (ms_regs ms) 10 = w64 m) by (rewrite P10, E34; reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (VAL (A_OBJ 8))) by (rewrite P11, E249; reflexivity).
assert (R12' : getr (ms_regs ms) 12 = w64 7) by (rewrite P12; reflexivity).
assert (R26' : getr (ms_regs ms) 26 = w64 (shadow_addr (m + seg_spec.MC_N))).
{ rewrite <- R26. exact (s20d_pres regs (ms_regs ms) 26%bv 26 HPR ltac:(unfold acallee_saved; lia)
    ltac:(apply bv_eq; reflexivity)). }
assert (Hnev : st_nev S <= EV_MAX) by (eapply s20d_nev; eassumption).
assert (HSMF : STK_m_find = 8240) by (vm_compute; reflexivity).
assert (HMFPRE : m_find_c.m_find_pre SEGS B ly S (rdW W (ms_mem ms)) m (VAL (A_OBJ 8)) 7 (x_mcF cx)
  (seg_spec.zb LIT_NOSUCH)).
{ split; [lia|]. split; [exact Hm16|]. split; [exact HMCF1|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HMin1 | lia]|].
  split; [exact HMad1|]. split; [exact HBYT|]. split; [exact HLB|]. split; [exact HADR7 | exact HLOC7]. }
eapply (s20d_call cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO0 c m STK_m_find
  (VAL A_TEXT + AF_m_find) LO_NMRA
  (fun ly' S' (W' : world SEGS) regs' mem' md' =>
     getr regs' 10 = w64 (m_find_c.m_find_ptr m (x_mcF cx) (seg_spec.zs (seg_spec.zb LIT_NOSUCH))) /\
     sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_m_find (fun _ => False) /\
     sa_noalloc B ly S ly' S')
  (lt_post B MT cx) HBASE HCTX1 ltac:(rewrite HSMF; unfold ASTACK; lia) R1'
  ltac:(unfold LO_NMRA; lia) ltac:(reflexivity)).
- intros ch HPRE1.
  exact (HM_FIND fx ly S W (ms_regs ms) (ms_mem ms) mdv ch m (VAL (A_OBJ 8)) 7 (x_mcF cx)
    (seg_spec.zb LIT_NOSUCH) HPRE1 HRO1 R10' ltac:(lia) R11' Hnrng R12' ltac:(lia) HMFPRE
    ltac:(unfold m_find_c.EV_m_find; lia)).
- intros ly' S' W' regs' mem' md' (_ & Hk1 & Hn1). exact (conj Hk1 Hn1).
- intros ly2 S2 W2 regs2 mem2 md2 Hle HCTX2 HPR2 (HX2 & _ & _) HKEEP2.
  rewrite HZB in HX2.
  assert (R26'' : getr regs2 26 = w64 (shadow_addr (m + seg_spec.MC_N))).
  { rewrite <- R26'. exact (s20d_pres (ms_regs ms) regs2 26%bv 26 HPR2 ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). }
  apply (s20d_after_mfind HNZ Hfrm cx ly2 S2 W2 regs2 mem2 md2 k acc c m
    (m_find_c.m_find_ptr m (x_mcF cx) LIT_NOSUCH) HBASE HCTX2 R26'' HX2).
  destruct (s20_m_find_ptr_cases m (x_mcF cx) LIT_NOSUCH ltac:(lia) ltac:(lia) Hn32)
    as [(HFNONE & HPTR0) | (j & HFSOME & HPTRj & Hjr)].
  + left. split; [exact HPTR0|]. eapply s20_absent_of; [exact HPOK | exact HFNONE].
  + right. rewrite HPTRj. lia.
Qed.

(* ================================ S20_A_stmt: the probe's three calls ================================ *)
(* a range a runtime entry may read, from its shadow fact, its presence and its place below the window *)
Lemma s20d_aread_of_addr : forall stk (W : world SEGS) regs mem x n,
  sa_addr (rdW W mem) x n -> 0 <= n < 2 ^ 32 ->
  (forall a, x <= a < x + n -> apresent (w_H W) mem a) ->
  x + n <= spZ regs - stk ->
  aread_ok SEGS stk W regs mem x n.
Proof.
intros stk W regs mem x n (H0 & H63 & Hm & Hra & Hv) Hn Hpres Hw.
split; [exact H0|]. split; [exact H63|]. split; [exact Hn|]. split.
- intros a Ha. split; [apply (aview_some_of_apresent SEGS); exact (Hpres a Ha) | unfold ascratch_stk; lia].
- split; [exact Hm|]. split; [exact Hra | exact Hv].
Qed.
(* a reader fact below a call's window survives the call *)
Lemma s20d_zs_kept : forall (W W2 : world SEGS) mem mem2 lo hi p l,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W2 mem2 a = rdW W mem a) ->
  0 <= p -> p + Z.of_nat (length l) <= lo -> lo <= 2 ^ 64 ->
  sa_zs (rdW W mem) p l -> sa_zs (rdW W2 mem2) p l.
Proof.
intros W W2 mem mem2 lo hi p l HK Hp Hl Hlo H j Hj.
assert (Hj' : Z.of_nat j < Z.of_nat (length l)) by lia.
rewrite (HK (p + Z.of_nat j) ltac:(lia) ltac:(lia)). exact (H j Hj).
Qed.
Lemma s20d_fframe_le : forall ly S q n n', sa_fframe ly S q n -> 0 <= n' <= n -> sa_fframe ly S q n'.
Proof.
intros ly S q n n' (cid & pos & Hin & Hc & H1 & H2) Hn.
exists cid, pos. split; [exact Hin|]. split; [exact Hc|]. split; [exact H1 | lia].
Qed.
(* the loop's callee-saved registers across a call *)
Lemma s20d_lregs_pres : forall cx regs regs2 m i,
  s20_lregs cx regs m i -> aregs_preserved regs regs2 -> s20_lregs cx regs2 m i.
Proof.
intros cx regs regs2 m i (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26) HP.
split; [rewrite (s20d_pres regs regs2 18%bv 18 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R18|].
split; [rewrite (s20d_pres regs regs2 19%bv 19 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R19|].
split; [rewrite (s20d_pres regs regs2 20%bv 20 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R20|].
split; [rewrite (s20d_pres regs regs2 21%bv 21 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R21|].
split; [rewrite (s20d_pres regs regs2 22%bv 22 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R22|].
split; [rewrite (s20d_pres regs regs2 23%bv 23 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R23|].
split; [rewrite (s20d_pres regs regs2 25%bv 25 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R25|].
rewrite (s20d_pres regs regs2 26%bv 26 HP ltac:(unfold acallee_saved; lia)
  ltac:(apply bv_eq; reflexivity)); exact R26.
Qed.

(* what the probe gives at a point of S11 where it is in scope and holds the turn's text *)
Lemma s20d_probe_facts : forall cx ly S (W : world SEGS) regs mem md k acc c m i,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc LFO_P c m ->
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  ~ In 0 (s20_T cx i) /\ (length (s20_T cx i) <= 16)%nat /\
  sa_addr (rdW W mem) (s20_probe cx) 18 /\ sa_fframe ly S (s20_probe cx) 18 /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a) /\
  x_fr cx mod 32 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  SegModel.probe_ok (x_rcF cx) (x_mcF cx) (s20_T cx i) = true.
Proof.
intros cx ly S W regs mem md k acc c m i HBASE HCTX Hi Hzs.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & _).
pose proof (proj1 HJ) as HAR.
destruct HCM as (HRCF & HMCF).
(* the name of segment i *)
assert (Hnm : sa_zs (rdW W mem) (seg_spec.mseg_addr m i) (SegModel.ms_name (x_seg cx i) ++ [0]) /\
  ~ In 0 (SegModel.ms_name (x_seg cx i)) /\ (length (SegModel.ms_name (x_seg cx i)) < 16)%nat /\
  (forall j, 0 <= j < 16 -> rdW W mem (seg_spec.mseg_addr m i + j) <> None))
  by (eapply s20_mconf_name; eassumption).
destruct Hnm as (_ & Hnm0 & Hnml & _).
assert (HT0 : ~ In 0 (s20_T cx i)).
{ unfold s20_T. intros Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Hnm0 Hin)|].
  cbn [In] in Hin. destruct Hin as [Heq | []]. discriminate Heq. }
assert (HTl : (length (s20_T cx i) <= 16)%nat)
  by (unfold s20_T; rewrite length_app; cbn [length]; lia).
(* the probe's shadow and place *)
assert (HPA : sa_addr (rdW W mem) (s20_probe cx) 18)
  by (eapply s20_probe_addr; first [eassumption | reflexivity]).
assert (HPF : sa_fframe ly S (s20_probe cx) 18)
  by (eapply s20_probe_fframe; first [eassumption | reflexivity]).
(* the class-3 frame: present, aligned, below the allocation ceiling *)
assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. left. reflexivity. }
assert (HFA : frame_addr (x_ly cx) LT_FCLS (x_fpos cx) = x_fr cx) by reflexivity.
assert (HFA2 : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ pose proof HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  unfold x_fr, frame_addr. rewrite HF. reflexivity. }
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HFin) as (Hal32 & _ & Hpres & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HFin) as (Hf4 & Hfc & _).
rewrite HFA2 in Hal32, Hpres, Hf4, Hfc.
change (fs_frame_bytes LT_FCLS) with 512 in Hpres, Hfc.
(* the harness's probe check of the run, at turn i *)
pose proof (s20_probe_ok_all (x_pl cx)) as (HALL & _).
rewrite forallb_forall in HALL.
assert (HIn : In (x_seg cx i) (SegModel.mc_seg (x_mcF cx))) by (apply nth_In; exact Hi).
pose proof (HALL (x_seg cx i) HIn) as HPO.
rewrite (s20_probe_text (SegModel.ms_name (x_seg cx i)) Hnm0 ltac:(lia)) in HPO.
split; [exact HT0|]. split; [exact HTl|]. split; [exact HPA|]. split; [exact HPF|].
split; [intros a Ha; exact (proj1 (Hpres a Ha))|].
split; [exact Hal32|]. split; [exact Hf4|]. split; [exact Hfc | exact HPO].
Qed.

(* the bytes after a string's NUL, up to its word's end, inside the class-3 frame *)
Lemma s20d_tail_of_frame : forall cx (W : world SEGS) mem e,
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a) ->
  x_fr cx <= e -> e + 8 <= x_fr cx + 512 -> sa_tail (rdW W mem) e.
Proof.
intros cx W mem e Hpres H1 H2 x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm.
apply (aview_some_of_apresent SEGS). apply Hpres. lia.
Qed.

(* 0x85738, with m_find's answer a0 for the probe: a miss (check_absent(c, probe)) or a hit (straight to
   0x85748 = BASE + LO_Z) *)
Lemma s20d_after_mfind_p : forall i, S20A_Z B MT i -> sa_frm0 ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m (a0 : Z),
  lt_base B MT cx -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx B MT cx ly S W regs mem md k acc LFO_P c m ->
  s20_lregs cx regs m i ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  getr regs 10 = w64 a0 ->
  (a0 = 0 /\ SegModel.absent (x_rcF cx) (s20_T cx i) = true) \/ 4096 <= a0 <= 2 ^ 63 ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_MFRA) regs mem md) (lt_post B MT cx).
Proof.
intros i HZ Hfrm cx ly S W regs mem md k acc c m a0 HBASE Hi HCTX HLR Hzs R10 Hcase.
pose proof (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HC as (HCin & Hc4 & Hc16 & HCad). pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (_ & _ & Hcc & _).
assert (HRC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity. rewrite HRC in Hcc.
destruct (s20d_probe_facts cx ly S W regs mem md k acc c m i HBASE HCTX Hi Hzs)
  as (HT0 & HTl & HPA & HPF & HPRES & Hal32 & Hf4 & Hfc & HPO).
assert (Hprobe : s20_probe cx = x_fr cx + 192) by reflexivity.
destruct HCM as (HRCF & HMCF).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20d_E regs (x_fr cx + FO_PROBE) c m) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs _ c m n rr Hn)).
assert (E32 : ew (s20d_E regs (x_fr cx + FO_PROBE) c m) 32%nat = Z_to_bv 64 (x_fr cx + FO_PROBE))
  by (apply (s20d_E_extra regs (x_fr cx + FO_PROBE) c m 0%nat); lia).
assert (E33 : ew (s20d_E regs (x_fr cx + FO_PROBE) c m) 33%nat = Z_to_bv 64 c)
  by (apply (s20d_E_extra regs (x_fr cx + FO_PROBE) c m 1%nat); lia).
destruct Hcase as [(-> & HABS) | Hfound].
- (* the miss: a0 := c, a1 := the probe, jal check_absent *)
  destruct (s20d_seed_at LO_MFRA 0 (2 ^ 64 - 1) cx ly S W regs mem md k acc LFO_P c m HBASE HCTX
    (s20d_a0_any regs)) as (HS & SHOK & HEI).
  remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
  unfold cfg_at.
  pose proof (st_ok_pi_pin_reg' E _ _ 10%bv 0 HS
    ltac:(first [exact R10 | (cbn [ms_regs restrict mkst]; exact R10)]) eq_refl) as HS2.
  clear HS. rename HS2 into HS.
  paj_run_tok RUN HS HJ SHOK S20Dspan.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
  assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m).
  { eapply (s20d_carry cx ly S W regs mem md k acc LFO_P c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
      [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
      | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
  assert (Hzs1 : sa_zs (rdW W (ms_mem ms)) (s20_probe cx) (s20_T cx i ++ [0])).
  { apply (s20d_zs_kept W W mem (ms_mem ms) (2 ^ 64) (2 ^ 64)); [intros a Ha _; exact (KM a Ha) | lia
      | rewrite length_app; cbn [length]; lia | lia | exact Hzs]. }
  destruct (s20d_probe_facts cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m i HBASE HCTX1 Hi Hzs1)
    as (_ & _ & HPA1 & HPF1 & HPRES1 & _ & _ & _ & _).
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  rewrite (SIGP SS_check_absent ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  replace (seg_af SS_check_absent) with AF_check_absent by (vm_compute; reflexivity).
  pose proof HCTX1 as (HCORE1 & HC1 & HM1 & HSL1 & HCM1).
  pose proof HCORE1 as (HFR1 & HIMG1 & HBL1 & HBUD1).
  pose proof HIMG1 as (HRO1 & _ & _).
  pose proof HC1 as (HCin1 & _ & _ & HCad1).
  destruct HCM1 as (HRCF1 & HMCF1).
  assert (R1' : getr (ms_regs ms) 1 = w64 (BASE + LO_CARA)) by (rewrite P1; reflexivity).
  assert (R10' : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, E33; reflexivity).
  assert (R11' : getr (ms_regs ms) 11 = w64 (s20_probe cx)) by (rewrite P11, E32; reflexivity).
  assert (Hnev : st_nev S <= EV_MAX) by (eapply s20d_nev; eassumption).
  assert (HSCA : STK_check_absent = 8288) by (vm_compute; reflexivity).
  assert (HCAPRE : check_absent_c.check_absent_pre SEGS B ly S (rdW W (ms_mem ms)) c (s20_probe cx)
    (x_rcF cx) (s20_T cx i)).
  { split; [|exact HABS].
    split; [lia|]. split; [exact Hc16|]. split; [exact HRCF1|].
    split; [exists c, seg_spec.SEG_C_SIZE; split; [exact HCin1 | lia]|].
    split; [exact HCad1|]. split; [lia|].
    split; [split; [exact (conj Hzs1 HT0)|
      apply (s20d_tail_of_frame cx W (ms_mem ms)); [exact HPRES1 | lia | lia]]|].
    split; [right; left; apply (s20d_fframe_le ly S _ 18); [exact HPF1 | lia]|].
    split; [apply (s20d_addr_le _ _ 18); [exact HPA1 | lia] | lia]. }
  eapply (s20d_call cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m STK_check_absent
    (VAL A_TEXT + AF_check_absent) LO_CARA
    (fun ly' S' (W' : world SEGS) regs' mem' md' =>
       sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_check_absent (fun _ => False) /\
       sa_noalloc B ly S ly' S')
    (lt_post B MT cx) HBASE HCTX1 ltac:(rewrite HSCA; unfold ASTACK; lia) R1'
    ltac:(unfold LO_CARA; lia) ltac:(reflexivity)).
  + intros ch HPRE1.
    exact (HCHECK_ABSENT fx ly S W (ms_regs ms) (ms_mem ms) mdv ch c (s20_probe cx) (x_rcF cx) (s20_T cx i)
      HPRE1 HRO1 R10' ltac:(lia) R11' ltac:(lia) HCAPRE
      ltac:(unfold check_absent_c.EV_check_absent; lia)).
  + intros ly' S' W' regs' mem' md' HQ. exact HQ.
  + intros ly2 S2 W2 regs2 mem2 md2 Hle HCTX2 HPR2 _ HKEEP2.
    apply (HZ fx cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE Hfrm Hi HCTX2).
    * apply (s20d_lregs_pres cx (ms_regs ms) regs2 m i);
        [exact (s20d_lregs_pres cx regs (ms_regs ms) m i HLR HPR) | exact HPR2].
    * apply (s20d_zs_kept W W2 (ms_mem ms) mem2 (x_s1 cx - STK_check_absent) (x_s1 cx));
        [exact HKEEP2 | lia | rewrite length_app; cbn [length]; rewrite HSCA; lia | lia | exact Hzs1].
- (* the hit: the bnez goes straight to 0x85748 *)
  assert (Ha0 : 4096 <= bv_unsigned (getr regs 10) <= 2 ^ 63)
    by (rewrite R10; unfold w64; rewrite unsigned_lit_small by lia; lia).
  destruct (s20d_seed_at LO_MFRA 4096 (2 ^ 63) cx ly S W regs mem md k acc LFO_P c m HBASE HCTX Ha0)
    as (HS & SHOK & HEI).
  remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
  unfold cfg_at.
  paj_run_to_tok RUNTO HS HJ SHOK S20Dspan LO_Z.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
  assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
  assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m).
  { eapply (s20d_carry cx ly S W regs mem md k acc LFO_P c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
      [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
      | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
  pmkst HS.
  apply (HZ fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HBASE Hfrm Hi HCTX1).
  + exact (s20d_lregs_pres cx regs (ms_regs ms) m i HLR HPR).
  + apply (s20d_zs_kept W W mem (ms_mem ms) (2 ^ 64) (2 ^ 64)); [intros a Ha _; exact (KM a Ha) | lia
      | rewrite length_app; cbn [length]; lia | lia | exact Hzs].
Qed.

(* 0x85728: strlen returned |T| in a0; a2 := |T|, a0 := m, a1 := the probe, jal m_find *)
Lemma s20d_after_strlen : forall i, S20A_Z B MT i -> sa_frm0 ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m,
  lt_base B MT cx -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx B MT cx ly S W regs mem md k acc LFO_P c m ->
  s20_lregs cx regs m i ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  getr regs 10 = w64 (Z.of_nat (length (s20_T cx i))) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_SLRA) regs mem md) (lt_post B MT cx).
Proof.
intros i HZ Hfrm cx ly S W regs mem md k acc c m HBASE Hi HCTX HLR Hzs R10.
pose proof (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HC as (HCin & Hc4 & Hc16 & HCad). pose proof HM as (HMin & Hm4 & Hm16 & HMad).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity. rewrite HRM in Hmc.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
destruct (s20d_probe_facts cx ly S W regs mem md k acc c m i HBASE HCTX Hi Hzs)
  as (HT0 & HTl & HPA & HPF & HPRES & Hal32 & Hf4 & Hfc & HPO).
assert (Hprobe : s20_probe cx = x_fr cx + 192) by reflexivity.
assert (Hn32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat).
{ destruct HCM as (_ & HMCF0).
  assert (Hmn : sa_val (rdW W mem) (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) /\
    (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat) by (eapply s20_mconf_n; eassumption).
  exact (proj2 Hmn). }
destruct HCM as (HRCF & HMCF).
assert (HZB : seg_spec.zs (seg_spec.zb (s20_T cx i)) = s20_T cx i /\
  sa_bytes (rdW W mem) (s20_probe cx) (seg_spec.zb (s20_T cx i))).
{ destruct (sa_strz_bytes SEGS (w_H W) mem (s20_probe cx) (s20_T cx i) (conj Hzs HT0)) as (HB & _ & HZS0).
  exact (conj HZS0 (s20d_bytes_app_l _ _ _ _ HB)). }
destruct HZB as (HZS & HBYT).
assert (HLB : Z.of_nat (length (seg_spec.zb (s20_T cx i))) = Z.of_nat (length (s20_T cx i)))
  by (unfold seg_spec.zb; rewrite length_map; reflexivity).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20d_E regs (x_fr cx + FO_PROBE) c m) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs _ c m n rr Hn)).
assert (E34 : ew (s20d_E regs (x_fr cx + FO_PROBE) c m) 34%nat = Z_to_bv 64 m)
  by (apply (s20d_E_extra regs (x_fr cx + FO_PROBE) c m 2%nat); lia).
pose proof HLR as (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
destruct (s20d_seed_at LO_SLRA 0 (2 ^ 64 - 1) cx ly S W regs mem md k acc LFO_P c m HBASE HCTX
  (s20d_a0_any regs)) as (HS & SHOK & HEI).
remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
unfold cfg_at.
paj_run_tok RUN HS HJ SHOK S20Dspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m).
{ eapply (s20d_carry cx ly S W regs mem md k acc LFO_P c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
    [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
    | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
assert (Hzs1 : sa_zs (rdW W (ms_mem ms)) (s20_probe cx) (s20_T cx i ++ [0])).
{ apply (s20d_zs_kept W W mem (ms_mem ms) (2 ^ 64) (2 ^ 64)); [intros a Ha _; exact (KM a Ha) | lia
    | rewrite length_app; cbn [length]; lia | lia | exact Hzs]. }
destruct (s20d_probe_facts cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m i HBASE HCTX1 Hi Hzs1)
  as (_ & _ & HPA1 & HPF1 & HPRES1 & _ & _ & _ & _).
assert (HBYT1 : sa_bytes (rdW W (ms_mem ms)) (s20_probe cx) (seg_spec.zb (s20_T cx i))).
{ intros j Hj. assert (Hj' : (j < length (s20_T cx i))%nat)
    by (unfold seg_spec.zb in Hj; rewrite length_map in Hj; exact Hj).
  rewrite (KM (s20_probe cx + Z.of_nat j) ltac:(lia)). exact (HBYT j Hj). }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
rewrite (SIGP SS_m_find ltac:(unfold seg_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
replace (seg_af SS_m_find) with AF_m_find by (vm_compute; reflexivity).
pose proof HCTX1 as (HCORE1 & HC1 & HM1 & HSL1 & HCM1).
pose proof HCORE1 as (HFR1 & HIMG1 & HBL1 & HBUD1).
pose proof HIMG1 as (HRO1 & _ & _).
pose proof HM1 as (HMin1 & _ & _ & HMad1).
destruct HCM1 as (HRCF1 & HMCF1).
assert (R1' : getr (ms_regs ms) 1 = w64 (BASE + LO_MFRA)) by (rewrite P1; reflexivity).
assert (R10' : getr (ms_regs ms) 10 = w64 m) by (rewrite P10, E34; reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (s20_probe cx))
  by (rewrite P11, (EEo 25%nat 25%bv eq_refl); exact R25).
assert (R12' : getr (ms_regs ms) 12 = w64 (Z.of_nat (length (s20_T cx i))))
  by (rewrite P12, (EEo 10%nat 10%bv eq_refl); exact R10).
assert (Hnev : st_nev S <= EV_MAX) by (eapply s20d_nev; eassumption).
assert (HSMF : STK_m_find = 8240) by (vm_compute; reflexivity).
assert (HMFPRE : m_find_c.m_find_pre SEGS B ly S (rdW W (ms_mem ms)) m (s20_probe cx)
  (Z.of_nat (length (s20_T cx i))) (x_mcF cx) (seg_spec.zb (s20_T cx i))).
{ split; [lia|]. split; [exact Hm16|]. split; [exact HMCF1|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HMin1 | lia]|].
  split; [exact HMad1|]. split; [exact HBYT1|]. split; [exact HLB|].
  split; [apply (s20d_addr_le _ _ 18); [exact HPA1 | lia]|].
  right; left. apply (s20d_fframe_le ly S _ 18); [exact HPF1 | lia]. }
eapply (s20d_call cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m STK_m_find
  (VAL A_TEXT + AF_m_find) LO_MFRA
  (fun ly' S' (W' : world SEGS) regs' mem' md' =>
     getr regs' 10 = w64 (m_find_c.m_find_ptr m (x_mcF cx) (seg_spec.zs (seg_spec.zb (s20_T cx i)))) /\
     sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_m_find (fun _ => False) /\
     sa_noalloc B ly S ly' S')
  (lt_post B MT cx) HBASE HCTX1 ltac:(rewrite HSMF; unfold ASTACK; lia) R1'
  ltac:(unfold LO_MFRA; lia) ltac:(reflexivity)).
- intros ch HPRE1.
  exact (HM_FIND fx ly S W (ms_regs ms) (ms_mem ms) mdv ch m (s20_probe cx)
    (Z.of_nat (length (s20_T cx i))) (x_mcF cx) (seg_spec.zb (s20_T cx i)) HPRE1 HRO1 R10' ltac:(lia)
    R11' ltac:(lia) R12' ltac:(lia) HMFPRE ltac:(unfold m_find_c.EV_m_find; lia)).
- intros ly' S' W' regs' mem' md' (_ & Hk1 & Hn1). exact (conj Hk1 Hn1).
- intros ly2 S2 W2 regs2 mem2 md2 Hle HCTX2 HPR2 (HX2 & _ & _) HKEEP2.
  rewrite HZS in HX2.
  apply (s20d_after_mfind_p i HZ Hfrm cx ly2 S2 W2 regs2 mem2 md2 k acc c m
    (m_find_c.m_find_ptr m (x_mcF cx) (s20_T cx i)) HBASE Hi HCTX2).
  + apply (s20d_lregs_pres cx (ms_regs ms) regs2 m i);
      [exact (s20d_lregs_pres cx regs (ms_regs ms) m i HLR HPR) | exact HPR2].
  + apply (s20d_zs_kept W W2 (ms_mem ms) mem2 (x_s1 cx - STK_m_find) (x_s1 cx));
      [exact HKEEP2 | lia | rewrite length_app; cbn [length]; rewrite HSMF; lia | lia | exact Hzs1].
  + exact HX2.
  + destruct (s20_m_find_ptr_cases m (x_mcF cx) (s20_T cx i) ltac:(lia) ltac:(lia) Hn32)
      as [(HFNONE & HPTR0) | (j & HFSOME & HPTRj & Hjr)].
    * left. split; [exact HPTR0|]. eapply s20_absent_of; [exact HPO | exact HFNONE].
    * right. rewrite HPTRj. lia.
Qed.

Lemma s20_L2 : forall i, S20A_Z B MT i -> S20_A_stmt B MT i.
Proof.
intros i HZ cx ly S W regs mem md k acc c m HBASE Hfrm Hi HCTX HLR Hzs.
pose proof (s20d_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof HCTX as (HCORE & HC & HM & HSL & HCM).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
destruct (s20d_probe_facts cx ly S W regs mem md k acc c m i HBASE HCTX Hi Hzs)
  as (HT0 & HTl & HPA & HPF & HPRES & Hal32 & Hf4 & Hfc & HPO).
assert (Hprobe : s20_probe cx = x_fr cx + 192) by reflexivity.
pose proof HLR as (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20d_E regs (x_fr cx + FO_PROBE) c m) n = getr regs rr)
  by (intros n rr Hn; exact (s20d_E_reg regs _ c m n rr Hn)).
destruct (s20d_seed_at LO_A 0 (2 ^ 64 - 1) cx ly S W regs mem md k acc LFO_P c m HBASE HCTX
  (s20d_a0_any regs)) as (HS & SHOK & HEI).
remember (s20d_E regs (x_fr cx + FO_PROBE) c m) as E eqn:HE. clear HE.
unfold cfg_at.
(* 0x85720: a0 := s9 (the probe); jal strlen *)
paj_run_tok RUN HS HJ SHOK S20Dspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (apply (s20d_nowin_kept E W mem (ms_mem ms)); exact HFr).
assert (HPR : aregs_preserved regs (ms_regs ms)) by (s20d_preserved HS EEo).
assert (HCTX1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m).
{ eapply (s20d_carry cx ly S W regs mem md k acc LFO_P c m ly S W (ms_regs ms) (ms_mem ms) mdv (x_s1 cx));
    [exact HBASE | exact HCTX | exact HJ | exact HPR | lia | intros a Ha _; exact (KM a Ha)
    | apply Permutation_refl | exists (st_fs S); destruct S; reflexivity]. }
assert (Hzs1 : sa_zs (rdW W (ms_mem ms)) (s20_probe cx) (s20_T cx i ++ [0])).
{ apply (s20d_zs_kept W W mem (ms_mem ms) (2 ^ 64) (2 ^ 64)); [intros a Ha _; exact (KM a Ha) | lia
    | rewrite length_app; cbn [length]; lia | lia | exact Hzs]. }
destruct (s20d_probe_facts cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m i HBASE HCTX1 Hi Hzs1)
  as (_ & _ & HPA1 & HPF1 & HPRES1 & _ & _ & _ & _).
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
assert (R1' : getr (ms_regs ms) 1 = w64 (BASE + LO_SLRA)) by (rewrite P1; reflexivity).
assert (R10' : getr (ms_regs ms) 10 = w64 (s20_probe cx))
  by (rewrite P10, (EEo 25%nat 25%bv eq_refl); exact R25).
assert (Hsp1 : spZ (ms_regs ms) = x_s1 cx).
{ unfold spZ. rewrite (s20d_pres regs (ms_regs ms) 2%bv 2 HPR ltac:(unfold acallee_saved; lia)
    ltac:(apply bv_eq; reflexivity)), F2. unfold w64. apply unsigned_lit_small. lia. }
assert (HLB : Z.of_nat (length (seg_spec.zb (s20_T cx i))) = Z.of_nat (length (s20_T cx i)))
  by (unfold seg_spec.zb; rewrite length_map; reflexivity).
assert (HSTR : astr_at SEGS W (ms_mem ms) (s20_probe cx) (seg_spec.zb (s20_T cx i))).
{ destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms) (s20_probe cx) (s20_T cx i) (conj Hzs1 HT0))
    as (HB & HN & _). exact (conj HB HN). }
assert (HRD : aread_ok SEGS ESTACK W (ms_regs ms) (ms_mem ms) (s20_probe cx)
  (astr_len (seg_spec.zb (s20_T cx i)) + 1)).
{ apply (s20d_aread_of_addr ESTACK W (ms_regs ms) (ms_mem ms) (s20_probe cx)); unfold astr_len.
  - apply (s20d_addr_le _ _ 18); [exact HPA1 | lia].
  - lia.
  - intros a Ha. apply HPRES1. lia.
  - rewrite Hsp1. unfold ESTACK. lia. }
assert (HTL : atail_vis SEGS W (ms_mem ms) (s20_probe cx + astr_len (seg_spec.zb (s20_T cx i)))).
{ intros a Ha. unfold astr_len in Ha. rewrite HLB in Ha.
  apply (aview_some_of_apresent SEGS). apply HPRES1.
  pose proof (Z.mod_pos_bound (s20_probe cx + Z.of_nat (length (s20_T cx i))) 8 ltac:(lia)). lia. }
eapply (s20d_strlen cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc LFO_P c m LO_SLRA
  (s20_probe cx) (seg_spec.zb (s20_T cx i)) (lt_post B MT cx) HBASE HCTX1 R1'
  ltac:(unfold LO_SLRA; lia) ltac:(reflexivity) R10' ltac:(lia) HSTR HRD HTL).
intros regs2 mem2 md2 HCTX2 HPR2 HX2 HKEEP2.
apply (s20d_after_strlen i HZ Hfrm cx ly S W regs2 mem2 md2 k acc c m HBASE Hi HCTX2).
- apply (s20d_lregs_pres cx (ms_regs ms) regs2 m i);
    [exact (s20d_lregs_pres cx regs (ms_regs ms) m i HLR HPR) | exact HPR2].
- apply (s20d_zs_kept W W (ms_mem ms) mem2 (x_s1 cx - ESTACK) (x_s1 cx));
    [exact HKEEP2 | lia | rewrite length_app; cbn [length]; unfold ESTACK; lia
    | unfold ESTACK; lia | exact Hzs1].
- rewrite HX2. unfold astr_len. rewrite HLB. reflexivity.
Qed.

End e.
End f.
End d.
