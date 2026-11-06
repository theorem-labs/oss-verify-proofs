(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its block A (hd_c3 / hd_c3_of, hd_bounds, hd_A: the start facts, the bounds and
   the run from C3 through the __asan_memcpy call) and its helpers hd_getr_z, hd_reg_atom, hd_reg_is,
   hd_frame_nil, hd_frame_ro, hd_aview_some, renamed to the h2_ prefix and moved to headamp's addresses,
   registers, real-frame cells and cut lists; the call is taken through lib/A/HPgIntrin.v hd_memcpy_at in place
   of the donor's own hd_memcpy; the donor's blocks B and C (the parse and its exits) are not taken; the run from
   the call's return to C4 and the segment's post are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM02.v at 3a3b1c484a4 for image B
   (fuzz_headamp.asan-ubsan): image B's modules, pcs (C3 0x82f00 .. C4 0x82f34, fourteen words), registers (pod
   to s9, cap to s4 from R+0x20, 1 - null to s7 from R+0x38, pp in s2, len in s5, 3 cap in s2 and 3 cap + 3 in s5
   at C4), real-frame cells and cut lists (headamp_B_L23 XPod, headamp_B_L45 XCap33); the first run's read-only
   region holds two chunks (R+0x20 and R+0x38); the memcpy step is lib/AU/HPgIntrinU.v hdu_memcpy_at; names
   h2_ -> h2b_. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the segment M02 of
   LLVMFuzzerTestOneInput (0x80c40), the copy into the pod block, from C3 = 0x82f00 to C4 = 0x82f34. It proves
   lib/A/HPgCSpec.v headamp_dup_contract at lib/AU/HPgImgB.v headamp_himg_B. Proves no function (kind: segment
   lemma).

   THE CODE (fuzz.h:73-80, fuzz_headamp.c:326)
     0x82f00  beqz a0,0x83a08      the pod block is not NULL: decided by a0's atom fact (pod >= 4096)
     0x82f04  mv s9,a0
     0x82f08  lbu s4,0x20(s1)      the cap, from the real-frame cell R+0x20 (a plain load, no shadow check)
     0x82f0c  ld s7,0x38(s1)       1 - the null flag, from the real-frame cell R+0x38 (a plain load)
     0x82f10  beqz s5,0x82f24      len = 0: decided by s5's atom fact (8 <= len <= 5440)
     0x82f14  mv a0,s9; mv a1,s2; mv a2,s5 (pod, pp, len); 0x82f20 jal __asan_memcpy (0x51d8c), ra 0x82f24
     0x82f24  slli s2,s4,1; add s2,s2,s4; addi s5,s2,3; mv a0,s5 (3 cap and 3 cap + 3)
     0x82f34  jal malloc(out): C4, the segment's end (not run).
   The walk is two engine runs (lib/Reusable: st_ok, aj_run_to) cut at the call; the call is the runtime's
   __asan_memcpy (YG0d.aintrin_realizes, the Section hypothesis AMEMCPY, through HPgIntrinU.hdu_memcpy_at). The
   only bytes the segment writes are the pod block's len bytes and the callee's stack [R - ESTACK, R), so every byte
   outside the pod block and [R - T_SEG_STK, R) is as at C3: the real-frame cells of the cut list, the frame's
   shadow bytes and the pp block among them. The segment changes no float register.
   REGISTERS this file reads: a0, s1, s2, s5 (x10, x9, x18, x21) and the cells R+0x20, R+0x38; it writes s9, s4, s7
   (x25, x20, x23), s2, s5, a0 (x18, x21, x10) and a1, a2 before the call. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps HPgIntrinU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table ============================== *)
(* the 14 words 0x82f00 .. 0x82f34 (the first run leaves them at the `jal` 0x82f20, the second stops at 0x82f34) *)
Definition H2B_PC0 : Z := 0x82f00.
Definition h2b_tbl : ctable := build_table rsegs H2B_PC0 14 TEmpty.
Lemma h2b_tbl_ok : table_ok rsegs h2b_tbl.
Proof. apply build_table_ok0. unfold H2B_PC0. lia. Qed.
Definition H2B_RET : Z := 0x82f24.
Definition H2B_C4 : Z := 0x82f34.
Definition H2BCEIL_HI : Z := 0x7fffff800000.
(* the first run reads the cap's cell R+0x20 and the null flag's cell R+0x38 (base s1 = atom 9) as the extra atoms
   32 and 33 *)
Definition h2b_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x20 0x40 0 0
  [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 33 0))].
Definition h2b_facts1 : facts :=
  mkFacts [(10%nat, mkAF 4096 H2BCEIL_HI 4); (21%nat, mkAF 8 5440 0); (32%nat, mkAF 0 9 0)] [] [].

(* a register named by Z_to_bv 5 n (HPgBase's cut lists) is the register named by the numeral n *)
Lemma h2b_getr_z : forall (regs : bvmap 5 word) (r : bv 5) n, bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof.
intros regs r n H. f_equal. apply bv_eq. subst n. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (u5_range r). change (bv_modulus 5) with 32. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a register the run left as its own atom holds its value at the run's start *)
Lemma h2b_reg_atom : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r : bv 5),
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fx' E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.

(* a register the run left as an atom of the entry env holds that atom's register *)
Lemma h2b_reg_is : forall (fx' : YK11.FPState) E ss ms (H : word -> bool) regs extra (r r' : bv 5) n,
@st_ok rsegs fx' E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros fx' E ss ms H regs extra r r' n HS [HA _] Hr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r'); lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* a run with no region left every byte as it was *)
Lemma h2b_frame_nil : forall E (H : word -> bool) (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & _). destruct Hin.
Qed.
(* a run whose one region writes nothing left every byte as it was *)
Lemma h2b_frame_ro : forall E (H : word -> bool) (m m' : word -> option byte),
frame_of E [h2b_rA] (mrestrict H m) (mrestrict H m') -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]]. cbn in Hr. lia.
Qed.
(* a byte a block holds is present *)
Lemma h2b_aview_some : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime's __asan_memcpy at image B's entry 0x51d8c, the target of the `jal` at 0x82f20 (discharged by the
   runtime layer) *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy HPgIntrinU.B_ASAN_MEMCPY.
(* the meter's laws: the post's mo_le MT Sc S2 0 at S2 = Sc is YC5d.mo_le_refl (the harness's ameter_triv gives
   them, YCbp.ameter_triv_laws) *)
Hypothesis MTL : ameter_laws MT.

Section w.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
  (lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model)
  (e : hd_env) (pos : Z) (r : Model.pod_rec).

(* ================= the start state at C3 (headamp_dup_contract's premises), unfolded ================= *)
Record h2b_c3 : Prop := H2BC3 {
h2b_cJ : ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k;
h2b_cr2 : getr regs 2 = w64 (e_R e);
h2b_cr3 : getr regs 3 = w64 (as_gp B);
h2b_cr4 : getr regs 4 = w64 (as_tp B);
h2b_cS : e_S e = sp0;
h2b_cR32 : e_R e mod 32 = 0;
h2b_cRS : e_R e + 0x220 <= e_S e;
h2b_cSTK : sp0 - STK <= e_R e - T_SEG_STK;
h2b_cown : In (4, pos) own;
h2b_cF : e_F e = frame_addr lyc 4 pos;
h2b_cfsh : hd_fsh rsegs (w_H W) memc (e_F e) headamp_B_shA;
h2b_ccap : 0 <= e_cap e <= 9;
h2b_cnull : 0 <= e_null e <= 1;
h2b_cppin : In (e_pp e, Layout.PP_SIZE) (ablocks B lyc Sc);
h2b_ca0 : getr regs (Z_to_bv 5 10) = w64 (e_pod e);
h2b_cs0 : getr regs (Z_to_bv 5 8) = w64 (e_S e);
h2b_cs1 : getr regs (Z_to_bv 5 9) = w64 (e_R e);
h2b_cs2 : getr regs (Z_to_bv 5 18) = w64 (e_pp e + 0);
h2b_cs3 : getr regs (Z_to_bv 5 19) = w64 (shadow_addr (e_F e));
h2b_cs5 : getr regs (Z_to_bv 5 21) = w64 (e_len e);
h2b_cs8 : getr regs (Z_to_bv 5 24) = w64 (e_pp e + 0x4d18);
h2b_cs11 : getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF;
h2b_cc8 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x8) 8 ((e_pp e + 0x4008) mod 2 ^ 64);
h2b_cc18 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x18) 8 ((e_F e + 0) mod 2 ^ 64);
h2b_cc20 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x20) 8 (e_cap e mod 2 ^ 64);
h2b_cc38 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x38) 8 ((1 - e_null e) mod 2 ^ 64);
h2b_cc48 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x48) 8 ((e_F e + 0) mod 2 ^ 64);
h2b_cce0 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0xe0) 8 (Z.shiftr (e_pp e + 0x4d14) 3 mod 2 ^ 64);
h2b_cc108 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x108) 8 ((-16381) mod 2 ^ 64);
h2b_cc120 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x120) 8 ((e_pp e + 0x4d14) mod 2 ^ 64);
h2b_cc148 : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x148) 8 ((e_pp e + 0) mod 2 ^ 64);
h2b_cwf : Model.pod_rec_wf r;
h2b_clen : e_len e = Z.of_nat (length (Model.buf r));
h2b_cpp : garr8 rsegs (mrestrict (w_H W) memc) (e_pp e) (hd_zbytes (Layout.pp_bytes r));
h2b_cpod0 : e_pod e <> 0;
h2b_cpodin : In (e_pod e, e_len e) (ablocks B lyc Sc);
h2b_cpodnew : ~ In (e_pod e, e_len e) (ablocks B ly S) }.

Lemma h2b_c3_of : forall RLO RHI,
hd_seg_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_B
  (hi_shA headamp_himg_B) RLO RHI e pos ->
hd_cut rsegs (w_H W) memc regs e (hi_L3 headamp_himg_B) ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 rsegs (mrestrict (w_H W) memc) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
h2b_c3.
Proof.
intros RLO RHI HP HL3 Hwf Hlen Hpp (Hpod0 & Hpodin & Hpodnew).
destruct HP as (HJ & _ & H2 & H3 & H4 & HeS & HR32 & HRS & HSTK & Hown & HeF & Hfsh & Hcap & Hnull &
  _ & _ & _ & _ & _ & _ & _ & (_ & Hppin & _)).
cbn [hi_cid hi_rsz hi_shA headamp_himg_B] in HRS, Hown, HeF, Hfsh.
unfold hd_cut in HL3. cbn [hi_L3 headamp_himg_B] in HL3. unfold headamp_B_L23 in HL3.
repeat rewrite Forall_cons_iff in HL3.
destruct HL3 as (A10 & A8 & A9 & A18 & A19 & A21 & A24 & A27 &
  C8 & C18 & C20 & C38 & C48 & CE0 & C108 & C120 & C148 & _).
cbn [fst snd hd_at hd_xv] in A10, A8, A9, A18, A19, A21, A24, A27, C8, C18, C20, C38, C48, CE0, C108, C120, C148.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C3's journal, the allocator's block and frame laws and the record's length *)
Lemma h2b_bounds : h2b_c3 ->
e_pp e mod 16 = 0 /\ 4096 <= e_pp e /\ e_pp e + 19744 <= alloc_ceiling /\
e_pod e mod 16 = 0 /\ 4096 <= e_pod e /\ e_pod e + e_len e <= alloc_ceiling /\ in_app (e_pod e) (e_len e) /\
8 <= e_len e <= 5440 /\
4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\
alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e + 0x220 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\
0x7fff7f800000 <= alloc_ceiling <= H2BCEIL_HI.
Proof.
intros HC. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (h2b_cJ HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (h2b_cppin HC)) as (Hm16 & H4096 & Hpc & _).
pose proof (Spa.buf_header r (h2b_cwf HC)) as (_ & _ & _ & Hlb). rewrite <- (h2b_clen HC) in Hlb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (h2b_cpodin HC)) as (Qm16 & Q4096 & Qpc & Qapp & _).
assert (Hfin : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact (h2b_cown HC)).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hfin) as (F4096 & Fc & _).
pose proof asan_consts as ((Ca1 & Ca2) & _).
replace (fs_frame_bytes 4) with 1024 in Fc by reflexivity.
rewrite <- (h2b_cF HC) in F4096, Fc.
pose proof (h2b_cRS HC) as HRS. pose proof (h2b_cS HC) as HS. pose proof (h2b_cSTK HC) as HSTK.
replace (req_size Layout.PP_SIZE) with 19744 in Hpc by reflexivity.
replace (req_size (e_len e)) with (e_len e) in Qpc, Qapp by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
unfold H2BCEIL_HI, T_SEG_STK, ASTACK in *. rewrite HS in HRS.
repeat (first [assumption | split]); lia.
Qed.

(* ===================== block A: C3 0x82f00 .. the memcpy's return 0x82f24 ===================== *)
(* what C3 becomes after the memcpy: the journal, the I/O state, the registers M02's end reads (s4 = cap from the
   cell R+0x20, s7 = 1 - null from R+0x38, s9 = pod, the others their C3 values), the pod block holding pp's first
   len bytes, and every byte outside the pod block and the callee's stack [R - ESTACK, R) as at C3 *)
Definition h2b_A_post (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k /\
same_io mdc md1 /\
(forall q, In q [2; 3; 4; 8; 9; 18; 19; 21; 24; 27] -> getr regs1 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) /\
getr regs1 (Z_to_bv 5 20) = w64 (e_cap e) /\
getr regs1 (Z_to_bv 5 23) = w64 (1 - e_null e) /\
getr regs1 (Z_to_bv 5 25) = w64 (e_pod e) /\
(forall i, 0 <= i < e_len e -> aview rsegs (w_H W) mem1 (e_pod e + i) = aview rsegs (w_H W) memc (e_pp e + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pod e <= a < e_pod e + e_len e) -> ~ (e_R e - ESTACK <= a < e_R e) ->
 aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a).

Lemma h2b_A : forall (Q : world rsegs -> config -> Prop), h2b_c3 ->
(forall regs1 mem1 md1, h2b_A_post regs1 mem1 md1 -> SRr rsegs W (cfg_at rsegs H2B_RET regs1 mem1 md1) Q) ->
SRr rsegs W (cfg_at rsegs (hi_c3 headamp_himg_B) regs memc mdc) Q.
Proof.
intros Q HC K.
pose proof (h2b_bounds HC) as (Pm16 & P4096 & Pc & Qm16 & Q4096 & Qc & Qapp & Hlen8 & F4096 & Fc &
  HRlo & HRS & H47 & Hs16 & Hceil).
destruct HC as [HJ H2 H3 H4 HeS HR32 _ HSTK Hown HeF Hfsh Hcap Hnull Hppin A10 A8 A9 A18 A19 A21 A24 A27
  C8 C18 C20 C38 C48 CE0 C108 C120 C148 Hwf Hlen Hpp Hpod0 Hpodin Hpodnew].
unfold H2BCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
assert (HR16 : e_R e mod 16 = 0)
  by (rewrite <- (Z.mod_mod_divide (e_R e) 32 16) by (exists 2; reflexivity); rewrite HR32; reflexivity).
assert (E9 : bv_unsigned (ew (Ereg regs [w64 (e_cap e); w64 (1 - e_null e)]) 9) = e_R e).
{ rewrite (ew_Ereg_nat regs [w64 (e_cap e); w64 (1 - e_null e)] 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64.
  apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs [w64 (e_cap e); w64 (1 - e_null e)]) 32 = Z_to_bv 64 (e_cap e)).
{ change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (E33 : ew (Ereg regs [w64 (e_cap e); w64 (1 - e_null e)]) 33 = Z_to_bv 64 (1 - e_null e)).
{ change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (HS : st_ok rsegs (Ereg regs [w64 (e_cap e); w64 (1 - e_null e)]) (mkSS 0x82f00 sr_atoms [h2b_rA] None h2b_facts1)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82f00) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold h2b_rA.
    apply (hm_ro_region rsegs _ (w_H W) memc 9 (e_R e) 0x20 0x40 _ E9); [lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs _ _ (e_R e) 0x20 8 (SOff 32 0) (e_cap e)).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * cbn. lia.
      * cbn. lia.
      * rewrite (Z.mod_small (e_cap e)) in C20 by lia. exact C20.
    + apply (chunk_ok_val rsegs _ _ (e_R e) 0x38 8 (SOff 33 0) (1 - e_null e)).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
      * cbn. lia.
      * cbn. lia.
      * rewrite (Z.mod_small (1 - e_null e)) in C38 by lia. exact C38.
  - cbn. tauto.
  - unfold facts_ok, h2b_facts1. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite (ew_Ereg_nat regs [w64 (e_cap e); w64 (1 - e_null e)] 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64.
      rewrite unsigned_lit_small by (unfold H2BCEIL_HI; lia). change (2 ^ 4) with 16. unfold H2BCEIL_HI. lia.
    + rewrite (ew_Ereg_nat regs [w64 (e_cap e); w64 (1 - e_null e)] 21 (Z_to_bv 5 21) eq_refl), A21. unfold w64.
      rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    + rewrite E32. rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
unfold cfg_at. cbn [hi_c3 headamp_himg_B]. change (w64 0x82f00) with (Z_to_bv 64 0x82f00).
aj_run_to h2b_tbl_ok HS HJ HPgIntrinU.B_ASAN_MEMCPY.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (HAE : env_agree 32 (Ereg regs [w64 (e_cap e); w64 (1 - e_null e)])
  (Ereg regs [w64 (e_cap e); w64 (1 - e_null e)])) by apply env_agree_refl.
(* the registers at the call and the ones the segment's end reads *)
assert (Rk : forall q, In q [2; 3; 4; 8; 9; 18; 19; 21; 24; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)).
{ intros q Hq. eapply (h2b_reg_atom _ _ _ ms (w_H W) regs _ (Z_to_bv 5 q) HS HAE).
  cbn [In] in Hq. repeat (destruct Hq as [<- | Hq]; [vm_compute; reflexivity|]). destruct Hq. }
assert (R20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (e_cap e)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 20)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 20)) with v end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32. }
assert (R23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (1 - e_null e)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 23)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 23)) with v end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33. }
assert (Ra10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs (Z_to_bv 5 10))
  by (eapply (h2b_reg_is _ _ _ ms (w_H W) regs _ _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs (Z_to_bv 5 18))
  by (eapply (h2b_reg_is _ _ _ ms (w_H W) regs _ _ _ 18 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Ra12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs (Z_to_bv 5 21))
  by (eapply (h2b_reg_is _ _ _ ms (w_H W) regs _ _ _ 21 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (R25 : getr (ms_regs ms) (Z_to_bv 5 25) = w64 (e_pod e)).
{ refine (eq_trans _ A10).
  eapply (h2b_reg_is _ _ _ ms (w_H W) regs _ _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]. }
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (h2b_reg_atom _ _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (h2b_reg_atom _ _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (h2b_reg_atom _ _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (e_R e - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
assert (Ra1 : getr (ms_regs ms) (1%bv : bv 5) = Z_to_bv 64 H2B_RET).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (1%bv : bv 5)) in
    change (sr_get (ss_regs ss) (1%bv : bv 5)) with v end. reflexivity. }
(* the read-only run kept every byte *)
pose proof (h2b_frame_ro _ _ _ _ HFr) as KA.
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
pose proof (proj1 HJ) as HAR.
destruct (hm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ (e_pod e) (e_len e) (e_pod e) (e_len e) HAR Hpodin ltac:(lia)
  ltac:(unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia)) as (Hrad & Hhd).
destruct (hm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ (e_pp e) Layout.PP_SIZE (e_pp e) (e_len e) HAR Hppin ltac:(lia)
  ltac:(unfold req_size, Layout.PP_SIZE; cbn; lia)) as (Hrax & Hhx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hppin) as (_ & _ & _ & _ & Hpres_pp & _).
assert (Hne : (e_pod e, e_len e) <> (e_pp e, Layout.PP_SIZE))
  by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; lia).
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hpodin Hppin Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
replace (req_size (e_len e)) with (e_len e) in Hdj by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
replace (req_size Layout.PP_SIZE) with 19744 in Hdj by reflexivity.
eapply SRr_bind.
{ eapply (HPgIntrinU.hdu_memcpy_at B AMEMCPY W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (e_pod e) (e_pp e) (e_len e) (e_R e - sp0) (Z_to_bv 64 H2B_RET) HJ).
  - rewrite <- (h2b_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact A10.
  - rewrite <- (h2b_getr_z (ms_regs ms) 11 11 eq_refl), Ra11, A18, Z.add_0_r. reflexivity.
  - rewrite <- (h2b_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. exact A21.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. unfold T_SEG_STK, ASTACK in HSTK. lia.
  - rewrite E3. exact H3.
  - rewrite E4. exact H4.
  - exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (e_pod e + (a - e_pod e)) by lia.
      apply (hd_fresh_awr_n STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (e_pod e) (e_len e)
        Hpodin Hpodnew); lia.
    + unfold ESTACK. lia.
  - eapply amem_range_of_block;
      [exact LAWS | exact HAR | exact Hpodin | lia | unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia].
  - exact Hrad.
  - exact Hhd.
  - lia.
  - lia.
  - intros a Ha. split.
    + apply h2b_aview_some. exact (proj1 (Hpres_pp a ltac:(unfold req_size, Layout.PP_SIZE in *; cbn; lia))).
    + rewrite Hsp. unfold ESTACK. lia.
  - lia.
  - eapply amem_range_of_block;
      [exact LAWS | exact HAR | exact Hppin | lia | unfold req_size, Layout.PP_SIZE; cbn; lia].
  - exact Hrax.
  - exact Hhx. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & Ha02 & Hcpy & Hkeep & Hgrow).
apply K. unfold h2b_A_post.
split; [exact HJ2|].
split; [eapply same_io_trans; [apply HPgSteps.same_io_wvb | exact Hio2]|].
split.
{ intros q Hq. rewrite (Hpres2 q) by (cbn [In] in Hq; unfold acallee_saved; lia). apply Rk. exact Hq. }
split; [rewrite (Hpres2 20) by (unfold acallee_saved; lia); exact R20|].
split; [rewrite (Hpres2 23) by (unfold acallee_saved; lia); exact R23|].
split; [rewrite (Hpres2 25) by (unfold acallee_saved; lia); exact R25|].
split.
{ intros i Hi. rewrite (Hcpy i Hi). apply KA. }
intros a Ha Hnp Hns. rewrite (Hkeep a Ha Hnp); [apply KA|].
intros Hc. apply Hns. lia.
Qed.

(* ===================== block B: the memcpy's return 0x82f24 .. C4 0x82f34 ===================== *)
(* headamp_dup_contract's post at image B's record *)
Definition h2b_post : world rsegs -> config -> Prop :=
hd_seg_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (hi_c4 headamp_himg_B)
(fun f => f = fx)
(fun a => hd_inw e (hi_w2 headamp_himg_B) a \/ e_pod e <= a < e_pod e + e_len e)
(fun W2 regs2 mem2 =>
 hd_cut rsegs (w_H W2) mem2 regs2 e (hi_L4 headamp_himg_B) /\
 hd_fsh rsegs (w_H W2) mem2 (e_F e) (hi_shA headamp_himg_B) /\
 garr8 rsegs (mrestrict (w_H W2) mem2) (e_pod e) (hd_zbytes (Model.buf r))).

Lemma h2b_B : forall regs1 mem1 md1, h2b_c3 -> h2b_A_post regs1 mem1 md1 ->
SRr rsegs W (cfg_at rsegs H2B_RET regs1 mem1 md1) h2b_post.
Proof.
intros regs1 mem1 md1 HC HA.
pose proof (h2b_bounds HC) as (Pm16 & P4096 & Pc & Qm16 & Q4096 & Qc & Qapp & Hlen8 & F4096 & Fc &
  HRlo & HRS & H47 & Hs16 & Hceil).
destruct HC as [_ H2 H3 H4 HeS HR32 _ HSTK Hown HeF Hfsh Hcap Hnull Hppin A10 A8 A9 A18 A19 A21 A24 A27
  C8 C18 C20 C38 C48 CE0 C108 C120 C148 Hwf Hlen Hpp Hpod0 Hpodin Hpodnew].
destruct HA as (HJ1 & Hio1 & Rk1 & R20 & R23 & R25 & Hcpy & Hkeep).
unfold H2BCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs1 []) (mkSS 0x82f24 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 0x82f24) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at, H2B_RET. change (w64 0x82f24) with (Z_to_bv 64 0x82f24).
aj_run_to h2b_tbl_ok HS HJ1 H2B_C4.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs1 []) (Ereg regs1 [])) by apply env_agree_refl.
assert (E20 : ew (Ereg regs1 []) 20 = Z_to_bv 64 (e_cap e))
  by (rewrite (ew_Ereg_nat regs1 [] 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (Rk : forall q, In q [2; 3; 4; 8; 9; 19; 20; 23; 24; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 q) = getr regs1 (Z_to_bv 5 q)).
{ intros q Hq. eapply (h2b_reg_atom _ _ _ ms (w_H W) regs1 _ (Z_to_bv 5 q) HS HAE).
  cbn [In] in Hq. repeat (destruct Hq as [<- | Hq]; [vm_compute; reflexivity|]). destruct Hq. }
(* s2 = 3 cap, s5 = a0 = 3 cap + 3 *)
assert (V3 : U (Ereg regs1 []) (SMd M_MUL (SOff 20 0) (SLit 3)) = 3 * e_cap e).
{ rewrite U_SMd, U_SLit, (U_atom _ 20 (e_cap e) E20) by lia. cbn [zmd_raw]. change (zcanon 3) with 3.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
assert (V33 : U (Ereg regs1 []) (SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit 3)) (SLit 3)) = 3 * e_cap e + 3).
{ rewrite U_SAlu, V3, U_SLit. cbn [zalu_raw]. change (zcanon 3) with 3.
  unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity. }
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (3 * e_cap e + 3)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
  rewrite denot_lit_U, V33. reflexivity. }
assert (R18 : getr (ms_regs ms) (Z_to_bv 5 18) = w64 (3 * e_cap e)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 18)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 18)) with v end.
  rewrite denot_lit_U, V3. reflexivity. }
assert (R21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (3 * e_cap e + 3)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 21)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 21)) with v end.
  rewrite denot_lit_U, V33. reflexivity. }
(* the last run has no region: every byte is as at the call's return *)
pose proof (h2b_frame_nil _ _ _ _ HFr) as KB.
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
(* the frame's shadow bytes lie in the shadow map, apart from the pod block and the callee's stack *)
assert (Hf8 : 0 <= e_F e / 8 /\ 8 * (e_F e / 8) <= e_F e) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
assert (Hqa : e_pod e + e_len e <= 0x7fff7000 \/ 0x10007fff8000 <= e_pod e)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Qapp; lia).
apply SRr_ret. unfold h2b_post, hd_seg_post. cbv beta.
exists fx, lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [reflexivity|].
split; [reflexivity|].
split; [exact HJ1|].
split.
{ intros q Hq. rewrite (Rk q) by (cbn [In]; lia). apply Rk1. cbn [In]; lia. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [exact Hio1 | apply HPgSteps.same_io_wvb]|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hs Hz. rewrite KB. apply Hkeep; [exact Ha | intros Hp; apply Hz; right; exact Hp |].
  intros Hr. apply Hs. unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small by lia.
  unfold T_SEG_STK, ASTACK. unfold ESTACK in Hr. lia. }
cbn [hi_L4 hi_shA headamp_himg_B].
split; [|split].
- unfold hd_cut, headamp_B_L45.
  repeat (apply Forall_cons; [cbn [fst snd hd_at hd_xv] |]); try apply Forall_nil.
  + exact R10.
  + rewrite (Rk 8) by (cbn [In]; lia). rewrite (Rk1 8) by (cbn [In]; lia). exact A8.
  + rewrite (Rk 9) by (cbn [In]; lia). rewrite (Rk1 9) by (cbn [In]; lia). exact A9.
  + exact R18.
  + rewrite (Rk 19) by (cbn [In]; lia). rewrite (Rk1 19) by (cbn [In]; lia). exact A19.
  + rewrite (Rk 20) by (cbn [In]; lia). exact R20.
  + exact R21.
  + rewrite (Rk 23) by (cbn [In]; lia). exact R23.
  + rewrite (Rk 24) by (cbn [In]; lia). rewrite (Rk1 24) by (cbn [In]; lia). exact A24.
  + rewrite (Rk 25) by (cbn [In]; lia). exact R25.
  + rewrite (Rk 27) by (cbn [In]; lia). rewrite (Rk1 27) by (cbn [In]; lia). exact A27.
  + eapply (val_mem_kept rsegs); [|exact C8].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
  + eapply (val_mem_kept rsegs); [|exact C18].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
  + eapply (val_mem_kept rsegs); [|exact C48].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
  + eapply (val_mem_kept rsegs); [|exact CE0].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
  + eapply (val_mem_kept rsegs); [|exact C108].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
  + eapply (val_mem_kept rsegs); [|exact C120].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
  + eapply (val_mem_kept rsegs); [|exact C148].
    intros kk Hkk. cbn in Hkk. rewrite KB. apply Hkeep; unfold ESTACK; lia.
- apply (hm_fsh_kept rsegs (w_H W) memc (w_H W) (ms_mem ms) (e_F e) headamp_B_shA Hfsh).
  intros i Hi. change (length headamp_B_shA) with 116%nat in Hi. cbn in Hi.
  rewrite KB. apply Hkeep; unfold shadow_addr, SHADOW_OFF, ESTACK; lia.
- apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
  apply (proj2 (hm_bytes_zbytes rsegs _ _ _ _)) in Hpp.
  unfold Layout.pp_bytes, Layout.pp_image in Hpp. apply hm_bytes_app in Hpp. destruct Hpp as (Hb & _).
  apply (hm_memcpy_bytes rsegs (w_H W) memc (w_H W) (ms_mem ms) (e_pp e) (e_pod e) (Model.buf r) Hb).
  intros i Hi. rewrite KB. apply Hcpy. lia.
Qed.

(* the segment, from its start facts *)
Lemma h2b_main : h2b_c3 -> SRr rsegs W (cfg_at rsegs (hi_c3 headamp_himg_B) regs memc mdc) h2b_post.
Proof.
intros HC. apply (h2b_A h2b_post HC). intros regs1 mem1 md1 HA. exact (h2b_B regs1 mem1 md1 HC HA).
Qed.
End w.

(* ===================== the contract ===================== *)
Theorem headamp_B_dup_holds : forall RLO RHI : Z, headamp_dup_contract rsegs B MT headamp_himg_B RLO RHI.
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos r HP HL3 Hwf Hlen Hpp Hpod _.
eapply h2b_main. eapply h2b_c3_of; eassumption.
Qed.
Print Assumptions headamp_B_dup_holds.
End b.

Print Assumptions headamp_B_dup_holds.
