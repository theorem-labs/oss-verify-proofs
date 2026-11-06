(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module names changed; 500 of its 575 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the two straight runs of the
   message path's queueing. Listing (internal path) (internal record, sha256 7bc02d6772b3):
     +0x1e9c  ld a0, 0(s9); bnez a0 -> +0x1eb4         w2.n (s9 = &w2.n)
     +0x1ea4  sw zero, 0(s5); w2.n := 4                 n = 0: an empty 4-byte message (put32(0))
     +0x1eb4  ld a0, 0x70(s1); lw a0, 0x200(a0)         a0 := n_chunks = j (slot KS_GQ = g_nl + 0x40000)
     +0x1ebc  ld s3, 0xb0(s1)                           s3 := a0 + 8 (slot KS_CN)
     +0x1ec4  blt 63, a0 -> +0x1f1c; ld s11, 0(s9); beqz s11 -> +0x1f1c   (j <= 2, s11 = n' >= 1: neither taken)
     +0x1ed0  a0 := (j << 12) + g_nl (s6 := slot KS_GNL); a1 := s5 = w2; a2 := s11; +0x1ee4 jal checked_memcpy
   (kq_qa: kin_qmsg -> kernel_qmsg_a.v kin_qcpy) and
     +0x1ee8  a2 := g_nl + 0x40000; a0 := n_chunks; [n_chunks] := j + 1
     +0x1ef8  a0 := g_nl + 0x40000 + 8 j; the instrumented check of chunk_len[j] (+0x1f10); [chunk_len[j]] := s11
     +0x1f1c  a1 := 0x202; a0 := slot KS_W2SH = shadow(w2); +0x1f24 jal meta_fill_f8
   (kq_qc: kin_qcnt -> kin_qfil).
   THE PROOF. Each run starts from the cut, rebuilt as a symbolic state: registers sr_atoms over Eimg (Ereg regs
   [x]) (atom 32 = n for kq_qa, shadow(w2) for kq_qc), g_nl as the image atom 243 = A_OBJ 2 (LinkVals; the slots
   hold `SOff 243 _`, so the chunk_len check resolves against the shadow entry `mkSHE 243 0x40000 0x40018`), the
   slots and the touched words of w2 / g_nl as regions with their writable windows exactly the bytes written. The
   case splits are j in {0, 1, 2} (the n_chunks chunk and the store address are literals) and, for kq_qa, n = 0
   or n >= 1 (atom 32 with the fact [1, 4096]); every branch is decided by the engine and each run ends at its cut.
   The cut after a run: kq_qa writes only w2's first 4 bytes and w2.n (kernel_kit.v kat_frame_w2); kq_qc writes only
   n_chunks and chunk_len[j] (kernel_qmsg_kit.v kq_kat_g with g_nl's new counter and chunk length, kq_gnl_next).
   Section hypotheses: LAWS, LV (g_nl's atom), TB (g_nl's shadow at a cut), KI (g_nl's writability).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the shadow base and g_nl: exact *)
Definition kq_atoms : list (nat * afact) := [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (243%nat, mkAF LA_G_NL LA_G_NL 0)].

(* ---- kq_qa's state at +0x1e9c ---- *)
Definition qa_sp : YP09.region := YP09.mkRegion (Some 9%nat) 0x38 0xb8 0 0
  [YP09.mkChunk 0x38 (CVal 8 (SOff 243 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 243 0x40000));
   YP09.mkChunk 0xb0 (CVal 8 (SOff 18 8))].
Definition qa_wn (nv : sv) (w : Z) : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 w [YP09.mkChunk 0 (CVal 8 nv)].
Definition qa_wb : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 4 [].
Definition qa_g (j : Z) : YP09.region :=
  YP09.mkRegion (Some 243%nat) 0x40200 0x40204 0 0 [YP09.mkChunk 0x40200 (CVal 4 (SLit j))].
Definition qa_atoms (nz : bool) : list (nat * afact) :=
  kq_atoms ++ [(21%nat, mkAF 4096 0x7fffff800000 0); (25%nat, mkAF 4096 0x7fffff800000 0)] ++
  (if nz then [(32%nat, mkAF 1 4096 0)] else []).
Definition qa_ss (nz : bool) (j : Z) : sstate :=
  mkSS (kpc KP_QMSG) sr_atoms
    (if nz then [qa_sp; qa_wn (SOff 32 0) 0; qa_g j] else [qa_sp; qa_wn (SLit 0) 8; qa_wb; qa_g j])
    None (mkFacts (qa_atoms nz) [] []).
Definition qa_SH : list shent := [mkSHE 21 0 4; mkSHE 25 0 8].

(* ---- kq_qc's state at +0x1ee8: s6 = g_nl as atom 243 ---- *)
Definition qc_sp : YP09.region := YP09.mkRegion (Some 9%nat) 0x70 0x88 0 0
  [YP09.mkChunk 0x70 (CVal 8 (SOff 243 0x40000)); YP09.mkChunk 0x80 (CVal 8 (SOff 32 0))].
Definition qc_gl (j : Z) : YP09.region :=
  YP09.mkRegion (Some 243%nat) (0x40000 + 8 * j) (0x40008 + 8 * j) (0x40000 + 8 * j) (0x40008 + 8 * j) [].
Definition qc_gn (j : Z) : YP09.region :=
  YP09.mkRegion (Some 243%nat) 0x40200 0x40204 0x40200 0x40204 [YP09.mkChunk 0x40200 (CVal 4 (SLit j))].
Definition qc_ss (j : Z) : sstate :=
  mkSS (kpc 0x1ee8) (sr_set sr_atoms (Z_to_bv 5 22) (SOff 243 0)) [qc_sp; qc_gl j; qc_gn j] None
    (mkFacts kq_atoms [] []).
Definition qc_SH : list shent := [mkSHE 243 0x40000 0x40018].

(* the bytes a run did not write, off its frame: each writable window lies in Zs *)
Ltac kq_un HFr Zs :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
  intros a Ha Hna;
  apply (kept_of_frame (segs := pa_segs) _ _ _ _ _ Zs HFr); [ | exact Ha | exact Hna ];
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hxx := fresh "Hxx" in
  intros bb wl wh x Hin Hxx; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hxx;
      repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hxx end;
      cbv beta; unfold NW_N, NW_FULL in *; clear - Hxx; lia
    | ]);
  destruct Hin.

(* a register's symbolic value at the end of a run, computed, then its value *)
Ltac kq_reg HS Ex ssx msn :=
  rewrite (st_ok_pi_restrict_reg _ Ex ssx msn _ HS);
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ =>
    let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end;
  cbn [sv_denot];
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu end;
  rewrite ?Z.add_0_r; reflexivity.

(* presence grows with the restricted memory *)
Lemma kq_apres_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb). split; [exact Hh|].
  specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply Hg; [rewrite Hb; discriminate | reflexivity].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)

(* the env's atoms a cut names *)
Lemma kq_env : forall cx fpos k2 ly3 S3 md3 (ms3 : machine_state) rl x (E : env),
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 -> kregs0 cx ms3 -> kregs_eq ms3 rl ->
  In (21%nat, kW2 cx fpos) rl -> In (24%nat, kS8 cx) rl -> In (25%nat, kW2 cx fpos + NW_N) rl ->
  0 <= x < 2 ^ 64 ->
  E = Eimg (Ereg (ms_regs ms3) [w64 x]) ->
  bv_unsigned (ew E 9%nat) = ksp1 cx /\ bv_unsigned (ew E 18%nat) = ka0 cx /\
  bv_unsigned (ew E 20%nat) = SHADOW_OFF /\ bv_unsigned (ew E 21%nat) = kW2 cx fpos /\
  bv_unsigned (ew E 24%nat) = kS8 cx /\ bv_unsigned (ew E 25%nat) = kW2 cx fpos + NW_N /\
  bv_unsigned (ew E 32%nat) = x /\ bv_unsigned (ew E 243%nat) = LA_G_NL.
Proof.
  intros cx fpos k2 ly3 S3 md3 ms3 rl x E HB HJB HR0 HRL H21 H24 H25 Hx HEdef.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1a & Hs1b & _ & Hsp47 & _).
  destruct (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (C0 & C16 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (rewrite HEdef, <- A9; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E18 : ew E 18%nat = w64 (ka0 cx)) by (rewrite HEdef, <- A18; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite HEdef, <- A20; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E21 : ew E 21%nat = w64 (kW2 cx fpos)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 21 (Z_to_bv 5 (Z.of_nat 21)) eq_refl). exact (kn_reg_of ms3 rl 21 _ HRL H21). }
  assert (E24 : ew E 24%nat = w64 (kS8 cx)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 24 (Z_to_bv 5 (Z.of_nat 24)) eq_refl). exact (kn_reg_of ms3 rl 24 _ HRL H24). }
  assert (E25 : ew E 25%nat = w64 (kW2 cx fpos + NW_N)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 25 (Z_to_bv 5 (Z.of_nat 25)) eq_refl). exact (kn_reg_of ms3 rl 25 _ HRL H25). }
  split; [rewrite E9; apply unsigned_lit_small; lia|].
  split; [rewrite E18; apply unsigned_lit_small; lia|].
  split; [rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia|].
  split; [rewrite E21; apply unsigned_lit_small; unfold kW2, KN_W2; lia|].
  split; [rewrite E24; apply unsigned_lit_small; unfold kS8, shadow_of_addr, SHADOW_OFF; lia|].
  split; [rewrite E25; apply unsigned_lit_small; unfold kW2, KN_W2, NW_N; lia|].
  split; [rewrite HEdef, (kq_E_32 SK B LAWS TB KI AMEMCPY LV); apply unsigned_lit_small; exact Hx|].
  rewrite HEdef. apply (kq_U243 SK B LAWS TB KI AMEMCPY LV).
Qed.

(* g_nl's counter at a cut *)
Lemma kq_nchunks : forall cx W3 ms3 j, kgnl_at cx W3 ms3 (Some j) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (LA_G_NL + NK_N_CHUNKS) 4 j.
Proof.
  intros cx W3 ms3 j HGN. cbn [kgnl_at] in HGN. destruct HGN as (kbs3 & ((HAB & _) & HAL) & HKG).
  destruct HKG as (_ & _ & K3 & _). rewrite <- K3. unfold nk_n_chunks, fld_u32.
  apply (val_mem_u32 SEGS _ _ _ NK_N_CHUNKS HAB); [unfold NK_N_CHUNKS; lia | unfold NK_N_CHUNKS, NK_SIZE in *; lia].
Qed.

(* the bytes of g_nl kernel writes: allowed by apre's ajw at the cut's layout *)
Lemma kq_ajw : forall cx fpos k2 ly3 S3 W3 mm md3 a,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kE cx a ->
  ajw B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) ly3 S3
    ((KN_CID, fpos) :: k_own cx) a.
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 a HB HJ HJB Ha.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _).
  pose proof HJB as (_ & _ & HPERM & _).
  eapply ajw_mono; [exact (Hajw a Ha) | | |].
  - intros b m Hin. exact (Permutation_in _ (Permutation_sym HPERM) Hin).
  - intros y Hy. right. exact Hy.
  - intros c q. exact (km_fa SK B cx fpos k2 ly3 S3 W3 mm md3 HB HJ c q).
Qed.

(* ---- kq_qa: kin_qmsg (+0x1e9c) -> kin_qcpy (+0x1ee4) ---- *)
Lemma qa_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 c ci j n f adv (nz : bool) (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos KP_QMSG [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  0 <= j <= 2 -> (if nz then 1 <= n else n = 0) ->
  E = Eimg (Ereg (ms_regs ms3) [w64 n]) ->
  st_ok_pi SEGS pa_val E (qa_ss nz j) (restrict (w_H W3) ms3) /\
  sh_ok SEGS kq_Bx qa_SH E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (qa_ss nz j)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j n f adv nz E HB HJ HW HK Hj Hnz HEdef.
  pose proof HK as (HMS & HR0 & HRL & _ & HFR & HSH & HSL & HJB & HKK & _ & HGN & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  destruct HW as (Ww0 & Wwl & Wpres & Wnv & Wfv & Wnr & Wfr). unfold NL_CHUNK_MAX in Wnr.
  pose proof (kn_sp1 SK B cx HB) as (Hs1l & Hs1m & Hs1a & Hs1b & _ & Hsp47 & _).
  pose proof (kn_sp SK B cx HB) as (S1 & _).
  destruct (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (_ & _ & _ & _ & F5 & _).
  rewrite kn_fsb8 in F5. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity. rewrite HKA in S1.
  assert (HW2b : 4096 <= kW2 cx fpos /\ kW2 cx fpos + NW_SIZE <= alloc_ceiling) by (unfold kW2, KN_W2, NW_SIZE; lia).
  destruct (kq_env cx fpos k2 ly3 S3 md3 ms3 _ n E HB HJB HR0 HRL ltac:(kn_in) ltac:(kn_in) ltac:(kn_in)
              ltac:(lia) HEdef) as (U9 & U18 & U20 & U21 & U24 & U25 & U32 & U243).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact U9.
  assert (BV21 : base_val E (Some 21%nat) = kW2 cx fpos) by exact U21.
  assert (BV25 : base_val E (Some 25%nat) = kW2 cx fpos + NW_N) by exact U25.
  assert (BV243 : base_val E (Some 243%nat) = LA_G_NL) by exact U243.
  pose proof (kn_slot_of cx W3 ms3 _ KS_GNL LA_G_NL HSL
                ltac:(unfold kq_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_GNL.
  pose proof (kn_slot_of cx W3 ms3 _ KS_GQ (LA_G_NL + NK_CHUNK_LEN) HSL
                ltac:(unfold kq_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_GQ.
  pose proof (kn_slot_of cx W3 ms3 _ KS_CN (ka0 cx + 8) HSL
                ltac:(unfold kq_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_CN.
  pose proof (kq_nchunks cx W3 ms3 j HGN) as HNC.
  assert (HFA : frame_addr ly3 KN_CID fpos = kF cx fpos) by exact (km_fa SK B cx fpos k2 ly3 S3 W3 _ md3 HB HJ KN_CID fpos).
  assert (AWF : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
            awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
              ((KN_CID, fpos) :: k_own cx) x /\ ~ (k_sp0 cx <= x < k_sp0 cx + k_XO cx)).
  { intros x Hx.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos x HJ).
    - left. reflexivity.
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA, kn_fsb8. unfold kW2, KN_W2, NW_SIZE in Hx. lia. }
  pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
  assert (RSP : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) qa_sp).
  { unfold qa_sp, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x38 (SOff 243 0) LA_G_NL); [|exact SL_GNL].
      cbn [sv_denot]. rewrite U243, Z.add_0_r. reflexivity.
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x70 (SOff 243 0x40000) (LA_G_NL + NK_CHUNK_LEN));
        [|exact SL_GQ].
      cbn [sv_denot]. rewrite U243. reflexivity.
    - apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8)); [|exact SL_CN].
      cbn [sv_denot]. rewrite U18. reflexivity. }
  assert (RWN : forall nv w, (w = 0 \/ w = 8) -> sv_denot E nv = Z_to_bv 64 n ->
            region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (qa_wn nv w)).
  { intros nv w Hw Hnv'. destruct Hw as [-> | ->];
      unfold qa_wn, region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      rewrite BV25; (split; [unfold NW_N; lia|]); (split; [unfold NW_N, NW_SIZE in *; lia|]); split.
    1, 3: intros o Ho; replace (kW2 cx fpos + NW_N + o) with (kW2 cx fpos + (NW_N + o)) by lia;
          exact (proj2 (Wpres (NW_N + o) ltac:(unfold NW_N, NW_SIZE; lia))).
    all: apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS E _ (kW2 cx fpos + NW_N) 0 8 nv n Hnv');
      [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia | rewrite Z.add_0_r; exact Wnv]. }
  assert (RWB : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) qa_wb).
  { unfold qa_wb, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV21. split; [lia|]. split; [unfold NW_SIZE in *; lia|]. split; [|apply Forall_nil].
    intros o Ho. exact (proj2 (Wpres o ltac:(unfold NW_SIZE; lia))). }
  assert (RG : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (qa_g j)).
  { unfold qa_g, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ LA_G_NL 0x40200 4 (SLit j) j); [reflexivity | cbn; lia | cbn; lia | exact HNC]. }
  split; [|split].
  - rewrite (km_ms_shape ms3 (BASE + kpc KP_QMSG) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
    unfold qa_ss. apply pa_entry_st_ok_full.
    + rewrite HEdef. apply regs_ok_Eimg_Ereg.
    + destruct nz; vm_compute; reflexivity.
    + destruct nz; cbv iota.
      * apply Forall_cons; [exact RSP|]. apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_nil]].
        apply RWN; [left; reflexivity|]. apply sv_off0. rewrite HEdef. apply (kq_E_32 SK B LAWS TB KI AMEMCPY LV).
      * apply Forall_cons; [exact RSP|].
        apply Forall_cons; [apply RWN; [right; reflexivity | cbv iota in Hnz; rewrite Hnz; reflexivity]|].
        apply Forall_cons; [exact RWB | apply Forall_cons; [exact RG | apply Forall_nil]].
    + destruct nz; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint, qa_sp, qa_wn, qa_wb, qa_g;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?BV9, ?BV21, ?BV25, ?BV243;
        unfold LA_G_NL, NW_N, kW2, KN_W2 in *; repeat split; lia.
    + unfold facts_ok, qa_atoms, kq_atoms. destruct nz;
        cbn [app f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite ?U20, ?U243, ?U21, ?U25, ?U32; change (2 ^ 0) with 1; rewrite ?Z.mod_1_r;
        cbv iota in Hnz; unfold SHADOW_OFF, LA_G_NL, NW_N, kW2, KN_W2 in *; repeat split; lia.
  - assert (HUB : U E kq_Bx = SHADOW_OFF)
      by (unfold kq_Bx; rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
    unfold sh_ok, qa_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 21 (kW2 cx fpos) NW_SIZE (kW2 cx fpos) 0 4 HRA HUB);
        [rewrite U_SOff, U21, Z.add_0_r; apply zcanon_id; unfold M64, kW2, KN_W2; lia | lia | unfold NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold kW2, KN_W2, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
      lia.
    + apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 25 (kW2 cx fpos) NW_SIZE (kW2 cx fpos + NW_N) 0 8
               HRA HUB);
        [rewrite U_SOff, U25, Z.add_0_r; apply zcanon_id; unfold M64, kW2, KN_W2, NW_N; lia
        | unfold NW_N; lia | unfold NW_N, NW_SIZE; lia |].
      intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
      unfold kW2, KN_W2, NW_N, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - unfold qa_ss. destruct nz; cbn [ss_mem]; cbv iota.
    + apply awr_ok_x_cons; [intros x Hx; unfold qa_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_cons; [intros x Hx; unfold qa_wn in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_cons; [intros x Hx; unfold qa_g in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_nil.
    + apply awr_ok_x_cons; [intros x Hx; unfold qa_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_cons.
      { intros x Hx. unfold qa_wn in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV25 in Hx.
        left. apply AWF. unfold NW_N, NW_SIZE in *. lia. }
      apply awr_ok_x_cons.
      { intros x Hx. unfold qa_wb in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV21 in Hx.
        left. apply AWF. unfold NW_SIZE. lia. }
      apply awr_ok_x_cons; [intros x Hx; unfold qa_g in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
      apply awr_ok_x_nil.
Qed.

(* the cut after kq_qa's run: the run wrote only w2's first 4 bytes and w2.n *)
Lemma qa_land : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv n' (ms : machine_state) md,
  kfrom SK B POST (kin_qcpy B Rc) ->
  kbase SK B cx -> frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= n' <= 4096 ->
  kat B cx fpos KP_QMSG [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  kms 0x1ee4 ms -> kregs0 cx ms -> kregs_eq ms (kq_rl_cpy cx fpos j n') ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_FULL) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv n' ms md HN HB HFRM HJ HRc Hc Hci Hj Hn HK HMS HR0 HRL
    Hfds Hfs UN HG.
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFRM).
  exists c, ci, j, n', adv. split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hn|].
  apply (kat_frame_w2 SK B LAWS 0 NW_FULL cx fpos KP_QMSG _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 0x1ee4 _ _
           W3 ms md HB HK HMS HR0 HRL (incl_refl _) (kq_sl_ok cx fpos c ci) (kfsh_fits _ _ _) Hfds Hfs
           ltac:(lia) ltac:(unfold NW_FULL, NW_SIZE; lia)).
  - intros a Ha Hn'. apply UN; [exact Ha|]. intros Hc'. apply Hn'. lia.
  - intros a Ha. exact (kq_apres_grows _ _ _ a HG Ha).
Qed.

(* the start of a kq_qa run: the seat of qa_seat at a concrete (nz, j) *)
Ltac qa_go1 HB HJ HW HK HEdef c ci nzv jv HS SHOK HAWR :=
  lazymatch type of HK with kat _ ?cx ?fpos _ _ _ _ _ ?adv _ ?k2 ?ly3 ?S3 ?W3 ?ms3 ?md3 =>
  lazymatch type of HW with kw_at _ _ _ ?n ?f =>
  lazymatch type of HEdef with ?E = _ =>
    destruct (qa_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv n f adv nzv E HB HJ HW HK ltac:(lia)
                ltac:(cbv iota; lia) HEdef) as (HS & SHOK & HAWR)
  end end end.

(* the cut after a kq_qa run *)
Ltac qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci jv nv' :=
  lazymatch type of HK with kat _ ?cx ?fpos _ _ _ _ _ ?adv _ ?k2 ?ly3 ?S3 ?W3 ?ms3 ?md3 =>
  lazymatch type of HNEXT with kfrom _ _ ?POST (kin_qcpy _ ?Rc) =>
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn), HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
      |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      apply (qa_land POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv nv' msn mdn HNEXT HB Hfrm HJ HRcv Hcr Hci
               ltac:(lia) ltac:(lia) HK);
      [ apply (kn_kms_of _ Ex ssx msn 0x1ee4 HS'); vm_compute; reflexivity
      | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
                 (proj1 (proj2 HK)))
      | unfold kregs_eq, kq_rl_cpy; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        kq_reg HS' Ex ssx msn
      | exact (proj1 (wvb_fds_fs _ _ _))
      | exact (proj2 (wvb_fds_fs _ _ _))
      | kq_un HFr' (fun x => kW2 cx fpos <= x < kW2 cx fpos + NW_FULL)
      | exact HG' ]
    end
  end end.

Theorem kq_qa : forall POST Rc, kfrom SK B POST (kin_qcpy B Rc) -> kfrom SK B POST (kin_qmsg B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & n & f & adv & HRcv & Hcr & Hci & Hj & HW & HK).
  pose proof HK as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof HW as (_ & _ & _ & _ & _ & Wnr & _). unfold NL_CHUNK_MAX in Wnr.
  remember (Eimg (Ereg (ms_regs ms3) [w64 n])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 n]) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (kq_env cx fpos k2 ly3 S3 md3 ms3 _ n E HB HJB HR0 HRL ltac:(kn_in) ltac:(kn_in) ltac:(kn_in)
              ltac:(lia) HEdef) as (U9 & U18 & U20 & U21 & U24 & U25 & U32 & U243).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0]; destruct Hj2 as [-> | [-> | ->]].
  - qa_go1 HB HJ HW HK HEdef c ci false 0 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1ee4); [exact HAWR|].
    qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci 0 4.
  - qa_go1 HB HJ HW HK HEdef c ci false 1 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1ee4); [exact HAWR|].
    qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci 1 4.
  - qa_go1 HB HJ HW HK HEdef c ci false 2 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1ee4); [exact HAWR|].
    qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci 2 4.
  - qa_go1 HB HJ HW HK HEdef c ci true 0 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1ee4); [exact HAWR|].
    qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci 0 n.
  - qa_go1 HB HJ HW HK HEdef c ci true 1 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1ee4); [exact HAWR|].
    qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci 1 n.
  - qa_go1 HB HJ HW HK HEdef c ci true 2 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1ee4); [exact HAWR|].
    qa_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci HAG c ci 2 n.
Qed.

(* ---- kq_qc: kin_qcnt (+0x1ee8) -> kin_qfil (+0x1f24) ---- *)
Lemma qc_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 c ci j n adv (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos 0x1ee8 (kq_rl_cnt cx fpos n) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  0 <= j <= 2 ->
  E = Eimg (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 0x226)]) ->
  st_ok_pi SEGS pa_val E (qc_ss j) (restrict (w_H W3) ms3) /\
  sh_ok SEGS kq_Bx qc_SH E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (qc_ss j)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j n adv E HB HJ HK Hj HEdef.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & _ & HGN & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof (kn_sp1 SK B cx HB) as (Hs1l & Hs1m & Hs1a & Hs1b & _ & Hsp47 & _).
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (kq_env cx fpos k2 ly3 S3 md3 ms3 _ (kFSH cx fpos + 0x226) E HB HJB HR0 HRL ltac:(kn_in) ltac:(kn_in)
              ltac:(kn_in) ltac:(unfold kHighMemBeg, SHADOW_OFF in *; lia) HEdef)
    as (U9 & U18 & U20 & U21 & U24 & U25 & U32 & U243).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact U9.
  assert (BV243 : base_val E (Some 243%nat) = LA_G_NL) by exact U243.
  assert (E243 : ew E 243%nat = Z_to_bv 64 LA_G_NL) by (rewrite HEdef; apply (kq_E_243 SK B LAWS TB KI AMEMCPY LV)).
  pose proof (kn_slot_of cx W3 ms3 _ KS_GQ (LA_G_NL + NK_CHUNK_LEN) HSL
                ltac:(unfold kq_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_GQ.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W2SH (kFSH cx fpos + 0x226) HSL
                ltac:(unfold kq_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W2SH.
  pose proof (kq_nchunks cx W3 ms3 j HGN) as HNC.
  assert (GW : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) a)
    by exact (writable_at_of_wseg SEGS _ LA_G_NL NK_SIZE ltac:(unfold LA_G_NL; lia)
                ltac:(unfold LA_G_NL, NK_SIZE; lia) (ki_gnl_wseg _ _ KI)).
  destruct (kq_gnl_ra SK B LAWS TB KI AMEMCPY LV cx fpos k2 ly3 S3 W3 ms3 md3 LA_G_NL NK_SIZE HB HJ HJB HKK
              ltac:(lia) ltac:(lia) ltac:(unfold NK_SIZE; lia)) as (HRAg & _).
  split; [|split].
  - rewrite (km_ms_shape ms3 (BASE + kpc 0x1ee8) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
    unfold qc_ss. apply pa_entry_st_ok_full.
    + apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite (sv_off0 E 243 LA_G_NL E243). symmetry. apply (kn_reg_of ms3 _ 22 _ HRL). unfold kq_rl_cnt. kn_in.
    + (* regions_wf on a closed state: j first (an open 8 * j under vm_compute blows up) *)
      assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
      destruct Hj3 as [-> | [-> | ->]]; vm_compute; reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil.
      * unfold qc_sp, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x70 (SOff 243 0x40000) (LA_G_NL + NK_CHUNK_LEN));
             [|exact SL_GQ].
           cbn [sv_denot]. rewrite U243. reflexivity.
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x80 (SOff 32 0) (kFSH cx fpos + 0x226));
             [|exact SL_W2SH].
           cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
      * unfold qc_gl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [|apply Forall_nil].
        intros o Ho. apply GW. unfold NK_SIZE. lia.
      * unfold qc_gn, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split.
        { intros o Ho. apply GW. unfold NK_SIZE. lia. }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ LA_G_NL 0x40200 4 (SLit j) j); [reflexivity | cbn; lia | cbn; lia | exact HNC].
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, qc_sp, qc_gl, qc_gn.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV243. unfold LA_G_NL. repeat split; lia.
    + unfold facts_ok, kq_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U243. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold SHADOW_OFF, LA_G_NL. repeat split; lia.
  - assert (HUB : U E kq_Bx = SHADOW_OFF)
      by (unfold kq_Bx; rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
    unfold sh_ok, qc_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 243 LA_G_NL NK_SIZE LA_G_NL 0x40000 0x40018 HRAg HUB);
      [rewrite U_SOff, U243, Z.add_0_r; apply zcanon_id; unfold M64, LA_G_NL; lia | lia | unfold NK_SIZE; lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold LA_G_NL, SHADOW_OFF in *. lia.
  - unfold qc_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold qc_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold qc_gl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV243 in Hx.
      exact (kq_ajw cx fpos k2 ly3 S3 W3 _ md3 x HB HJ HJB
               (kq_kE_gnl SK B LAWS TB KI AMEMCPY LV cx x ltac:(unfold NK_OPEN; lia))).
    + intros x Hx. unfold qc_gn in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV243 in Hx.
      exact (kq_ajw cx fpos k2 ly3 S3 W3 _ md3 x HB HJ HJB
               (kq_kE_gnl SK B LAWS TB KI AMEMCPY LV cx x ltac:(unfold NK_OPEN; lia))).
Qed.

(* the cut after kq_qc's run: n_chunks = j + 1, chunk_len[j] = n *)
Lemma qc_land : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j n adv (E : env) (ms : machine_state) md
    cs1 cs2,
  kfrom SK B POST (kin_qfil B Rc) ->
  kbase SK B cx -> frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= n <= 4096 ->
  kat B cx fpos 0x1ee8 (kq_rl_cnt cx fpos n) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 27%nat) = n -> bv_unsigned (ew E 243%nat) = LA_G_NL ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms))
    (YP09.mkRegion (Some 243%nat) (0x40000 + 8 * j) (0x40008 + 8 * j) (0x40000 + 8 * j) (0x40008 + 8 * j) cs1) ->
  In (YP09.mkChunk (0x40000 + 8 * j) (CVal 8 (SOff 27 0))) cs1 ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 243%nat) 0x40200 0x40204 0x40200 0x40204 cs2) ->
  In (YP09.mkChunk 0x40200 (CVal 4 (SLit (j + 1)))) cs2 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((LA_G_NL + (0x40000 + 8 * j) <= a < LA_G_NL + (0x40008 + 8 * j)) \/ (LA_G_NL + 0x40200 <= a < LA_G_NL + 0x40204)) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms 0x1f24 ms -> kregs0 cx ms -> kregs_eq ms (kq_rl_fil cx fpos) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j n adv E ms md cs1 cs2 HN HB HFRM HJ HRc Hc Hci Hj Hn HK
    U27 U243 HR1 Hin1 HR2 Hin2 UN HG HMS HR0 HRL Hfds Hfs.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _ & _ & HGN & _).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFRM).
  exists c, ci, (j + 1), adv. split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [lia|].
  assert (HCL : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (LA_G_NL + (NK_CHUNK_LEN + 8 * j)) 8 n).
  { exact (field_of_region E _ 243 LA_G_NL _ _ _ _ _ (0x40000 + 8 * j) 8 (SOff 27 0) n HR1 U243 Hin1
             ltac:(cbn [sv_denot]; rewrite U27, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (HNC : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (LA_G_NL + NK_N_CHUNKS) 4 (j + 1)).
  { exact (field_of_region E _ 243 LA_G_NL _ _ _ _ _ 0x40200 4 (SLit (j + 1)) (j + 1) HR2 U243 Hin2
             eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  apply (kq_kat_g SK B LAWS TB KI AMEMCPY LV (fun _ => False)
           (fun a => (LA_G_NL + (0x40000 + 8 * j) <= a < LA_G_NL + (0x40008 + 8 * j)) \/
                     (LA_G_NL + 0x40200 <= a < LA_G_NL + 0x40204))
           cx fpos 0x1ee8 (kq_rl_cnt cx fpos n) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j)
           k2 ly3 S3 W3 ms3 md3 0x1f24 (kq_rl_fil cx fpos) (kq_sl cx fpos c ci) (Some (j + 1)) W3 ms md HB HK HMS HR0 HRL
           (incl_refl _) (kfsh_fits _ _ _) Hfds Hfs).
  - intros a Ha _ Hg. exact (UN a Ha Hg).
  - intros a Ha. exact (kq_apres_grows _ _ _ a HG Ha).
  - intros a [].
  - exact (kq_miss0 SK B LAWS TB KI AMEMCPY LV cx fpos (kq_sl cx fpos c ci) _ (kq_sl_ok cx fpos c ci)).
  - intros a [Ha | Ha]; unfold NK_OPEN; lia.
  - assert (HnM : 0 <= n <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
    apply (kq_gnl_next SK B LAWS TB KI AMEMCPY LV cx W3 ms3 ms j (j + 1) n HGN ltac:(lia)
             (or_intror (conj eq_refl HnM))).
    + intros i Hi. apply (kq_aview_grows SK B LAWS TB KI AMEMCPY LV _ _ _ _ HG).
      exact (kq_gnl_vis SK B LAWS TB KI AMEMCPY LV cx W3 ms3 (Some j) HGN i Hi).
    + intros i Hi Hc1 Hc2. apply UN; [unfold LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *; lia|].
      unfold NK_CHUNK_LEN, NK_N_CHUNKS in *. lia.
    + exact HNC.
    + exact HCL.
Qed.

(* the start of a kq_qc run: the seat of qc_seat at a concrete j *)
Ltac qc_go1 HB HJ HK HEdef c ci n jv HS SHOK HAWR :=
  lazymatch type of HK with kat _ ?cx ?fpos _ _ _ _ _ ?adv _ ?k2 ?ly3 ?S3 ?W3 ?ms3 ?md3 =>
  lazymatch type of HEdef with ?E = _ =>
    destruct (qc_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv n adv E HB HJ HK ltac:(lia) HEdef) as (HS & SHOK & HAWR)
  end end.

(* the cut after a kq_qc run *)
Ltac qc_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci Hn U27 U243 HAG c ci n jv :=
  lazymatch type of HK with kat _ ?cx ?fpos _ _ _ _ _ ?adv _ ?k2 ?ly3 ?S3 ?W3 ?ms3 ?md3 =>
  lazymatch type of HNEXT with kfrom _ _ ?POST (kin_qfil _ ?Rc) =>
    lazymatch goal with
    | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn), HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
      HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
      |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      let HR1 := fresh "HR1" in let HR2 := fresh "HR2" in
      spregion HS' 1%nat HR1; spregion HS' 2%nat HR2;
      lazymatch type of HR1 with region_ok _ _ _ ?r1 =>
      lazymatch type of HR2 with region_ok _ _ _ ?r2 =>
      let cs1 := eval vm_compute in (YP09.r_chunks r1) in
      let cs2 := eval vm_compute in (YP09.r_chunks r2) in
      apply (qc_land POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv n adv Ex msn mdn cs1 cs2 HNEXT HB Hfrm HJ HRcv Hcr
               Hci ltac:(lia) Hn HK U27 U243 HR1 ltac:(kn_in) HR2 ltac:(kn_in));
      [ kq_un HFr' (fun x => (LA_G_NL + (0x40000 + 8 * jv) <= x < LA_G_NL + (0x40008 + 8 * jv)) \/
                             (LA_G_NL + 0x40200 <= x < LA_G_NL + 0x40204))
      | exact HG'
      | apply (kn_kms_of _ Ex ssx msn 0x1f24 HS'); vm_compute; reflexivity
      | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
                 (proj1 (proj2 HK)))
      | unfold kregs_eq, kq_rl_fil; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        kq_reg HS' Ex ssx msn
      | exact (proj1 (wvb_fds_fs _ _ _))
      | exact (proj2 (wvb_fds_fs _ _ _)) ]
      end end
    end
  end end.

Theorem kq_qc : forall POST Rc, kfrom SK B POST (kin_qfil B Rc) -> kfrom SK B POST (kin_qcnt B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & n & adv & HRcv & Hcr & Hci & Hj & Hn & HK).
  pose proof HK as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  remember (Eimg (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 0x226)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 0x226)]) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (kq_env cx fpos k2 ly3 S3 md3 ms3 _ (kFSH cx fpos + 0x226) E HB HJB HR0 HRL ltac:(kn_in) ltac:(kn_in)
              ltac:(kn_in) ltac:(unfold kHighMemBeg, SHADOW_OFF in *; lia) HEdef)
    as (U9 & U18 & U20 & U21 & U24 & U25 & U32 & U243).
  assert (U27 : bv_unsigned (ew E 27%nat) = n).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 27 (Z_to_bv 5 (Z.of_nat 27)) eq_refl).
    rewrite (kn_reg_of ms3 _ 27 n HRL ltac:(unfold kq_rl_cnt; kn_in)). apply unsigned_lit_small. lia. }
  assert (U19 : bv_unsigned (ew E 19%nat) = ka0 cx + 8).
  { rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 19 (Z_to_bv 5 (Z.of_nat 19)) eq_refl).
    rewrite (kn_reg_of ms3 _ 19 _ HRL ltac:(unfold kq_rl_cnt; kn_in)). apply unsigned_lit_small.
    destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (C0 & C16 & _). lia. }
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]].
  - qc_go1 HB HJ HK HEdef c ci n 0 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1f24); [exact HAWR|].
    qc_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci Hn U27 U243 HAG c ci n 0.
  - qc_go1 HB HJ HK HEdef c ci n 1 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1f24); [exact HAWR|].
    qc_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci Hn U27 U243 HAG c ci n 1.
  - qc_go1 HB HJ HK HEdef c ci n 2 HS SHOK HAWR.
    paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x1f24); [exact HAWR|].
    qc_go2 HB HJ HK HNEXT Hfrm HRcv Hcr Hci Hn U27 U243 HAG c ci n 2.
Qed.

End b.
End a.
