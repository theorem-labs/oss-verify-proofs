(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 972 of its 1016 lines of code are new or changed and 1261 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the message count: from +0x5c4
   (checked_memset of w2 returned; kernel_msg0_kit.v kin_m5c4) to the message loop's head (kin_loop, +0x63c) or to the message
   path's end (kin_qmsg, +0x1e9c). Listing (internal path) (internal record, sha256 7bc02d6772b3):
     +0x5c4  bnez s3 / +0x5c8 j +0x1e9c          s3 = the cursor's n: n = 0 ends the message path, m = 0
     +0x5cc  lbu a0, 0(s8); beqz; errpath         the instrumented check of the cursor's n word
     +0x5d8  s3 := n - 1; sd s3, 8(s2)
     +0x5e0  ld a0, 0xc0(s1); lbu a0, 0(a0)       the check of the cursor's p word (slot 0xc0 = shadow(a0))
     +0x5f0  a0 := p; [a0] := p + 1
     +0x5fc  lb a1, shadow(p); beqz -> +0x610; j +0x211c: andi a2, a0, 7; bge a2, a1 -> errpath; j +0x610
     +0x610  lbu a0, 0(a0)                         the input byte b
     +0x614  ld a1, 0xb8(s1) (0x2aaaaaaaaaaaaaab); mulhu; s6 := b - 6 * mulhu(b, M) = b % 6
     +0x62c  bnez s6 / +0x630 j +0x1e9c            m = 0 ends the message path
     +0x634  a4 := 0; sd s6, 0x68(s1); +0x63c the loop's head
   THE PROOF. n = 0 (mc_zero): one run with s3 the literal 0, no memory written. n >= 1: the input byte b at p and its
   shadow byte s (both at the current memory: kernel_msg0_kit.v kn_input_at) are atoms; the proof cases in Coq on s = 0
   or s in [1, 7] (an atom with the condition p & 7 < s, saddr_ok from the call's range_addressable) and on b % 6 = 0 or
   not (a condition on the engine's own expression of s6, mc_m6, whose value is b % 6 by mc_m6_val, a table over the
   256 bytes), so the engine decides both branches and each of the four runs ends at its cut. The cut after a run is
   mc_land (kernel_kit.v's part lemmas with the change set {the cursor, the slot 0x68}; the cursor restated at adv + 1).
   kn_m5c: kin_m5c4 -> kin_loop (k = 0) / kin_qmsg.
   Section hypotheses: LAWS, TB (the read set's shadow at the current memory).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit kernel_next kernel_msg0_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


(* ---- the symbolic states at +0x5c4 ---- *)
(* n = 0: s3 is the literal 0, no region *)
Definition mc0_ss : sstate := mkSS (kpc 0x5c4) (sr_set sr_atoms 19%bv (SLit 0)) [] None (mkFacts [] [] []).

(* n >= 1: atoms 32 = p, 33 = shadow(p), 34 = s (the shadow byte of p), 35 = b (the input byte at p) *)
Definition mc_m6 : sv :=
  SAlu ALU_ADD (SOff 35 0)
    (SAlu ALU_SUB (SAlu ALU_SLL (SMd M_MULHU (SOff 35 0) (SLit 3074457345618258603)) (SLit 1))
                  (SAlu ALU_SLL (SMd M_MULHU (SOff 35 0) (SLit 3074457345618258603)) (SLit 3))).
Definition mc_cur : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 19 0))].
Definition mc_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x68 0xc8 0x68 0x70
    [YP09.mkChunk 0xb8 (CVal 8 (SLit KI_M6_V)); YP09.mkChunk 0xc0 (CVal 8 (km_sh 18 0))].
Definition mc_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition mc_shr (fast : bool) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (if fast then SLit 0 else SOff 34 0))].
Definition mc_regs : list sv := sr_set sr_atoms (Z_to_bv 5 24) (km_sh 18 8).
Definition mc_facts (fast zero : bool) : facts :=
  mkFacts (km_atoms ++ [(19%nat, mkAF 1 (2 ^ 64 - 1) 0); (35%nat, mkAF 0 255 0)] ++
           (if fast then [] else [(34%nat, mkAF 1 7 0)]))
    ((if fast then [] else [mkAC BC_LT (SAlu ALU_AND (SOff 32 0) (SLit 7)) (SOff 34 0)]) ++
     [mkAC (if zero then BC_EQ else BC_NE) mc_m6 (SLit 0)])
    [(km_sh 32 0, SOff 33 0)].
Definition mc_ss (fast zero : bool) : sstate :=
  mkSS (kpc 0x5c4) mc_regs [mc_cur; mc_sl; mc_in; mc_shr fast] None (mc_facts fast zero).

(* the engine's s6 is b % 6 *)
Lemma mc_m6_val : forall (E : env) b, ew E 35%nat = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E mc_m6 = Z_to_bv 64 (b mod 6).
Proof.
  intros E b Hb Hr. unfold mc_m6. cbn [sv_denot]. rewrite !Hb.
  assert (Hin : In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [apply Z2Nat.id; lia | apply in_seq; lia]. }
  clear Hr. cbn [seq map] in Hin.
  repeat (destruct Hin as [<- | Hin]; [apply bv_eq; vm_compute; reflexivity |]). destruct Hin.
Qed.

Lemma mc_beq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma mc_bne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof.
  intros x y Hx Hy. change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg, mc_beq by assumption. reflexivity.
Qed.

Lemma mc_blt : forall a b, 0 <= a < 8 -> 0 <= b < 8 -> a < b ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Ha Hb Hab.
  assert (Ga : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7) by lia.
  assert (Gb : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  clear Ha Hb.
  destruct Ga as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    destruct Gb as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    first [exfalso; lia | vm_compute; reflexivity].
Qed.

(* a register the symbolic file names by a value the machine already has (attr_text.v at_regs_ok_set) *)
Lemma mc_regs_ok_set : forall E sr regs (rd : bv 5) e,
  regs_ok E sr regs -> bv_eqb rd 0 = false -> sv_denot E e = getr regs rd ->
  regs_ok E (sr_set sr rd e) regs.
Proof.
  intros E sr regs rd e H H0 He r. destruct (bv_eqb r rd) eqn:Heq.
  - unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq. subst r. rewrite sr_get_set_same by exact H0.
    rewrite He. reflexivity.
  - rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in Heq; discriminate). apply H.
Qed.

Lemma mc_bv19 : (Z_to_bv 5 (Z.of_nat 19) : bv 5) = 19%bv.
Proof. apply bv_eq. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)

Definition mc_E (ms : machine_state) (p s b : Z) : env :=
  Eimg (Ereg (ms_regs ms) [w64 p; w64 (SHADOW_OFF + p / 8); w64 s; w64 b]).

Lemma mc_E_reg : forall ms p s b (jj : nat) (r : bv 5), Z.of_nat jj = bv_unsigned r ->
  ew (mc_E ms p s b) jj = getr (ms_regs ms) r.
Proof. intros ms p s b jj r H. unfold mc_E. apply ew_Eimg_Ereg_nat. exact H. Qed.

Lemma mc_E_ext : forall ms p s b,
  ew (mc_E ms p s b) 32%nat = w64 p /\ ew (mc_E ms p s b) 33%nat = w64 (SHADOW_OFF + p / 8) /\
  ew (mc_E ms p s b) 34%nat = w64 s /\ ew (mc_E ms p s b) 35%nat = w64 b.
Proof.
  intros ms p s b. unfold mc_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  split; [exact (ew_Ereg_extra _ _ 0)|]. split; [exact (ew_Ereg_extra _ _ 1)|].
  split; [exact (ew_Ereg_extra _ _ 2) | exact (ew_Ereg_extra _ _ 3)].
Qed.

Lemma mc_E_agree : forall ms p s b,
  YP06.env_agree 32 (Ereg (ms_regs ms) [w64 p; w64 (SHADOW_OFF + p / 8); w64 s; w64 b]) (mc_E ms p s b).
Proof. intros ms p s b. unfold mc_E. split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* the cursor's bytes may be written: the call's ajw, moved to the cut's journal *)
Lemma mc_awr_cur : forall cx fpos k2 ly3 S3 W3 mm md3, kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 ->
  forall a, ka0 cx <= a < ka0 cx + 16 ->
  (awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
     ((KN_CID, fpos) :: k_own cx) a /\ ~ (k_sp0 cx <= a < k_sp0 cx + k_XO cx)) \/
  inG (k_G cx) a \/ (inFP (k_OUT cx) a /\ k_sp0 cx <= a < k_sp0 cx + k_XO cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 HB HJ HJB a Ha.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HJB as (_ & _ & Hperm & _).
  assert (HE : inFP (kernel_awr (k_regs cx) (km0 cx)) a).
  { exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16). split; [unfold kernel_awr; km_inl |].
    cbn [fst snd]. unfold ka0 in Ha. lia. }
  destruct (Hajw a HE) as [[Haw Hnout] | [HGa | Hout]]; [left; split; [|exact Hnout] | right; left; exact HGa |
    right; right; exact Hout].
  destruct Haw as [Hw | [(Hfp & b0 & n0 & Hbn & Hr) | [(b0 & n0 & Hbn & Hnb & Hr) | (cid & pos & Hown & Hr)]]].
  - left. exact Hw.
  - right; left. split; [exact Hfp|]. exists b0, n0. split; [|exact Hr].
    exact (Permutation_in _ (Permutation_sym Hperm) Hbn).
  - right; right; left. exists b0, n0. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hbn)|].
    split; [exact Hnb | exact Hr].
  - right; right; right. exists cid, pos. split; [right; exact Hown|].
    rewrite (km_fa SK B cx fpos k2 ly3 S3 W3 mm md3 HB HJ). exact Hr.
Qed.

(* ---- n = 0: +0x5c4 `bnez s3` falls through to `j +0x1e9c` ---- *)
Lemma mc_zero : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW2 cx fpos) 0 0 ->
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv)) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  k_wn cx - adv = 0 ->
  kfrom SK B POST (kin_qmsg B Rc) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HB HJ HFR HRc Hc Hci Hj HW HAT Hn HQ.
  pose proof HAT as (HMS & HR0 & HRL & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof HB as ((_ & HGok & _) & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HRG : regs_ok E sr_atoms (ms_regs ms3)) by (subst E; apply regs_ok_Eimg_Ereg).
  assert (R19 : getr (ms_regs ms3) 19%bv = w64 0).
  { rewrite <- mc_bv19, <- Hn. exact (kn_reg_in ms3 _ 19 _ HRL ltac:(unfold kregs_m5; kn_in)). }
  clearbody E.
  assert (HS : st_ok_pi SEGS pa_val E mc0_ss (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc 0x5c4) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx. unfold mc0_ss.
    apply pa_entry_st_ok_full.
    - apply mc_regs_ok_set; [exact HRG | reflexivity | rewrite R19; reflexivity].
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS km_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_QMSG); [apply awr_ok_x_nil|].
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF'; intros Hw;
          destruct Hw as (rr & Hin & _); exact (False_ind _ Hin));
    assert (HMS' : kms KP_QMSG msn)
      by (apply (kn_kms_of _ E ssx msn KP_QMSG HS'); vm_compute; reflexivity);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) [] nx_keep0 HS' HAG
                   ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r nx_keepN ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) []
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    apply (HQ cx fpos k2 ly3 S3 W3 msn mdn HB HJ HFR)
  end.
  exists c, ci, j, 0, 0, adv.
  split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
  split; [unfold kw_at in *; rewrite Hmem; exact HW|].
  refine (kat_move B cx fpos 0x5c4 KP_QMSG _ _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ HAT HMS' HR0' _ Hmem _
    Hfds Hfs).
  - unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite HKN by (unfold nx_keepN; kn_in)); apply (kn_reg_in ms3 _ _ _ HRL); unfold kregs_m5; kn_in.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
Qed.


(* the state at +0x5c4, n >= 1: the four cases of the input byte's shadow byte s and of b % 6 *)
Lemma mc_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv (fast zero : bool) s (b : byte),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv)) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  (if fast then s = 0 else s <> 0) ->
  (if zero then bv_unsigned b mod 6 = 0 else bv_unsigned b mod 6 <> 0) ->
  st_ok_pi SEGS pa_val (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) (mc_ss fast zero) (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv fast zero s b HB HJ HK Hadv Hs Hsok Hb Hf Hz.
  pose proof HK as (Hkms & Hkr0 & Hkre & _ & _ & _ & Hksl & HJB & _ & Hkcur & _ & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct Hkcur as (Hadv0 & HCP & HCN & HCW).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & HAP).
  destruct HAP as (HAPF & HAPG & HAPL & HAPC).
  unfold apart_frame, apart in HAPF, HAPC. change (spZ (k_regs cx)) with (ksp cx) in HAPF.
  change (aarg (k_regs cx) 0) with (ka0 cx) in HAPC.
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6, HAPF.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (proj2 (CL (ka0 cx) ltac:(lia))) as CLa. pose proof (proj2 (CL (ka0 cx + 15) ltac:(lia))) as CLb.
  rewrite HK8 in CLa, CLb.
  pose proof (proj1 (CL (ka0 cx) ltac:(lia))) as CAa. pose proof (proj1 (CL (ka0 cx + 15) ltac:(lia))) as CAb.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  assert (Hpard : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + adv)).
  { pose proof HB as (_ & _ & _ & _ & _ & HWP & HWN & _).
    unfold kernel_ard. right. left. exists (k_wp cx), (k_wn cx). unfold ka0 in *.
    refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hpard) as (PL1 & PL2 & _ & PL4).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  unfold aview in Hs.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)))
    as [bs|] eqn:Ebs; [|discriminate Hs].
  cbn [option_map] in Hs. assert (Hs' : bv_unsigned bs = s) by (injection Hs; auto). clear Hs.
  assert (Hsr : 0 <= s < 8) by (pose proof (bv_unsigned_in_range 8 bs); unfold saddr_ok in Hsok; lia).
  unfold kregs_eq, kregs_m5 in Hkre. rewrite !Forall_cons_iff in Hkre.
  destruct Hkre as (R21 & R22 & R24 & R25 & R19 & _). cbn [fst snd] in R21, R22, R24, R25, R19.
  destruct Hkr0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  destruct (mc_E_ext ms3 (k_wp cx + adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35).
  assert (E18 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (mc_E_reg _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (mc_E_reg _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (mc_E_reg _ _ _ _ 20 20%bv eq_refl); exact A20).
  assert (E19 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 19%nat = w64 (k_wn cx - adv))
    by (rewrite (mc_E_reg _ _ _ _ 19 (Z_to_bv 5 (Z.of_nat 19)) eq_refl); exact R19).
  remember (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) as E eqn:HEdef.
  set (p := k_wp cx + adv) in *.
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (BV32 : bv_unsigned (ew E 32%nat) = p) by (apply km_bv; [exact E32 | lia]).
  assert (Hq : SHADOW_OFF <= SHADOW_OFF + p / 8 < SHADOW_OFF + 2 ^ 44)
    by (split; [pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia |
                pose proof (Z.div_lt_upper_bound p 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]).
  assert (BV33 : bv_unsigned (ew E 33%nat) = SHADOW_OFF + p / 8) by (apply km_bv; [exact E33 | unfold SHADOW_OFF in *; lia]).
  pose proof (kn_slot_of cx W3 ms3 _ KS_M6 KI_M6_V Hksl ltac:(apply in_or_app; left; unfold kslots_setup; km_inl)) as SL_M6.
  pose proof (kn_slot_of cx W3 ms3 _ KS_CSH (shadow_of_addr SHADOW_OFF (ka0 cx)) Hksl
    ltac:(apply in_or_app; left; unfold kslots_setup; km_inl)) as SL_CSH.
  rewrite (km_ms_shape ms3 (BASE + kpc 0x5c4) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val E (mkSS (kpc 0x5c4) sr_atoms [mc_cur; mc_sl; mc_in; mc_shr fast] None
                 (mc_facts fast zero))
                 (mkst (ms_regs ms3) (w64 (BASE + kpc 0x5c4)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. unfold mc_E. apply regs_ok_Eimg_Ereg.
    - destruct fast; vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      + unfold mc_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o Ho)|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) p);
            [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 19 0) (k_wn cx - adv));
            [apply sv_off0; exact E19 | cbn; lia | cbn; lia | exact HCN].
      + unfold mc_sl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite BV9. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply kn_apresent_writable;
                apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb8 (SLit KI_M6_V) KI_M6_V eq_refl SL_M6).
        * apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (km_sh 18 0) (shadow_of_addr SHADOW_OFF (ka0 cx)));
            [|exact SL_CSH].
          rewrite (km_denot_sh E 18 (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
          rewrite Z.add_0_r. reflexivity.
      + unfold mc_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite BV32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ p 0 1 (SOff 35 0) (bv_unsigned b));
          [apply sv_off0; exact E35 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. intros k Hk. destruct k as [|k]; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb.
        rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
        change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + unfold mc_shr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite BV33. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
        split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (SHADOW_OFF + p / 8) 0 1 (if fast then SLit 0 else SOff 34 0) s);
          [destruct fast; [cbn in Hf; rewrite Hf; reflexivity | apply sv_off0; exact E34] | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. intros k Hk. destruct k as [|k]; [|cbn in Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
        unfold shadow_of_addr in Ebs. rewrite Ebs, <- Hs'.
        rewrite le_byte_small by (pose proof (bv_unsigned_in_range 8 bs); change (2 ^ (8 * Z.of_nat 1)) with 256;
                                  change (bv_modulus 8) with 256 in *; lia).
        change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, mc_cur, mc_sl, mc_in, mc_shr. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite BV18, BV9, BV32, BV33.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *.
      repeat split; lia.
    - unfold facts_ok, mc_facts. cbn [f_atoms f_conds f_alias]. split; [|split].
      + unfold km_atoms. destruct fast; cbn [app atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite ?E18, ?E9, ?E20, ?E19, ?E35, ?E34; unfold w64;
          rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia);
          change (2 ^ 0) with 1; change (2 ^ 5) with 32; rewrite !Z.mod_1_r; unfold SHADOW_OFF;
          repeat split; first [lia | exact I | exact S5].
      + assert (Dslow : sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 7)) = Z_to_bv 64 (p mod 8)).
        { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
          rewrite (U_atom_off E 32 p 0 E32 ltac:(lia) ltac:(lia)), Z.add_0_r.
          change (zcanon 7) with 7.
          assert (Hl7 : Z.land p 7 = p mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
          rewrite Hl7. apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound p 8). lia. }
        assert (Dm6 : sv_denot E mc_m6 = Z_to_bv 64 (bv_unsigned b mod 6)) by (apply mc_m6_val; [exact E35 | lia]).
        pose proof (Z.mod_pos_bound (bv_unsigned b) 6 ltac:(lia)) as Hm6.
        pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hm8.
        destruct fast; cbn [app conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b].
        * rewrite Dm6. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). split; [|exact I].
          destruct zero; [rewrite mc_beq by lia; apply Z.eqb_eq; lia | rewrite mc_bne by lia; apply negb_true_iff, Z.eqb_neq; lia].
        * rewrite Dslow, (sv_off0 E 34 _ E34). split; [apply mc_blt; [lia | lia | unfold saddr_ok in Hsok; lia]|].
          rewrite Dm6. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). split; [|exact I].
          destruct zero; [rewrite mc_beq by lia; apply Z.eqb_eq; lia | rewrite mc_bne by lia; apply negb_true_iff, Z.eqb_neq; lia].
      + cbn [alias_ok]. split; [|exact I].
        rewrite (km_denot_sh E 32 p 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
        rewrite (sv_off0 E 33 _ E33). rewrite Z.add_0_r. reflexivity. }
  assert (HD24 : sv_denot E (km_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 24)).
  { rewrite (km_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    symmetry. exact R24. }
  exact (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 24) (km_sh 18 8) HS0 eq_refl HD24).
Qed.


(* the registers a run does not write: the same symbolic value at its start and at its end *)
Lemma mc_reg_same : forall E ss0 ss1 (H : word -> bool) (ms0 ms1 : machine_state) (l : list Z),
  st_ok_pi SEGS pa_val E ss0 (restrict H ms0) -> st_ok_pi SEGS pa_val E ss1 (restrict H ms1) ->
  forallb (fun k => sv_eqb (sr_get (ss_regs ss1) (Z_to_bv 5 k)) (sr_get (ss_regs ss0) (Z_to_bv 5 k))) l = true ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) l = true -> getr (ms_regs ms1) r = getr (ms_regs ms0) r.
Proof.
  intros E ss0 ss1 H ms0 ms1 l HS0 HS1 Hl r Hr.
  apply existsb_exists in Hr as (k & Hk & Hrk). apply Z.eqb_eq in Hrk.
  rewrite forallb_forall in Hl. pose proof (Hl k Hk) as Hs. apply sv_eqb_eq in Hs.
  assert (Er : r = Z_to_bv 5 k) by (rewrite <- Hrk; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (st_ok_pi_restrict_reg H E ss1 ms1 r HS1), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0), Er, Hs.
  reflexivity.
Qed.

(* THE CUT AFTER A RUN that wrote the cursor and the slots [s1 + lo, s1 + hi): kernel_kit.v's part lemmas, the cursor
   restated *)
Lemma mc_land : forall cx fpos pc rl sl sl' sh adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' adv' lo hi,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  (length sh <= 2048)%nat -> incl sl' sl -> 0x18 <= lo -> hi <= 0xf8 ->
  (forall ov, In ov sl' -> 0x18 <= fst ov <= 0xf0 /\ (fst ov + 8 <= lo \/ hi <= fst ov)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) -> ~ (ksp1 cx + lo <= a < ksp1 cx + hi) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' -> kcursor cx W3 ms' adv' ->
  kat B cx fpos pc' rl' sl' sh true adv' g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc rl sl sl' sh adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' adv' lo hi
    HB HK Hsh Hincl Hlo Hhi Hsl UN HP Hfds Hfs Hkms Hr0 Hrl Hcur.
  pose proof HK as (_ & _ & _ & HSAV & HFR & HSH & HSL & HJB & HKEPT & _ & HGNL & HLA).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & _ & F5 & _).
  rewrite kn_fsb8 in F2, F3, F5. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  pose proof (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2). unfold kHighMemBeg in FS2.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (kn_apre SK B cx HB) as (AG & AL & _).
  unfold apart_gnl, apart in AG, AL.
  set (X := fun a => (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + lo <= a < ksp1 cx + hi)).
  assert (UNX : forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hx. apply UN; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H]. }
  (* the cursor is off the window, F, F's shadow, g_nl and long_alias *)
  assert (CW : forall a, ka0 cx <= a < ka0 cx + 16 ->
            ~ (ksp cx - 4640 <= a < ksp cx) /\ (a < kLowMemEnd \/ kHighMemBeg <= a) /\
            ~ (kF cx fpos <= a < kF cx fpos + 16384)).
  { intros a Ha. destruct (CL a Ha) as (CL1 & CL2). rewrite HK8 in CL2. split; [exact CL2|]. split; [exact CL1|].
    assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in Ha; exact Ha).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hx) as HnF. rewrite kn_fsb8 in HnF. exact HnF. }
  unfold kat.
  refine (conj Hkms (conj Hr0 (conj Hrl (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hcur
    (conj _ _))))))))))).
  - apply (ksaved_frame SK B X cx W3 ms3 W3 ms' HB UNX); [|exact HSAV].
    intros a Ha [Hx | Hx]; [destruct (CW a Hx) as (CW1 & _); lia | lia].
  - apply (kframe_frame B LAWS X cx fpos true k2 ly3 S3 md3 W3 ms3 W3 ms' HJB UNX HP); [| | exact HFR];
      rewrite ?kn_fsb8; intros a Ha [Hx | Hx]; first [destruct (CW a Hx) as (_ & _ & CW3); lia | lia].
  - apply (kshadow_frame B LAWS X cx fpos sh k2 ly3 S3 md3 W3 ms3 W3 ms' HJB UNX Hsh); [|exact HSH].
    intros a Ha [Hx | Hx].
    + destruct (CW a Hx) as (_ & CW2 & _). unfold kFSH, shadow_of_addr, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
    + unfold kFSH, shadow_of_addr, SHADOW_OFF in *. lia.
  - apply (kslots_frame SK B X cx sl sl' W3 ms3 W3 ms' HB UNX Hincl); [|exact HSL].
    intros ov Hov. destruct (Hsl ov Hov) as ((Ho1 & Ho2) & Ho3). split; [lia|].
    intros a Ha [Hx | Hx]; [destruct (CW a Hx) as (CW1 & _); lia | lia].
  - exact (kjbk_md B cx fpos k2 ly3 S3 md3 md' HJB Hfds Hfs).
  - apply (kkept_frame SK B LAWS X cx fpos k2 ly3 S3 md3 W3 ms3 W3 ms' HB HJB UNX HP); [|exact HKEPT].
    intros a [Hx | Hx]; unfold kX_in.
    + left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
      split; [unfold kernel_awr; km_inl | cbn [fst snd]; unfold ka0 in Hx; exact Hx].
    + right. right. right. rewrite HK8. lia.
  - apply (kgnl_frame X cx g W3 ms3 W3 ms' UNX HP); [|exact HGNL].
    intros a Ha [Hx | Hx]; unfold LA_G_NL, NK_SIZE in *; lia.
  - apply (kla_frame X W3 ms3 W3 ms' UNX HP); [|exact HLA].
    intros a Ha [Hx | Hx]; unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in *; lia.
Qed.

(* +0x5c4 -> +0x1e9c, s = 0, b % 6 = 0 *)
Lemma mc_go_FZ : forall POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s (b : byte),
  (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  kfrom SK B POST (kin_loop B Rc Rm) -> kfrom SK B POST (kin_qmsg B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW2 cx fpos) 0 0 ->
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv)) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  s = 0 -> bv_unsigned b mod 6 = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK Hadv
    Hs Hsok Hb Hf Hz.
  pose proof (mc_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv true true s b HB HJ HK Hadv Hs Hsok Hb Hf Hz) as HS.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & _).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HRL as HRL'.
  unfold kregs_eq, kregs_m5 in HRL'. rewrite !Forall_cons_iff in HRL'.
  destruct HRL' as (R21 & R22 & R24 & R25 & R19 & _). cbn [fst snd] in R21, R22, R24, R25, R19.
  destruct (mc_E_ext ms3 (k_wp cx + adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35).
  assert (E18 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (mc_E_reg _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (mc_E_reg _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (mc_E_reg _ _ _ _ 20 20%bv eq_refl); exact A20).
  assert (E19 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 19%nat = w64 (k_wn cx - adv))
    by (rewrite (mc_E_reg _ _ _ _ 19 (Z_to_bv 5 (Z.of_nat 19)) eq_refl); exact R19).
  pose proof (mc_E_agree ms3 (k_wp cx + adv) s (bv_unsigned b)) as HAG.
  remember (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (SHOK : sh_ok SEGS km_Bx km_SHA E (mrestrict (w_H W3) (ms_mem ms3)))
    by exact (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20).
  pose proof HS as HS0.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_QMSG).
  { intros a (r & Hin & Hr). cbn [mc_ss ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [mc_cur mc_sl mc_in mc_shr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    - rewrite BV18 in Hr. exact (mc_awr_cur cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB a ltac:(lia)).
    - rewrite BV9 in Hr. left. split; [left; lia | lia].
    - lia.
    - lia. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E (ss_mem (mc_ss true true)) (w_H W3) (ms_mem ms3) (ms_mem ms2)
      (fun a => (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70)) Hx) as UN1 end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) -> ~ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70) ->
            aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha H1 H2. apply UN1; [| exact Ha | intros [H|H]; contradiction].
    intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-; cbn [base_val] in Hx;
      [rewrite BV18 in Hx; left; lia | rewrite BV9 in Hx; right; lia | lia | lia]. }
  clear UN1.
  spregion HS 0%nat HRC. spregion HS 1%nat HRS.
  pose proof (mc_reg_same E (mc_ss true true) _ (w_H W3) ms3 ms2 [2; 3; 4; 8; 9; 18; 20; 21; 24; 25] HS0 HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  assert (DP1 : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
  { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  assert (DN1 : sv_denot E (SOff 19 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
  { cbn [sv_denot]. rewrite E19. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) _ HRC BV18
    ltac:(km_inl) DP1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VP.
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 19 (-1)) _ HRC BV18
    ltac:(km_inl) DN1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VN.
  assert (HCUR' : kcursor cx W3 ms2 (adv + 1)).
  { split; [lia|]. split; [rewrite Z.add_0_r in VP; exact VP|]. split; [exact VN|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)). }
  assert (HKMS : kms KP_QMSG ms2).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms2 HS eq_refl) as Hsh. unfold kms. rewrite Hsh.
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ss_pc]. repeat split; reflexivity. }
  assert (HR0' : kregs0 cx ms2).
  { unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by reflexivity; assumption. }
  assert (HWK : kw_at W3 ms2 (kW2 cx fpos) 0 0).
  { apply (kn_kw_keep W3 ms3 ms2 _ 0 0 HW); [|intros a Ha; exact (apresent_grows _ _ _ a HG Ha)].
    intros i Hi. unfold kW2, KN_W2, NW_SIZE in *. apply UN; [lia | | lia].
    intros Hx. destruct (CL _ Hx) as (_ & _).
    assert (Hx' : kernel_ard SEGS (k_regs cx) (km0 cx) (kF cx fpos + 0x1130 + i)) by (left; unfold ka0 in Hx; exact Hx).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hx') as HnF. rewrite kn_fsb8 in HnF. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) end.
  assert (Hfds : m_fds md2 = m_fds md3) by (subst md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity).
  assert (Hfs : m_fs md2 = m_fs md3) by (subst md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).

  apply (HQ cx fpos k2 ly3 S3 W3 ms2 md2 HB); [exact HJ | exact HFR |].
  exists c, ci, j, 0, 0, (adv + 1).
  split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|]. split; [exact HWK|].
  apply (mc_land cx fpos 0x5c4 _ _ _ _ adv (Some j) k2 ly3 S3 W3 ms3 md3 ms2 md2 KP_QMSG _ (adv + 1) 0x68 0x70 HB HK).
  - rewrite kfsh_length. lia.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx | Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
  - lia.
  - lia.
  - intros ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov].
    + unfold kslots_setup in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov];
        [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
              KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2]; lia |]).
      destruct Hov.
    + cbn [In] in Hov. destruct Hov as [<- | []]. cbv [fst KS_CI]. lia.
  - exact UN.
  - intros a Hp. exact (apresent_grows _ _ _ a HG Hp).
  - exact Hfds.
  - exact Hfs.
  - exact HKMS.
  - exact HR0'.
  - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite KEEP by reflexivity; assumption.
  - exact HCUR'.
Qed.

(* +0x5c4 -> +0x63c, s = 0, b % 6 <> 0 *)
Lemma mc_go_FN : forall POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s (b : byte),
  (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  kfrom SK B POST (kin_loop B Rc Rm) -> kfrom SK B POST (kin_qmsg B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW2 cx fpos) 0 0 ->
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv)) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  s = 0 -> bv_unsigned b mod 6 <> 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK Hadv
    Hs Hsok Hb Hf Hz.
  pose proof (mc_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv true false s b HB HJ HK Hadv Hs Hsok Hb Hf Hz) as HS.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & _).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HRL as HRL'.
  unfold kregs_eq, kregs_m5 in HRL'. rewrite !Forall_cons_iff in HRL'.
  destruct HRL' as (R21 & R22 & R24 & R25 & R19 & _). cbn [fst snd] in R21, R22, R24, R25, R19.
  destruct (mc_E_ext ms3 (k_wp cx + adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35).
  assert (E18 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (mc_E_reg _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (mc_E_reg _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (mc_E_reg _ _ _ _ 20 20%bv eq_refl); exact A20).
  assert (E19 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 19%nat = w64 (k_wn cx - adv))
    by (rewrite (mc_E_reg _ _ _ _ 19 (Z_to_bv 5 (Z.of_nat 19)) eq_refl); exact R19).
  pose proof (mc_E_agree ms3 (k_wp cx + adv) s (bv_unsigned b)) as HAG.
  remember (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (SHOK : sh_ok SEGS km_Bx km_SHA E (mrestrict (w_H W3) (ms_mem ms3)))
    by exact (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20).
  pose proof HS as HS0.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_LOOP).
  { intros a (r & Hin & Hr). cbn [mc_ss ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [mc_cur mc_sl mc_in mc_shr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    - rewrite BV18 in Hr. exact (mc_awr_cur cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB a ltac:(lia)).
    - rewrite BV9 in Hr. left. split; [left; lia | lia].
    - lia.
    - lia. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E (ss_mem (mc_ss true false)) (w_H W3) (ms_mem ms3) (ms_mem ms2)
      (fun a => (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70)) Hx) as UN1 end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) -> ~ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70) ->
            aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha H1 H2. apply UN1; [| exact Ha | intros [H|H]; contradiction].
    intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-; cbn [base_val] in Hx;
      [rewrite BV18 in Hx; left; lia | rewrite BV9 in Hx; right; lia | lia | lia]. }
  clear UN1.
  spregion HS 0%nat HRC. spregion HS 1%nat HRS.
  pose proof (mc_reg_same E (mc_ss true false) _ (w_H W3) ms3 ms2 [2; 3; 4; 8; 9; 18; 20; 21; 24; 25] HS0 HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  assert (DP1 : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
  { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  assert (DN1 : sv_denot E (SOff 19 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
  { cbn [sv_denot]. rewrite E19. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) _ HRC BV18
    ltac:(km_inl) DP1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VP.
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 19 (-1)) _ HRC BV18
    ltac:(km_inl) DN1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VN.
  assert (HCUR' : kcursor cx W3 ms2 (adv + 1)).
  { split; [lia|]. split; [rewrite Z.add_0_r in VP; exact VP|]. split; [exact VN|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)). }
  assert (HKMS : kms KP_LOOP ms2).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms2 HS eq_refl) as Hsh. unfold kms. rewrite Hsh.
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ss_pc]. repeat split; reflexivity. }
  assert (HR0' : kregs0 cx ms2).
  { unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by reflexivity; assumption. }
  assert (HWK : kw_at W3 ms2 (kW2 cx fpos) 0 0).
  { apply (kn_kw_keep W3 ms3 ms2 _ 0 0 HW); [|intros a Ha; exact (apresent_grows _ _ _ a HG Ha)].
    intros i Hi. unfold kW2, KN_W2, NW_SIZE in *. apply UN; [lia | | lia].
    intros Hx. destruct (CL _ Hx) as (_ & _).
    assert (Hx' : kernel_ard SEGS (k_regs cx) (km0 cx) (kF cx fpos + 0x1130 + i)) by (left; unfold ka0 in Hx; exact Hx).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hx') as HnF. rewrite kn_fsb8 in HnF. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) end.
  assert (Hfds : m_fds md2 = m_fds md3) by (subst md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity).
  assert (Hfs : m_fs md2 = m_fs md3) by (subst md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).

  set (m := bv_unsigned b mod 6).
  assert (Hm : 1 <= m <= 5) by (subst m; pose proof (Z.mod_pos_bound (bv_unsigned b) 6 ltac:(lia)); lia).
  assert (Dm6 : sv_denot E mc_m6 = Z_to_bv 64 m) by (subst m; apply mc_m6_val; [exact E35 | lia]).
  prreg HS (Z_to_bv 5 (Z.of_nat 14)) R14.
  pose proof (st_ok_pi_restrict_reg (w_H W3) E _ ms2 (Z_to_bv 5 (Z.of_nat 22)) HS) as R22'.
  lazymatch type of R22' with _ = sv_denot _ ?t => replace t with mc_m6 in R22' by (vm_compute; reflexivity) end.
  rewrite Dm6 in R22'.
  pose proof (km_rd_of_region E (w_H W3) (ms_mem ms2) 9 (ksp1 cx) _ _ _ _ _ 0x68 mc_m6 m HRS BV9
    ltac:(km_inl) Dm6 ltac:(lia)) as RKM.
  apply (HLOOP cx fpos k2 ly3 S3 W3 ms2 md2 HB); [exact HJ | exact HFR |].
  exists c, ci, j, m, 0, 0, 0, (adv + 1).
  split; [exact HRc|]. split; [rewrite Z.sub_0_r; exact (HRm cx m Hm)|]. split; [exact Hc|]. split; [exact Hci|].
  split; [exact Hj|]. split; [exact Hm|]. split; [lia|]. split; [exact HWK|].
  replace (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m)])
    with ((kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)]) ++ [(KS_M, m)])
    by (rewrite <- app_assoc; reflexivity).
  apply km_kat_sl; [|unfold kslots_eq; apply Forall_cons; [cbn [fst snd]; exact RKM | apply Forall_nil]].
  apply (mc_land cx fpos 0x5c4 _ _ _ _ adv (Some j) k2 ly3 S3 W3 ms3 md3 ms2 md2 KP_LOOP _ (adv + 1) 0x68 0x70 HB HK).
  - rewrite kfsh_length. lia.
  - apply incl_refl.
  - lia.
  - lia.
  - intros ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov].
    + unfold kslots_setup in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov];
        [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
              KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2]; lia |]).
      destruct Hov.
    + cbn [In] in Hov. destruct Hov as [<- | [<- | []]]; cbv [fst KS_CI KS_ROOM]; lia.
  - exact UN.
  - intros a Hp. exact (apresent_grows _ _ _ a HG Hp).
  - exact Hfds.
  - exact Hfs.
  - exact HKMS.
  - exact HR0'.
  - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ exact R14 | exact R22' | rewrite KEEP by reflexivity; assumption ].
  - exact HCUR'.
Qed.

(* +0x5c4 -> +0x1e9c, s in [1, 7], b % 6 = 0 *)
Lemma mc_go_SZ : forall POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s (b : byte),
  (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  kfrom SK B POST (kin_loop B Rc Rm) -> kfrom SK B POST (kin_qmsg B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW2 cx fpos) 0 0 ->
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv)) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  s <> 0 -> bv_unsigned b mod 6 = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK Hadv
    Hs Hsok Hb Hf Hz.
  pose proof (mc_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv false true s b HB HJ HK Hadv Hs Hsok Hb Hf Hz) as HS.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & _).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HRL as HRL'.
  unfold kregs_eq, kregs_m5 in HRL'. rewrite !Forall_cons_iff in HRL'.
  destruct HRL' as (R21 & R22 & R24 & R25 & R19 & _). cbn [fst snd] in R21, R22, R24, R25, R19.
  destruct (mc_E_ext ms3 (k_wp cx + adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35).
  assert (E18 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (mc_E_reg _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (mc_E_reg _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (mc_E_reg _ _ _ _ 20 20%bv eq_refl); exact A20).
  assert (E19 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 19%nat = w64 (k_wn cx - adv))
    by (rewrite (mc_E_reg _ _ _ _ 19 (Z_to_bv 5 (Z.of_nat 19)) eq_refl); exact R19).
  pose proof (mc_E_agree ms3 (k_wp cx + adv) s (bv_unsigned b)) as HAG.
  remember (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (SHOK : sh_ok SEGS km_Bx km_SHA E (mrestrict (w_H W3) (ms_mem ms3)))
    by exact (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20).
  pose proof HS as HS0.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_QMSG).
  { intros a (r & Hin & Hr). cbn [mc_ss ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [mc_cur mc_sl mc_in mc_shr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    - rewrite BV18 in Hr. exact (mc_awr_cur cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB a ltac:(lia)).
    - rewrite BV9 in Hr. left. split; [left; lia | lia].
    - lia.
    - lia. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E (ss_mem (mc_ss false true)) (w_H W3) (ms_mem ms3) (ms_mem ms2)
      (fun a => (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70)) Hx) as UN1 end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) -> ~ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70) ->
            aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha H1 H2. apply UN1; [| exact Ha | intros [H|H]; contradiction].
    intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-; cbn [base_val] in Hx;
      [rewrite BV18 in Hx; left; lia | rewrite BV9 in Hx; right; lia | lia | lia]. }
  clear UN1.
  spregion HS 0%nat HRC. spregion HS 1%nat HRS.
  pose proof (mc_reg_same E (mc_ss false true) _ (w_H W3) ms3 ms2 [2; 3; 4; 8; 9; 18; 20; 21; 24; 25] HS0 HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  assert (DP1 : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
  { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  assert (DN1 : sv_denot E (SOff 19 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
  { cbn [sv_denot]. rewrite E19. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) _ HRC BV18
    ltac:(km_inl) DP1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VP.
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 19 (-1)) _ HRC BV18
    ltac:(km_inl) DN1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VN.
  assert (HCUR' : kcursor cx W3 ms2 (adv + 1)).
  { split; [lia|]. split; [rewrite Z.add_0_r in VP; exact VP|]. split; [exact VN|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)). }
  assert (HKMS : kms KP_QMSG ms2).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms2 HS eq_refl) as Hsh. unfold kms. rewrite Hsh.
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ss_pc]. repeat split; reflexivity. }
  assert (HR0' : kregs0 cx ms2).
  { unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by reflexivity; assumption. }
  assert (HWK : kw_at W3 ms2 (kW2 cx fpos) 0 0).
  { apply (kn_kw_keep W3 ms3 ms2 _ 0 0 HW); [|intros a Ha; exact (apresent_grows _ _ _ a HG Ha)].
    intros i Hi. unfold kW2, KN_W2, NW_SIZE in *. apply UN; [lia | | lia].
    intros Hx. destruct (CL _ Hx) as (_ & _).
    assert (Hx' : kernel_ard SEGS (k_regs cx) (km0 cx) (kF cx fpos + 0x1130 + i)) by (left; unfold ka0 in Hx; exact Hx).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hx') as HnF. rewrite kn_fsb8 in HnF. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) end.
  assert (Hfds : m_fds md2 = m_fds md3) by (subst md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity).
  assert (Hfs : m_fs md2 = m_fs md3) by (subst md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).

  apply (HQ cx fpos k2 ly3 S3 W3 ms2 md2 HB); [exact HJ | exact HFR |].
  exists c, ci, j, 0, 0, (adv + 1).
  split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|]. split; [exact HWK|].
  apply (mc_land cx fpos 0x5c4 _ _ _ _ adv (Some j) k2 ly3 S3 W3 ms3 md3 ms2 md2 KP_QMSG _ (adv + 1) 0x68 0x70 HB HK).
  - rewrite kfsh_length. lia.
  - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx | Hx]; [left; exact Hx|].
    right. cbn [In] in Hx |- *. tauto.
  - lia.
  - lia.
  - intros ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov].
    + unfold kslots_setup in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov];
        [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
              KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2]; lia |]).
      destruct Hov.
    + cbn [In] in Hov. destruct Hov as [<- | []]. cbv [fst KS_CI]. lia.
  - exact UN.
  - intros a Hp. exact (apresent_grows _ _ _ a HG Hp).
  - exact Hfds.
  - exact Hfs.
  - exact HKMS.
  - exact HR0'.
  - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite KEEP by reflexivity; assumption.
  - exact HCUR'.
Qed.

(* +0x5c4 -> +0x63c, s in [1, 7], b % 6 <> 0 *)
Lemma mc_go_SN : forall POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s (b : byte),
  (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  kfrom SK B POST (kin_loop B Rc Rm) -> kfrom SK B POST (kin_qmsg B Rc) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  kw_at W3 ms3 (kW2 cx fpos) 0 0 ->
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv)) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  adv < k_wn cx ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  saddr_ok (k_wp cx + adv) s ->
  mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b ->
  s <> 0 -> bv_unsigned b mod 6 <> 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK Hadv
    Hs Hsok Hb Hf Hz.
  pose proof (mc_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv false false s b HB HJ HK Hadv Hs Hsok Hb Hf Hz) as HS.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & _).
  destruct HCUR as (Hadv0 & HCP & HCN & HCW).
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv + 1 <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HRL as HRL'.
  unfold kregs_eq, kregs_m5 in HRL'. rewrite !Forall_cons_iff in HRL'.
  destruct HRL' as (R21 & R22 & R24 & R25 & R19 & _). cbn [fst snd] in R21, R22, R24, R25, R19.
  destruct (mc_E_ext ms3 (k_wp cx + adv) s (bv_unsigned b)) as (E32 & E33 & E34 & E35).
  assert (E18 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 18%nat = w64 (ka0 cx))
    by (rewrite (mc_E_reg _ _ _ _ 18 18%bv eq_refl); exact A18).
  assert (E9 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 9%nat = w64 (ksp1 cx))
    by (rewrite (mc_E_reg _ _ _ _ 9 9%bv eq_refl); exact A9).
  assert (E20 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 20%nat = w64 SHADOW_OFF)
    by (rewrite (mc_E_reg _ _ _ _ 20 20%bv eq_refl); exact A20).
  assert (E19 : ew (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) 19%nat = w64 (k_wn cx - adv))
    by (rewrite (mc_E_reg _ _ _ _ 19 (Z_to_bv 5 (Z.of_nat 19)) eq_refl); exact R19).
  pose proof (mc_E_agree ms3 (k_wp cx + adv) s (bv_unsigned b)) as HAG.
  remember (mc_E ms3 (k_wp cx + adv) s (bv_unsigned b)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (SHOK : sh_ok SEGS km_Bx km_SHA E (mrestrict (w_H W3) (ms_mem ms3)))
    by exact (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20).
  pose proof HS as HS0.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK km_span (kpc KP_LOOP).
  { intros a (r & Hin & Hr). cbn [mc_ss ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | []]]]];
      cbn [mc_cur mc_sl mc_in mc_shr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    - rewrite BV18 in Hr. exact (mc_awr_cur cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ HJB a ltac:(lia)).
    - rewrite BV9 in Hr. left. split; [left; lia | lia].
    - lia.
    - lia. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E (ss_mem (mc_ss false false)) (w_H W3) (ms_mem ms3) (ms_mem ms2)
      (fun a => (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70)) Hx) as UN1 end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ka0 cx <= a < ka0 cx + 16) -> ~ (ksp1 cx + 0x68 <= a < ksp1 cx + 0x70) ->
            aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha H1 H2. apply UN1; [| exact Ha | intros [H|H]; contradiction].
    intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-; cbn [base_val] in Hx;
      [rewrite BV18 in Hx; left; lia | rewrite BV9 in Hx; right; lia | lia | lia]. }
  clear UN1.
  spregion HS 0%nat HRC. spregion HS 1%nat HRS.
  pose proof (mc_reg_same E (mc_ss false false) _ (w_H W3) ms3 ms2 [2; 3; 4; 8; 9; 18; 20; 21; 24; 25] HS0 HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  assert (DP1 : sv_denot E (SOff 32 1) = Z_to_bv 64 (k_wp cx + (adv + 1))).
  { cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  assert (DN1 : sv_denot E (SOff 19 (-1)) = Z_to_bv 64 (k_wn cx - (adv + 1))).
  { cbn [sv_denot]. rewrite E19. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 0 8 (SOff 32 1) _ HRC BV18
    ltac:(km_inl) DP1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VP.
  pose proof (field_of_region (segs := SEGS) E _ 18%nat (ka0 cx) _ _ _ _ _ 8 8 (SOff 19 (-1)) _ HRC BV18
    ltac:(km_inl) DN1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia))
    as VN.
  assert (HCUR' : kcursor cx W3 ms2 (adv + 1)).
  { split; [lia|]. split; [rewrite Z.add_0_r in VP; exact VP|]. split; [exact VN|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)). }
  assert (HKMS : kms KP_LOOP ms2).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms2 HS eq_refl) as Hsh. unfold kms. rewrite Hsh.
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ss_pc]. repeat split; reflexivity. }
  assert (HR0' : kregs0 cx ms2).
  { unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by reflexivity; assumption. }
  assert (HWK : kw_at W3 ms2 (kW2 cx fpos) 0 0).
  { apply (kn_kw_keep W3 ms3 ms2 _ 0 0 HW); [|intros a Ha; exact (apresent_grows _ _ _ a HG Ha)].
    intros i Hi. unfold kW2, KN_W2, NW_SIZE in *. apply UN; [lia | | lia].
    intros Hx. destruct (CL _ Hx) as (_ & _).
    assert (Hx' : kernel_ard SEGS (k_regs cx) (km0 cx) (kF cx fpos + 0x1130 + i)) by (left; unfold ka0 in Hx; exact Hx).
    pose proof (kn_ard_not_F SK B LAWS cx fpos k2 ly3 S3 md3 _ HB HJB Hx') as HnF. rewrite kn_fsb8 in HnF. lia. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2 := mdx) end.
  assert (Hfds : m_fds md2 = m_fds md3) by (subst md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity).
  assert (Hfs : m_fs md2 = m_fs md3) by (subst md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).

  set (m := bv_unsigned b mod 6).
  assert (Hm : 1 <= m <= 5) by (subst m; pose proof (Z.mod_pos_bound (bv_unsigned b) 6 ltac:(lia)); lia).
  assert (Dm6 : sv_denot E mc_m6 = Z_to_bv 64 m) by (subst m; apply mc_m6_val; [exact E35 | lia]).
  prreg HS (Z_to_bv 5 (Z.of_nat 14)) R14.
  pose proof (st_ok_pi_restrict_reg (w_H W3) E _ ms2 (Z_to_bv 5 (Z.of_nat 22)) HS) as R22'.
  lazymatch type of R22' with _ = sv_denot _ ?t => replace t with mc_m6 in R22' by (vm_compute; reflexivity) end.
  rewrite Dm6 in R22'.
  pose proof (km_rd_of_region E (w_H W3) (ms_mem ms2) 9 (ksp1 cx) _ _ _ _ _ 0x68 mc_m6 m HRS BV9
    ltac:(km_inl) Dm6 ltac:(lia)) as RKM.
  apply (HLOOP cx fpos k2 ly3 S3 W3 ms2 md2 HB); [exact HJ | exact HFR |].
  exists c, ci, j, m, 0, 0, 0, (adv + 1).
  split; [exact HRc|]. split; [rewrite Z.sub_0_r; exact (HRm cx m Hm)|]. split; [exact Hc|]. split; [exact Hci|].
  split; [exact Hj|]. split; [exact Hm|]. split; [lia|]. split; [exact HWK|].
  replace (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m)])
    with ((kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)]) ++ [(KS_M, m)])
    by (rewrite <- app_assoc; reflexivity).
  apply km_kat_sl; [|unfold kslots_eq; apply Forall_cons; [cbn [fst snd]; exact RKM | apply Forall_nil]].
  apply (mc_land cx fpos 0x5c4 _ _ _ _ adv (Some j) k2 ly3 S3 W3 ms3 md3 ms2 md2 KP_LOOP _ (adv + 1) 0x68 0x70 HB HK).
  - rewrite kfsh_length. lia.
  - apply incl_refl.
  - lia.
  - lia.
  - intros ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov].
    + unfold kslots_setup in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov];
        [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
              KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2]; lia |]).
      destruct Hov.
    + cbn [In] in Hov. destruct Hov as [<- | [<- | []]]; cbv [fst KS_CI KS_ROOM]; lia.
  - exact UN.
  - intros a Hp. exact (apresent_grows _ _ _ a HG Hp).
  - exact Hfds.
  - exact Hfs.
  - exact HKMS.
  - exact HR0'.
  - unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ exact R14 | exact R22' | rewrite KEEP by reflexivity; assumption ].
  - exact HCUR'.
Qed.

(* THE PHASE: +0x5c4 -> +0x63c (kin_loop, k = 0) / +0x1e9c (kin_qmsg) *)
Theorem kn_m5c : forall POST Rc Rm, (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  kfrom SK B POST (kin_loop B Rc Rm) -> kfrom SK B POST (kin_qmsg B Rc) -> kfrom SK B POST (kin_m5c4 B Rc).
Proof.
  intros POST Rc Rm HRm HLOOP HQ cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & adv & HRc & Hc & Hci & Hj & HW & HK).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & HKK & HCUR & _).
  destruct HCUR as (Hadv0 & _).
  destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hn0 | Hn1].
  - exact (mc_zero POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv HB HJ HFR HRc Hc Hci Hj HW HK Hn0 HQ).
  - assert (Hadv : adv < k_wn cx) by lia.
    pose proof HB as (_ & _ & _ & _ & _ & HWP & HWN & HWPr & HWNr & HD & HDL & _).
    assert (Hpard : kernel_ard SEGS (k_regs cx) (km0 cx) (k_wp cx + adv)).
    { unfold kernel_ard. right. left. exists (k_wp cx), (k_wn cx). unfold ka0 in *.
      refine (conj HWP (conj HWN (conj HWPr (conj HWNr _)))). lia. }
    destruct (kn_input_at SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) HB HJ HJB HKK ltac:(lia))
      as ((s & Hs & Hsok) & Hview).
    destruct HD as (_ & _ & HD).
    assert (Hi : (Z.to_nat adv < length (k_d cx))%nat) by lia.
    destruct (nth_error (k_d cx) (Z.to_nat adv)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
    pose proof (HD (Z.to_nat adv) Hi) as Hm. rewrite Eb, Z2Nat.id in Hm by lia.
    assert (Hb : mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (k_wp cx + adv) = Some b).
    { rewrite <- Hm. exact (mbyte_of_aview SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms3) _ Hview). }
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0]; destruct (Z.eq_dec (bv_unsigned b mod 6) 0) as [Hz0 | Hz0].
    + exact (mc_go_FZ POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK
               Hadv Hs Hsok Hb Hs0 Hz0).
    + exact (mc_go_FN POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK
               Hadv Hs Hsok Hb Hs0 Hz0).
    + exact (mc_go_SZ POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK
               Hadv Hs Hsok Hb Hs0 Hz0).
    + exact (mc_go_SN POST Rc Rm cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv s b HRm HLOOP HQ HB HJ HFR HRc Hc Hci Hj HW HK
               Hadv Hs Hsok Hb Hs0 Hz0).
Qed.

End b.
End a.
