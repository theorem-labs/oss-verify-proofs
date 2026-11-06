(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 127 of its 178 lines of code are new or changed and 353 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write's cuts after the name selector.

   w_regs: the registers the loop keeps (lf_lregs) with s5 = the name and s6 = the text_of answer.
   w_fresh: the fresh text block (none, or the one text_of made) is a block of the state, no block of the entry,
     and apart from the two blocks of the call, its FILE block and its input; and a state of the arm before
     text_of (own list the two blocks of the call) with its block bytes within LF_LIVE_HELD, which the tail's
     counters need once the fresh block is freed (ArmK.v lf_bl_bytes_eq).
   w_k_inv: the cut at +0x1014, after kernel(&cursor).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LW_kret : Z := AF_LLVMFuzzerTestOneInput + 0x1014.   (* 0x837e8, kernel's return in op_write *)
Definition LW_mb : Z := AF_LLVMFuzzerTestOneInput + 0x1078.     (* 0x8384c, after model_begin's five stores *)
Definition LW_mret : Z := AF_LLVMFuzzerTestOneInput + 0x1088.   (* 0x8385c, model_write's return *)

(* a range inside an application-memory range *)
Lemma w_amem_sub : forall p n k, amem_range p n -> 0 <= k <= n -> amem_range p k.
Proof. intros p n k H Hk. unfold amem_range in *. lia. Qed.


(* two different elements of a pairwise list are related, in some order *)
Lemma w_pairwise_map2 : forall {A X} (R : X -> X -> Prop) (f : A -> X) (l : list A) a b,
  pairwise R (map f l) -> In a l -> In b l -> a <> b -> R (f a) (f b) \/ R (f b) (f a).
Proof.
  intros A X R f l. induction l as [|x l IH]; intros a b HP Ha Hb Hne; [destruct Ha|].
  cbn [map pairwise] in HP. destruct HP as (HF & HP). rewrite Forall_forall in HF.
  destruct Ha as [<- | Ha]; destruct Hb as [<- | Hb].
  - contradiction.
  - left. apply HF. apply in_map. exact Hb.
  - right. apply HF. apply in_map. exact Ha.
  - exact (IH a b HP Ha Hb Hne).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variables LF_MO_SET LF_MO_OP : Z.

Definition w_regs (cx : lcx) (fp i s s6v : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms3) 21 = w64 s /\
  getr (ms_regs ms3) 22 = w64 s6v /\
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

Definition w_fresh (cx : lcx) (md mk : Z) (T3 : list (Z * Z)) (ly : alayout) (S : astate) (nb : list (Z * Z)) : Prop :=
  (forall b, In b nb -> In b (ablocks B ly S) /\ ~ In b (ablocks B (c_ly cx) (c_S cx)) /\
    (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
       zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))) /\
  (exists ly0 S0, lf_bl B cx [(md, MD_SIZE); (mk, MK_SIZE)] T3 ly0 S0 /\
     blocks_bytes S0 <= blocks_bytes (c_S cx) + LF_LIVE_HELD).

(* the cut after kernel(&cursor) (+0x1014) *)
Definition w_k_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s s6v own1 : Z) (nm : option (list byte)) (t : list byte) (kbs mbs gbs : list byte)
    (T3 nb : list (Z * Z)),
  0 <= i <= 47 /\ lf_shape fy LW_kret ms3 /\ lf_core cx ms3 /\ w_regs cx fp i s s6v ms3 /\ w_name s nm /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 1) (lf_mo LF_MO_SET LF_MO_OP i) (S (lf_wl i)) (LF_LIVE_HELD + TEXT_OF_LIVE) k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  dec_ans B ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\ tx_ans B SEGS own1 nb ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_T130) = Some own1 /\ tx_nb own1 nb /\
  (own1 <> 0 -> own1 = s6v) /\ w_fresh cx md mk T3 ly3 S3 nb /\
  nk_next kbs = 0 /\ 0 <= nk_n_chunks kbs <= 3 /\ In (nk_end_errno kbs) nl_errno_tab /\
  (nk_socket_errno kbs = 0 \/ In (nk_socket_errno kbs) nl_errno_tab) /\
  (nk_send_errno kbs = 0 \/ In (nk_send_errno kbs) nl_errno_tab).

(* the cut after model_begin's five stores and `lw s4, 0x218(s7)` (+0x1078): kbs / mbs are the lists after the
   stores (Mb.v lf_kbs_mb / lf_mbs_mb) *)
Definition w_b_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s s6v own1 : Z) (nm : option (list byte)) (t : list byte) (kbs mbs gbs : list byte)
    (T3 nb : list (Z * Z)),
  0 <= i <= 47 /\ lf_shape fy LW_mb ms3 /\ lf_core cx ms3 /\ w_regs cx fp i s s6v ms3 /\ w_name s nm /\
  getr (ms_regs ms3) 20 = w64 (nk_opened kbs) /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 1) (lf_mo LF_MO_SET LF_MO_OP i) (S (lf_wl i)) (LF_LIVE_HELD + TEXT_OF_LIVE) k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  dec_ans B ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\ tx_ans B SEGS own1 nb ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_T130) = Some own1 /\ tx_nb own1 nb /\
  (own1 <> 0 -> own1 = s6v) /\ w_fresh cx md mk T3 ly3 S3 nb /\
  nk_next kbs = 0 /\ 0 <= nk_n_chunks kbs <= 3 /\ In (nk_end_errno kbs) nl_errno_tab /\
  (nk_socket_errno kbs = 0 \/ In (nk_socket_errno kbs) nl_errno_tab) /\
  (nk_send_errno kbs = 0 \/ In (nk_send_errno kbs) nl_errno_tab) /\
  md_kstate mbs kbs = nk_kstate kbs /\ md_reqs mbs = [] /\ nk_sent kbs = [] /\ requests_are kbs mbs.

(* the cut at model_write's return (+0x1088): a0 is the model's code, the model block holds the requests the
   model owes; g_nl is the one of w_b_inv (nk_sent = [], the kernel state the model copied) *)
Definition w_m_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s s6v own1 : Z) (nm : option (list byte)) (t : list byte) (kbs mbs gbs : list byte)
    (T3 nb : list (Z * Z)),
  0 <= i <= 47 /\ lf_shape fy LW_mret ms3 /\ lf_core cx ms3 /\ w_regs cx fp i s s6v ms3 /\ w_name s nm /\
  getr (ms_regs ms3) 20 = w64 (nk_opened kbs) /\
  getr (ms_regs ms3) 10 = w64 (w_rc (write_model lf_tab nm (Some t) [] (nk_kstate kbs))) /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 1) (lf_mo LF_MO_SET LF_MO_OP i) (S (lf_wl i)) (LF_LIVE_HELD + TEXT_OF_LIVE) k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i /\
  dec_ans B ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\ tx_ans B SEGS own1 nb ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_T130) = Some own1 /\ tx_nb own1 nb /\
  (own1 <> 0 -> own1 = s6v) /\ w_fresh cx md mk T3 ly3 S3 nb /\
  nk_sent kbs = [] /\ md_reqs mbs = w_reqs (write_model lf_tab nm (Some t) [] (nk_kstate kbs)) /\
  - 2 ^ 31 <= w_rc (write_lib lf_tab nm (Some t) [] (nk_kstate kbs)) < 2 ^ 31.

(* the fresh blocks across a step that keeps the block list *)
Lemma w_fresh_sub : forall cx md mk T3 ly S ly' S' nb,
  (forall c, In c (ablocks B ly S) -> In c (ablocks B ly' S')) ->
  w_fresh cx md mk T3 ly S nb -> w_fresh cx md mk T3 ly' S' nb.
Proof.
  intros cx md mk T3 ly S ly' S' nb Hsub (H & Hbb). split; [|exact Hbb].
  intros b Hb. destruct (H b Hb) as (H1 & H2 & H3).
  split; [exact (Hsub b H1)|]. split; [exact H2 | exact H3].
Qed.

(* the answer across a state change that keeps the blocks and misses the answer's block *)
Lemma tx_ans_keep : forall own1 nb ly S ly' S' (m m' : word -> option byte) (X : Z -> Prop) s t,
  tx_ans B SEGS own1 nb ly S m s t ->
  (forall c, In c (ablocks B ly S) -> In c (ablocks B ly' S')) ->
  kagree SEGS X m m' ->
  (forall k a, In (own1, k) (ablocks B ly S) -> own1 <= a < own1 + k -> ~ X a) ->
  tx_ans B SEGS own1 nb ly' S' m' s t.
Proof.
  intros own1 nb ly S ly' S' m m' X s t [Hl | (k & Hne & Es & Hnb & Hin & Hk & Hcs)] Hsub HK HX; [left; exact Hl|].
  right. exists k. split; [exact Hne|]. split; [exact Es|]. split; [exact Hnb|]. split; [exact (Hsub _ Hin)|].
  split; [exact Hk|].
  apply (acstr_keep SEGS _ _ _ s t HK); [|exact Hcs].
  intros i Hi. apply (HX k (s + i) Hin). subst s. lia.
Qed.

Lemma tx_ans_dec : forall own1 nb ly S (m : word -> option byte) s t,
  tx_ans B SEGS own1 nb ly S m s t -> dec_ans B ly S m s t.
Proof.
  intros own1 nb ly S m s t [(_ & _ & Hl) | (k & _ & Es & _ & Hin & Hk & Hcs)]; [left; exact Hl|].
  right. exists k. subst s. split; [exact Hin|]. split; [exact Hk | exact Hcs].
Qed.

(* two different blocks of an AR state do not overlap *)
Lemma w_blk_disj : forall ly S (W : world SEGS) mem mdl b1 b2, AR_laws SEGS B ->
  AR SEGS B ly S W mem mdl -> In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
  zdisjoint (fst b1, req_size (snd b1)) (fst b2, req_size (snd b2)).
Proof.
  intros ly S W mem mdl b1 b2 LAWS HAR H1 H2 Hne.
  destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (HP & _).
  apply pairwise_app_inv in HP as (HP & _ & _).
  destruct (w_pairwise_map2 zdisjoint (fun b => (fst b, req_size (snd b))) _ b1 b2 HP H1 H2 Hne) as [D | D];
    [exact D | unfold zdisjoint in *; cbn [fst snd] in *; lia].
Qed.

(* the bytes after a string's NUL through its granule's end, from their visibility *)
Lemma w_slack_of_tail : forall (m : word -> option byte) p n, 0 <= p -> 0 <= n -> p + n + 8 <= 2 ^ 64 ->
  (forall b, p + n < b < p + n - (p + n) mod 8 + 8 -> ard SEGS m b <> None) ->
  exists slack, abytes SEGS m (p + n + 1) slack /\ (- (p + n + 1)) mod 8 <= Z.of_nat (length slack).
Proof.
  intros m p n Hp Hn Hb HT.
  pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hm.
  assert (Eq8 : (- (p + n + 1)) mod 8 = 7 - (p + n) mod 8).
  { symmetry. apply Z.mod_unique_pos with (q := - ((p + n) / 8) - 1); [lia|].
    pose proof (Z.div_mod (p + n) 8 ltac:(lia)). lia. }
  exists (abytes_of SEGS m (p + n + 1) (Z.to_nat ((- (p + n + 1)) mod 8))).
  rewrite abytes_of_length. split; [|lia].
  apply abytes_of_abytes; [lia | lia|].
  intros i Hi. specialize (HT (p + n + 1 + Z.of_nat i) ltac:(lia)). unfold ard in HT.
  destruct (mbyte SEGS m (p + n + 1 + Z.of_nat i)) as [b|]; [exists b; reflexivity | cbn in HT; congruence].
Qed.

End a.
