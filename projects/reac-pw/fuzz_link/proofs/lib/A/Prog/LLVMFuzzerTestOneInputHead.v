(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 447 of its 504 lines of code are new or changed and 347 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE LOOP HEAD of the
   walk, +0x598 .. +0x604 (0x82d6c .. 0x82dd8), against the cut interface lib/A/Prog/LLVMFuzzerTestOneInputDefs.v:

     +0x598  ld   a1, 0x120(s1)        N, the input left
     +0x59c  beqz a1, +0x13b0          N = 0: to the exit
     +0x5a0  ld   a0, 0x118(s1)        P, the cursor
     +0x5a4  srli a2, a0, 3 ; add a2, a2, s11 ; lb a2, 0(a2)      the shadow byte of P
     +0x5b0  addi a1, a1, -1 ; addi a3, a0, 1 ; sd a3, 0x118(s1) ; sd a1, 0x120(s1)    the cursor moves on
     +0x5c0  bnez a2, +0x1200          the slow check (+0x1200 andi a1, a0, 7; blt a1, a2, +0x5c4)
     +0x5c4  lbu  a0, 0(a0)            the operation byte b
     +0x5c8  ..  +0x5e4                a0 := b mod 6 (b * 0xab >> 10 is b / 6)
     +0x5e8  bltu 4, a0, +0x958        b mod 6 = 5: op_refused
     +0x5f0  slli a0, a0, 2 ; ld a1, 0xb8(s1) ; add a0, a0, a1 ; lw a0, 0(a0) ; add a0, a0, a1 ; jr a0

   lf_head : forall POST i, 0 <= i <= 47 ->
             (forall op, 0 <= op <= 5 -> FROM POST (ARM op i)) -> FROM POST EXIT -> FROM POST (LH i)

   The jump goes to lf_op_pc op: the table's five words are read from the image's bytes (hd_tw_checks, by
   computation at tfibsegs through the read-only image arodata_okP), and table + word = link_text + lf_op_pc op
   (hd_tw_target). The cursor byte is P's input byte: the shadow check's fast path needs the shadow byte 0
   (range_addressable_of_block on the input block), its slow path is refuted by the same fact.

   Section hypotheses (all discharged by the image instance, LinkImgInst.v / ACej.v):
     LAWS : AR_laws pa_segs B          the allocator's laws (the runner paj_run_x)
     TB : PcapSyms B                   link's owned statics and errno (the table words' read-only bytes)
     HSEGS : pa_segs = tfibsegs        the image's segments (the table words by computation)
     LV : LinkVals                     BASE = link_text (the jump's target)

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YFen YK0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LLVMFuzzerTestOneInputDefs LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the spill slots the head reads and writes: the jump table's address, the cursor P (atom 32) and N *)
Definition hd_spill (vN : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_JT (LS_N + 8) LS_P (LS_N + 8)
    [YP09.mkChunk LS_JT (CVal 8 (SLit LA_JT)); YP09.mkChunk LS_P (CVal 8 (SOff 32 0));
     YP09.mkChunk LS_N (CVal 8 vN)].
Definition hd_ss0 : sstate :=
  mkSS LF_lh sr_atoms [hd_spill (SLit 0)] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).

(* N >= 1: atoms 32 = P, 33 = N, 34 = the byte b at P; s11 (atom 27) is the shadow base *)
Definition hd_byte : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition hd_facts1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 1 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 255 0)] [] [].
Definition hd_ss1 : sstate := mkSS LF_lh sr_atoms [hd_spill (SOff 33 0); hd_byte] None hd_facts1.
Definition hd_Bx : sv := SOff 27 0.
Definition hd_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition hd_SH : list shent := [mkSHE 32 0 1].

Lemma hd_val_mem1 : forall segs m a b, mbyte segs m a = Some b -> val_mem segs m a 1 (bv_unsigned b).
Proof.
  intros segs m a b Hb k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* +0x5c8 .. +0x5e4 on the byte b (atom 34): b - 6 * ((b * 171) >> 10), masked to a byte, is b mod 6 *)
Definition hd_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 34 0) (SLit 171)) (SLit 10).
Definition hd_mod : sv :=
  SAlu ALU_AND (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SUB (SAlu ALU_SLL hd_q (SLit 1)) (SAlu ALU_SLL hd_q (SLit 3))))
    (SLit 255).
Definition hd_Eb (b : Z) : env := mkEnv (fun _ => Z_to_bv 64 b) (fun _ => []).
Lemma hd_mod_all : forallb (fun b => Z.eqb (bv_unsigned (sv_denot (hd_Eb b) hd_mod)) (b mod 6))
  (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_mod_val : forall E b, ew E 34 = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E hd_mod = Z_to_bv 64 (b mod 6).
Proof.
  intros E b HE Hb.
  rewrite (YFen.sv_denot_agree_on (fun n => Nat.eqb n 34) (hd_Eb b) E hd_mod); [|intros n Hn; apply Nat.eqb_eq in Hn;
    subst n; exact HE | reflexivity].
  pose proof (proj1 (forallb_forall _ _) hd_mod_all b ltac:(apply in_map_iff; exists (Z.to_nat b);
    split; [apply Z2Nat.id; lia | apply in_seq; lia])) as H. apply Z.eqb_eq in H.
  apply bv_eq. rewrite H, unsigned_lit_small by (pose proof (Z.mod_pos_bound b 6); lia). reflexivity.
Qed.

(* the jump table at .rodata 0x20f64: entry k holds the arm's address minus the table's (op_read, op_write,
   op_mark, op_unmark, op_decide for k = 0 .. 4), checked against the image's bytes below *)
Definition hd_tw (k : Z) : Z :=
  if k =? 0 then 0x61e78 else if k =? 1 then 0x62154 else if k =? 2 then 0x61f18 else if k =? 3 then 0x61f58
  else 0x61eb8.
Definition hd_jt (k : Z) : YP09.region :=
  YP09.mkRegion None (LA_JT + 4 * k) (LA_JT + 4 * k + 4) 0 0 [YP09.mkChunk (LA_JT + 4 * k) (CVal 4 (SLit (hd_tw k)))].
Lemma hd_tw_checks :
  forallb (fun k => kp_bytes_b tfibsegs Tfib_owned_static TFIB_ERRNO (LA_JT + 4 * k) (kp_le4 (hd_tw k)))
    [0; 1; 2; 3; 4] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_tw_target : forallb (fun k => LA_JT + hd_tw k =? link_text + lf_op_pc k) [0; 1; 2; 3; 4] = true.
Proof. vm_compute. reflexivity. Qed.

(* the table's address the head computes: a0 = (b mod 6) << 2, plus the table *)
Lemma hd_jt_addr : forall E k, sv_denot E hd_mod = Z_to_bv 64 k -> 0 <= k <= 4 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL hd_mod (SLit 2)) (SLit LA_JT)) = Z_to_bv 64 (LA_JT + 4 * k).
Proof.
  intros E k H Hk. cbn [sv_denot]. rewrite H.
  assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity.
Qed.

Lemma hd_kt : forall segs (X : Z -> Prop) m1 m2 m3,
  kagree segs X m1 m2 -> kagree segs X m2 m3 -> kagree segs X m1 m3.
Proof. intros segs X m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* the journal's write clause for the head's regions: the cursor's two words lie in the real frame's window;
   the byte region writes nothing *)
Ltac hd_awr E9 S1u :=
  repeat (apply awr_ok_x_cons;
    [cbn [r_base r_wlo r_whi base_val hd_spill hd_byte hd_jt]; repeat rewrite ew_ewset_other by lia;
     try rewrite E9, S1u; intros ?a ?Ha;
     first [lia | left; split; [left; unfold LS_P, LS_N, LLVMF_STK, LF_MFRAME in *; lia | lia]] |]);
  apply awr_ok_x_nil.

(* the bytes a run may write, from its frame_of: inside its regions' writable windows *)
Ltac hd_inw E9 S1u :=
  let a := fresh "a" in let r := fresh "r" in let Hi := fresh "Hi" in let Hr := fresh "Hr" in
  intros a _ (r & Hi & Hr);
  repeat (destruct Hi as [<- | Hi];
    [cbn [r_base r_wlo r_whi base_val hd_spill hd_byte hd_jt] in Hr; repeat rewrite ew_ewset_other in Hr by lia;
     rewrite ?E9, ?S1u in Hr; cbv beta; unfold LS_P, LS_N in *; lia |]);
  destruct Hi.
Ltac hd_inbv := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac hd_inch := cbn [r_chunks In]; repeat (first [left; reflexivity | right]).
Ltac hd_kag cx HFr E9 S1u KN :=
  let K0 := fresh "K0" in
  pose proof (lf_frame_kagree _ _ _ _ (fun a => lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_N + 8) HFr) as K0;
  lazymatch type of K0 with _ -> kagree ?s _ ?m1 ?m2 =>
    assert (KN : kagree s (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8) m1 m2)
      by (apply K0; hd_inw E9 S1u)
  end; clear K0.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.
(* the image instance: its symbols, its segments and its values (LinkImgInst.v: pi_link_segs, pi_link_vals) *)
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (PI := PI).

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).

(* the realigned stack pointer lies at most 0x1a0 + 31 below the entry's *)
Lemma hd_sp1 : forall cx, lf_sp1 cx + LF_MFRAME <= spZ (c_regs cx) /\ spZ (c_regs cx) - LF_MFRAME - 32 < lf_sp1 cx
  /\ spZ (c_regs cx) < 2 ^ 64.
Proof.
  intros cx. pose proof (lf_sp1_le cx) as (P1 & P2). split; [exact P1|]. split; [|exact P2].
  unfold lf_sp1, lf_sp1_of. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - LF_MFRAME) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ (c_regs cx) - LF_MFRAME) 32 ltac:(lia)) as D. lia.
Qed.

(* a spill slot from the final state's spill region *)
Lemma hd_slot_of : forall (fy : YK11.FPState) (W : world SEGS) EB ss ms cx (i : nat) r off e v,
  st_ok_pi (fx := fy) SEGS pa_val EB ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> r_base r = Some 9%nat -> bv_unsigned (ew EB 9) = lf_sp1 cx ->
  In (YP09.mkChunk off (CVal 8 e)) (r_chunks r) -> sv_denot EB e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  lf_slot cx W ms off v.
Proof.
  intros fy W EB ss ms cx i r off e v HS Hn Hb H9 Hc He Hv.
  pose proof (st_ok_pi_region_nth EB ss _ i r HS Hn) as (_ & _ & _ & Hch).
  rewrite Forall_forall in Hch. pose proof (Hch _ Hc) as Hok.
  assert (Eb : base_val EB (r_base r) = lf_sp1 cx) by (rewrite Hb; exact H9). rewrite Eb in Hok.
  pose proof (val_of_chunk_ok SEGS EB _ (lf_sp1 cx) off 8 e v Hok He ltac:(cbn; lia) ltac:(cbn; lia)) as Hvm.
  unfold lf_slot, lf_at. exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms) _ v Hvm Hv).
Qed.

(* the table word of entry k as a read-only region, from the read-only image *)
Lemma hd_jt_ok : forall E (W : world SEGS) mem k, In k [0; 1; 2; 3; 4] ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  YP09.region_ok SEGS E (rdW W mem) (hd_jt k).
Proof.
  intros E W mem k Hk HR. unfold YP09.region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks hd_jt base_val].
  assert (Kr : 0 <= k <= 4) by (cbn [In] in Hk; lia).
  assert (Tw : 0 <= hd_tw k < 2 ^ 32)
    by (unfold hd_tw; repeat match goal with |- context [?x =? ?y] => destruct (x =? y) end; lia).
  split; [unfold LA_JT; lia|]. split; [unfold LA_JT; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0 (LA_JT + 4 * k) 4 (SLit (hd_tw k)) (hd_tw k)); [reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_l.
  apply (kp_val_mem4 SEGS Tfib_owned_static TFIB_ERRNO B (w_H W) mem _ _ (ts_owned B TB) (ts_errno B TB) HR).
  rewrite HSEGS. exact (proj1 (forallb_forall _ _) hd_tw_checks k Hk).
Qed.

(* a slot as a chunk of the spill region *)
Lemma hd_chunk : forall cx (W3 : world SEGS) ms3 E off e v,
  lf_slot cx W3 ms3 off v -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (lf_sp1 cx) (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros cx W3 ms3 E off e v Hs He. unfold lf_slot, lf_at in Hs.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) Hs) as Hv.
  apply (chunk_ok_val SEGS E _ (lf_sp1 cx) off 8 e v He); [cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ v Hs).
Qed.

Lemma lf_head : forall POST i, 0 <= i <= 47 ->
  (forall op, 0 <= op <= 5 -> FROM POST (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP op i)) ->
  FROM POST (lf_exit_inv B MT MS la_nul LF_MO_SET LF_MO_OP) ->
  FROM POST (lf_lh_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i Hi HARM HEX cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HT.
  pose proof HT as (md & mk & P & N & kbs & mbs & gbs & T3 & _ & Hsh & Hcore & Hlr & Hsv & Hhd & Hfs & Hsl & Hcur
    & Hjbk & Hblk & Hdat & Hop).
  pose proof HB as (_ & _ & HGX & _).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hcur as (HcP & HcN & (q & Hq & EP & EN)).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SJT & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & _ & Hshi & Hs47 & Hpres & HAR).
  pose proof (hd_sp1 cx) as (P1 & P2 & P3).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcP) as RP.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcN) as RN.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (S1r : alloc_ceiling <= lf_sp1 cx) by (unfold LLVMF_STK, LF_MFRAME in *; lia).
  assert (S1u : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx).
  { rewrite C9. unfold w64. apply unsigned_lit_small. unfold LF_MFRAME in *. lia. }
  assert (S1f : forall E, ew E 9 = getr (ms_regs ms3) 9 -> afact_ok E 9 (mkAF (2 ^ 46) (2 ^ 47) 5)).
  { intros E HE. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE, S1u.
    split; [unfold LF_MFRAME in *; lia|]. split; [|lia].
    unfold lf_sp1, lf_sp1_of. rewrite Z.mul_comm. change (2 ^ 5) with 32. apply Z_mod_mult. }
  (* every byte the cut's memory clauses read misses the cursor's 16 bytes, the only bytes the head writes *)
  assert (XN : forall a, lf_cut_fp MS la_nul cx fp md mk T3 a ->
            ~ (lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)).
  { intros a Ha. assert (HFR : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
    destruct (lf_cut_fp_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp k2
      ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ ms3 md3 md mk T3 _ a HB HJ HFR Hjbk Hblk Ha) as [Hp | [Hp | Hp]];
      rewrite Z.mod_small by (unfold LF_MFRAME in *; lia); unfold LS_P, LS_N, LF_MFRAME in *; lia. }
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & MO1 & MO2 & MO3 & _ & _ & ML & _).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  rewrite (lf_shape_eta fy LF_lh ms3 Hsh).
  destruct (Z.eq_dec N 0) as [HN0 | HN0].
  - (* N = 0: beqz goes to the exit *)
    set (E := Eimg (Ereg (ms_regs ms3) [w64 P])).
    assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
    assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
    assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E hd_ss0
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_lh)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor].
        unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks hd_spill base_val]. rewrite E9, S1u.
        unfold LS_JT, LS_N, LS_P, LF_MFRAME in *.
        split; [lia|]. split; [lia|]. split.
        + intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
        + constructor; [|constructor; [|constructor; [|constructor]]].
          * apply (hd_chunk cx W3 ms3 E LS_JT (SLit LA_JT) LA_JT SJT). reflexivity.
          * apply (hd_chunk cx W3 ms3 E LS_P (SOff 32 0) P HcP). rewrite (lf_sv_off E 32 P 0 E32) by lia.
            rewrite Z.add_0_r. reflexivity.
          * apply (hd_chunk cx W3 ms3 E LS_N (SLit 0) N HcN). rewrite HN0. reflexivity.
      - cbn. tauto.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [exact (S1f E E9) | exact I]. }
    pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
    assert (SHOK : sh_ok pa_segs (SLit 0) [] E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_lh)) (ms_mem ms3) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LF_exit.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      cbn [r_base r_wlo r_whi hd_spill base_val]. rewrite E9, S1u. intros a Ha. left. split; [|lia].
      left. unfold LS_P, LS_N, LLVMF_STK, LF_MFRAME in *. lia. }
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (lf_frame_kagree _ _ _ _ (fun a => lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_N + 8) HFrB) as KB.
    assert (KB' : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
                   (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))).
    { apply KB. intros a _ (r & Hin & Hr). destruct Hin as [<- | []].
      cbn [r_base r_wlo r_whi hd_spill base_val] in Hr. rewrite E9, S1u in Hr. lia. }
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E).
    { split; [intros n Hn; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia;
              reflexivity | reflexivity]. }
    assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
    destruct (lf_cut_keep B MT MS la_nul _ cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
      W3 msB md4 KB' (wcarry_on_grows _ _ _ HGB) Fd Fs XN Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
      as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
    pose proof Hsl' as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17
      & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29).
    pose proof Hblk' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17).
    apply (HEX cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJ Hfr).
    exists md, mk, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [repeat split; (rewrite KR by (vm_compute; reflexivity)); assumption|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L19|].
    split; [rewrite KR by (vm_compute; reflexivity); exact L22|].
    split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|].
    split; [exact S15|]. split; [exact S5|]. split; [exact S6|].
    split.
    { refine (lf_jbk_mono B MT MS la_nul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ML _ _ _ _ Hjbk');
        unfold lf_ev, lf_mo, lf_wl, LF_EV_SET, LF_EV_OP, LF_WILD_OP; [lia | nia | | lia].
      apply Nat.mul_le_mono_l. apply Z2Nat.inj_le; lia. }
    do 6 (split; [assumption|]).
    split; [intros Heq; subst mk; unfold apart, MD_SIZE, MK_SIZE in B11; lia|].
    split; [exact B14 | exact B15].
  - (* N >= 1: the byte at P is read and dispatched *)
    assert (HN1 : 1 <= N) by lia.
    assert (Hq' : 0 <= q < c_n cx) by lia.
    pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J13 & J14 & J15).
    destruct J14 as (Pl0 & Pl1 & Pl2).
    assert (Hqn : (Z.to_nat q < length (c_pl cx))%nat) by (unfold c_n in Hq'; lia).
    pose proof (Pl2 (Z.to_nat q) Hqn) as Hb. rewrite Z2Nat.id in Hb by lia. rewrite <- EP in Hb.
    destruct (nth_error (c_pl cx) (Z.to_nat q)) as [bb|] eqn:Ebb; [|apply nth_error_None in Ebb; lia].
    pose proof (bv_unsigned_in_range _ bb) as Rb. change (bv_modulus 8) with 256 in Rb.
    assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (apply (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp
                   ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ); lia).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Pb0 & Pbc & Pbapp & _).
    assert (Rn : req_size (c_n cx) = c_n cx)
      by (unfold req_size; destruct (c_n cx =? 0) eqn:En; [apply Z.eqb_eq in En; lia | reflexivity]).
    rewrite Rn in Pbc, Pbapp.
    set (E := Eimg (Ereg (ms_regs ms3) [w64 P; w64 N; Z_to_bv 64 (bv_unsigned bb)])).
    assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
    assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
    assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
      by (transitivity (getr (ms_regs ms3) 27); [apply ew_Eimg_Ereg_nat; reflexivity | exact L27]).
    assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E33 : ew E 33 = Z_to_bv 64 N) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned bb))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E hd_ss1
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_lh)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor; [|constructor]].
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks hd_spill base_val]. rewrite E9, S1u.
          unfold LS_JT, LS_N, LS_P, LF_MFRAME in *.
          split; [lia|]. split; [lia|]. split.
          * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
          * constructor; [|constructor; [|constructor; [|constructor]]].
            -- apply (hd_chunk cx W3 ms3 E LS_JT (SLit LA_JT) LA_JT SJT). reflexivity.
            -- apply (hd_chunk cx W3 ms3 E LS_P (SOff 32 0) P HcP). rewrite (lf_sv_off E 32 P 0 E32) by lia.
               rewrite Z.add_0_r. reflexivity.
            -- apply (hd_chunk cx W3 ms3 E LS_N (SOff 33 0) N HcN). rewrite (lf_sv_off E 33 N 0 E33) by lia.
               rewrite Z.add_0_r. reflexivity.
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks hd_byte base_val].
          rewrite E32, unsigned_lit_small by lia.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          constructor; [|constructor].
          apply (chunk_ok_val SEGS E _ P 0 1 (SOff 34 0) (bv_unsigned bb)); [| cbn; lia | cbn; lia |].
          * rewrite (lf_sv_off E 34 (bv_unsigned bb) 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
          * rewrite Z.add_0_r. exact (hd_val_mem1 _ _ _ _ Hb).
      - split; [split; [|exact I] | split; exact I].
        unfold extent_disjoint. cbn [r_base r_lo r_hi hd_spill hd_byte base_val].
        rewrite E9, S1u, E32, unsigned_lit_small by lia. right. unfold LS_JT. lia.
      - split; [|split; exact I]. cbn [hd_facts1 f_atoms atoms_ok].
        split; [exact (S1f E E9)|].
        unfold afact_ok; cbn [af_lo af_hi af_al2].
        rewrite E27, E32, E33, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r. pose proof alloc_ceiling_lt as CL.
        repeat split; try lia; try exact I. }
    pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
    pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
    pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
    assert (RA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF P 1)
      by (eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia]).
    assert (SHOK : sh_ok pa_segs hd_Bx hd_SH E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_lh)) (ms_mem ms3) (seg_rom SEGS))))).
    { unfold sh_ok, hd_SH. constructor; [|constructor]. unfold shent_ok, app_apart, hd_Bx.
      cbn [she_m she_lo she_hi ms_mem mkst].
      rewrite (U_atom E 32 P E32) by lia. rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
      split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
      intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
    (* the arm's cut, from any state the head's runs end in *)
    assert (ARM : forall (msB : machine_state) md4 op,
      0 <= op <= 5 -> bv_unsigned bb mod 6 = op -> lf_shape fy (lf_op_pc op) msB ->
      (forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
         getr (ms_regs msB) r = getr (ms_regs ms3) r) ->
      kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
        (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
      mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
      m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
      lf_slot cx W3 msB LS_P (P + 1) -> lf_slot cx W3 msB LS_N (N - 1) ->
      lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP op i cx fy fp k2 ly3 S3 W3 msB md4).
    { intros msB md4 op Hop5 Hb6 Hsh' KR KBm GBm Fd Fs CP CN.
      destruct (lf_cut_keep B MT MS la_nul _ cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
        W3 msB md4 KBm (wcarry_on_grows _ _ _ GBm) Fd Fs XN Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
        as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
      exists md, mk, P, N, kbs, mbs, gbs, T3, bb.
      split; [lia|]. split; [exact Hop5|]. split; [exact Hsh'|].
      split; [unfold lf_core; rewrite !KR by hd_inbv; repeat split; assumption|].
      split; [unfold lf_lregs; rewrite !KR by hd_inbv; repeat split; assumption|].
      split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|].
      split; [exact HN1|].
      split.
      { split; [lia|]. split; [cbn [length]; lia|]. intros k Hk. cbn [length] in Hk. destruct k; [|lia].
        cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
        rewrite (KBm P) by (rewrite Z.mod_small by lia; unfold LS_P, LS_N, LF_MFRAME in *; lia). exact Hb. }
      split; [exact Hb6|].
      split; [split; [exact CP|]; split; [exact CN|]; exists (q + 1); lia|].
      split; [exists q; lia|].
      split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdat' | exact Hop]. }
    pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hin) as Hoff.
    rewrite Rn in Hoff. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
    paj_run_tok RUN HS HJ SHOK hd_span; [hd_awr E9 S1u|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    hd_kag cx HFrA E9 S1u KA.
    assert (M6 : 0 <= bv_unsigned bb mod 6 < 6) by (apply Z.mod_pos_bound; lia).
    lazymatch type of HS with st_ok_pi _ _ ?EA _ _ =>
      assert (MV : sv_denot EA hd_mod = Z_to_bv 64 (bv_unsigned bb mod 6))
        by (apply (hd_mod_val EA (bv_unsigned bb)); [repeat rewrite ew_ewset_other by lia; exact E34 | exact Rb])
    end.
    unfold hd_mod, hd_q in MV.
    psrr_branch_tok RUN BR HS SHOK hd_span.
    + (* +0x5ec taken: b mod 6 = 5, op_refused *)
      rewrite MV in Hc. cbn [sv_denot] in Hc. rewrite YK0f.branch_ltu_lit_l, unsigned_lit_small in Hc by lia.
      apply Z.ltb_lt in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK hd_span LF_op5; [hd_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      hd_kag cx HFrB E9 S1u KB.
      lazymatch type of HS with st_ok_pi _ _ ?EB ?ssB _ =>
        assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) EB)
          by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                      rewrite !ew_Ereg_lt by lia; reflexivity | reflexivity]);
        assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
        assert (E32B : ew EB 32 = Z_to_bv 64 P) by (repeat rewrite ew_ewset_other by lia; exact E32);
        assert (E33B : ew EB 33 = Z_to_bv 64 N) by (repeat rewrite ew_ewset_other by lia; exact E33);
        assert (KR : forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
                                            26%bv; 27%bv] -> getr (ms_regs msB) r = getr (ms_regs ms3) r)
          by (intros r Hr; apply (lf_reg_atom fy W3 _ ssB msB _ r HS HA);
              repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr);
        assert (CP : lf_slot cx W3 msB LS_P (P + 1))
          by (apply (hd_slot_of fy W3 EB ssB msB cx 0%nat _ LS_P (SOff 32 1) (P + 1) HS eq_refl eq_refl S9B);
              [hd_inch | exact (lf_sv_off EB 32 P 1 E32B ltac:(lia) ltac:(lia)) | lia]);
        assert (CN : lf_slot cx W3 msB LS_N (N - 1))
          by (apply (hd_slot_of fy W3 EB ssB msB cx 0%nat _ LS_N (SOff 33 (-1)) (N - 1) HS eq_refl eq_refl S9B);
              [hd_inch | exact (lf_sv_off EB 33 N (-1) E33B ltac:(lia) ltac:(lia)) | lia])
      end.
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
      apply (HARM 5 ltac:(lia) cx fy fp k2 ly3 S3 W3 msB md4 HB Hfx HJ Hfr).
      apply (ARM msB md4 5); [lia | lia | | exact KR | exact (hd_kt _ _ _ _ _ KA KB) | intros x Hx; apply HGB, HGA, Hx
        | subst md4; rewrite !lf_wvb_fds; reflexivity | subst md4; rewrite !lf_wvb_fs; reflexivity | exact CP | exact CN].
      lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ => exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl) end.
    + (* +0x5ec not taken: op = b mod 6 in 0 .. 4, the jump table *)
      rewrite MV in Hc. cbn [sv_denot] in Hc. rewrite YK0f.branch_ltu_lit_l, unsigned_lit_small in Hc by lia.
      apply Z.ltb_ge in Hc.
      paj_run_tok RUN HS HJ SHOK hd_span; [hd_awr E9 S1u|].
      rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
      hd_kag cx HFrC E9 S1u KC.
      pose proof (hd_kt _ _ _ _ _ KA KC) as KAC.
      assert (HRC : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) (ms_mem msC))).
      { change (arodata_okP SEGS PCAP_RLO PCAP_RHI B (ard SEGS (rdW W3 (ms_mem msC)))).
        apply (arodata_keep SEGS _ (rdW W3 (ms_mem ms3)) _ PCAP_RLO PCAP_RHI B KAC); [|exact J13].
        intros a Ha. pose proof (in_roP_low a Ha) as La. unfold kLowMemEnd in La.
        rewrite Z.mod_small by lia. unfold LS_P, LS_N, LF_MFRAME in *. lia. }
      remember (bv_unsigned bb mod 6) as op eqn:Eop.
      assert (Hop4 : op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?EC ?ssC _ =>
        assert (MVC : sv_denot EC hd_mod = Z_to_bv 64 op)
          by (rewrite Eop; apply (hd_mod_val EC (bv_unsigned bb)); [repeat rewrite ew_ewset_other by lia; exact E34 | exact Rb]);
        assert (A0 : getr (ms_regs msC) 10%bv = sv_denot EC (SLit (LA_JT + 4 * op)))
          by (rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msC 10%bv HS);
              replace (sr_get (ss_regs ssC) 10%bv) with (SAlu ALU_ADD (SAlu ALU_SLL hd_mod (SLit 2)) (SLit LA_JT))
                by (vm_compute; reflexivity);
              rewrite (hd_jt_addr EC op MVC ltac:(lia)); reflexivity);
        pose proof (st_ok_pi_set_reg EC ssC _ 10%bv (SLit (LA_JT + 4 * op)) HS
          ltac:(intros Habs; apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs) A0) as HS1;
        assert (JOK : forall k, In k [0; 1; 2; 3; 4] -> YP09.region_ok SEGS EC (rdW W3 (ms_mem msC)) (hd_jt k))
          by (intros k Hk; exact (hd_jt_ok EC W3 (ms_mem msC) k Hk HRC))
      end.
      clear HS.
      destruct Hop4 as [Eo | [Eo | [Eo | [Eo | Eo]]]]; rewrite Eo in *; clear Eo.
      (* the table word of entry op, as a read-only region apart from the spill slots and the input byte *)
      all: lazymatch type of Eop with ?k = _ =>
        lazymatch type of HS1 with st_ok_pi _ _ ?EC ?ss1 _ =>
          pose proof (st_ok_pi_add_region EC ss1 _ (hd_jt k) HS1 eq_refl (JOK k ltac:(hd_inbv))) as HS2
        end end.
      all: lazymatch type of HS2 with ?d -> _ => assert (HD : d) end;
        [cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val hd_jt];
         repeat rewrite ew_ewset_other by lia; rewrite E9, S1u, E32, unsigned_lit_small by lia;
         unfold LS_JT, LS_N, LA_JT in *; repeat split; lia
        |specialize (HS2 HD); clear HD HS1].
      all: paj_run_to_tok RUNTO HS2 HJ SHOK hd_span (LF_lh + 0x6c); [hd_awr E9 S1u|].
      all: rename ms into msD, HF into HFD, HFr into HFrD, HG into HGD.
      all: hd_kag cx HFrD E9 S1u KD.
      (* jr a0: the table's target is the arm's entry *)
      all: lazymatch type of Eop with ?k = _ =>
        lazymatch type of HS2 with st_ok_pi _ _ ?ED ?ssD _ =>
          lazymatch goal with HE : img_env _ _ ED |- _ =>
            assert (A1 : getr (ms_regs msD) 10%bv = sv_denot ED (SOff A_TEXT (lf_op_pc k)))
              by (rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msD 10%bv HS2);
                  rewrite (codeptr_val ED (lf_op_pc k) HE), (lv_text LV); apply bv_eq; vm_compute; reflexivity);
            pose proof (st_ok_pi_set_reg ED ssD _ 10%bv (SOff A_TEXT (lf_op_pc k)) HS2
              ltac:(intros Habs; apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs) A1) as HS3
          end end end.
      all: clear HS2.
      all: lazymatch type of Eop with ?k = _ => paj_run_to_tok RUNTO HS3 HJ SHOK hd_span (lf_op_pc k) end;
        [hd_awr E9 S1u|].
      all: rename ms into msE, HF into HFE, HFr into HFrE, HG into HGE.
      all: hd_kag cx HFrE E9 S1u KE.
      all: lazymatch type of HS3 with st_ok_pi _ _ ?EB ?ssB _ =>
        assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) EB)
          by (split; [intros n Hn; repeat rewrite ew_ewset_other by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                      rewrite !ew_Ereg_lt by lia; reflexivity | reflexivity]);
        assert (S9B : bv_unsigned (ew EB 9) = lf_sp1 cx) by (repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u);
        assert (E32B : ew EB 32 = Z_to_bv 64 P) by (repeat rewrite ew_ewset_other by lia; exact E32);
        assert (E33B : ew EB 33 = Z_to_bv 64 N) by (repeat rewrite ew_ewset_other by lia; exact E33);
        assert (KR : forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
                                            26%bv; 27%bv] -> getr (ms_regs msE) r = getr (ms_regs ms3) r)
          by (intros r Hr; apply (lf_reg_atom fy W3 _ ssB msE _ r HS3 HA);
              repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr);
        assert (CP : lf_slot cx W3 msE LS_P (P + 1))
          by (apply (hd_slot_of fy W3 EB ssB msE cx 1%nat _ LS_P (SOff 32 1) (P + 1) HS3 eq_refl eq_refl S9B);
              [hd_inch | exact (lf_sv_off EB 32 P 1 E32B ltac:(lia) ltac:(lia)) | lia]);
        assert (CN : lf_slot cx W3 msE LS_N (N - 1))
          by (apply (hd_slot_of fy W3 EB ssB msE cx 1%nat _ LS_N (SOff 33 (-1)) (N - 1) HS3 eq_refl eq_refl S9B);
              [hd_inch | exact (lf_sv_off EB 33 N (-1) E33B ltac:(lia) ltac:(lia)) | lia]);
        assert (SHE : lf_shape fy (ss_pc ssB) msE) by exact (lf_shape_of_st_ok fy W3 _ ssB msE HS3 eq_refl)
      end.
      all: lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
      all: lazymatch type of Eop with ?k = _ =>
        apply (HARM k ltac:(lia) cx fy fp k2 ly3 S3 W3 msE md4 HB Hfx HJ Hfr);
        apply (ARM msE md4 k); [lia | lia | exact SHE | exact KR
          | exact (hd_kt _ _ _ _ _ (hd_kt _ _ _ _ _ (hd_kt _ _ _ _ _ KA KC) KD) KE)
          | intros x Hx; apply HGE, HGD, HGC, HGA, Hx
          | subst md4; rewrite !lf_wvb_fds; reflexivity | subst md4; rewrite !lf_wvb_fs; reflexivity
          | exact CP | exact CN]
      end.
Qed.
End a.
