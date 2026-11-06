(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v; 159 of its 211 lines of code are new or changed and 528 lines of the source are left out. *)
(* The record loop's test of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan, 0x81400 / 0x81404): its two
   exits. Statements: seg_loop and seg_rec_exit of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v. The induction over
   the record index that composes them with seg_D1 .. seg_D6 is the LOOP step of pb_LLVMFuzzerTestOneInput in
   that file (SRr_loop on m_nrec g - i); this file proves only the two loop-test segments it consumes.

   The loop is rotated. The body starts at 0x80b20 and its test is at the bottom:
     0x813f4 addiw s4,s5,1      x20 := i + 1
     0x813f8 ld a0,112(s1)      x10 := nrec
     0x81400 bne s4,a0,80b20    on to the next record
     0x81404 j 8157c            out of the loop
   inv_D6_end is the state at 0x81400. Neither 0x81400 nor 0x81404 reads or writes memory or a register, so the
   state after them is the state before them at another pc; the only change the machine makes is the lazy-page
   bookkeeping of the model (with_vm_backing), which no boundary fact depends on except through m_fds / m_fs.
   The branch is decided by x20 = i + 1 and x10 = nrec (0 <= nrec < 65), against S i < m_nrec g (seg_loop) or
   S i = m_nrec g (seg_rec_exit).

   seg_loop moves the state to inv_rec (S i) at 0x80b20, seg_rec_exit to inv_exit at 0x8157c. Every fact of either
   boundary is a fact of inv_D6_end or of rec_live (S i) (inv_exit's mf_hw and mf_id3 are two of mf_fixed's slots).
   m_nrec g is the number of records in the plain model (SlotModel.nrecn, input[0] mod 65). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The registers x1 .. x31. *)
Definition LOOP_REGS : list (bv 5) := map (fun n => Z_to_bv 5 (Z.of_nat n)) (seq 1 31).
Lemma in_loop_regs : forall r : bv 5, bv_eqb r 0 = false -> In r LOOP_REGS.
Proof.
intros r Hr. unfold LOOP_REGS. apply in_map_iff. exists (Z.to_nat (bv_unsigned r)).
pose proof (u5_range r) as Hb.
assert (Hn0 : bv_unsigned r <> 0).
{ intros E. unfold bv_eqb in Hr. rewrite E in Hr. vm_compute in Hr. discriminate Hr. }
split.
- apply bv_eq. rewrite Z_to_bv_unsigned, Z2Nat.id by lia. apply bv_wrap_small. apply bv_unsigned_in_range.
- apply in_seq. lia.
Qed.

(* A run of the listing's engine from ss that neither reads nor writes memory and keeps every register: it
   stops (PRS_running) at slot stop with x1 .. x31 the entry atoms. Checked by computation. *)
Definition loop_neutral (n : N) (stop : Z) (ss : sstate) : bool :=
match sym_run_toN_pi ident_tpi n stop ss with
| (ss', PRS_running) =>
(ss_pc ss' =? stop) && match ss_resv ss' with None => true | Some _ => false end &&
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) LOOP_REGS
| _ => false
end.

(* The symbolic state at the loop test: every register its own atom, no region, no fact. *)
Definition ss_test : sstate := mkSS 0xcf4 sr_atoms [] None (mkFacts [] [] []).

Lemma bne_w64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_NE (w64 a) (w64 b) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_eqb, w64. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).

Lemma sv_reg : forall (regs : bvmap 5 word) (n : nat) (r : bv 5) v, (n <? 32)%nat = true -> Z.of_nat n = bv_unsigned r ->
getr regs r = w64 v -> sv_denot (Eimg (Ereg regs [])) (SOff n 0) = w64 v.
Proof.
intros regs n r v Hn Hr Hg. apply Nat.ltb_lt in Hn. cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs [] n r Hr), Hg, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned.
Qed.

(* The entry state of the test's engine run, from the registers and memory of a boundary at 0x81400. *)
Lemma ss_test_ok : forall (W : world SEGS) regs mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_test
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xcf4)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_test. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

Section c.
(* The Section of the contract and of the boundary layer, in the same order (LLVMFuzzerTestOneInput_inv.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* The only hypothesis of the loop test's two lemmas: the allocator's laws (for the journal through the model's
   lazy-page bookkeeping, YCbq ajournal_materialize, and for the engine's run). *)
Hypothesis LAWS : AR_laws SEGS B.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

(* A boundary moved to another pc by a run that keeps memory and every register (x0 aside): the journal goes
   through the model's lazy-page bookkeeping (ajournal_materialize), every other fact is the same. *)
Lemma acut_moved : forall g pos mf k pc'
(P' : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
(W2 : world SEGS) ly2 S2 regs2 mem2 md2 regs' X,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k ->
frames S2 = [(4, pos)] -> 0 <= k <= EV_LLVMF ->
mo_le MT (e_S g) S2 (k * (mo_malloc MT 256 + mo_free MT)) ->
mo_ok MT S2 ((EV_LLVMF - k) * (mo_malloc MT 256 + mo_free MT)) ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
(forall r, bv_eqb r 0 = false -> getr regs' r = getr regs2 r) ->
P' ly2 S2 W2 regs' mem2 (with_vm_backing (m_vm_lazy md2) X md2) ->
ACUT g pos mf k pc' P' W2 (cfg_at SEGS pc' regs' mem2 (with_vm_backing (m_vm_lazy md2) X md2)).
Proof.
intros g pos mf k pc' P' W2 ly2 S2 regs2 mem2 md2 regs' X HJ Hfr Hk Hmo Hmok HEC HRG HP.
exists ly2, S2, regs', mem2, (with_vm_backing (m_vm_lazy md2) X md2).
split; [reflexivity|].
split; [exact (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ)|].
split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact Hmok|].
split; [|exact HP].
clear - HEC HRG. unfold ecommon in HEC |- *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end;
try (repeat (rewrite HRG by reflexivity); assumption).
Qed.

(* The engine's run from a boundary's registers and memory to slot stop, when loop_neutral holds of it. *)
Lemma loop_run : forall (W : world SEGS) regs mem md ss k0 (n : N) (stop : Z) (Q : world SEGS -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
ss_pc ss = k0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + k0)) mem (seg_rom SEGS))) ->
ss_mem ss = [] ->
loop_neutral n stop ss = true ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall regs' X, (forall r, bv_eqb r 0 = false -> getr regs' r = getr regs r) ->
Q W (cfg_at SEGS (BASE + stop) regs' mem (with_vm_backing (m_vm_lazy md) X md))) ->
SRr SEGS W (cfg_at SEGS (BASE + k0) regs mem md) Q.
Proof.
intros W regs mem md ss k0 n stop Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Hk0 HS Hm Hok HJ HQ.
subst k0. unfold loop_neutral in Hok.
destruct (sym_run_toN_pi ident_tpi n stop ss) as [ss' st] eqn:Hrun.
destruct st; try discriminate Hok.
apply andb_prop in Hok as [Hok Hregs]. apply andb_prop in Hok as [Hpc Hrv].
apply Z.eqb_eq in Hpc.
assert (Hrv' : ss_resv ss' = None) by (destruct (ss_resv ss'); [discriminate Hrv | reflexivity]).
unfold cfg_at. change (w64 (BASE + ss_pc ss)) with (Z_to_bv 64 (BASE + ss_pc ss)).
eapply (@SRr_run_to_pi_AJ _ _ _ ident_listing PL_ident PI B LAWS W n stop (Eimg (Ereg regs [])) ss ss'
PRS_running _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k Q (Eimg_env _) HS Hrun I HJ).
- rewrite Hm. apply awr_ok_nil.
- intros ms' mat' HS' _ HF _ _.
pose proof (st_ok_pi_restrict_mkst (w_H W) _ ss' ms' HS' Hrv') as Hshape.
assert (Hmem : ms_mem ms' = mem).
{ apply functional_extensionality. intros x.
exact (HF x ltac:(rewrite Hm; intros (r & Hr & _); exact Hr)). }
assert (HRG : forall r, bv_eqb r 0 = false -> getr (ms_regs ms') r = getr regs r).
{ intros r Hr.
refine (regs_kept_of_st_ok_pi _ ss' (restrict (w_H W) ms') regs [] LOOP_REGS HS' _ Hregs r (in_loop_regs r Hr)).
split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; clear - Hn0; lia | reflexivity]. }
rewrite Hshape, Hpc, Hmem. apply SRr_ret. exact (HQ (ms_regs ms') mat' HRG).
Qed.

(* nrec is input[0] mod 65 (SlotModel.v:10), and m_nrec g its natural number. *)
Lemma nrec_range : forall g : ectx, 0 <= SlotModel.nrec (e_pl g) < 65.
Proof. intros g. unfold SlotModel.nrec. apply Z.mod_pos_bound. lia. Qed.
Lemma m_nrec_Z : forall g : ectx, Z.of_nat (m_nrec g) = SlotModel.nrec (e_pl g).
Proof. intros g. unfold m_nrec, SlotModel.nrecn. apply Z2Nat.id. apply (nrec_range g). Qed.

(* 0x81400 -> 0x80b20: the back edge, taken while S i < m_nrec g. *)
Theorem seg_loop_holds : seg_loop B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_loop. intros g pos mf i W2 c2 HD Hlt.
unfold inv_D6_end, acut in HD.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo & Hmok & HEC & HP).
pose proof HP as (Hi & R20 & R10 & _).
pose proof (nrec_range g) as Hnr. pose proof (m_nrec_Z g) as Hnz.
assert (Hlt' : Z.of_nat (S i) < SlotModel.nrec (e_pl g)) by (rewrite <- Hnz; clear - Hlt; lia).
pose proof (ss_test_ok W2 regs2 mem2) as HS.
unfold cfg_at.
eapply (paj_branch W2 (Eimg (Ereg regs2 [])) ss_test _ md2 _ BC_NE (SOff 20 0) (SOff 10 0) HS).
- intros _ HSc.
eapply (loop_run W2 regs2 mem2 md2 (add_cond ss_test (mkAC BC_NE (SOff 20 0) (SOff 10 0))) 0xcf4 2 0x414);
[reflexivity | exact HSc | reflexivity | vm_compute; reflexivity | exact HJ |].
intros regs' X HRG.
unfold inv_rec. replace (4 * Z.of_nat (S i)) with (4 * Z.of_nat i + 4) by (rewrite Nat2Z.inj_succ; ring).
apply (acut_moved g pos mf _ _ _ W2 ly2 S2 regs2 mem2 md2 regs' X HJ Hfr Hk Hmo Hmok HEC HRG).
cbv beta. unfold rec_live, cur_at in HP |- *.
clear - HP Hlt HRG.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end;
try (repeat (rewrite HRG by reflexivity); assumption).
- intros Hbt _. exfalso.
rewrite (sv_reg regs2 20 20%bv _ eq_refl eq_refl R20), (sv_reg regs2 10 10%bv _ eq_refl eq_refl R10) in Hbt.
rewrite bne_w64 in Hbt by (clear - Hlt' Hnr; lia).
apply negb_false_iff, Z.eqb_eq in Hbt. clear - Hbt Hlt'. lia.
Qed.

(* 0x81400 -> 0x81404 -> 0x8157c: the exit, when S i = m_nrec g. *)
Theorem seg_rec_exit_holds : seg_rec_exit B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_rec_exit. intros g pos mf i W2 c2 HD Heq.
unfold inv_D6_end, acut in HD.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo & Hmok & HEC & HP).
pose proof HP as (Hi & R20 & R10 & _).
pose proof (nrec_range g) as Hnr. pose proof (m_nrec_Z g) as Hnz.
assert (Heq' : Z.of_nat (S i) = SlotModel.nrec (e_pl g)) by (rewrite <- Hnz, Heq; reflexivity).
pose proof (ss_test_ok W2 regs2 mem2) as HS.
unfold cfg_at.
eapply (paj_branch W2 (Eimg (Ereg regs2 [])) ss_test _ md2 _ BC_NE (SOff 20 0) (SOff 10 0) HS).
- intros Hbt _. exfalso.
rewrite (sv_reg regs2 20 20%bv _ eq_refl eq_refl R20), (sv_reg regs2 10 10%bv _ eq_refl eq_refl R10) in Hbt.
rewrite bne_w64 in Hbt by (clear - Heq' Hnr; lia).
apply negb_true_iff, Z.eqb_neq in Hbt. exact (Hbt Heq').
- intros _ HSc.
eapply (loop_run W2 regs2 mem2 md2 (add_cond ss_test (mkAC (neg_bc BC_NE) (SOff 20 0) (SOff 10 0))) 0xcf4 3 0xe70);
[reflexivity | exact HSc | reflexivity | vm_compute; reflexivity | exact HJ |].
intros regs' X HRG.
unfold inv_exit. rewrite <- Heq. replace (4 * Z.of_nat (S i)) with (4 * Z.of_nat i + 4) by (rewrite Nat2Z.inj_succ; ring).
apply (acut_moved g pos mf _ _ _ W2 ly2 S2 regs2 mem2 md2 regs' X HJ Hfr Hk Hmo Hmok HEC HRG).
cbv beta. unfold rec_live, cur_at, mf_fixed, mf_hw, mf_id3 in HP |- *.
clear - HP HRG.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end;
try (repeat (rewrite HRG by reflexivity); assumption).
Qed.

End c.
End b.
End a.
