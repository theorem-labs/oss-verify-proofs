(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1j.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_litS : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word src0segs p = Some w.
Proof.
intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply src0tbl_ok. exact H.
Qed.
End c.
Local Ltac ftac := apply fetch_litS; vm_compute; reflexivity.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma FS_51c : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x51c)) = Some (0x00584333%bv : bv 32). Proof. ftac. Qed.
Lemma DS_51c : decode_any (0x00584333%bv : bv 32) = Some (Op ALU_XOR 6 16 5, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_520 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x520)) = Some (0x00f282bb%bv : bv 32). Proof. ftac. Qed.
Lemma DS_520 : decode_any (0x00f282bb%bv : bv 32) = Some (Op32 ALU_ADD 5 5 15, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_524 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x524)) = Some (0x0017071b%bv : bv 32). Proof. ftac. Qed.
Lemma DS_524 : decode_any (0x0017071b%bv : bv 32) = Some (OpImm32 14 14 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_528 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x528)) = Some (0x00f8083b%bv : bv 32). Proof. ftac. Qed.
Lemma DS_528 : decode_any (0x00f8083b%bv : bv 32) = Some (Op32 ALU_ADD 16 16 15, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_52c : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x52c)) = Some (0xff1348e3%bv : bv 32). Proof. ftac. Qed.
Lemma DS_52c : decode_any (0xff1348e3%bv : bv 32) = Some (Branch BC_LT 6 17 8176, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_530 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x530)) = Some (0x01f6f693%bv : bv 32). Proof. ftac. Qed.
Lemma DS_530 : decode_any (0x01f6f693%bv : bv 32) = Some (OpImm ALU_AND 13 13 31, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_534 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x534)) = Some (0x00168693%bv : bv 32). Proof. ftac. Qed.
Lemma DS_534 : decode_any (0x00168693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_538 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x538)) = Some (0x00d76463%bv : bv 32). Proof. ftac. Qed.
Lemma DS_538 : decode_any (0x00d76463%bv : bv 32) = Some (Branch BC_LTU 14 13 8, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_53c : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x53c)) = Some (0x00068713%bv : bv 32). Proof. ftac. Qed.
Lemma DS_53c : decode_any (0x00068713%bv : bv 32) = Some (OpImm ALU_ADD 14 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_540 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x540)) = Some (0xfff70713%bv : bv 32). Proof. ftac. Qed.
Lemma DS_540 : decode_any (0xfff70713%bv : bv 32) = Some (OpImm ALU_ADD 14 14 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_544 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x544)) = Some (0x01f77713%bv : bv 32). Proof. ftac. Qed.
Lemma DS_544 : decode_any (0x01f77713%bv : bv 32) = Some (OpImm ALU_AND 14 14 31, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_548 : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x548)) = Some (0x0e067613%bv : bv 32). Proof. ftac. Qed.
Lemma DS_548 : decode_any (0x0e067613%bv : bv 32) = Some (OpImm ALU_AND 12 12 224, 4%Z). Proof. vm_refl_bv. Qed.
Lemma FS_54c : fetch_word src0segs (Z_to_bv 64 (src0_A_alloc_slot + 0x54c)) = Some (0x00c76633%bv : bv 32). Proof. ftac. Qed.
Lemma DS_54c : decode_any (0x00c76633%bv : bv 32) = Some (Op ALU_OR 12 14 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma step_val_at : forall segs st regs (rd : reg) (V v : word) pc' mem rom,
RiscvSemantics.step segs st =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd V) pc' mem rom) ->
bv_eqb rd 0 = false -> V = v ->
RiscvSemantics.step segs st = MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros * H Hrd HV. rewrite H, Hrd, HV. reflexivity. Qed.
Lemma msteps_pc : forall segs regs (pc pc' : word) mem rom st,
bv_unsigned pc = bv_unsigned pc' ->
msteps segs (mkst regs pc' mem rom) st -> msteps segs (mkst regs pc mem rom) st.
Proof. intros * E H. replace pc with pc' by (apply bv_eq; symmetry; exact E). exact H. Qed.
Lemma mst_refl_pc : forall segs regs (pc pc' : word) mem rom,
bv_unsigned pc = bv_unsigned pc' ->
msteps segs (mkst regs pc mem rom) (mkst regs pc' mem rom).
Proof. intros * E. replace pc' with pc by (apply bv_eq; exact E). apply mst_refl. Qed.
End d.
Local Ltac sva F0 D L vv tac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_val_at with (v := vv);
[ eapply L; [exact F | reflexivity | exact D] | reflexivity | tac ]
| step_simpl ].
Local Ltac seg_done := apply mst_refl_pc; vm_compute; reflexivity.
Local Ltac brz :=
gr; rwH;
rewrite ?brz_eq, ?brz_ne, ?brz_ltu, ?brz_geu, ?brz_lt, ?brz_ge by lia;
rewrite ?s64_small by lia;
first [ reflexivity
| apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
| apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
| apply negb_true_iff; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia]
| apply negb_false_iff; first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia] ].
Local Ltac stepbtz F0 D := let F := litF F0 in
chain_step; [ reflexivity | eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | brz ] | step_simpl ].
Local Ltac stepbfz F0 D := let F := litF F0 in
chain_step; [ reflexivity | eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | brz ] | step_simpl ].
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition span_cond (span size : Z) : bool := Z.lxor span (span + size - 1) <? 4096.
Fixpoint span_stops (fuel : nat) (span size : Z) : bool :=
match fuel with
| O => false
| S f => if span_cond span size then span_stops f (span + size) size else true
end.
Lemma span_loop_unfold f cnt span size :
span_loop (S f) cnt span size = if span_cond span size then span_loop f (cnt + 1) (span + size) size else cnt.
Proof. reflexivity. Qed.
Lemma lxor_range31 a b : 0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 31 -> 0 <= Z.lxor a b < 2 ^ 31.
Proof. intros Ha Hb. apply (lxor_range a b 31); assumption. Qed.
Section g.
Variables (mem rom : word -> option byte) (size : Z).
Hypothesis Hsize : 0 < size.
Lemma span_loop_steps : forall fuel regs cnt span,
span_stops fuel span size = true ->
16 <= span -> span + size * (Z.of_nat fuel + 2) < 2 ^ 31 -> 1 <= cnt -> cnt + Z.of_nat fuel < 2 ^ 31 ->
getr regs 5 = Z64 span -> getr regs 16 = Z64 (span + size - 1) -> getr regs 14 = Z64 (cnt - 1) ->
getr regs 15 = Z64 size -> getr regs 17 = Z64 4096 ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_alloc_slot + 0x51c)) mem rom) (mkst regs' (Z64 (src0_A_alloc_slot + 0x530)) mem rom) /\
getr regs' 14 = Z64 (span_loop fuel cnt span size) /\ getr regs' 15 = Z64 size /\ getr regs' 17 = Z64 4096 /\
(forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 14%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
induction fuel as [|fuel IH]; intros regs cnt span ST Hsp Hov Hc Hcov R5 R16 R14 R15 R17; [discriminate|].
cbn [span_stops] in ST. rewrite span_loop_unfold.
assert (Hsz : size * (Z.of_nat fuel + 2) = size * (Z.of_nat fuel + 1) + size) by lia.
assert (Hs1 : 0 < size * (Z.of_nat fuel + 1)) by (apply Z.mul_pos_pos; lia).
pose proof (lxor_range31 (span + size - 1) span ltac:(lia) ltac:(lia)) as HX.
assert (BODY : forall K : machine_state -> Prop,
(forall regs1, getr regs1 6 = Z64 (Z.lxor (span + size - 1) span) -> getr regs1 5 = Z64 (span + size) ->
getr regs1 14 = Z64 cnt -> getr regs1 16 = Z64 (span + size + size - 1) -> getr regs1 15 = Z64 size -> getr regs1 17 = Z64 4096 ->
(forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 14%bv -> r <> 16%bv -> getr regs1 r = getr regs r) ->
exists st, msteps src0segs (mkst regs1 (Z64 (src0_A_alloc_slot + 0x52c)) mem rom) st /\ K st) ->
exists st, msteps src0segs (mkst regs (Z64 (src0_A_alloc_slot + 0x51c)) mem rom) st /\ K st).
{ intros K HK.
edestruct (HK (regupd (regupd (regupd (regupd regs 6 (Z64 (Z.lxor (span + size - 1) span))) 5 (Z64 (span + size))) 14 (Z64 cnt)) 16 (Z64 (span + size + size - 1))))
as (st & MS & Kst); [gr; reflexivity | gr; reflexivity | gr; reflexivity | gr; reflexivity | gr; exact R15 | gr; exact R17 | intros r H5 H6 H14 H16; rewrite !getr_other by assumption; reflexivity |].
exists st. split; [|exact Kst].
norm_pc.
sva FS_51c DS_51c step_xor (Z64 (Z.lxor (span + size - 1) span)) ltac:(gr; rwH; rewrite vz_xor by lia; reflexivity).
sva FS_520 DS_520 step_addw (Z64 (span + size)) ltac:(gr; rwH; rewrite vz_addw by lia; f_equal; apply addw_small; lia).
sva FS_524 DS_524 step_addiw (Z64 cnt) ltac:(gr; rwH; imm_norm; rewrite vz_addiw by lia; f_equal; rewrite addw_small by lia; lia).
sva FS_528 DS_528 step_addw (Z64 (span + size + size - 1)) ltac:(gr; rwH; rewrite vz_addw by lia; f_equal; rewrite addw_small by lia; lia).
eapply msteps_pc; [|exact MS]. vm_compute; reflexivity. }
match goal with |- exists regs', msteps _ ?st0 (mkst regs' ?pc1 _ _) /\ @?P regs' =>
enough (H : exists st, msteps src0segs st0 st /\ (exists regs', st = mkst regs' pc1 mem rom /\ P regs'))
by (destruct H as (st & MS & regs' & -> & R); exists regs'; split; [exact MS | exact R]) end.
destruct (span_cond span size) eqn:EC.
-
apply BODY. intros regs1 Q6 Q5 Q14 Q16 Q15 Q17 Qfr.
edestruct (IH regs1 (cnt + 1) (span + size)) as (regs' & MS & P14 & P15 & P17 & Pfr);
[exact ST | lia | lia | lia | lia | exact Q5 | rewrite Q16; f_equal; lia | rewrite Q14; f_equal; lia | exact Q15 | exact Q17 |].
exists (mkst regs' (Z64 (src0_A_alloc_slot + 0x530)) mem rom). split; [| exists regs'; split; [reflexivity|]].
+ norm_pc. unfold span_cond in EC. apply Z.ltb_lt in EC. rewrite Z.lxor_comm in EC.
stepbtz FS_52c DS_52c.
eapply msteps_pc; [|exact MS]. vm_compute; reflexivity.
+ split; [exact P14|]. split; [exact P15|]. split; [exact P17|]. intros r H5 H6 H14 H16. rewrite (Pfr r H5 H6 H14 H16). apply Qfr; assumption.
-
apply BODY. intros regs1 Q6 Q5 Q14 Q16 Q15 Q17 Qfr.
exists (mkst regs1 (Z64 (src0_A_alloc_slot + 0x530)) mem rom). split; [| exists regs1; split; [reflexivity|]].
+ norm_pc. unfold span_cond in EC. apply Z.ltb_ge in EC. rewrite Z.lxor_comm in EC.
stepbfz FS_52c DS_52c.
seg_done.
+ split; [exact Q14|]. split; [exact Q15|]. split; [exact Q17|]. exact Qfr.
Qed.
End g.
Definition span_clamp (cnt last : Z) : Z := if cnt <? last + 1 then cnt else last + 1.
Definition span_byte (cnt last aib : Z) : Z := Z.lor (Z.land (span_clamp cnt last - 1) 31) (Z.land aib 224).
Lemma span_tail_steps : forall mem rom regs cnt bits aib,
getr regs 14 = Z64 cnt -> getr regs 13 = Z64 bits -> getr regs 12 = Z64 aib ->
0 <= bits < 2 ^ 64 -> 0 <= aib < 256 -> 1 <= cnt < 2 ^ 31 ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_alloc_slot + 0x530)) mem rom) (mkst regs' (Z64 (src0_A_alloc_slot + 0x550)) mem rom) /\
getr regs' 12 = Z64 (span_byte cnt (Z.land bits 31) aib) /\
(forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
intros mem rom regs cnt bits aib R14 R13 R12 Hbits Haib Hcnt.
set (last := Z.land bits 31).
assert (Hlast : 0 <= last < 32) by (subst last; split; [apply Z.land_nonneg; lia | change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia]).
assert (Hcl : 1 <= span_clamp cnt last <= cnt) by (unfold span_clamp; destruct (Z.ltb_spec cnt (last + 1)); lia).
assert (Hlo : 0 <= Z.land (span_clamp cnt last - 1) 31 < 32).
{ split; [apply Z.land_nonneg; lia | change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia]. }
assert (Hhi : 0 <= Z.land aib 224 < 256).
{ split; [apply Z.land_nonneg; lia|]. rewrite Z.land_comm. eapply Z.le_lt_trans; [apply YO14.land_le_l; lia | lia]. }
assert (TAIL : forall regs1, getr regs1 14 = Z64 (span_clamp cnt last) -> getr regs1 13 = Z64 (last + 1) -> getr regs1 12 = Z64 aib ->
(forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs1 r = getr regs r) ->
exists regs', msteps src0segs (mkst regs1 (Z64 (src0_A_alloc_slot + 0x540)) mem rom) (mkst regs' (Z64 (src0_A_alloc_slot + 0x550)) mem rom) /\
getr regs' 12 = Z64 (span_byte cnt last aib) /\
(forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r)).
{ intros regs1 Q14 Q13 Q12 Qfr. eexists. split; [|split].
- norm_pc.
sva FS_540 DS_540 step_addi (Z64 (span_clamp cnt last - 1)) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; lia).
sva FS_544 DS_544 step_andi (Z64 (Z.land (span_clamp cnt last - 1) 31)) ltac:(gr; imm_norm; rewrite vz_andi by lia; reflexivity).
sva FS_548 DS_548 step_andi (Z64 (Z.land aib 224)) ltac:(gr; rwH; imm_norm; rewrite vz_andi by lia; reflexivity).
sva FS_54c DS_54c step_or (Z64 (span_byte cnt last aib)) ltac:(gr; rewrite vz_or by lia; reflexivity).
seg_done.
- gr. reflexivity.
- intros r H12 H13 H14. rewrite !getr_other by assumption. apply Qfr; assumption. }
assert (HEAD : forall K : machine_state -> Prop,
(forall regs1, getr regs1 13 = Z64 (last + 1) -> getr regs1 14 = Z64 cnt -> getr regs1 12 = Z64 aib ->
(forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs1 r = getr regs r) ->
exists st, msteps src0segs (mkst regs1 (Z64 (src0_A_alloc_slot + 0x538)) mem rom) st /\ K st) ->
exists st, msteps src0segs (mkst regs (Z64 (src0_A_alloc_slot + 0x530)) mem rom) st /\ K st).
{ intros K HK.
edestruct (HK (regupd (regupd regs 13 (Z64 last)) 13 (Z64 (last + 1)))) as (st & MS & Kst);
[gr; reflexivity | gr; exact R14 | gr; exact R12 | intros r H12 H13 H14; rewrite !getr_other by assumption; reflexivity |].
exists st. split; [|exact Kst]. norm_pc.
sva FS_530 DS_530 step_andi (Z64 last) ltac:(gr; rwH; imm_norm; rewrite vz_andi by lia; reflexivity).
sva FS_534 DS_534 step_addi (Z64 (last + 1)) ltac:(gr; imm_norm; rewrite v_addi_lit; reflexivity).
eapply msteps_pc; [|exact MS]. vm_compute; reflexivity. }
match goal with |- exists regs', msteps _ ?st0 (mkst regs' ?pc1 _ _) /\ @?P regs' =>
enough (H : exists st, msteps src0segs st0 st /\ (exists regs', st = mkst regs' pc1 mem rom /\ P regs'))
by (destruct H as (st & MS & regs' & -> & R); exists regs'; split; [exact MS | exact R]) end.
apply HEAD. intros regs1 Q13 Q14 Q12 Qfr.
destruct (Z.ltb_spec cnt (last + 1)) as [LT|GE].
-
edestruct (TAIL regs1) as (regs' & MS & P12 & Pfr); [rewrite Q14; unfold span_clamp; replace (cnt <? last + 1) with true by (symmetry; apply Z.ltb_lt; exact LT); reflexivity | exact Q13 | exact Q12 | exact Qfr |].
exists (mkst regs' (Z64 (src0_A_alloc_slot + 0x550)) mem rom). split; [| exists regs'; split; [reflexivity | split; [exact P12 | exact Pfr]]].
norm_pc. stepbtz FS_538 DS_538. eapply msteps_pc; [|exact MS]. vm_compute; reflexivity.
-
edestruct (TAIL (regupd regs1 14 (Z64 (last + 1)))) as (regs' & MS & P12 & Pfr);
[gr; unfold span_clamp; replace (cnt <? last + 1) with false by (symmetry; apply Z.ltb_ge; exact GE); reflexivity | gr; exact Q13 | gr; exact Q12 | intros r H12 H13 H14; rewrite !getr_other by assumption; apply Qfr; assumption |].
exists (mkst regs' (Z64 (src0_A_alloc_slot + 0x550)) mem rom). split; [| exists regs'; split; [reflexivity | split; [exact P12 | exact Pfr]]].
norm_pc. stepbfz FS_538 DS_538.
sva FS_53c DS_53c step_addi (Z64 (last + 1)) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; lia).
eapply msteps_pc; [|exact MS]. vm_compute; reflexivity.
Qed.
Definition span_entry_ok (sc aidx : Z) : bool :=
let size := class_size sc in
let span0 := UNIT + size * (aidx + 2) in
span_stops 299 span0 size && (span0 + size * (299 + 2) <? 2 ^ 31).
Lemma span_table_ok : forallb (fun sc => forallb (fun aidx => span_entry_ok sc aidx) (zseq 0 32)) (zseq 1 47) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma span_entry_facts sc aidx : 1 <= sc < 48 -> 0 <= aidx <= 31 ->
span_stops 299 (UNIT + class_size sc * (aidx + 2)) (class_size sc) = true /\
UNIT + class_size sc * (aidx + 2) + class_size sc * (299 + 2) < 2 ^ 31.
Proof.
intros Hsc Ha.
pose proof (proj1 (forallb_forall _ _) span_table_ok sc ltac:(apply In_zseq; lia)) as H. cbn beta in H.
pose proof (proj1 (forallb_forall _ _) H aidx ltac:(apply In_zseq; lia)) as H2. unfold span_entry_ok in H2.
apply andb_prop in H2 as [H2 H3]. apply Z.ltb_lt in H3. split; [exact H2 | exact H3].
Qed.
Lemma span_stops_mono f span size : span_stops f span size = true -> span_stops (S f) span size = true.
Proof.
revert span. induction f as [|f IH]; intros span H; [discriminate|].
cbn [span_stops] in H |- *. destruct (span_cond span size); [apply IH; exact H | reflexivity].
Qed.
Lemma span_loop_fuel f cnt span size : span_stops f span size = true -> span_loop (S f) cnt span size = span_loop f cnt span size.
Proof.
revert cnt span. induction f as [|f IH]; intros cnt span H; [discriminate|].
cbn [span_stops] in H. rewrite !span_loop_unfold. destruct (span_cond span size); [|reflexivity]. apply IH. exact H.
Qed.
Lemma span_loop_bounds f cnt span size : cnt <= span_loop f cnt span size <= cnt + Z.of_nat f.
Proof.
revert cnt span. induction f as [|f IH]; intros cnt span; [cbn; lia|].
rewrite span_loop_unfold. destruct (span_cond span size); [|lia]. specialize (IH (cnt + 1) (span + size)). lia.
Qed.
End e.
