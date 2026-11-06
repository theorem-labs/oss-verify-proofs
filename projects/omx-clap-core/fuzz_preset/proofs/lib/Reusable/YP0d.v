(* copied from proofs/cgif/cgif_file_fuzzer/lib/YP0d.v (origin/ossv/recipes c8557374ad2e), unrelocated; module paths moved to fuzz_preset lib.Reusable *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable psym : Type.
Lemma ptree_from_spec : forall (l : list (pinstr psym)) i t p,
0 <= i -> tget p (ptree_of_list_from psym i l t) =
match (if (Z.pos p - 1 <? i) then None else nth_error l (Z.to_nat (Z.pos p - 1 - i))) with Some e => Some e | None => tget p t end.
Proof.
induction l as [|e l IH]; intros i t p Hi; cbn [ptree_of_list_from].
- destruct (Z.pos p - 1 <? i); [reflexivity|]. destruct (Z.to_nat (Z.pos p - 1 - i)); reflexivity.
- rewrite IH by lia.
destruct (Z.ltb_spec (Z.pos p - 1) (i + 1)) as [Hl|Hl]; destruct (Z.ltb_spec (Z.pos p - 1) i) as [Hl2|Hl2].
+   rewrite tget_tset_other by (intros Heq; lia). reflexivity.
+   assert (Hp : Z.to_pos (i + 1) = p) by lia. rewrite Hp, tget_tset_same.
replace (Z.to_nat (Z.pos p - 1 - i)) with 0%nat by lia. reflexivity.
+ exfalso. lia.
+ rewrite tget_tset_other by (intros Heq; lia).
replace (Z.to_nat (Z.pos p - 1 - i)) with (S (Z.to_nat (Z.pos p - 1 - (i + 1)))) by lia. reflexivity.
Qed.
Lemma plookup_list_of_tree : forall (l : ptable psym) k e,
plookup (ptree_of_list l) k = Some e -> plookup_list psym l k = Some e.
Proof.
intros l k e H. unfold plookup in H. unfold plookup_list.
destruct ((0 <=? k) && (k mod 4 =? 0))%bool eqn:Hg; [|discriminate].
apply andb_prop in Hg as [H0 H4]. apply Z.leb_le in H0. apply Z.eqb_eq in H4.
replace ((k <? 0) || negb (k mod 4 =? 0))%bool with false.
2: { symmetry. apply Bool.orb_false_intro; [apply Z.ltb_ge; lia | rewrite H4; reflexivity]. }
unfold ptree_of_list, pkey in H. rewrite ptree_from_spec in H by lia.
replace (Z.pos (Z.to_pos (k / 4 + 1)) - 1) with (k / 4) in H by (pose proof (Z.div_pos k 4 ltac:(lia) ltac:(lia)); lia).
destruct (Z.ltb_spec (k / 4) 0) as [Hl|Hl]; [pose proof (Z.div_pos k 4 ltac:(lia) ltac:(lia)); lia|].
rewrite Z.sub_0_r in H. destruct (nth_error l (Z.to_nat (k / 4))) as [e'|]; [exact H|]. destruct (Z.to_pos (k / 4 + 1)); cbn in H; discriminate H.
Qed.
End d.
Definition pinstr_atoms_ltb {psym : Type} (A : nat) (e : pinstr psym) : bool :=
match e with
| PHi _ j => Nat.ltb (A_HI j) A
| PAddHi _ _ j a _ => Nat.ltb (A_HI j) A && Nat.ltb a A
| PLdHi _ _ j a _ _ _ => Nat.ltb (A_HI j) A && Nat.ltb a A
| _ => true
end.
Section f.
Variable psym : Type.
Variable segs : list Segment.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Context {fx : FPState}.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64.
#[local] Notation tpi := (ptree_of_list listing).
#[local] Notation B := (val A_TEXT).
Definition img_env (A_LIM : nat) (E : env) : Prop := forall a, (A_TEXT <= a < A_LIM)%nat -> bv_unsigned (ew E a) = val a.
Definition abs_ss (ss : sstate) : sstate := setpc ss (B + ss_pc ss).
Definition st_ok_pi (E : env) (ss : sstate) (ms : machine_state) : Prop := st_ok segs E (abs_ss ss) ms.
Lemma cert_slot : forall k e, plookup tpi k = Some e -> pi_slot_check psym fetch val sigma k e = true /\ 0 <= k /\ k mod 4 = 0.
Proof.
intros k e H. split; [exact (pi_check_lookup psym fetch val sigma listing k e Hcert (plookup_list_of_tree psym listing k e H))|].
unfold plookup in H. destruct ((0 <=? k) && (k mod 4 =? 0))%bool eqn:Hg; [|discriminate].
apply andb_prop in Hg as [H0 H4]. apply Z.leb_le in H0. apply Z.eqb_eq in H4. lia.
Qed.
Lemma st_ok_ext : forall E s1 s2 ms, st_ok segs E s1 ms ->
ss_regs s2 = ss_regs s1 -> ss_mem s2 = ss_mem s1 -> ss_resv s2 = ss_resv s1 -> ss_facts s2 = ss_facts s1 -> ss_pc s2 = ss_pc s1 ->
st_ok segs E s2 ms.
Proof. intros E s1 s2 ms HS H1 H2 H3 H4 H5. unfold st_ok in *. rewrite H1, H2, H3, H4, H5. exact HS. Qed.
Lemma sload_pi_sload : forall G rs b off sz sg v,
sload_pi G rs b off sz sg = Some v -> sload segs G rs b off sz sg = Some v.
Proof.
intros G rs b off sz sg v H. unfold sload_pi in H. unfold sload.
destruct (find_region rs b off (Z.of_nat (nbytes sz))) as [r|]; [|discriminate].
destruct (find_chunk (r_chunks r) off (Z.of_nat (nbytes sz))) as [c|]; [|discriminate].
destruct (YP09.c_val c); try exact H. discriminate H.
Qed.
Definition tbl1 (pc w : Z) : ctable := tset (ckey pc) w TEmpty.
Lemma tbl1_lookup : forall pc w, 0 <= pc -> clookup (tbl1 pc w) pc = Some w.
Proof. intros pc w Hpc. unfold clookup, tbl1. replace (0 <=? pc) with true by (symmetry; apply Z.leb_le; lia). apply tget_tset_same. Qed.
Lemma tbl1_ok : forall pc w, 0 <= pc -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w) -> table_ok segs (tbl1 pc w).
Proof.
intros pc w Hpc Hf pc' w' Hl. unfold clookup, tbl1 in Hl. destruct (0 <=? pc') eqn:H0; [|discriminate]. apply Z.leb_le in H0.
destruct (Pos.eq_dec (ckey pc) (ckey pc')) as [Heq|Hne].
- rewrite <- Heq, tget_tset_same in Hl. injection Hl as <-. apply ckey_inj in Heq; [|lia|lia]. subst pc'. exact Hf.
- rewrite tget_tset_other in Hl by exact Hne. destruct (ckey pc'); cbn in Hl; discriminate Hl.
Qed.
Definition plain_instr (i : instr) : bool :=
match i with
| Lui _ _ | Load _ _ _ _ _ | Store _ _ _ _ | OpImm _ _ _ _ | ShiftImm _ _ _ _ | Op _ _ _ _ | OpImm32 _ _ _ | ShiftImm32 _ _ _ _
| Op32 _ _ _ _ | Mul _ _ _ _ | Mul32 _ _ _ _ | Fence _ _ _ _ _ | FenceI _ _ _ => true
| _ => false
end.
Lemma pw_plain_step : forall ss ss' wz i,
plookup tpi (ss_pc ss) = Some (PW wz) ->
decode_any (Z_to_bv 32 wz) = Some (i, 4) -> is_ecall (Z_to_bv 32 wz) = false -> plain_instr i = true ->
sym_step_pi tpi ss = PRun ss' ->
exists ss1, sym_step segs (tbl1 (B + ss_pc ss) wz) (abs_ss ss) = SRun ss1 /\
ss_regs ss1 = ss_regs ss' /\ ss_mem ss1 = ss_mem ss' /\ ss_resv ss1 = ss_resv ss' /\ ss_facts ss1 = ss_facts ss' /\ ss_fregs ss1 = ss_fregs ss' /\
ss_pc ss1 = B + ss_pc ss'.
Proof.
intros ss ss' wz i Hlk Hdec Hec Hpl H.
pose proof (cert_slot _ _ Hlk) as (_ & Hk0 & _).
unfold sym_step_pi in H. rewrite Hlk in H. cbv zeta in H. rewrite Hec, Hdec in H. cbn [negb Z.eqb Pos.eqb] in H.
unfold sym_step. cbn [ss_pc abs_ss setpc ss_facts ss_regs ss_mem ss_resv ss_fregs].
rewrite tbl1_lookup by lia. cbv zeta. rewrite Hec, Hdec. cbn [negb Z.eqb Pos.eqb].
destruct i; try discriminate Hpl.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
-   destruct (addr_of _) as [[b off]|]; [|discriminate].
destruct (sload_pi _ _ _ _ _ _) as [v|] eqn:Hsl; [|discriminate]. injection H as <-.
rewrite (sload_pi_sload _ _ _ _ _ _ _ Hsl). eexists. split; [reflexivity|]. cbn. repeat split; lia.
-   cbn [ss_resv abs_ss setpc] in *. destruct (ss_resv ss); [discriminate|].
destruct (addr_of _) as [[b off]|]; [|discriminate].
destruct (sstore _ _ _ _ _) as [m'|]; [|discriminate]. injection H as <-.
eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
- injection H as <-. eexists. split; [reflexivity|]. cbn. repeat split; lia.
Qed.
Variable A_LIM : nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Lemma lim_slot : forall k e, plookup tpi k = Some e -> pinstr_atoms_ltb A_LIM e = true.
Proof.
intros k e H. apply plookup_list_of_tree in H. unfold plookup_list in H.
destruct ((k <? 0) || negb (k mod 4 =? 0))%bool; [discriminate H|].
apply nth_error_In in H. rewrite forallb_forall in HLIM. exact (HLIM e H).
Qed.
End f.
Lemma land_m2_64 : forall y, 0 <= y < 2 ^ 64 -> Z.land y (2 ^ 64 - 2) = Z.land y (-2).
Proof.
intros y Hy. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec.
replace (2 ^ 64 - 2) with (Z.ldiff (Z.ones 64) 1) by reflexivity.
replace (-2) with (Z.lnot 1) by reflexivity.
rewrite Z.ldiff_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
- rewrite Z.ones_spec_low by lia. reflexivity.
- assert (Hb : Z.testbit y n = false).
{ destruct (Z.eq_dec y 0) as [->|Hnz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite Hb. reflexivity.
Qed.
Lemma jalr_even_target : forall x, x mod 2 = 0 -> Z_to_bv 64 (zalu64 ALU_AND x (-2)) = Z_to_bv 64 x.
Proof.
intros x Hx. unfold zalu64. rewrite lit_canon. cbn [zalu_raw]. unfold zcanon, M64.
change (2 ^ 64) with 18446744073709551616 in *.
replace ((-2) mod 18446744073709551616) with (18446744073709551616 - 2) by reflexivity.
change 18446744073709551616 with (2 ^ 64). rewrite land_m2_64 by (apply Z.mod_pos_bound; lia).
rewrite YK0s.land_m2_even.
- rewrite <- (lit_canon (x mod 2 ^ 64)). unfold zcanon, M64. rewrite Z.mod_mod by lia. rewrite <- (lit_canon x). unfold zcanon, M64. reflexivity.
-
rewrite (Z.mod_mod_divide x (2 ^ 64) 2); [exact Hx | exists (2 ^ 63); reflexivity].
Qed.
Lemma not_ecall_of_decode : forall w i z, decode_any w = Some (i, z) -> i <> Ecall -> is_ecall w = false.
Proof.
intros w i z Hd Hi. unfold is_ecall. destruct (bv_eqb w (Z_to_bv 32 115)) eqn:E; [|reflexivity].
exfalso. apply Hi. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst w. vm_compute in Hd. congruence.
Qed.
Lemma lit_zalu_add : forall a b, Z_to_bv 64 (zalu64 ALU_ADD a b) = Z_to_bv 64 (a + b).
Proof.
intros a b. unfold zalu64. rewrite lit_canon. cbn [zalu_raw]. unfold zcanon.
rewrite <- (lit_canon (a mod M64 + b mod M64)). unfold zcanon. rewrite <- Zdiv.Zplus_mod. fold (zcanon (a + b)). apply lit_canon.
Qed.
Section g.
Variable psym : Type.
Variable segs : list Segment.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Context {fx : FPState}.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
#[local] Notation tpi := (ptree_of_list listing).
#[local] Notation B := (val A_TEXT).
#[local] Notation img_env := (img_env val A_LIM).
#[local] Notation lim_slot := (lim_slot psym listing A_LIM HLIM).
#[local] Notation st_ok_pi := (st_ok_pi segs val).
#[local] Notation abs_ss := (abs_ss val).
Let HB0 : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 := conj (proj1 HB) (proj1 (proj2 HB)).
Lemma img_env_atom : forall E a, img_env E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (val a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Theorem sym_step_pi_sound : forall E ss ss' ms,
img_env E -> st_ok_pi E ss ms -> sym_step_pi tpi ss = PRun ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok_pi E ss' ms'
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros E ss ss' ms HE HS H.
destruct (plookup tpi (ss_pc ss)) as [e|] eqn:Hlk.
2: { unfold sym_step_pi in H. rewrite Hlk in H. discriminate H. }
pose proof (cert_slot psym fetch val sigma listing Hcert _ _ Hlk) as (Hck & Hk0 & Hk4). unfold pi_slot_check in Hck.
destruct (fetch (B + ss_pc ss)) as [wz|] eqn:Hfw; [|discriminate Hck].
pose proof (Hfetch _ _ Hfw) as Hf.
destruct e as [w | s rd | s | rd j | rd rs j a off | rd rs j a off sz sg].
-   apply Z.eqb_eq in Hck. subst wz.
destruct (is_ecall (Z_to_bv 32 w)) eqn:Hec.
{ unfold sym_step_pi in H. rewrite Hlk in H. cbv zeta in H. rewrite Hec in H. discriminate H. }
destruct (decode_any (Z_to_bv 32 w)) as [[i isz]|] eqn:Hdec.
2: { unfold sym_step_pi in H. rewrite Hlk in H. cbv zeta in H. rewrite Hec, Hdec in H. discriminate H. }
destruct (Z.eqb_spec isz 4) as [->|Hne].
2: { unfold sym_step_pi in H. rewrite Hlk in H. cbv zeta in H. rewrite Hec, Hdec in H. replace (isz =? 4) with false in H by (symmetry; apply Z.eqb_neq; exact Hne). discriminate H. }
destruct (plain_instr i) eqn:Hpl.
+ pose proof (pw_plain_step psym segs fetch val sigma listing Hcert HB0 ss ss' w i Hlk Hdec Hec Hpl H) as (ss1 & Hst & R1 & R2 & R3 & R4 & R5 & R6).
pose proof (sym_step_sound segs (tbl1 (B + ss_pc ss) w) (tbl1_ok segs (B + ss_pc ss) w ltac:(lia) Hf) E (abs_ss ss) ss1 ms HS Hst)
as (ms' & Hstep & HS1 & Hfr1).
exists ms'. split; [exact Hstep|]. split; [| exact Hfr1].
apply (st_ok_ext segs E ss1); [exact HS1 | ..]; cbn; congruence || (cbn; lia).
+
unfold sym_step_pi in H. rewrite Hlk in H. cbv zeta in H. rewrite Hec, Hdec in H. cbn [negb Z.eqb Pos.eqb] in H.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
unfold st_ok_pi, YP0d.st_ok_pi, abs_ss, YP0d.abs_ss in HS |- *.
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts ss_fregs setpc] in Hfr, Hpc, Hpend, Hresv, Hfcsr, Hrom, Hregs, Hmem, HG. subst pcv pend rom fregs fcsr.
rewrite (step_on_fetch segs _ (Z_to_bv 32 w)) by exact Hf.
rewrite (YP00.decode_exec_compat segs). rewrite Hec, Hdec. cbn [Z.eqb Pos.eqb negb].
assert (HR : forall r, rget (Core regs fp_regs (Z_to_bv 64 (B + ss_pc ss)) fp_csr resv) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
pose proof (img_env_atom E A_TEXT HE ltac:(split; [unfold A_TEXT; lia | exact HLIM0])) as ET. pose proof (HE A_TEXT ltac:(split; [unfold A_TEXT; lia | exact HLIM0])) as ETu.
destruct i; try discriminate Hpl; try discriminate H;
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?HR.
*   injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_machL; cbn; auto; [apply regs_ok_set'; [exact Hregs|] |].
-- cbn [sv_denot]. rewrite ETu, lit_add. f_equal. lia.
-- rewrite sext64_lit, lit_add. f_equal. lia.
*   destruct (sr_get (ss_regs ss) rs1) as [t|n t| | | | | | | | |] eqn:Hrs1; try discriminate H.
destruct (Nat.eqb n A_TEXT && ((t + bv_signed imm) mod 2 =? 0))%bool eqn:Hc; [|discriminate H].
apply andb_prop in Hc as [Hn Hev]. apply Nat.eqb_eq in Hn. apply Z.eqb_eq in Hev. subst n.
injection H as <-. eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_machL; cbn; auto; [apply regs_ok_set'; [exact Hregs|] |].
-- cbn [sv_denot]. rewrite ETu, lit_add. f_equal. lia.
-- cbn [sv_denot]. rewrite ETu, sext64_lit, !lit_add, bv_not_w1.
match goal with |- context [bv_and ?x ?y] => change (bv_and x y) with (alu64 ALU_AND x y) end.
rewrite zalu64_sound, jalr_even_target. 2: { pose proof HB as (_ & _ & HB4). pose proof (Z.div_mod B 4 ltac:(lia)) as Hdm.
replace (B + t + bv_signed imm) with ((t + bv_signed imm) + (2 * (B / 4)) * 2) by lia. rewrite Z.mod_add by lia. exact Hev. }
f_equal. lia.
*
destruct (decide_cond2 (ss_facts ss) c (sr_get (ss_regs ss) rs1) (sr_get (ss_regs ss) rs2)) as [[|]|] eqn:Hdc;
try discriminate H; injection H as <-;
rewrite (decide_cond2_sound E _ _ _ _ _ HG Hdc);
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]); apply st_ok_machL; cbn; auto.
-- rewrite sext64_lit, lit_add. f_equal. lia.
-- rewrite pc_plus4. f_equal. lia.
- unfold sym_step_pi in H. rewrite Hlk in H. discriminate H.
- unfold sym_step_pi in H. rewrite Hlk in H. discriminate H.
-
pose proof (lim_slot _ _ Hlk) as HLj. cbn [pinstr_atoms_ltb] in HLj. apply Nat.ltb_lt in HLj.
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck. apply andb_prop in Hck as [Hrd Hv]. apply reg_eqb_eq in Hrd. subst rd0. apply Z.eqb_eq in Hv.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
unfold sym_step_pi in H. rewrite Hlk in H. injection H as <-.
unfold st_ok_pi, YP0d.st_ok_pi, abs_ss, YP0d.abs_ss in HS |- *.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts ss_fregs setpc] in Hfr, Hpc, Hpend, Hresv, Hfcsr, Hrom, Hregs, Hmem, HG. subst pcv pend rom fregs fcsr.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (YP00.decode_exec_compat segs). rewrite Hec, Hdec. cbn [Z.eqb Pos.eqb negb].
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ Sem.exec Sem.load_val Sem.store_val Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_machL; cbn [ss_regs ss_pc ss_resv ss_mem ss_facts ss_fregs setreg setpc]; [apply regs_ok_set'; [exact Hregs|] | rewrite pc_plus4; f_equal; lia | exact Hresv | exact Hmem | exact HG].
cbn [sv_denot]. rewrite Z.add_0_r. rewrite (HE (A_HI j)) by (split; [unfold A_HI, A_TEXT; lia | exact HLj]). rewrite <- Hv. unfold auipc_val. rewrite lit_canon, sext64_lit, lit_add. reflexivity.
-
pose proof (lim_slot _ _ Hlk) as HLj. cbn [pinstr_atoms_ltb] in HLj. apply andb_prop in HLj as [HLj HLa]. apply Nat.ltb_lt in HLj. apply Nat.ltb_lt in HLa.
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck. destruct op; try discriminate Hck.
apply andb_prop in Hck as [Hck Hv]. apply andb_prop in Hck as [Hrd Hrs]. apply reg_eqb_eq in Hrd. apply reg_eqb_eq in Hrs. subst rd0 rs1. apply Z.eqb_eq in Hv.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
unfold sym_step_pi in H. rewrite Hlk in H.
destruct (is_hi (sr_get (ss_regs ss) rs) j) eqn:Hhi; [|discriminate H].
destruct (Nat.leb A_TEXT a) eqn:Ha; [|discriminate H]. apply Nat.leb_le in Ha. injection H as <-.
unfold is_hi in Hhi. destruct (sr_get (ss_regs ss) rs) as [|n z| | | | | | | | |] eqn:Hrsv; try discriminate Hhi.
apply andb_prop in Hhi as [Hn Hz]. apply Nat.eqb_eq in Hn. apply Z.eqb_eq in Hz. subst n z.
unfold st_ok_pi, YP0d.st_ok_pi, abs_ss, YP0d.abs_ss in HS |- *.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts ss_fregs setpc] in Hfr, Hpc, Hpend, Hresv, Hfcsr, Hrom, Hregs, Hmem, HG. subst pcv pend rom fregs fcsr.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (YP00.decode_exec_compat segs). rewrite Hec, Hdec. cbn [Z.eqb Pos.eqb negb].
assert (HR : forall r, rget (Core regs fp_regs (Z_to_bv 64 (B + ss_pc ss)) fp_csr resv) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ Sem.exec Sem.load_val Sem.store_val Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv]; rewrite ?HR.
eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_ok_machL; cbn [ss_regs ss_pc ss_resv ss_mem ss_facts ss_fregs setreg setpc]; [apply regs_ok_set'; [exact Hregs|] | rewrite pc_plus4; f_equal; lia | exact Hresv | exact Hmem | exact HG].
rewrite Hrsv. cbn [sv_denot]. rewrite Z.add_0_r. rewrite (HE (A_HI j)) by (split; [unfold A_HI, A_TEXT; lia | exact HLj]). rewrite (HE a (conj Ha HLa)). rewrite sext64_lit, zalu64_sound, lit_zalu_add. f_equal. lia.
-
pose proof (lim_slot _ _ Hlk) as HLj. cbn [pinstr_atoms_ltb] in HLj. apply andb_prop in HLj as [HLj HLa]. apply Nat.ltb_lt in HLj. apply Nat.ltb_lt in HLa.
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Hv]. apply andb_prop in Hck as [Hck Hsg]. apply andb_prop in Hck as [Hck Hszq]. apply andb_prop in Hck as [Hrd Hrs].
apply reg_eqb_eq in Hrd. apply reg_eqb_eq in Hrs. apply msize_eqb_eq in Hszq. subst rd0 rs1 sz0.
assert (Hsg' : signed = sg) by (destruct sg, signed; try reflexivity; discriminate Hsg). subst signed. apply Z.eqb_eq in Hv.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
unfold sym_step_pi in H. rewrite Hlk in H.
destruct (is_hi (sr_get (ss_regs ss) rs) j) eqn:Hhi; [|discriminate H].
destruct (Nat.leb A_TEXT a) eqn:Ha; [|discriminate H]. apply Nat.leb_le in Ha.
destruct (sload_pi (ss_facts ss) (ss_mem ss) (Some a) off sz sg) as [v|] eqn:Hsl; [|discriminate H]. injection H as <-.
unfold is_hi in Hhi. destruct (sr_get (ss_regs ss) rs) as [|n z| | | | | | | | |] eqn:Hrsv; try discriminate Hhi.
apply andb_prop in Hhi as [Hn Hz]. apply Nat.eqb_eq in Hn. apply Z.eqb_eq in Hz. subst n z.
unfold st_ok_pi, YP0d.st_ok_pi, abs_ss, YP0d.abs_ss in HS |- *.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts ss_fregs setpc] in Hfr, Hpc, Hpend, Hresv, Hfcsr, Hrom, Hregs, Hmem, HG. subst pcv pend rom fregs fcsr.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (YP00.decode_exec_compat segs). rewrite Hec, Hdec. cbn [Z.eqb Pos.eqb negb].
assert (HR : forall r, rget (Core regs fp_regs (Z_to_bv 64 (B + ss_pc ss)) fp_csr resv) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem (sload_pi_sload segs _ _ _ _ _ _ _ Hsl)) as (bs & Hrd & Hvv).
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs) + sext 64 imm)%bv = Z_to_bv 64 (base_val E (Some a) + off)).
{ rewrite Hrsv. cbn [sv_denot base_val]. rewrite Z.add_0_r. rewrite (HE (A_HI j)) by (split; [unfold A_HI, A_TEXT; lia | exact HLj]). rewrite (HE a (conj Ha HLa)).
rewrite sext64_lit, lit_add. f_equal. lia. }
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ Sem.exec Sem.load_val Sem.store_val Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv]; rewrite ?HR.
rewrite Haddr.
destruct sz; cbn [nbytes nbits] in Hrd, Hvv;
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ov_rdn, Hrd; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]);
(apply st_ok_machL; cbn [ss_regs ss_pc ss_resv ss_mem ss_facts ss_fregs setreg setpc]; [apply regs_ok_set'; [exact Hregs|] | rewrite pc_plus4; f_equal; lia | exact Hresv | exact Hmem | exact HG]);
rewrite Hvv, ?bv_extract_0_64; cbn [load_result nbits]; destruct sg; reflexivity.
Qed.
Theorem sym_step_pi_call : forall E ss ss1 s ms,
img_env E -> st_ok_pi E ss ms -> sym_step_pi tpi ss = PCallx s ss1 ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok segs E (setpc ss1 (sigma s)) ms'
/\ ms_mem ms' = ms_mem ms /\ ss_mem ss1 = ss_mem ss /\ ss_facts ss1 = ss_facts ss.
Proof.
intros E ss ss1 s ms HE HS H.
destruct (plookup tpi (ss_pc ss)) as [e|] eqn:Hlk.
2: { unfold sym_step_pi in H. rewrite Hlk in H. discriminate H. }
pose proof (cert_slot psym fetch val sigma listing Hcert _ _ Hlk) as (Hck & Hk0 & Hk4). unfold pi_slot_check in Hck.
destruct (fetch (B + ss_pc ss)) as [wz|] eqn:Hfw; [|discriminate Hck].
pose proof (Hfetch _ _ Hfw) as Hf. pose proof (HE A_TEXT ltac:(split; [unfold A_TEXT; lia | exact HLIM0])) as ETu.
assert (CASES : exists rd imm, decode_any (Z_to_bv 32 wz) = Some (Jal rd imm, 4) /\ zcanon (B + ss_pc ss + bv_signed imm) = sigma s
/\ ss1 = (if bv_eqb rd (Z_to_bv 5 0) then ss else setreg ss rd (codeptr (ss_pc ss + 4)) (ss_pc ss + 4))).
{ unfold sym_step_pi in H. rewrite Hlk in H.
destruct e as [w | s' rd | s' | rd j | rd rs j a off | rd rs j a off sz sg]; try discriminate H.
- exfalso. cbv zeta in H. destruct (is_ecall _); [discriminate H|]. destruct (decode_any _) as [[i isz]|]; [|discriminate H].
destruct (negb _); [discriminate H|]. destruct i; try discriminate H;
repeat match type of H with context [match ?x with _ => _ end] => destruct x; try discriminate H | context [if ?x then _ else _] => destruct x; try discriminate H end.
- injection H as <- <-. destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz. destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd Hnz]. apply reg_eqb_eq in Hrd. subst rd0. apply Z.eqb_eq in Ht.
exists rd, imm. split; [reflexivity|]. split; [exact Ht|]. destruct (bv_eqb rd (Z_to_bv 5 0)); [discriminate Hnz | reflexivity].
- injection H as <- <-. destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz. destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hrd Ht]. apply reg_eqb_eq in Hrd. subst rd. apply Z.eqb_eq in Ht.
exists (Z_to_bv 5 0), imm. split; [reflexivity|]. split; [exact Ht|]. rewrite bv_eqb_refl. reflexivity.
- destruct (is_hi _ _); [destruct (Nat.leb _ _); discriminate H | discriminate H].
- destruct (is_hi _ _); [| discriminate H]. destruct (negb _); [discriminate H|]. destruct (sload_pi _ _ _ _ _ _); discriminate H. }
clear H Hck. destruct CASES as (rd & imm & Hdec & Ht & ->).
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
unfold st_ok_pi, YP0d.st_ok_pi, abs_ss, YP0d.abs_ss in HS.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG).
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts ss_fregs setpc] in Hfr, Hpc, Hpend, Hresv, Hfcsr, Hrom, Hregs, Hmem, HG. subst pcv pend rom fregs fcsr.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (YP00.decode_exec_compat segs). rewrite Hec, Hdec. cbn [Z.eqb Pos.eqb negb].
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ Sem.exec Sem.load_val Sem.store_val Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
eexists. split; [reflexivity|]. split; [| cbn [ms_mem]; destruct (bv_eqb rd (Z_to_bv 5 0)); repeat split; reflexivity].
destruct (bv_eqb rd (Z_to_bv 5 0)) eqn:Hx0.
-
apply reg_eqb_eq in Hx0. subst rd.
apply st_ok_machL; cbn [ss_regs ss_pc ss_resv ss_mem ss_facts ss_fregs setreg setpc]; [ | rewrite sext64_lit, lit_add, <- Ht, lit_canon; f_equal; lia | exact Hresv | exact Hmem | exact HG].
cbn [is_x0]. rewrite bv_eqb_refl || idtac. exact Hregs.
- apply st_ok_machL; cbn [ss_regs ss_pc ss_resv ss_mem ss_facts ss_fregs setreg setpc]; [apply regs_ok_set'; [exact Hregs|] | rewrite sext64_lit, lit_add, <- Ht, lit_canon; f_equal; lia | exact Hresv | exact Hmem | exact HG].
unfold codeptr. cbn [sv_denot]. rewrite ETu, lit_add. f_equal. lia.
Qed.
Lemma sym_step_pi_skeleton : forall ss ss', sym_step_pi tpi ss = PRun ss' -> skeleton (ss_mem ss') = skeleton (ss_mem ss).
Proof.
intros ss ss' H. unfold sym_step_pi in H.
destruct (plookup tpi (ss_pc ss)) as [e|]; [|discriminate H].
destruct e as [w | s rd | s | rd j | rd rs j a off | rd rs j a off sz sg]; try discriminate H.
- cbv zeta in H. destruct (is_ecall (Z_to_bv 32 w)); [discriminate H|].
destruct (decode_any (Z_to_bv 32 w)) as [[i isz]|]; [|discriminate H]. destruct (isz =? 4); cbn [negb] in H; [|discriminate H].
destruct i; try discriminate H;
repeat match type of H with
| context [sstore ?rs ?b ?off ?sz ?v] => destruct (sstore rs b off sz v) eqn:?Hst; [|try discriminate H]
| context [match ?x with _ => _ end] => destruct x; try discriminate H
end;
try (injection H as <-; cbn; try reflexivity).
all: try (injection H as <-; cbn; eapply store_region_skeleton; eassumption).
all: try (eapply store_region_skeleton; eassumption).
- injection H as <-. reflexivity.
- destruct (is_hi _ _); [|discriminate H]. destruct (Nat.leb _ _); [|discriminate H]. injection H as <-. reflexivity.
- destruct (is_hi _ _); [|discriminate H]. destruct (negb _); [discriminate H|].
destruct (sload_pi _ _ _ _ _ _); [|discriminate H]. injection H as <-. reflexivity.
Qed.
Definition prun_post (E : env) (ss' : sstate) (st : prun_status psym) (ms' : machine_state) : Prop :=
match st with
| PRS_ecall => st_ok_ecall segs E (abs_ss ss') ms'
| PRS_call s => st_ok segs E (setpc ss' (sigma s)) ms'
| _ => st_ok_pi E ss' ms'
end.
Theorem sym_run_pi_sound : forall fuel E ss ss' st ms,
img_env E -> st_ok_pi E ss ms -> sym_run_pi tpi fuel ss = (ss', st) ->
exists ms', msteps segs ms ms' /\ prun_post E ss' st ms'
/\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros E ss ss' st ms HE HS H; cbn [sym_run_pi] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity | apply frame_of_refl].
- destruct (sym_step_pi tpi ss) as [ss1|ss1|s ss1|why] eqn:Hs.
+ destruct (sym_step_pi_sound E ss ss1 ms HE HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_step_pi_skeleton ss ss1 Hs) as Hsk1.
destruct (IH E ss1 ss' st ms1 HE HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|]. eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+
injection H as <- <-. unfold sym_step_pi in Hs. destruct (plookup tpi (ss_pc ss)) as [e|]; [|discriminate Hs].
destruct e; try discriminate Hs; cbv zeta in Hs.
* destruct (is_ecall _) eqn:Hec; [discriminate Hs | ].
destruct (decode_any _) as [[i isz]|]; [|discriminate Hs]. destruct (negb _); [discriminate Hs|]. destruct i; try discriminate Hs;
repeat match type of Hs with context [match ?x with _ => _ end] => destruct x; try discriminate Hs | context [if ?x then _ else _] => destruct x; try discriminate Hs end.
* destruct (is_hi _ _); [destruct (Nat.leb _ _); discriminate Hs | discriminate Hs].
* destruct (is_hi _ _); [|discriminate Hs]. destruct (negb _); [discriminate Hs|]. destruct (sload_pi _ _ _ _ _ _); discriminate Hs.
+ injection H as <- <-.
destruct (sym_step_pi_call E ss ss1 s ms HE HS Hs) as (ms1 & Hstep & HS1 & Hm & Hmem1 & _).
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [rewrite Hmem1; reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity | apply frame_of_refl].
Qed.
Theorem sym_run_to_pi_sound : forall fuel stop_k E ss ss' st ms,
img_env E -> st_ok_pi E ss ms -> sym_run_to_pi tpi fuel stop_k ss = (ss', st) ->
exists ms', msteps segs ms ms' /\ prun_post E ss' st ms'
/\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros stop_k E ss ss' st ms HE HS H; cbn [sym_run_to_pi] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity | apply frame_of_refl].
- destruct (ss_pc ss =? stop_k).
{ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity | apply frame_of_refl]. }
destruct (sym_step_pi tpi ss) as [ss1|ss1|s ss1|why] eqn:Hs.
+ destruct (sym_step_pi_sound E ss ss1 ms HE HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_step_pi_skeleton ss ss1 Hs) as Hsk1.
destruct (IH stop_k E ss1 ss' st ms1 HE HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|]. eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-. unfold sym_step_pi in Hs. destruct (plookup tpi (ss_pc ss)) as [e|]; [|discriminate Hs].
destruct e; try discriminate Hs; cbv zeta in Hs.
* destruct (is_ecall _) eqn:Hec; [discriminate Hs | ].
destruct (decode_any _) as [[i isz]|]; [|discriminate Hs]. destruct (negb _); [discriminate Hs|]. destruct i; try discriminate Hs;
repeat match type of Hs with context [match ?x with _ => _ end] => destruct x; try discriminate Hs | context [if ?x then _ else _] => destruct x; try discriminate Hs end.
* destruct (is_hi _ _); [destruct (Nat.leb _ _); discriminate Hs | discriminate Hs].
* destruct (is_hi _ _); [|discriminate Hs]. destruct (negb _); [discriminate Hs|]. destruct (sload_pi _ _ _ _ _ _); discriminate Hs.
+ injection H as <- <-.
destruct (sym_step_pi_call E ss ss1 s ms HE HS Hs) as (ms1 & Hstep & HS1 & Hm & Hmem1 & _).
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [rewrite Hmem1; reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity | apply frame_of_refl].
Qed.
End g.
