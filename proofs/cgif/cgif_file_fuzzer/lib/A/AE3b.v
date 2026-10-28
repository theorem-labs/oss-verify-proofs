(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup tfibmusl_tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word tfibsegs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply tfibmusl_tbl_ok. exact H.
Qed.
End c.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_000 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x0)) = Some (0x02060063%bv : bv 32).
Proof. ftac. Qed.
Lemma D_000 : decode_any (0x02060063%bv : bv 32) = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_004 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x4)) = Some (0x00054683%bv : bv 32).
Proof. ftac. Qed.
Lemma D_004 : decode_any (0x00054683%bv : bv 32) = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_008 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x8)) = Some (0x0005c703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_008 : decode_any (0x0005c703%bv : bv 32) = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_00c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0xc)) = Some (0x00e69e63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_00c : decode_any (0x00e69e63%bv : bv 32) = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_010 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x10)) = Some (0xfff60613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_010 : decode_any (0xfff60613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_014 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x14)) = Some (0x00150513%bv : bv 32).
Proof. ftac. Qed.
Lemma D_014 : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_018 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x18)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_018 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_01c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x1c)) = Some (0xfe0614e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_01c : decode_any (0xfe0614e3%bv : bv 32) = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_020 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x20)) = Some (0x00000513%bv : bv 32).
Proof. ftac. Qed.
Lemma D_020 : decode_any (0x00000513%bv : bv 32) = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_024 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x24)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma D_024 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_028 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x28)) = Some (0x40e68533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_028 : decode_any (0x40e68533%bv : bv 32) = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_02c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x2c)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma D_02c : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma bv_eqb_eq : forall {k} (a b : bv k), bv_eqb a b = true -> a = b.
Proof. intros k a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Fixpoint memcmp_spec (l r : list byte) : Z :=
match l, r with
| a :: l', b :: r' => if bv_eqb a b then memcmp_spec l' r' else bv_unsigned a - bv_unsigned b
| _, _ => 0
end.
Lemma memcmp_spec_range : forall l r, -256 < memcmp_spec l r < 256.
Proof.
induction l as [|a l IH]; intros [|b r]; cbn; try lia.
pose proof (bv_unsigned_in_range 8 a). pose proof (bv_unsigned_in_range 8 b).
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
destruct (bv_eqb a b); [apply IH|lia].
Qed.
Lemma memcmp_spec_zero_iff : forall l r, length l = length r -> (memcmp_spec l r = 0 <-> l = r).
Proof.
induction l as [|a l IH]; intros [|b r] Hlen; cbn in *; try (split; [reflexivity|]; intros; reflexivity); try lia.
destruct (bv_eqb a b) eqn:E.
- apply bv_eqb_eq in E. subst b. rewrite IH by lia. split; [intros ->; reflexivity|intros H; injection H; auto].
- unfold bv_eqb in E. apply Z.eqb_neq in E. split; [intros; exfalso; lia|].
intros H. injection H. intros _ Hab. subst. lia.
Qed.
Lemma memcmp_spec_skipn_eq : forall l r i, (i < length l)%nat -> length l = length r ->
nth i l NUL = nth i r NUL ->
memcmp_spec (skipn i l) (skipn i r) = memcmp_spec (skipn (S i) l) (skipn (S i) r).
Proof.
intros l r i Hi Hlen Heq.
rewrite <- (firstn_skipn i l) in Heq. rewrite <- (firstn_skipn i r) in Heq.
rewrite !app_nth2 in Heq by (rewrite length_firstn; lia).
rewrite !length_firstn in Heq. replace (i - Nat.min i (length l))%nat with 0%nat in Heq by lia.
replace (i - Nat.min i (length r))%nat with 0%nat in Heq by lia.
replace (S i) with (1 + i)%nat by lia. rewrite <- !skipn_skipn.
destruct (skipn i l) as [|a l'] eqn:El; [exfalso; apply (f_equal (@length byte)) in El; rewrite length_skipn in El; cbn in El; lia|].
destruct (skipn i r) as [|b r'] eqn:Er; [exfalso; apply (f_equal (@length byte)) in Er; rewrite length_skipn in Er; cbn in Er; lia|].
cbn in Heq |- *. subst b. rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma memcmp_spec_skipn_ne : forall l r i, (i < length l)%nat -> length l = length r ->
nth i l NUL <> nth i r NUL ->
memcmp_spec (skipn i l) (skipn i r) = bv_unsigned (nth i l NUL) - bv_unsigned (nth i r NUL).
Proof.
intros l r i Hi Hlen Hne.
rewrite (skipn_nth l i NUL) by lia. rewrite (skipn_nth r i NUL) by lia. cbn.
destruct (bv_eqb (nth i l NUL) (nth i r NUL)) eqn:E; [|reflexivity].
exfalso. apply Hne. apply bv_eqb_eq. exact E.
Qed.
Lemma memcmp_spec_nil : forall l r i, (length l <= i)%nat -> memcmp_spec (skipn i l) (skipn i r) = 0.
Proof. intros l r i Hi. rewrite skipn_all2 by lia. reflexivity. Qed.
Section e.
Variables l r : list byte.
Variables p q : word.
Variables mem rom : word -> option byte.
Definition P : Z := bv_unsigned p.
Definition Q : Z := bv_unsigned q.
Definition LEN : nat := length l.
Hypothesis Hlen : length r = length l.
Hypothesis Hl : rdn tfibsegs mem p (length l) = Some l.
Hypothesis Hr : rdn tfibsegs mem q (length l) = Some r.
Hypothesis Hnp : bv_unsigned p + Z.of_nat (length l) < 2^64.
Hypothesis Hnq : bv_unsigned q + Z.of_nat (length l) < 2^64.
Lemma PQ_facts : P = bv_unsigned p /\ Q = bv_unsigned q /\ 0 <= P /\ 0 <= Q /\
P + Z.of_nat LEN < 2^64 /\ Q + Z.of_nat LEN < 2^64 /\ LEN = length l.
Proof. pose proof (u64_range p). pose proof (u64_range q). unfold P, Q, LEN. lia. Qed.
Ltac pq := pose proof PQ_facts as HPQ; destruct HPQ as (HP_ & HQ_ & HPr & HQr & HPn & HQn & HLEN).
Lemma read_l : forall i, (i < length l)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (P + Z.of_nat i)) 1 = Some [nth i l NUL].
Proof.
intros i Hi. pq. replace (Z_to_bv 64 (P + Z.of_nat i)) with (p + nat_to_word i)%bv
by (rewrite word_add_nat; f_equal; lia).
rewrite (rdn_sub tfibsegs mem p (length l) l i 1 Hl) by lia.
rewrite (skipn_nth l i NUL) by lia. reflexivity.
Qed.
Lemma read_r : forall i, (i < length l)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (Q + Z.of_nat i)) 1 = Some [nth i r NUL].
Proof.
intros i Hi. pq. replace (Z_to_bv 64 (Q + Z.of_nat i)) with (q + nat_to_word i)%bv
by (rewrite word_add_nat; f_equal; lia).
rewrite (rdn_sub tfibsegs mem q (length l) r i 1 Hr) by lia.
rewrite (skipn_nth r i NUL) by lia. reflexivity.
Qed.
Definition keep (x : reg) : Prop :=
x <> 10%bv /\ x <> 11%bv /\ x <> 12%bv /\ x <> 13%bv /\ x <> 14%bv.
Definition fin (regs : bvmap 5 word) (pc : word) (res : Z) : Prop :=
exists regs',
msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 res
/\ forall x, keep x -> getr regs' x = getr regs x.
Lemma keep_1 : keep 1.
Proof. unfold keep. repeat split; reg_neq_tac. Qed.
Lemma fin_steps : forall regs pc regs2 pc2 res,
msteps tfibsegs (mkst regs pc mem rom) (mkst regs2 pc2 mem rom) ->
(forall x, keep x -> getr regs2 x = getr regs x) ->
fin regs2 pc2 res -> fin regs pc res.
Proof.
intros regs pc regs2 pc2 res Hms Hfr (regs' & Hms' & Ha & Hfr').
exists regs'. split; [|split; [exact Ha|]].
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keep_1). exact Hms'.
- intros x Hx. rewrite (Hfr' x Hx). apply Hfr. exact Hx.
Qed.
Lemma fin_pc : forall regs (pc pc' : word) res,
bv_unsigned pc = bv_unsigned pc' -> fin regs pc' res -> fin regs pc res.
Proof. intros regs pc pc' res H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold keep in Hx;
destruct Hx as (?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_apply L :=
eapply fin_pc; [ | eapply L ]; [ vm_compute; reflexivity | .. ].
Ltac svt F D vv tac := let F' := litF F in stepiv F' D vv tac.
Ltac steplb F0 D0 RD :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D0
| gr; rwH; imm_norm; rewrite ?v_addi_lit; first [apply RD; lia | rewrite Z.add_0_r; apply RD; lia] ]
| step_simpl ].
Lemma mc_loop : forall j i regs,
(i + j = length l)%nat -> (0 < j)%nat ->
getr regs 10 = Z_to_bv 64 (P + Z.of_nat i) ->
getr regs 11 = Z_to_bv 64 (Q + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 (Z.of_nat j) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x4)) (memcmp_spec (skipn i l) (skipn i r)).
Proof.
induction j as [|j IH]; intros i regs Hij Hj H10 H11 H12; [lia|]. pq.
pose proof (bv_unsigned_in_range 8 (nth i l NUL)) as Ha.
pose proof (bv_unsigned_in_range 8 (nth i r NUL)) as Hb.
unfold bv_modulus in Ha, Hb. change (2 ^ Z.of_N 8) with 256 in Ha, Hb.
destruct (bv_eqb (nth i l NUL) (nth i r NUL)) eqn:E.
-
apply bv_eqb_eq in E.
rewrite (memcmp_spec_skipn_eq l r i) by (try lia; exact E).
assert (Eu : bv_unsigned (nth i l NUL) = bv_unsigned (nth i r NUL)) by (rewrite E; reflexivity).
destruct j as [|j'].
+
rewrite memcmp_spec_nil by lia.
eapply fin_steps.
* norm_pc.
steplb F_004 D_004 read_l.
steplb F_008 D_008 read_r.
stepbf F_00c D_00c.
svt F_010 D_010 (Z_to_bv 64 0) val.
svt F_014 D_014 (Z_to_bv 64 (P + Z.of_nat (S i))) val.
svt F_018 D_018 (Z_to_bv 64 (Q + Z.of_nat (S i))) val.
stepbf F_01c D_01c.
svt F_020 D_020 (Z_to_bv 64 0) val.
stepret F_024 D_024.
apply mst_refl.
* frame.
* exists (regupd (regupd (regupd (regupd (regupd (regupd regs 13 (Z_to_bv 64 (bv_unsigned (nth i l NUL)))) 14
(Z_to_bv 64 (bv_unsigned (nth i r NUL)))) 12 (Z_to_bv 64 0)) 10 (Z_to_bv 64 (P + Z.of_nat (S i)))) 11
(Z_to_bv 64 (Q + Z.of_nat (S i)))) 10 (Z_to_bv 64 0)).
split; [gr; apply mst_refl|]. split; [gr; reflexivity|]. frame.
+ eapply fin_steps.
* norm_pc.
steplb F_004 D_004 read_l.
steplb F_008 D_008 read_r.
stepbf F_00c D_00c.
svt F_010 D_010 (Z_to_bv 64 (Z.of_nat (S j'))) val.
svt F_014 D_014 (Z_to_bv 64 (P + Z.of_nat (S i))) val.
svt F_018 D_018 (Z_to_bv 64 (Q + Z.of_nat (S i))) val.
stepbt F_01c D_01c.
apply mst_refl.
* frame.
* fin_apply (IH (S i)); try lia; gr; reflexivity.
-
assert (Hne : nth i l NUL <> nth i r NUL) by (intros HH; rewrite HH, bv_eqb_refl in E; discriminate).
rewrite (memcmp_spec_skipn_ne l r i) by (try lia; exact Hne).
unfold bv_eqb in E. apply Z.eqb_neq in E.
eapply fin_steps.
+ norm_pc.
steplb F_004 D_004 read_l.
steplb F_008 D_008 read_r.
stepbt F_00c D_00c.
svt F_028 D_028 (Z_to_bv 64 (bv_unsigned (nth i l NUL) - bv_unsigned (nth i r NUL))) val.
stepret F_02c D_02c.
apply mst_refl.
+ frame.
+ eexists. split; [gr; apply mst_refl|]. split; [gr; reflexivity|]. frame.
Qed.
Lemma mc_entry : forall regs,
getr regs 10 = Z_to_bv 64 P -> getr regs 11 = Z_to_bv 64 Q -> getr regs 12 = Z_to_bv 64 (Z.of_nat (length l)) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memcmp + 0x0)) (memcmp_spec l r).
Proof.
intros regs H10 H11 H12. pq.
destruct l as [|a l'] eqn:El.
-
assert (r = []) as -> by (destruct r; [reflexivity|cbn in Hlen; lia]). cbn [memcmp_spec].
eapply fin_steps.
+ norm_pc. cbn [length Z.of_nat] in H12.
stepbt F_000 D_000.
svt F_020 D_020 (Z_to_bv 64 0) val.
stepret F_024 D_024.
apply mst_refl.
+ frame.
+ eexists. split; [gr; apply mst_refl|]. split; [gr; reflexivity|]. frame.
- assert (Hl0 : (0 < length l)%nat) by (rewrite El; cbn; lia). rewrite <- El in *. clear El.
eapply fin_steps.
+ norm_pc. stepbf F_000 D_000. apply mst_refl.
+ intros; reflexivity.
+ change l with (skipn 0 l). change r with (skipn 0 r).
fin_apply (mc_loop (length l) 0%nat); try lia.
* rewrite H10. f_equal. lia.
* rewrite H11. f_equal. lia.
* exact H12.
Qed.
End e.
Theorem tfib_memcmp :
forall (l r : list byte) (p q nw : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = p -> getr regs 11 = q -> getr regs 12 = nw ->
bv_unsigned nw = Z.of_nat (length l) -> length r = length l ->
rdn tfibsegs mem p (length l) = Some l ->
rdn tfibsegs mem q (length l) = Some r ->
bv_unsigned p + Z.of_nat (length l) < 2^64 ->
bv_unsigned q + Z.of_nat (length l) < 2^64 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_memcmp) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (memcmp_spec l r)
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv ->
getr regs' x = getr regs x).
Proof.
intros l r p q nw mem rom regs H10 H11 H12 Hn Hlen Hl Hr Hnp Hnq.
assert (H10' : getr regs 10 = Z_to_bv 64 (P p)) by (rewrite H10; unfold P; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (H11' : getr regs 11 = Z_to_bv 64 (Q q)) by (rewrite H11; unfold Q; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (H12' : getr regs 12 = Z_to_bv 64 (Z.of_nat (length l))) by (rewrite H12, <- Hn, Z_to_bv_bv_unsigned; reflexivity).
destruct (mc_entry l r p q mem rom Hlen Hl Hr Hnp Hnq regs H10' H11' H12') as (regs' & Hms & Ha0 & Hfr).
exists regs'. split; [|split; [exact Ha0|]].
- change (Z_to_bv 64 tfib_A_musl_memcmp) with (Z_to_bv 64 (tfib_A_musl_memcmp + 0x0)). exact Hms.
- intros. apply Hfr. unfold keep. repeat split; assumption.
Qed.
Corollary tfib_memcmp_zero_iff : forall l r, length r = length l ->
(Z_to_bv 64 (memcmp_spec l r) = Z_to_bv 64 0 <-> l = r).
Proof.
intros l r Hlen. rewrite <- (memcmp_spec_zero_iff l r) by lia.
pose proof (memcmp_spec_range l r).
split; [|intros ->; reflexivity]. intros E.
apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
change (2 ^ Z.of_N 64) with (2^64) in E. rewrite (Z.mod_small 0) in E by lia.
destruct (Z_lt_le_dec (memcmp_spec l r) 0).
- replace (memcmp_spec l r) with ((memcmp_spec l r + 2^64) + (-1) * 2^64) in E by lia.
rewrite Z.mod_add, Z.mod_small in E by lia. lia.
- rewrite Z.mod_small in E by lia. exact E.
Qed.
End d.
