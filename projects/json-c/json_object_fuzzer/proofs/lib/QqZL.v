(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI Q85Z QsSk Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q3bI.
Import Q85Z.
Import QsSk Q6EJ.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
QsSk.node_ok segs c unit (fun _ => []) (fun _ => c') ->
P_of T c' -> P_of T c :=
fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.

Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
QsSk.node_ok segs c unit (fun _ => []) (fun _ => c') ->
SP_of T c' -> SP_of T c :=
fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
m_halted model = None ->
msteps segs (restrict H ms) msr' ->
(forall model',
MInv A model' -> same_but_materialized model model' ->
hclean H msr' ->
srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
srealizes segs (mkCfg ms model) T.
Proof.
intros A ms msr' model T.
exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE QU0c Q61E Qt8n QWtD.
From Stdlib Require FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Q61E.
Import Qt8n QWtD.
Import Stdlib.Logic.FunctionalExtensionality. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition PW0 : bv 32 := 0x00465713.
Definition PW1 : bv 32 := 0xfff54793.
Definition PW2 : bv 32 := 0x00150513.
Definition PW3 : bv 32 := 0x00279793.
Definition PW4 : bv 32 := 0x00f587b3.
Definition PW5 : bv 32 := 0x00e7a023.
Definition PW6 : bv 32 := 0x01560633.
Definition PW7 : bv 32 := 0xff3562e3.

Lemma PD0 : decode_any PW0 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z). Proof. vm_refl. Qed.
Lemma PD1 : decode_any PW1 = Some (OpImm ALU_XOR 15 10 4095, 4%Z). Proof. vm_refl. Qed.
Lemma PD2 : decode_any PW2 = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl. Qed.
Lemma PD3 : decode_any PW3 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z). Proof. vm_refl. Qed.
Lemma PD4 : decode_any PW4 = Some (Op ALU_ADD 15 11 15, 4%Z). Proof. vm_refl. Qed.
Lemma PD5 : decode_any PW5 = Some (Store SZ4 15 14 0, 4%Z). Proof. vm_refl. Qed.
Lemma PD6 : decode_any PW6 = Some (Op ALU_ADD 12 12 21, 4%Z). Proof. vm_refl. Qed.
Lemma PD7 : decode_any PW7 = Some (Branch BC_LTU 10 19 8164, 4%Z). Proof. vm_refl. Qed.

Fixpoint pf_mem (mem : word -> option byte) (e c s i : Z) (k : nat) : word -> option byte :=
match k with
| O => mem
| S k' => pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))))
e (c + s) s (i + 1) k'
end.

Fixpoint pf_bytes (c s : Z) (k : nat) : list byte :=
match k with
| O => []
| S k' => Z_to_le_bytes 4 ((c + Z.of_nat k' * s) / 16) ++ pf_bytes c s k'
end.

Lemma pf_bytes_length : forall c s k, length (pf_bytes c s k) = (4 * k)%nat.
Proof. intros c s k. induction k as [|k IH]; cbn [pf_bytes length]; [reflexivity|]. rewrite length_app, length_Z_to_le_bytes, IH. lia. Qed.

Lemma pf_bytes_nth : forall c s k j t,
(0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
nth (Z.to_nat (4 * j) + t) (pf_bytes c s k) (Z_to_bv 8 0) = nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0).
Proof.
intros c s k. induction k as [|k IH]; intros j t Hj Ht; [lia|].
cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
destruct (Z.eq_dec j 0) as [->|Hj0].
- rewrite app_nth1 by (rewrite length_Z_to_le_bytes; lia). replace (Z.to_nat (4 * 0) + t)%nat with t by lia. f_equal. f_equal. f_equal. lia.
- rewrite app_nth2 by (rewrite length_Z_to_le_bytes; lia). rewrite length_Z_to_le_bytes.
replace (Z.to_nat (4 * j) + t - 4)%nat with (Z.to_nat (4 * (j - 1)) + t)%nat by lia.
rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma pf_bytes_cell : forall c s k j,
(0 <= j < Z.of_nat k)%Z ->
firstn 4 (skipn (Z.to_nat (4 * j)) (pf_bytes c s k)) = Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16).
Proof.
intros c s k. induction k as [|k IH]; intros j Hj; [lia|].
cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
destruct (Z.eq_dec j 0) as [->|Hj0].
- replace (Z.to_nat (4 * 0)) with 0%nat by lia. rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). f_equal. f_equal. lia.
- rewrite skipn_app, length_Z_to_le_bytes. rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
replace (Z.to_nat (4 * j) - 4)%nat with (Z.to_nat (4 * (j - 1)))%nat by lia.
rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Definition popfree_spec (SEGS : list Segment) (p : Z) : Prop :=
forall regs mem (i e c s n : Z),
getr regs 10%bv = Z_to_bv 64 i -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 c ->
getr regs 21%bv = Z_to_bv 64 s -> getr regs 19%bv = Z_to_bv 64 n ->
(0 <= i < n)%Z -> (4 * n <= e < 2 ^ 64)%Z -> (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
store_ok SEGS mem (Z_to_bv 64 (e - 4 * n)) (Z.to_nat (4 * (n - i))) = true ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 p) mem (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 (p + 32)) (wbytes mem (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) (seg_rom SEGS))
/\ getr regs' 10%bv = Z_to_bv 64 n /\ getr regs' 12%bv = Z_to_bv 64 (c + (n - i) * s)
/\ getr regs' 14%bv = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15%bv = Z_to_bv 64 (e - 4 * n)
/\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).

Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.

Definition iter_regs (regs : bvmap 5 word) (i e c s : Z) : bvmap 5 word :=
regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 (c / 16))) 10 (Z_to_bv 64 (i + 1)))
15 (Z_to_bv 64 (e - 4 * (i + 1)))) 12 (Z_to_bv 64 (c + s)).

Ltac red_if :=
repeat match goal with
| |- context [if bv_eqb ?a ?b then ?x else ?y] =>
let v := eval vm_compute in (bv_eqb a b) in
lazymatch v with
| true => change (if bv_eqb a b then x else y) with x
| false => change (if bv_eqb a b then x else y) with y
end
end.

Lemma u64_of_Z : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

Lemma pf_iter : forall regs mem rom i e c s n,
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
(0 <= i)%Z -> (i + 1 <= n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
(0 <= c)%Z -> (0 <= s)%Z -> (c + s < 2 ^ 64)%Z ->
RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true ->
exists regs',
msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
(mkst regs' (Z_to_bv 64 (if (i + 1 <? n)%Z then p else p + 32))
(wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
/\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 e /\ getr regs' 12 = Z_to_bv 64 (c + s)
/\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
/\ getr regs' 14 = Z_to_bv 64 (c / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
/\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hok.
destruct Hp as [Hp0 Hp1].

assert (V14 : v_srli (Z_to_bv 64 c) (bv_unsigned (4 : bv 6)) = Z_to_bv 64 (c / 16)).
{ unfold v_srli. rewrite u64_of_Z by lia. change (bv_unsigned (4 : bv 6)) with 4%Z.
rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
assert (V15a : v_xori (Z_to_bv 64 i) (bv_signed (4095 : bv 12)) = Z_to_bv 64 (2 ^ 64 - 1 - i)).
{ unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (bv_signed (4095 : bv 12))) with (2 ^ 64 - 1)%Z.
rewrite AX2S.lxor_ones64 by lia. reflexivity. }
assert (V10 : v_addi (Z_to_bv 64 i) (bv_signed (1 : bv 12)) = Z_to_bv 64 (i + 1)).
{ change (bv_signed (1 : bv 12)) with 1%Z. apply v_addi_lit. }
assert (V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) (bv_unsigned (2 : bv 6)) = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)).
{ unfold v_slli. rewrite u64_of_Z by lia. change (bv_unsigned (2 : bv 6)) with 2%Z.
rewrite Z.shiftl_mul_pow2 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal. lia. }
assert (V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)) = Z_to_bv 64 (e - 4 * (i + 1))).
{ unfold v_add. rewrite u64_of_Z by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite Z.add_mod_idemp_r by lia.
replace (e + (2 ^ 66 - 4 - 4 * i))%Z with ((e - 4 * (i + 1)) + 4 * 2 ^ 64)%Z by lia.
rewrite Z_mod_plus_full. reflexivity. }
assert (Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) (bv_signed (0 : bv 12)) = Z_to_bv 64 (e - 4 * (i + 1))).
{ change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_lit. f_equal. lia. }
assert (V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s)).
{ unfold v_add. rewrite !u64_of_Z by lia. reflexivity. }
eexists. split.
- eapply mst_step; [reflexivity | eapply (step_srli segs); [exact HF0 | reflexivity | exact PD0] |].
red_if. rewrite v_addi_lit, H12, V14.
eapply mst_step; [reflexivity | eapply (step_xori segs); [exact HF1 | reflexivity | exact PD1] |].
red_if. rewrite v_addi_lit. replace (p + 4 + 4)%Z with (p + 8)%Z by lia. gr. rewrite H10, V15a.
eapply mst_step; [reflexivity | eapply (step_addi segs); [exact HF2 | reflexivity | exact PD2] |].
red_if. rewrite v_addi_lit. replace (p + 8 + 4)%Z with (p + 12)%Z by lia. gr. rewrite H10, V10.
eapply mst_step; [reflexivity | eapply (step_slli segs); [exact HF3 | reflexivity | exact PD3] |].
red_if. rewrite v_addi_lit. replace (p + 12 + 4)%Z with (p + 16)%Z by lia. gr. rewrite V15b.
eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF4 | reflexivity | exact PD4] |].
red_if. rewrite v_addi_lit. replace (p + 16 + 4)%Z with (p + 20)%Z by lia. gr. rewrite H11, V15c.
eapply mst_step; [reflexivity | eapply (step_sw_val segs); [exact HF5 | reflexivity | exact PD5 | gr; rewrite Vst; exact Hok] |].
rewrite v_addi_lit. replace (p + 20 + 4)%Z with (p + 24)%Z by lia. gr. rewrite Vst.
eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF6 | reflexivity | exact PD6] |].
red_if. rewrite v_addi_lit. replace (p + 24 + 4)%Z with (p + 28)%Z by lia. gr. rewrite H12, H21, V12.
destruct (Z.ltb (i + 1) n) eqn:Hlt.
+ eapply mst_step; [reflexivity | eapply (step_bltu_tk segs); [exact HF7 | reflexivity | exact PD7 | ] |].
{ gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
rewrite btgt_lit. change (bv_signed (8164 : bv 13)) with (-28)%Z.
replace (p + 28 + -28)%Z with p by lia. apply mst_refl.
+ eapply mst_step; [reflexivity | eapply (step_bltu_ft segs); [exact HF7 | reflexivity | exact PD7 | ] |].
{ gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
rewrite v_addi_lit. replace (p + 28 + 4)%Z with (p + 32)%Z by lia. apply mst_refl.
- gr. rewrite H11, H21, H19.
repeat (split; [reflexivity|]).
intros r Hr10 Hr12 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma pf_loop : forall k regs mem rom i e c s n,
n = (i + Z.of_nat (S k))%Z ->
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
(0 <= i)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
(0 <= c)%Z -> (0 <= s)%Z -> (c + Z.of_nat (S k) * s < 2 ^ 64)%Z ->
(forall j, (i <= j < n)%Z -> RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true) ->
exists regs',
msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
(mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (S k)) rom)
/\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
/\ getr regs' 12 = Z_to_bv 64 (c + Z.of_nat (S k) * s)
/\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
/\ getr regs' 14 = Z_to_bv 64 ((c + Z.of_nat k * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
/\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
induction k as [|k IH]; intros regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok.
-
change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
(Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
cbn [pf_mem].
split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
repeat (split; [reflexivity|]). exact Rothers.
-
rewrite Nat2Z.inj_succ in Hn, Hcs |- *. rewrite Nat2Z.inj_succ in Hcs |- *.
assert (Hks : (0 <= Z.of_nat k * s)%Z) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
(Hok i ltac:(lia))) as (regs1 & Hms1 & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
destruct (Z.ltb_spec (i + 1) n); [|lia].
destruct (IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
(i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
ltac:(rewrite Nat2Z.inj_succ; lia))
as (regs2 & Hms2 & S10 & S11 & S12 & S21 & S19 & S14 & S15 & Sothers).
{ intros j Hj. eapply store_ok_mono; [apply wbytes_grows | apply Hok; lia]. }
exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
rewrite S10, S11, S12, S21, S19, S14, S15.
split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [f_equal; f_equal; lia|]. split; [reflexivity|].
intros r A B C D. rewrite (Sothers r A B C D). apply Rothers; assumption.
Qed.

Lemma pf_wbytes_inside : forall bs m (a x : word),
(bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
(bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
cbn [wbytes length] in *.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Z.sub_diag. cbn [Z.to_nat nth].
destruct rest as [|b' rest'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in Hnw. rewrite wbytes_below.
* rewrite bv_eqb_refl. reflexivity.
* rewrite u_add1 by lia. cbn [length]. lia.
* rewrite u_add1 by lia. lia.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.

Lemma pf_wbytes_outside : forall bs m (a x : word),
(bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
wbytes m a bs x = m x.
Proof.
intros bs m a x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.

Lemma pf_mem_frame : forall k mem e c s i (a : word),
(0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
(bv_unsigned a < e - 4 * (i + Z.of_nat k) \/ e - 4 * i <= bv_unsigned a)%Z ->
pf_mem mem e c s i k a = mem a.
Proof.
induction k as [|k IH]; intros mem e c s i a Hi Hk He Ha; [reflexivity|].
cbn [pf_mem]. rewrite IH by lia.
apply pf_wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; cbn [Z.of_nat]; lia.
Qed.

Lemma word_to_le_bytes4_Z : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof. intros v. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. apply Z_to_le_bytes_wrap. cbn; lia. Qed.

Lemma pf_mem_cell : forall k mem e c s i j t,
(0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
(0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
pf_mem mem e c s i k (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t))
= Some (nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0)).
Proof.
induction k as [|k IH]; intros mem e c s i j t Hi Hk He Hj Ht; [lia|].
rewrite Nat2Z.inj_succ in *.
cbn [pf_mem].
destruct (Z.eq_dec j (Z.of_nat k)) as [->|Hne].
-
rewrite pf_mem_frame; [| lia | lia | lia | rewrite u64_of_Z by lia; lia].
rewrite pf_wbytes_inside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
rewrite word_to_le_bytes4_Z. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
- replace (e - 4 * (i + Z.succ (Z.of_nat k)) + 4 * j + Z.of_nat t)%Z
with (e - 4 * ((i + 1) + Z.of_nat k) + 4 * j + Z.of_nat t)%Z by lia.
rewrite (IH _ e (c + s)%Z s (i + 1)%Z j t) by lia.
f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Theorem popfree_loop_run : forall regs mem rom i e c s n,
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
(0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
(0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
(forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
exists regs',
msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
(mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
/\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
/\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
/\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
/\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
/\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hwr.
destruct (Z.to_nat (n - i)) as [|k] eqn:Hk; [lia|].
assert (Hkz : (Z.of_nat (S k) = n - i)%Z) by lia.
destruct (pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))
as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
{ intros j Hj. replace (e - 4 * (j + 1))%Z with (e - 4 * n + 4 * (n - j - 1))%Z by lia. apply Hwr; lia. }
exists regs'. rewrite R10, R11, R12, R21, R19, R14, R15, Hkz.
replace (Z.of_nat k) with (n - i - 1)%Z by lia.
repeat (split; [first [exact Hms | reflexivity]|]). exact Ro.
Qed.

Lemma pf_mem_wbytes : forall k mem e c s i,
(0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
pf_mem mem e c s i k = wbytes mem (Z_to_bv 64 (e - 4 * (i + Z.of_nat k))) (pf_bytes c s k).
Proof.
intros k mem e c s i Hi Hk He. apply functional_extensionality. intros a.
pose proof (u64_range a) as Ra. pose proof (pf_bytes_length c s k) as L.
destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * (i + Z.of_nat k))) as [Hlt|Hge];
[|destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * i)) as [Hlt2|Hge2]].
- rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
- set (base := (e - 4 * (i + Z.of_nat k))%Z) in *.
set (j := ((bv_unsigned a - base) / 4)%Z). set (t := Z.to_nat ((bv_unsigned a - base) mod 4)).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (Hj : (0 <= j < Z.of_nat k)%Z) by (subst j base; lia).
assert (Ht : (t < 4)%nat) by (subst t; lia).
assert (Ha : a = Z_to_bv 64 (base + 4 * j + Z.of_nat t)).
{ apply bv_eq. rewrite u64_of_Z by (subst j t base; lia). subst j t base. lia. }
rewrite Ha. subst base. rewrite (pf_mem_cell k mem e c s i j t Hi Hk He Hj Ht).
rewrite pf_wbytes_inside; rewrite ?L, ?u64_of_Z by lia; [|lia|lia].
replace (Z.to_nat (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t - (e - 4 * (i + Z.of_nat k)))) with (Z.to_nat (4 * j) + t)%nat by lia.
symmetry. f_equal. apply pf_bytes_nth; assumption.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
Qed.

Theorem popfree_spec_of_code : popfree_spec segs p.
Proof.
intros regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok.
destruct (popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
{ intros d m Hd Hdm. eapply (store_ok_sub segs mem _ _ (Z.to_nat (4 * (n - i))) m); [| exact Hok | |]; rewrite !u64_of_Z by lia; lia. }
exists regs'. rewrite (pf_mem_wbytes (Z.to_nat (n - i)) mem e c s i) in Hms by lia.
replace (i + Z.of_nat (Z.to_nat (n - i)))%Z with n in Hms by lia.
split; [exact Hms|]. split; [exact R10|]. split; [exact R12|]. split; [exact R14|]. split; [exact R15|]. exact Ro.
Qed.

End PopFreeLoop.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.Riscv Require Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Q61E.
Import Qt8n QWtD. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2S.

Definition vals_ev (vals : list word) : nat -> word :=
fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
| EExt _ _ _ x => expr_vars_lt b x
| EBlob _ _ _ _ => true
end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
match K with
| KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
| KZero a n => saddr_vars_lt b a && expr_vars_lt b n
| KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KImg _ _ => true
| KAlign e _ => expr_vars_lt b e
| KRange e _ _ => expr_vars_lt b e
| KWr a n => saddr_vars_lt b a && expr_vars_lt b n
| KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
| KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
match log with
| [] => true
| SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
end.

Definition env_agree (b : nat) (E E' : env) : Prop :=
(forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Lemma edenot_agree : forall b E E' e,
env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
try reflexivity;
try (rewrite IHe1, IHe2 by assumption; reflexivity);
try (rewrite IHe by assumption; reflexivity).
- apply Nat.ltb_lt in H. apply Hv. exact H.
- rewrite Hb. reflexivity.
Qed.

Lemma adenot_agree : forall b E E' a,
env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : forall b E E' sr regs,
env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
{ clear HR r. induction sr as [|e t IH]; intros i.
- destruct i; reflexivity.
- cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
destruct i; [exact He | apply IH; exact Ht]. }
apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.

Lemma flat_agree : forall b E E' a n,
env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
intros b E E' a n Ha H. unfold flat, estart.
rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma know_ok_agree : forall segs b E E' base kn,
env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
- constructor.
- apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
constructor; [| apply IH; assumption].
destruct Ha as [Hv Hb].
destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
[ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
| rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
| apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
| apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
unfold estart, elenZ in *;
rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
<- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
| | ].
+ apply andb_prop in HK as [H1 H2].
rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ exact Hk1.
+
apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+
apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.

Section Run.
Variable segs : list Segment.

Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
regs_ok E sr regs -> know_ok segs E base kn ->
st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
regs_ok E sr regs -> know_ok segs E base kn ->
scs_denot segs base E scs ->
exists R, regs_ok E (s_regs ss') R
/\ log_flat E (s_log ss')
/\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
(mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

Lemma eagree_env_agree : forall b E E', eagree b E E' <-> env_agree b E E'.
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.

Lemma st_okX_entry : forall E base rom pc sr kn nx regs,
regs_ok E sr regs -> know_ok segs E base kn ->
sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
forall E', eagree nx E E' -> st_ok segs E' base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
apply st_ok_entry.
- eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
- eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.

Theorem runTX_sound : forall t K fuel stops pc sr kn nx E base rom regs,
itab_sound segs t ->
regs_ok E sr regs -> know_ok segs E base kn ->
sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
let ss' := sym_execTX segs t K fuel true stops (SS pc sr [] kn nx) in
exists E' R, env_agree nx E E'
/\ (nx <= s_next ss')%nat
/\ regs_ok E' (s_regs ss') R
/\ log_flat E' (s_log ss')
/\ know_ok segs E' base (s_know ss')
/\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
(mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
/\ (forall E'', env_agree (s_next ss') E' E'' ->
st_ok segs E'' base rom ss' (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
(st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.

Lemma regs_ok_set : forall E sr R (rd : reg) v e,
regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
intros E sr R rd v e HR Hrd He.
pose proof (regs_ok_upd E sr R rd v e HR He) as H.
assert (Hb : bv_eqb rd 0 = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
rewrite Hb in H. exact H.
Qed.

End Run.

Definition sr_init : list expr :=
[ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].

Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
forall (a : word) (n : nat),
(bv_unsigned sp - K <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
store_ok segs mem a n = true.

Lemma stk_ok_vaddi : forall segs mem sp K off n,
stk_ok segs mem sp K -> (K <= bv_unsigned sp)%Z ->
(- K <= off)%Z -> (off + Z.of_nat n <= 0)%Z ->
store_ok segs mem (v_addi sp off) n = true.
Proof.
intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_lit : forall segs mem sp K z n,
stk_ok segs mem sp K ->
(bv_unsigned sp - K <= z)%Z -> (z + Z.of_nat n <= bv_unsigned sp)%Z -> (0 <= z)%Z ->
store_ok segs mem (Z_to_bv 64 z) n = true.
Proof.
intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
apply Hs; rewrite u_small by lia; lia.
Qed.

Ltac split_scs :=
lazymatch goal with
| |- scs_denot _ _ _ [] => constructor
| |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
| |- Forall _ [] => constructor
| |- Forall _ (_ :: _) => constructor; [| split_scs]
end.

Ltac ground_mod :=
repeat match goal with
| |- context [ (?a mod ?b)%Z ] =>
lazymatch a with
| context [bv_unsigned _] => fail
| _ => lazymatch b with
| context [bv_unsigned _] => fail
| _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
end
end
end.

Ltac sc_unfold :=
unfold sc_denot, flat, estart, elenZ, adenot;
cbn [a_base a_off edenot ev eb vals_ev nth];
rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

Ltac lit_u :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [bv_unsigned _] => fail
| _ => rewrite (u_small z) by (cbn; lia)
end
end.

Ltac sc_store :=
match goal with
| Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
| Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
end.

Ltac sc_auto extra :=
sc_unfold;
first [ lia
| sc_store
| extra
| match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
| idtac ].

Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
lazymatch type of HR with
| regs_ok ?E ?sr ?regs =>
lazymatch type of HK with
| know_ok _ _ ?base ?kn =>
lazymatch goal with
| |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let Hsc := fresh "Hsc" in
assert (Hsc : scs_denot segs base E scs);
[ split_scs; sc_auto extra
| destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
(eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
clear Hsc ]
end
end
end
end.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Export Q6EJ.Mq2 QG64.Mq3.
Import QWTC. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
match ws with
| [] => True
| w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
end.

Ltac code_at_vm :=
cbn [code_at Z.add Pos.add Pos.succ];
repeat split;
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Ltac zlit_at :=
repeat match goal with
| |- context [at_ ?b (?x + ?y)%Z] =>
is_Z_lit x; is_Z_lit y;
let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
end.

Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.

Ltac fold_at_vars :=
repeat match goal with
| |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
end.

Ltac vn :=
gres; rwH; imm_norm; unfold btgt;
rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
fold_at_vars; rewrite ?at_addi; zlit_at; vals_lit.
Ltac pcn := vn.

Ltac an F D :=
lazymatch type of D with
| decode_any _ = Some (Jal _ _, _) => stepj F D; vn
| _ => stepi F D; vn
end.

Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.

Ltac ab_tk F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
end;
[ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
| step_simpl; vn ].

Ltac ab_ft F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
end;
[ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
| step_simpl; vn ].

Ltac aret F D k :=
stepjr F D k ltac:(gres; rwH; reflexivity);
imm_norm;
try lazymatch goal with
| Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
end.

Ltac condz :=
rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).

Lemma v_add_at : forall (a : word) z, (0 <= z < 2 ^ 64)%Z -> v_add a (Z_to_bv 64 z) = at_ a z.
Proof. intros a z Hz. unfold v_add, at_. rewrite (u_Z2bv z) by lia. reflexivity. Qed.

Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
cHn : (0 <= n)%Z;
cHlen : length bs = Z.to_nat n;
cHsrc : rdn segs mem0 src (length bs) = Some bs;
cHdst : store_ok segs mem0 dst (length bs) = true;
cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MEMK.
Variable segs : list Segment.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Hypothesis HOK : cpyH segs mem0 dst src n bs.

Let Hn := cHn _ _ _ _ _ _ HOK.
Let Hlen := cHlen _ _ _ _ _ _ HOK.
Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
Let Hdst := cHdst _ _ _ _ _ _ HOK.
Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
Let Hnws := cHnws _ _ _ _ _ _ HOK.
Let Hnwd := cHnwd _ _ _ _ _ _ HOK.

Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).

Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

Lemma memk_n : memk n = wbytes mem0 dst bs.
Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

Lemma rd_src1 : forall k j,
(0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
rdn segs (memk k) (at_ src j) 1 = Some [b_ j].
Proof.
intros k j Hk Hj H1. unfold memk, b_.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite rdn_wbytes_out.
- replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
rewrite (rdn_sub segs mem0 (length bs) src bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
- rewrite length_firstn, Hlen, at_u; cbn; lia.
- rewrite at_u; cbn; lia.
- rewrite length_firstn, Hlen. lia.
Qed.

Lemma wr_dst : forall k j m,
(0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
store_ok segs (memk k) (at_ dst j) m = true.
Proof.
intros k j m Hj Hm. unfold memk.
apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?Hlen; lia.
Qed.

Lemma memk_extend1 : forall k,
(0 <= k)%Z -> (k + 1 <= n)%Z ->
wbytes (memk k) (at_ dst k) [b_ k] = memk (k + 1).
Proof.
intros k Hk H1. unfold memk, b_.
replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
rewrite <- sub_nth by (rewrite Hlen; lia).
rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
Qed.

Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (b_ j)))) (v_addi pc 4) (memk k) rom).
Proof.
intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
Qed.

Lemma mc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ k ->
(0 <= k)%Z -> (k + 1 <= n)%Z ->
RiscvSemantics.step segs (mkst regs pc (memk k) rom) =
MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
Proof.
intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
rewrite <- (memk_extend1 k) by lia.
eapply QHup.Mq1.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
- rewrite Hrs1, at_addi, Hk. reflexivity.
- apply wr_dst; cbn; lia.
Qed.

End MEMK.

Lemma sb_val_b : forall bs j, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (b_ bs j)))) = b_ bs j.
Proof.
intros bs j. pose proof (u8_range (b_ bs j)). rewrite u_Z2bv by lia. apply Z_to_bv_bv_unsigned.
Qed.

Section MSETK.
Variable segs : list Segment.
Variable mem0 : word -> option byte.
Variable s : word.
Variable n : Z.
Variable b : byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.

Definition msetk (k : Z) : word -> option byte := wbytes mem0 s (repeat b (Z.to_nat k)).

Lemma wr_s : forall k j m,
(0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
store_ok segs (msetk k) (at_ s j) m = true.
Proof.
intros k j m Hj Hm. unfold msetk.
apply (store_ok_at segs mem0 s (Z.to_nat n)); try assumption; lia.
Qed.

Lemma msetk_extend : forall k m,
(0 <= k)%Z ->
wbytes (msetk k) (at_ s k) (repeat b m) = msetk (k + Z.of_nat m).
Proof.
intros k m Hk. unfold msetk.
replace (Z.to_nat (k + Z.of_nat m)) with (Z.to_nat k + m)%nat by lia.
rewrite repeat_app, wbytes_app, repeat_length. f_equal. f_equal. lia.
Qed.

Lemma msetk_extend1 : forall k, (0 <= k)%Z -> wbytes (msetk k) (at_ s k) [b] = msetk (k + 1).
Proof. intros k Hk. apply (msetk_extend k 1). exact Hk. Qed.
End MSETK.

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
Z.land (a * 2 ^ k) b = 0%Z.
Proof.
intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hl|Hh].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
intros a b k Ha Hk Hb.
rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma v_slli_mul : forall (x : word) k, (0 <= k)%Z -> v_slli x k = Z_to_bv 64 (bv_unsigned x * 2 ^ k).
Proof. intros x k Hk. unfold v_slli. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_or_shl : forall (x : word) a k, (0 <= a)%Z -> (0 <= k)%Z -> (a * 2 ^ k < 2 ^ 64)%Z ->
(bv_unsigned x < 2 ^ k)%Z ->
v_or (Z_to_bv 64 (a * 2 ^ k)) x = Z_to_bv 64 (a * 2 ^ k + bv_unsigned x).
Proof.
intros x a k Ha Hk Hak Hx. pose proof (u64_range x). unfold v_or.
pose proof (Z.pow_nonneg 2 k ltac:(lia)).
rewrite u_Z2bv by nia. rewrite lor_shl_disjoint by lia. reflexivity.
Qed.

Definition M8 : Z := 72340172838076673.

Lemma M8_digit : forall c k, (0 <= c < 256)%Z ->
(k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z ->
(Z.shiftr (c * M8) (8 * k) mod 256 = c)%Z.
Proof.
intros c k Hc Hk. unfold M8. rewrite Z.shiftr_div_pow2 by lia.
assert (G : forall Mhi Mlo B, (0 < B)%Z -> (Mhi * B + Mlo = 72340172838076673)%Z -> (0 <= Mlo)%Z ->
(255 * Mlo < B)%Z -> (Mhi mod 256 = 1)%Z ->
(c * 72340172838076673 / B mod 256 = c)%Z).
{ intros Mhi Mlo B HB HM Hlo Hlt Hm1.
replace (c * 72340172838076673)%Z with (c * Mhi * B + c * Mlo)%Z by nia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small (c * Mlo) B) by nia.
rewrite Z.add_0_r, <- Zmult_mod_idemp_r, Hm1, Z.mul_1_r. apply Z.mod_small. lia. }
destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
- apply (G 72340172838076673 0 1)%Z; reflexivity || lia.
- apply (G 282578800148737 1 (2^8))%Z; try reflexivity; lia.
- apply (G 1103823438081 257 (2^16))%Z; try reflexivity; lia.
- apply (G 4311810305 65793 (2^24))%Z; try reflexivity; lia.
- apply (G 16843009 16843009 (2^32))%Z; try reflexivity; lia.
- apply (G 65793 4311810305 (2^40))%Z; try reflexivity; lia.
- apply (G 257 1103823438081 (2^48))%Z; try reflexivity; lia.
- apply (G 1 282578800148737 (2^56))%Z; try reflexivity; lia.
Qed.

Lemma byte_eq_mod : forall x y, (x mod 256 = y mod 256)%Z -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma rep8_bytes : forall c, (0 <= c < 256)%Z ->
word_to_le_bytes 8 (Z_to_bv 64 (c * M8)) = repeat (Z_to_bv 8 c) 8.
Proof.
intros c Hc. unfold word_to_le_bytes. rewrite u_Z2bv by (unfold M8; lia).
cbn [Z_to_le_bytes repeat]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
pose proof (M8_digit c) as D.
repeat match goal with
| |- (_ :: _) = (_ :: _) => f_equal
| |- Z_to_bv 8 _ = Z_to_bv 8 _ => apply byte_eq_mod; rewrite (Z.mod_small c 256) by lia
| |- [] = [] => reflexivity
end.
- rewrite <- (D 0%Z) at 2 by lia. rewrite Z.shiftr_0_r || (cbn [Z.mul]; rewrite Z.shiftr_0_r). reflexivity.
- apply (D 1%Z); lia.
- apply (D 2%Z); lia.
- apply (D 3%Z); lia.
- apply (D 4%Z); lia.
- apply (D 5%Z); lia.
- apply (D 6%Z); lia.
- apply (D 7%Z); lia.
Qed.

Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_or (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Ltac av_or F D vv tac :=
chain_step;
[ reflexivity
| eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
| step_simpl ]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWXq.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ki. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBCP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBCP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ.
Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.

Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
vm_add_lazy a n (mmap_model a n m).

Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.

Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Section WithSegs.
Variable segs : list Segment.

Inductive msteps_acc
: machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms
= MachineOk (@mkAccessReport machine_state ms1 ranges) ->
msteps_acc ms1 ms2 accs ->
msteps_acc ms ms2 (ranges ++ accs).

End WithSegs.

End WithFP1.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkst];
rewrite Hfetch;
cbv beta iota;
unfold RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.

Section AsanInitReal.
Variable segs : list Segment.

Variables (ms1 : machine_state) (model : Model) (x8a : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc1 : ms_svc_pending ms1 = Some x8a.
Hypothesis Hno1 : bv_unsigned x8a = 222%Z.
Hypothesis Hargs1 : mmap_args_ok_noreserve ms1.

Let nZ1 : Z := page_round_up_Z (bv_unsigned (ms_gpr ms1 1)).
Let n1 : word := page_round_up (ms_gpr ms1 1).
Let model1 (a1 : word) : Model := mmap_model_noreserve a1 n1 model.
Let post1 (a1 : word) : machine_state :=
advance_past_svc (apply_effect ms1 (mkEffect a1 [] [(a1, n1)])).

Hypothesis Hrefuse1 : forall e, In e mmap_errnos ->
to_spin segs (advance_past_svc (set_gpr0 ms1 (errno_ret e))) model.
Hypothesis Hex1 : exists a, grant_ok_nr (ms_gpr ms1 0) model a nZ1 = true.

Variable ms2 : word -> machine_state.
Variable accs1 : word -> list (word * nat).
Hypothesis Hwalk1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
msteps_acc segs (post1 a1) (ms2 a1) (accs1 a1).
Hypothesis Hout1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
accesses_outside_lazy (accs1 a1) (m_vm_lazy (model1 a1)).

Variable x8b : word.
Hypothesis Hno2 : bv_unsigned x8b = 222%Z.
Hypothesis Hsvc2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
ms_svc_pending (ms2 a1) = Some x8b.
Hypothesis Hargs2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
mmap_args_ok (ms2 a1).

Let nZ2 (a1 : word) : Z := page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1)).
Let n2 (a1 : word) : word := page_round_up (ms_gpr (ms2 a1) 1).
Let model2 (a1 a2 : word) : Model := mmap_model a2 (n2 a1) (model1 a1).
Let post2 (a1 a2 : word) : machine_state :=
advance_past_svc (apply_effect (ms2 a1) (mkEffect a2 [] [(a2, n2 a1)])).

Hypothesis Hrefuse2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
forall e, In e mmap_errnos ->
to_spin segs (advance_past_svc (set_gpr0 (ms2 a1) (errno_ret e))) (model1 a1).
Hypothesis Hex2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
exists a2, grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true.

Variable ms3 : word -> word -> machine_state.
Variable accs2 : word -> word -> list (word * nat).
Hypothesis Hwalk2 : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
msteps_acc segs (post2 a1 a2) (ms3 a1 a2) (accs2 a1 a2).
Hypothesis Hout2 : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
accesses_outside_lazy (accs2 a1 a2) (m_vm_lazy (model2 a1 a2)).

Variable buf : list byte.
Hypothesis Hbufnb : (1 <= length buf)%nat.
Hypothesis Hbufmod : buf_modeled buf.
Variable x8c : word.
Hypothesis Hno3 : bv_unsigned x8c = 64%Z.
Hypothesis Hw_svc : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
ms_svc_pending (ms3 a1 a2) = Some x8c.
Hypothesis Hw_fd1 : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
ms_gpr (ms3 a1 a2) 0 = Z_to_bv 64 1.
Hypothesis Hw_read : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
ms_read_bytes (ms3 a1 a2) (ms_gpr (ms3 a1 a2) 1) (ms_gpr (ms3 a1 a2) 2) = Some buf.
Hypothesis Hw_out : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
accesses_outside_lazy [(ms_gpr (ms3 a1 a2) 1, length buf)]
(m_vm_lazy (model2 a1 a2)).

Variable msE : word -> word -> nat -> machine_state.
Variable accs3 : word -> word -> nat -> list (word * nat).
Hypothesis Hwalk3 : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
msteps_acc segs
(advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (firstn n buf))))
(msE a1 a2 n) (accs3 a1 a2 n).
Hypothesis Hout3 : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
accesses_outside_lazy (accs3 a1 a2 n) (m_vm_lazy (model2 a1 a2)).

Variables (x8d : word) (cs : word).
Hypothesis HE_no : is_exit_no x8d.
Hypothesis HE_svc : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
ms_svc_pending (msE a1 a2 n) = Some x8d.
Hypothesis HE_code : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
bv_and (ms_gpr (msE a1 a2 n) 0) (Z_to_bv 64 255) = cs.

End AsanInitReal.
End WithFP2.
