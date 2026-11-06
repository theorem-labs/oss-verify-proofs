From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02 YP03 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Module PStrFun := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.

(* The two byte loops strndup calls on plugin-hostd/fuzz_command's memory-checking image, walked instruction by
   instruction. internal_strnlen 0x69d74 (12 instructions) returns the index of the first zero byte below n, or n;
   it writes a0, a2, a3 only. __sanitizer_internal_memcpy 0x69940 (9 instructions) copies a2 bytes from a1 to a0
   one at a time and returns a0; it writes a1..a4 only. *)
Definition A_ISN : Z := 0x69d74.
Definition A_IMC : Z := 0x69940.
Definition tbl_imc : ctable := Eval vm_compute in build_table tfibsegs A_IMC 9 TEmpty.
Lemma tbl_imc_eq : tbl_imc = build_table tfibsegs A_IMC 9 TEmpty. Proof. vm_cast_no_check (eq_refl tbl_imc). Qed.
Lemma tbl_imc_ok : table_ok tfibsegs tbl_imc.
Proof. rewrite tbl_imc_eq. apply build_table_ok; [unfold A_IMC; lia | exact (table_ok_empty tfibsegs)]. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_of_tbl : forall t, table_ok tfibsegs t -> forall (p : word) (w : bv 32),
clookup t (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof.
intros t Ht p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply Ht. exact H.
Qed.
End a.
Ltac ftac_i := apply (fetch_of_tbl tbl_icpt tbl_icpt_ok); vm_compute; reflexivity.
Ltac ftac_m := apply (fetch_of_tbl tbl_imc tbl_imc_ok); vm_compute; reflexivity.
Ltac stepLB F0 D0 RD :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D0
| gr; rwH; imm_norm; rewrite ?v_addi_lit; first [apply RD; lia | rewrite Z.add_0_r; apply RD; lia] ]
| step_simpl ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma N_00 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x0)) = Some (0x02058463%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_00 : decode_any (0x02058463%bv : bv 32) = Some (Branch BC_EQ 11 0 40, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_04 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x4)) = Some (0x00050613%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_04 : decode_any (0x00050613%bv : bv 32) = Some (OpImm ALU_ADD 12 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_08 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x8)) = Some (0x00000513%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_08 : decode_any (0x00000513%bv : bv 32) = Some (OpImm ALU_ADD 10 0 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_0c : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0xc)) = Some (0x00a606b3%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_0c : decode_any (0x00a606b3%bv : bv 32) = Some (Op ALU_ADD 13 12 10, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_10 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x10)) = Some (0x0006c683%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_10 : decode_any (0x0006c683%bv : bv 32) = Some (Load SZ1 false 13 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_14 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x14)) = Some (0x00068863%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_14 : decode_any (0x00068863%bv : bv 32) = Some (Branch BC_EQ 13 0 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_18 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x18)) = Some (0x00150513%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_18 : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_1c : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x1c)) = Some (0xfea598e3%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_1c : decode_any (0xfea598e3%bv : bv 32) = Some (Branch BC_NE 11 10 8176, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_20 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x20)) = Some (0x00058513%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_20 : decode_any (0x00058513%bv : bv 32) = Some (OpImm ALU_ADD 10 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_24 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x24)) = Some (0x00008067%bv : bv 32). Proof. ftac_i. Qed.
Lemma DN_24 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma N_28 : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x28)) = Some (0x00000513%bv : bv 32). Proof. ftac_i. Qed.
Lemma N_2c : fetch_word tfibsegs (Z_to_bv 64 (A_ISN + 0x2c)) = Some (0x00008067%bv : bv 32). Proof. ftac_i. Qed.
Lemma M_00 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x0)) = Some (0x02060063%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_00 : decode_any (0x02060063%bv : bv 32) = Some (Branch BC_EQ 12 0 32, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_04 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x4)) = Some (0x00c50633%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_04 : decode_any (0x00c50633%bv : bv 32) = Some (Op ALU_ADD 12 10 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_08 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x8)) = Some (0x00050693%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_08 : decode_any (0x00050693%bv : bv 32) = Some (OpImm ALU_ADD 13 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_0c : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0xc)) = Some (0x0005c703%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_0c : decode_any (0x0005c703%bv : bv 32) = Some (Load SZ1 false 14 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_10 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x10)) = Some (0x00e68023%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_10 : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_14 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x14)) = Some (0x00168693%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_14 : decode_any (0x00168693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_18 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x18)) = Some (0x00158593%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_18 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_1c : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x1c)) = Some (0xfec698e3%bv : bv 32). Proof. ftac_m. Qed.
Lemma DM_1c : decode_any (0xfec698e3%bv : bv 32) = Some (Branch BC_NE 13 12 8176, 4%Z). Proof. vm_refl_bv. Qed.
Lemma M_20 : fetch_word tfibsegs (Z_to_bv 64 (A_IMC + 0x20)) = Some (0x00008067%bv : bv 32). Proof. ftac_m. Qed.

(* The value internal_strnlen returns, read off strnlen_res and memchr_ok. *)
Lemma strnlen_res_facts : forall A n buf, 0 <= n -> PStrFun.memchr_ok A 0 n buf ->
let k := PStrFun.strnlen_res n buf in
0 <= k <= n /\ k <= Z.of_nat (length buf) /\
(forall j, (j < Z.to_nat k)%nat -> bv_unsigned (nth j buf NUL) <> 0) /\
(k < n -> k < Z.of_nat (length buf) /\ bv_unsigned (nth (Z.to_nat k) buf NUL) = 0).
Proof.
intros A n buf Hn Hok k. subst k. unfold PStrFun.strnlen_res. unfold PStrFun.memchr_ok in Hok.
destruct (PStrFun.find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:E.
- destruct (PStrFun.find_byte_Some _ _ _ E) as (Hl & (b & Hb & Hb0) & Hmin).
rewrite length_firstn in Hl.
assert (Hnth : forall j, (j < Z.to_nat n)%nat -> (j < length buf)%nat -> nth_error (firstn (Z.to_nat n) buf) j = Some (nth j buf NUL)).
{ intros j Hj1 Hj2. rewrite nth_error_firstn. destruct (Nat.ltb_spec j (Z.to_nat n)) as [_|]; [|lia].
apply nth_error_nth'. exact Hj2. }
split; [lia|]. split; [lia|]. split.
+ intros j Hj. rewrite Nat2Z.id in Hj. apply (Hmin j); [exact Hj|]. apply Hnth; lia.
+ intros _. rewrite Nat2Z.id. split; [lia|]. rewrite (Hnth i) in Hb by lia. injection Hb as ->. exact Hb0.
- split; [lia|]. split; [exact Hok|]. split.
+ intros j Hj. apply (PStrFun.find_byte_None _ _ E j). rewrite nth_error_firstn.
destruct (Nat.ltb_spec j (Z.to_nat n)) as [_|]; [|lia]. apply nth_error_nth'. lia.
+ intros H. lia.
Qed.

(* internal_strnlen. *)
Section c.
Variables (buf : list byte) (p : word) (n : Z).
Variables mem rom : word -> option byte.
Definition XN : Z := bv_unsigned p.
Definition KN : Z := PStrFun.strnlen_res n buf.
Hypothesis Hn : 0 <= n < 2 ^ 63.
Hypothesis Hok : PStrFun.memchr_ok XN 0 n buf.
Hypothesis Hrd : forall j, (j < length buf)%nat -> (j <= Z.to_nat KN)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (XN + Z.of_nat j)) 1 = Some [nth j buf NUL].
Definition keepN (x : reg) : Prop := x <> 10%bv /\ x <> 12%bv /\ x <> 13%bv.
Definition finN (regs : bvmap 5 word) (pc : word) : Prop :=
exists regs',
msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 KN
/\ forall x, keepN x -> getr regs' x = getr regs x.
Lemma keepN_1 : keepN 1.
Proof. unfold keepN. repeat split; reg_neq_tac. Qed.
Lemma finN_steps : forall regs pc regs2 pc2,
msteps tfibsegs (mkst regs pc mem rom) (mkst regs2 pc2 mem rom) ->
(forall x, keepN x -> getr regs2 x = getr regs x) ->
finN regs2 pc2 -> finN regs pc.
Proof.
intros regs pc regs2 pc2 Hms Hfr (regs' & Hms' & Ha & Hfr').
exists regs'. split; [|split; [exact Ha|]].
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keepN_1). exact Hms'.
- intros x Hx. rewrite (Hfr' x Hx). apply Hfr. exact Hx.
Qed.
Lemma finN_pc : forall regs (pc pc' : word), bv_unsigned pc = bv_unsigned pc' -> finN regs pc' -> finN regs pc.
Proof. intros regs pc pc' H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frameN := let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold keepN in Hx; destruct Hx as (?&?&?); rewrite ?getr_other by assumption; reflexivity.
Ltac svN F D vv := let F' := litF F in stepiv F' D vv val.
Lemma KN_facts : 0 <= KN <= n /\ KN <= Z.of_nat (length buf) /\
(forall j, (j < Z.to_nat KN)%nat -> bv_unsigned (nth j buf NUL) <> 0) /\
(KN < n -> KN < Z.of_nat (length buf) /\ bv_unsigned (nth (Z.to_nat KN) buf NUL) = 0).
Proof. exact (strnlen_res_facts XN n buf ltac:(lia) Hok). Qed.
Lemma XN_range : 0 <= XN < 2 ^ 64.
Proof. unfold XN. pose proof (u64_range p). lia. Qed.
Lemma isn_loop : forall j i regs,
(i + j = Z.to_nat KN + 1)%nat -> (i <= Z.to_nat KN)%nat -> Z.of_nat i < n ->
getr regs 12 = Z_to_bv 64 XN ->
getr regs 10 = Z_to_bv 64 (Z.of_nat i) ->
getr regs 11 = Z_to_bv 64 n ->
finN regs (Z_to_bv 64 (A_ISN + 0xc)).
Proof.
pose proof KN_facts as (K0 & Kl & Knz & Kz). pose proof XN_range as XR.
induction j as [|j IH]; intros i regs Hij Hik Hin H12 H10 H11; [lia|].
assert (Hil : (i < length buf)%nat).
{ destruct (Z.eq_dec (Z.of_nat i) KN) as [E|E]; [|lia]. assert (KN < n) by lia. destruct (Kz ltac:(lia)). lia. }
assert (RD : forall z, z = XN + Z.of_nat i -> rdn tfibsegs mem (Z_to_bv 64 z) 1 = Some [nth i buf NUL]).
{ intros z ->. apply Hrd; [exact Hil | exact Hik]. }
pose proof (bv_unsigned_in_range 8 (nth i buf NUL)) as Ha.
unfold bv_modulus in Ha. change (2 ^ Z.of_N 8) with 256 in Ha.
destruct (Z.eq_dec (Z.of_nat i) KN) as [Hi|Hi].
- assert (Hb0 : bv_unsigned (nth i buf NUL) = 0).
{ replace i with (Z.to_nat KN) by lia. apply Kz. lia. }
eapply finN_steps.
+ norm_pc.
svN N_0c DN_0c (Z_to_bv 64 (XN + Z.of_nat i)).
stepLB N_10 DN_10 RD.
stepbt N_14 DN_14.
stepret N_24 DN_24.
apply mst_refl.
+ frameN.
+ eexists. split; [gr; apply mst_refl|]. split; [gr; rewrite H10, Hi; reflexivity|]. frameN.
- assert (Hlt : (i < Z.to_nat KN)%nat) by lia.
assert (Hb1 : bv_unsigned (nth i buf NUL) <> 0) by (apply Knz; exact Hlt).
destruct (Z.eq_dec (Z.of_nat (S i)) n) as [Hsn|Hsn].
+ assert (HKn : KN = n) by lia.
eapply finN_steps.
* norm_pc.
svN N_0c DN_0c (Z_to_bv 64 (XN + Z.of_nat i)).
stepLB N_10 DN_10 RD.
stepbf N_14 DN_14.
svN N_18 DN_18 (Z_to_bv 64 (Z.of_nat (S i))).
stepbf N_1c DN_1c.
svN N_20 DN_20 (Z_to_bv 64 n).
stepret N_24 DN_24.
apply mst_refl.
* frameN.
* eexists. split; [gr; apply mst_refl|]. split; [gr; rewrite HKn; reflexivity|]. frameN.
+ eapply finN_steps.
* norm_pc.
svN N_0c DN_0c (Z_to_bv 64 (XN + Z.of_nat i)).
stepLB N_10 DN_10 RD.
stepbf N_14 DN_14.
svN N_18 DN_18 (Z_to_bv 64 (Z.of_nat (S i))).
stepbt N_1c DN_1c.
apply mst_refl.
* frameN.
* eapply finN_pc; [|apply (IH (S i))]; [vm_compute; reflexivity | lia | lia | lia | gr; assumption | gr; reflexivity | gr; assumption].
Qed.
Lemma isn_entry : forall regs,
getr regs 10 = Z_to_bv 64 XN -> getr regs 11 = Z_to_bv 64 n ->
finN regs (Z_to_bv 64 (A_ISN + 0x0)).
Proof.
intros regs H10 H11. pose proof KN_facts as (K0 & Kl & Knz & Kz). pose proof XN_range as XR.
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
- assert (HK0 : KN = 0) by lia.
eapply finN_steps.
+ norm_pc.
stepbt N_00 DN_00.
svN N_28 DN_08 (Z_to_bv 64 0).
stepret N_2c DN_24.
apply mst_refl.
+ frameN.
+ eexists. split; [gr; apply mst_refl|]. split; [gr; rewrite HK0; reflexivity|]. frameN.
- eapply finN_steps.
+ norm_pc.
stepbf N_00 DN_00.
svN N_04 DN_04 (Z_to_bv 64 XN).
svN N_08 DN_08 (Z_to_bv 64 0).
apply mst_refl.
+ frameN.
+ eapply finN_pc; [|apply (isn_loop (Z.to_nat KN + 1) 0%nat)]; [vm_compute; reflexivity | lia | lia | lia | gr; reflexivity | gr; reflexivity | gr; assumption].
Qed.
End c.

(* __sanitizer_internal_memcpy. *)
Lemma firstn_S_nth : forall {A} (l : list A) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
intros A l. induction l as [|x t IH]; intros i d Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. cbn in Hi. lia.
Qed.
Lemma addr_nat : forall (a : word) i, bv_unsigned a + Z.of_nat i < 2 ^ 64 ->
(a + nat_to_word i)%bv = Z_to_bv 64 (bv_unsigned a + Z.of_nat i).
Proof.
intros a i H. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
pose proof (u64_range a). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (Z.of_nat i)) by lia. reflexivity.
Qed.
Section m.
Variables (src : list byte) (pd ps : word).
Variables mem rom : word -> option byte.
Definition DM : Z := bv_unsigned pd.
Definition XM : Z := bv_unsigned ps.
Definition LM : Z := Z.of_nat (length src).
Hypothesis Hrd : forall j, (j < length src)%nat -> rdn tfibsegs mem (Z_to_bv 64 (XM + Z.of_nat j)) 1 = Some [nth j src NUL].
Hypothesis Hpr : forall i, 0 <= i < LM -> present mem (DM + i).
Hypothesis Hdj : DM + LM <= XM \/ XM + LM <= DM.
Hypothesis HD : DM + LM < 2 ^ 64.
Hypothesis HX : XM + LM < 2 ^ 64.
Definition keepM (x : reg) : Prop := x <> 11%bv /\ x <> 12%bv /\ x <> 13%bv /\ x <> 14%bv.
Definition finM (regs : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
exists regs',
msteps tfibsegs (mkst regs pc m rom) (mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem pd src) rom)
/\ forall x, keepM x -> getr regs' x = getr regs x.
Lemma keepM_1 : keepM 1.
Proof. unfold keepM. repeat split; reg_neq_tac. Qed.
Lemma finM_steps : forall regs pc m regs2 pc2 m2,
msteps tfibsegs (mkst regs pc m rom) (mkst regs2 pc2 m2 rom) ->
(forall x, keepM x -> getr regs2 x = getr regs x) ->
finM regs2 pc2 m2 -> finM regs pc m.
Proof.
intros regs pc m regs2 pc2 m2 Hms Hfr (regs' & Hms' & Hfr').
exists regs'. split.
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keepM_1). exact Hms'.
- intros x Hx. rewrite (Hfr' x Hx). apply Hfr. exact Hx.
Qed.
Lemma finM_pc : forall regs (pc pc' : word) m, bv_unsigned pc = bv_unsigned pc' -> finM regs pc' m -> finM regs pc m.
Proof. intros regs pc pc' m H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frameM := let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold keepM in Hx; destruct Hx as (?&?&?&?); rewrite ?getr_other by assumption; reflexivity.
Ltac svM F D vv := let F' := litF F in stepiv F' D vv val.
Ltac stepSB F0 D0 aa Hst := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sb_l with (a := aa); [ exact F | reflexivity | exact D0 | val | gr; apply sb_lbu | exact Hst ]
| step_simpl ].
Lemma DM_range : 0 <= DM < 2 ^ 64. Proof. unfold DM. pose proof (u64_range pd). lia. Qed.
Lemma XM_range : 0 <= XM < 2 ^ 64. Proof. unfold XM. pose proof (u64_range ps). lia. Qed.
Lemma mem_i_read : forall i j, (i <= length src)%nat -> (j < length src)%nat ->
rdn tfibsegs (wbytes mem pd (firstn i src)) (Z_to_bv 64 (XM + Z.of_nat j)) 1 = Some [nth j src NUL].
Proof.
intros i j Hi Hj. pose proof DM_range. pose proof XM_range. unfold LM in *.
rewrite rdn_wbytes_out.
all: try (apply Hrd; exact Hj).
all: rewrite ?length_firstn, ?unsigned_lit_small by lia; fold DM; cbn [Z.of_nat]; lia.
Qed.
Lemma mem_i_store : forall i, (i < length src)%nat ->
RiscvSemantics.store_ok tfibsegs (wbytes mem pd (firstn i src)) (Z_to_bv 64 (DM + Z.of_nat i)) 1%nat = true.
Proof.
intros i Hi. pose proof DM_range. unfold LM in *.
destruct (Hpr (Z.of_nat i) ltac:(lia)) as [b Hb].
assert (E : wbytes mem pd (firstn i src) (Z_to_bv 64 (DM + Z.of_nat i)) = Some b).
{ rewrite wbytes_above; [exact Hb|]. rewrite length_firstn, unsigned_lit_small by lia. fold DM. lia. }
cbn [RiscvSemantics.store_ok]. unfold wview. rewrite E. reflexivity.
Qed.
Lemma mem_i_next : forall i, (i < length src)%nat ->
wbytes (wbytes mem pd (firstn i src)) (Z_to_bv 64 (DM + Z.of_nat i)) [nth i src NUL] = wbytes mem pd (firstn (S i) src).
Proof.
intros i Hi. pose proof DM_range. unfold LM in *.
rewrite (firstn_S_nth src i NUL Hi), wbytes_app, length_firstn.
replace (Init.Nat.min i (length src)) with i by lia.
rewrite addr_nat by (fold DM; lia). reflexivity.
Qed.
Lemma imc_loop : forall j i regs,
(i + j = length src)%nat -> (i < length src)%nat ->
getr regs 13 = Z_to_bv 64 (DM + Z.of_nat i) ->
getr regs 11 = Z_to_bv 64 (XM + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 (DM + LM) ->
finM regs (Z_to_bv 64 (A_IMC + 0xc)) (wbytes mem pd (firstn i src)).
Proof.
pose proof DM_range as DR. pose proof XM_range as XR. unfold LM in *.
induction j as [|j IH]; intros i regs Hij Hi H13 H11 H12; [lia|].
assert (RD : forall z, z = XM + Z.of_nat i -> rdn tfibsegs (wbytes mem pd (firstn i src)) (Z_to_bv 64 z) 1 = Some [nth i src NUL]).
{ intros z ->. apply mem_i_read; lia. }
pose proof (bv_unsigned_in_range 8 (nth i src NUL)) as Ha.
unfold bv_modulus in Ha. change (2 ^ Z.of_N 8) with 256 in Ha.
pose proof (mem_i_store i Hi) as Hst. pose proof (mem_i_next i Hi) as Hnx.
destruct (Nat.eq_dec (S i) (length src)) as [Hs|Hs].
- eapply finM_steps.
+ norm_pc.
stepLB M_0c DM_0c RD.
stepSB M_10 DM_10 (DM + Z.of_nat i) Hst.
rewrite Hnx.
svM M_14 DM_14 (Z_to_bv 64 (DM + Z.of_nat (S i))).
svM M_18 DM_18 (Z_to_bv 64 (XM + Z.of_nat (S i))).
stepbf M_1c DM_1c.
stepret M_20 DN_24.
apply mst_refl.
+ frameM.
+ rewrite Hs, firstn_all. eexists. split; [gr; apply mst_refl|]. frameM.
- eapply finM_steps.
+ norm_pc.
stepLB M_0c DM_0c RD.
stepSB M_10 DM_10 (DM + Z.of_nat i) Hst.
rewrite Hnx.
svM M_14 DM_14 (Z_to_bv 64 (DM + Z.of_nat (S i))).
svM M_18 DM_18 (Z_to_bv 64 (XM + Z.of_nat (S i))).
stepbt M_1c DM_1c.
apply mst_refl.
+ frameM.
+ eapply finM_pc; [|apply (IH (S i))]; [vm_compute; reflexivity | lia | lia | gr; first [reflexivity | assumption] ..].
Qed.
Lemma imc_entry : forall regs,
getr regs 10 = Z_to_bv 64 DM -> getr regs 11 = Z_to_bv 64 XM -> getr regs 12 = Z_to_bv 64 LM ->
finM regs (Z_to_bv 64 (A_IMC + 0x0)) mem.
Proof.
intros regs H10 H11 H12. pose proof DM_range as DR. pose proof XM_range as XR. unfold LM in *.
destruct (Nat.eq_dec (length src) 0) as [H0|H0].
- eapply finM_steps.
+ norm_pc.
stepbt M_00 DM_00.
stepret M_20 DN_24.
apply mst_refl.
+ frameM.
+ assert (Hs0 : src = []) by (destruct src as [|b0 t]; [reflexivity | cbn in H0; lia]).
unfold finM. rewrite Hs0. cbn [wbytes]. eexists. split; [gr; apply mst_refl|]. frameM.
- eapply finM_steps.
+ norm_pc.
stepbf M_00 DM_00.
svM M_04 DM_04 (Z_to_bv 64 (DM + Z.of_nat (length src))).
svM M_08 DM_08 (Z_to_bv 64 DM).
apply mst_refl.
+ frameM.
+ eapply finM_pc; [|apply (imc_loop (length src) 0%nat)]; [vm_compute; reflexivity | lia | lia | gr; rwH; first [reflexivity | f_equal; lia] ..].
Qed.
End m.

Theorem cmd_istrnlen : forall (buf : list byte) (p : word) (n : Z) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = p -> getr regs 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 63 ->
PStrFun.memchr_ok (bv_unsigned p) 0 n buf ->
(forall j, (j < length buf)%nat -> (j <= Z.to_nat (PStrFun.strnlen_res n buf))%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j buf NUL]) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 A_ISN) mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (PStrFun.strnlen_res n buf)
/\ (forall x : reg, x <> 10%bv -> x <> 12%bv -> x <> 13%bv -> getr regs' x = getr regs x).
Proof.
intros buf p n mem rom regs H10 H11 Hn Hok Hrd.
assert (H10' : getr regs 10 = Z_to_bv 64 (XN p)) by (rewrite H10; unfold XN; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (isn_entry buf p n mem rom Hn Hok Hrd regs H10' H11) as (regs' & Hms & Ha0 & Hfr).
exists regs'. split; [|split; [exact Ha0|]].
- change (Z_to_bv 64 A_ISN) with (Z_to_bv 64 (A_ISN + 0x0)). exact Hms.
- intros. apply Hfr. unfold keepN. repeat split; assumption.
Qed.
Theorem cmd_imemcpy : forall (src : list byte) (pd ps : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = pd -> getr regs 11 = ps -> getr regs 12 = Z_to_bv 64 (Z.of_nat (length src)) ->
(forall j, (j < length src)%nat -> rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned ps + Z.of_nat j)) 1 = Some [nth j src NUL]) ->
(forall i, 0 <= i < Z.of_nat (length src) -> present mem (bv_unsigned pd + i)) ->
(bv_unsigned pd + Z.of_nat (length src) <= bv_unsigned ps \/ bv_unsigned ps + Z.of_nat (length src) <= bv_unsigned pd) ->
bv_unsigned pd + Z.of_nat (length src) < 2 ^ 64 -> bv_unsigned ps + Z.of_nat (length src) < 2 ^ 64 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 A_IMC) mem rom) (mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem pd src) rom)
/\ (forall x : reg, x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv -> getr regs' x = getr regs x).
Proof.
intros src pd ps mem rom regs H10 H11 H12 Hrd Hpr Hdj HD HX.
assert (H10' : getr regs 10 = Z_to_bv 64 (DM pd)) by (rewrite H10; unfold DM; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (H11' : getr regs 11 = Z_to_bv 64 (XM ps)) by (rewrite H11; unfold XM; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (imc_entry src pd ps mem rom Hrd Hpr Hdj HD HX regs H10' H11' H12) as (regs' & Hms & Hfr).
exists regs'. split.
- change (Z_to_bv 64 A_IMC) with (Z_to_bv 64 (A_IMC + 0x0)). exact Hms.
- intros. apply Hfr. unfold keepM. repeat split; assumption.
Qed.
End b.
