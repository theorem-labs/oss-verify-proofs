From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w YK0e YK0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0a YO0c YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32 YN3h YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDStrndupTbl RtDStrndupL RtDStrndupS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* plugin-hostd/fuzz_command's strndup entry on its ASan+UBSan image (fuzz_command.asan-ubsan) after the malloc body
   returns (0x457bc), stepped one instruction at a time on the memory the entry sees; the walk of
   lib/A/Rt/RtDStrndupP.v moved by the name-keyed A-to-B address map, with the auipc value at 0x457bc,
   0x457bc + (0x60 << 12) = 0xa57bc, read from this image's code. The pieces:
     0x457bc-0x457d4  common_flags() (GOT 0xa5f40 -> 0x142768); intercept_strndup (+252) = 1, strict_string_checks
                      (+245) = 0, so the entry goes to 0x4583c
     0x4583c-0x4584c  s4 = min(n, k + 1) (0x458ec when n >= k + 1); the overflow test ~x < s4 is false
     0x45850-0x45858  the size class of s4: 1..64 goes to the inline check 0x4585c (RtDStrndupS.v), 0 to 0x45898
                      through 0x45968, 65 and more to the range check 0x5a1f8 through 0x459a4 (ra = 0x459b0)
     0x459b0          the range check answered 0: on to 0x45898
     0x45898-0x458b0  a null block skips the copy; else internal_memcpy(p, x, k) (RtDStrndupL.v cmd_imemcpy) and
                      the terminator p[k] = 0
     0x458b4-0x458e8  the epilogue: a0 = p, the ten saved registers back from [sp0 - 80, sp0), ret. *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma u_negz : forall z, - 2 ^ 64 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2 ^ 64.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rdn_eqaddr : forall (mm : word -> option byte) a b (n : nat) r, a = b ->
rdn tfibsegs mm (Z_to_bv 64 b) n = r -> rdn tfibsegs mm (Z_to_bv 64 a) n = r.
Proof. intros mm a b n r -> H. exact H. Qed.
Lemma nth_firstn_lt : forall {A} (l : list A) k j (d : A), (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
intros A l k; revert l. induction k as [|k IH]; intros l j d Hj; [lia|].
destruct l as [|a l]; [destruct j; reflexivity|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma lxor_m1 : forall z, 0 <= z < 2 ^ 64 -> v_xori (Z_to_bv 64 z) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - z).
Proof.
intros z Hz. unfold v_xori. rewrite u_Z2bv by lia.
replace (bv_wrap 64 (-1)) with (Z.ones 64) by (vm_compute; reflexivity).
rewrite (YE2y.lxor_ones z 64) by lia. rewrite Z.ones_equiv. f_equal; lia.
Qed.
Lemma mst_refl_pc'' : forall regs (pc pc' : word) mem rom, bv_unsigned pc = bv_unsigned pc' ->
msteps tfibsegs (mkst regs pc mem rom) (mkst regs pc' mem rom).
Proof. intros regs pc pc' mem rom E. replace pc' with pc by (apply bv_eq; exact E). apply mst_refl. Qed.
End a.

Ltac kept := let r := fresh "r" in intros r; intros; rewrite ?getr_other by assumption; reflexivity.
Ltac sdsb F0 D aa tacA tacB Hst := let F := litF F0 in
chain_step; [ reflexivity | eapply step_sb_l with (a := aa); [ exact F | reflexivity | exact D | tacA | tacB | exact Hst ] | step_simpl ].

(* ---- 0x457bc to 0x45898 or to the range check, on the memory m the malloc body returns ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (m rom : word -> option byte) (x n k p sp0 : Z).
Definition mm : Z := Z.min n (k + 1).
Hypothesis Hx : 0 < x.
Hypothesis Hxn : x + n + 1 <= 2 ^ 63.
Hypothesis Hk : 0 <= k <= n.
Hypothesis Hn : n < 2 ^ 32.
Hypothesis Hp : 0 <= p < 2 ^ 64.
Hypothesis Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47.
Hypothesis HF0 : word_mem tfibsegs m 0xa5f40 0x142768.
Hypothesis HF1 : rdn tfibsegs m (Z_to_bv 64 0x142864) 1 = Some [Z_to_bv 8 1].
Hypothesis HF2 : rdn tfibsegs m (Z_to_bv 64 0x14285d) 1 = Some [Z_to_bv 8 0].

Lemma mm_facts : 0 <= mm <= k + 1 /\ mm <= n /\ (mm = k + 1 \/ mm = n).
Proof. unfold mm. lia. Qed.

(* 0x457bc .. 0x45850 *)
Lemma snp_flags : forall regs,
getr regs 10 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 x -> getr regs 20 = Z_to_bv 64 n ->
getr regs 21 = Z_to_bv 64 (k + 1) -> getr regs 8 = Z_to_bv 64 sp0 ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x457bc) m rom) (mkst regs' (Z_to_bv 64 0x45850) m rom) /\
getr regs' 19 = Z_to_bv 64 p /\ getr regs' 20 = Z_to_bv 64 mm /\ getr regs' 22 = Z_to_bv 64 0x142768 /\
getr regs' 23 = Z_to_bv 64 (sp0 - 2152) /\
(forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 19%bv -> r <> 20%bv -> r <> 22%bv -> r <> 23%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H9 H20 H21 H8.
destruct (word_mem_ld tfibsegs m 0xa5f40 0x142768 HF0 ltac:(lia) ltac:(lia)) as (bf & Hbf & Vbf).
assert (Hprefix : exists regs1, msteps tfibsegs (mkst regs (Z_to_bv 64 0x457bc) m rom) (mkst regs1 (Z_to_bv 64 0x4583c) m rom) /\
getr regs1 19 = Z_to_bv 64 p /\ getr regs1 22 = Z_to_bv 64 0x142768 /\
(forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 19%bv -> r <> 22%bv -> getr regs1 r = getr regs r)).
{ eexists. split.
- norm_pc.
svx S_45770 DS_45770 (Z_to_bv 64 0xa57bc) ltac:(gr; apply bv_eq; vm_compute; reflexivity).
sdld S_45774 DS_45774 bf (Z_to_bv 64 0x142768) ltac:(addr_tac; exact Hbf) ltac:(exact Vbf).
sdlbu S_45778 DS_45778 ltac:(addr_tac; exact HF1).
sv S_4577c DS_4577c (Z_to_bv 64 p).
sdbf S_45780 DS_45780 ltac:(gr; vm_compute; reflexivity).
sdlbu S_45784 DS_45784 ltac:(addr_tac; exact HF2).
sdbt S_45788 DS_45788 ltac:(gr; vm_compute; reflexivity).
apply mst_refl_pc''. vm_compute. reflexivity.
- split; [gr; reflexivity|]. split; [gr; reflexivity|]. kept. }
destruct Hprefix as (regs1 & Hms1 & B19 & B22 & K1).
assert (G9 : getr regs1 9 = Z_to_bv 64 x) by (rewrite K1 by reg_neq_tac; exact H9).
assert (G20 : getr regs1 20 = Z_to_bv 64 n) by (rewrite K1 by reg_neq_tac; exact H20).
assert (G21 : getr regs1 21 = Z_to_bv 64 (k + 1)) by (rewrite K1 by reg_neq_tac; exact H21).
assert (G8 : getr regs1 8 = Z_to_bv 64 sp0) by (rewrite K1 by reg_neq_tac; exact H8).
destruct (Z_le_gt_dec (k + 1) n) as [Hle|Hgt].
- (* n >= k + 1: s4 = k + 1 *)
assert (Emm : mm = k + 1) by (unfold mm; lia).
eexists. split.
+ eapply msteps_trans; [exact Hms1|]. norm_pc.
sdbt S_457f0 DS_457f0 ltac:(gr; rwH; rewrite branch_geu; apply negb_true_iff; apply Z.ltb_ge; rewrite !u_Z2bv by lia; lia).
sv S_458a0 DS_458a0 (Z_to_bv 64 (k + 1)).
svx S_458a4 DS_458a4 (Z_to_bv 64 (2 ^ 64 - 1 - x)) ltac:(gr; rwH; imm_norm; apply lxor_m1; lia).
sv S_458a8 DS_458a8 (Z_to_bv 64 (sp0 - 2048)).
sv S_458ac DS_458ac (Z_to_bv 64 (sp0 - 2152)).
sdbt S_458b0 DS_458b0 ltac:(gr; rwH; rewrite branch_geu; apply negb_true_iff; apply Z.ltb_ge; rewrite !u_Z2bv by lia; lia).
apply mst_refl_pc''. vm_compute. reflexivity.
+ split; [gr; exact B19|]. split; [gr; rewrite Emm; reflexivity|]. split; [gr; exact B22|]. split; [gr; reflexivity|].
intros r Q10 Q11 Q19 Q20 Q22 Q23. rewrite ?getr_other by assumption. apply K1; assumption.
- (* n < k + 1, so n = k: s4 = n *)
assert (Emm : mm = n) by (unfold mm; lia).
eexists. split.
+ eapply msteps_trans; [exact Hms1|]. norm_pc.
sdbf S_457f0 DS_457f0 ltac:(gr; rwH; rewrite branch_geu; apply negb_false_iff; apply Z.ltb_lt; rewrite !u_Z2bv by lia; lia).
svx S_457f4 DS_457f4 (Z_to_bv 64 (2 ^ 64 - 1 - x)) ltac:(gr; rwH; imm_norm; apply lxor_m1; lia).
sv S_457f8 DS_457f8 (Z_to_bv 64 (sp0 - 2048)).
sv S_457fc DS_457fc (Z_to_bv 64 (sp0 - 2152)).
sdbf S_45800 DS_45800 ltac:(gr; rwH; rewrite branch_ltu; apply Z.ltb_ge; rewrite !u_Z2bv by lia; lia).
apply mst_refl_pc''. vm_compute. reflexivity.
+ split; [gr; exact B19|]. split; [gr; rewrite Emm; exact G20|]. split; [gr; exact B22|]. split; [gr; reflexivity|].
intros r Q10 Q11 Q19 Q20 Q22 Q23. rewrite ?getr_other by assumption. apply K1; assumption.
Qed.

(* 0x45850, 1 <= mm <= 64: the inline check (RtDStrndupS.v snc_block) *)
Lemma snp_small : forall regs,
1 <= mm <= 64 ->
word_mem tfibsegs m 0xa5f50 0xb0c38 -> word_mem tfibsegs m 0xb0c38 SN_SB ->
(forall g, g0 x <= g < g1 x (mm - 1) -> rdn tfibsegs m (Z_to_bv 64 (SN_SB + g)) 1%nat = Some [Z_to_bv 8 0]) ->
(exists b : byte, rdn tfibsegs m (Z_to_bv 64 (A1 x (mm - 1))) 1%nat = Some [b] /\
(bv_unsigned b = 0 \/ ((x + (mm - 1)) mod 8 < bv_unsigned b < 8))) ->
(exists bs, rdn tfibsegs m (Z_to_bv 64 (A0 x - A0 x mod 8)) 8%nat = Some bs /\ length bs = 8%nat) ->
(exists bs, rdn tfibsegs m (Z_to_bv 64 (A1 x (mm - 1) - A1 x (mm - 1) mod 8)) 8%nat = Some bs /\ length bs = 8%nat) ->
getr regs 9 = Z_to_bv 64 x -> getr regs 20 = Z_to_bv 64 mm ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x45850) m rom) (mkst regs' (Z_to_bv 64 0x45898) m rom) /\
(forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r).
Proof.
intros regs Hmm G1 G2 GZ GL W0 W1 H9 H20. pose proof mm_facts as MF.
set (regs1 := regupd (regupd regs 10 (Z_to_bv 64 (mm - 65))) 11 (Z_to_bv 64 (-65))).
assert (Hms1 : msteps tfibsegs (mkst regs (Z_to_bv 64 0x45850) m rom) (mkst regs1 (Z_to_bv 64 0x4585c) m rom)).
{ norm_pc.
sv S_45804 DS_45804 (Z_to_bv 64 (mm - 65)).
sv S_45808 DS_45808 (Z_to_bv 64 (-65)).
sdbf S_4580c DS_4580c ltac:(gr; rewrite branch_geu; apply negb_false_iff; apply Z.ltb_lt;
rewrite !u_negz by lia; lia).
apply mst_refl_pc''. vm_compute. reflexivity. }
destruct (snc_block x (mm - 1) m rom ltac:(lia) ltac:(lia) ltac:(lia) G1 G2 GZ GL W0 W1 regs1) as (regs2 & pcf & Hms2 & Hpc & K2).
- subst regs1. gr. exact H9.
- subst regs1. gr. rewrite H20. f_equal. lia.
- replace pcf with (Z_to_bv 64 0x45898 : word) in Hms2 by (apply bv_eq; rewrite Hpc; reflexivity).
exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
intros r Q10 Q11 Q12 Q13 Q14. rewrite K2 by (unfold keepS; tauto). subst regs1. rewrite ?getr_other by assumption. reflexivity.
Qed.

(* 0x45850, mm = 0: nothing to check *)
Lemma snp_zero : forall regs,
mm = 0 -> getr regs 20 = Z_to_bv 64 mm ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x45850) m rom) (mkst regs' (Z_to_bv 64 0x45898) m rom) /\
(forall r : bv 5, r <> 10%bv -> r <> 11%bv -> getr regs' r = getr regs r).
Proof.
intros regs Hmm H20. rewrite Hmm in H20.
eexists. split.
- norm_pc.
sv S_45804 DS_45804 (Z_to_bv 64 (-65)).
sv S_45808 DS_45808 (Z_to_bv 64 (-65)).
sdbt S_4580c DS_4580c ltac:(gr; rewrite branch_geu; apply negb_true_iff; apply Z.ltb_ge; lia).
sdbf S_4591c DS_4591c ltac:(gr; rwH; rewrite branch_ne; vm_compute; reflexivity).
stepj' S_45920 DS_45920.
apply mst_refl_pc''. vm_compute. reflexivity.
- kept.
Qed.

(* 0x45850, mm >= 65: the call of the range check, a0 = x, a1 = mm, ra = 0x459b0 *)
Lemma snp_big : forall regs,
65 <= mm -> getr regs 9 = Z_to_bv 64 x -> getr regs 20 = Z_to_bv 64 mm ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x45850) m rom) (mkst regs' (Z_to_bv 64 0x5a1f8) m rom) /\
getr regs' 10 = Z_to_bv 64 x /\ getr regs' 11 = Z_to_bv 64 mm /\ getr regs' 1 = Z_to_bv 64 0x459b0 /\
(forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 11%bv -> getr regs' r = getr regs r).
Proof.
intros regs Hmm H9 H20. pose proof mm_facts as MF.
eexists. split.
- norm_pc.
sv S_45804 DS_45804 (Z_to_bv 64 (mm - 65)).
sv S_45808 DS_45808 (Z_to_bv 64 (-65)).
sdbt S_4580c DS_4580c ltac:(gr; rewrite branch_geu; apply negb_true_iff; apply Z.ltb_ge;
rewrite (u_negz (-65)) by lia; rewrite u_Z2bv by lia; lia).
sdbt S_4591c DS_4591c ltac:(gr; rwH; rewrite branch_ne; apply negb_true_iff; apply Z.eqb_neq; rewrite !u_Z2bv by lia; lia).
sv S_45958 DS_45958 (Z_to_bv 64 x).
sv S_4595c DS_4595c (Z_to_bv 64 mm).
stepj' S_45960 DS_45960.
apply mst_refl_pc''. vm_compute. reflexivity.
- split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; apply bv_eq; vm_compute; reflexivity|].
kept.
Qed.
End d.

(* 0x459b0: the range check answered 0 *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma snp_ret : forall (m rom : word -> option byte) regs, getr regs 10 = Z_to_bv 64 0 ->
msteps tfibsegs (mkst regs (Z_to_bv 64 0x459b0) m rom) (mkst regs (Z_to_bv 64 0x45898) m rom).
Proof.
intros m rom regs H10. norm_pc.
sdbt S_45964 DS_45964 ltac:(gr; rwH; rewrite branch_eq; vm_compute; reflexivity).
apply mst_refl_pc''. vm_compute. reflexivity.
Qed.
End r.

(* ---- 0x45898 to the return, on the memory m the check leaves ---- *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (m rom : word -> option byte) (sp0 : Z).
Variables (va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : Z).
Hypothesis Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47.

(* the epilogue, on any memory that holds the ten saved words *)
Lemma snp_epi : forall (m3 : word -> option byte) regs p,
word_mem tfibsegs m3 (sp0 - 8) va -> word_mem tfibsegs m3 (sp0 - 16) vs0 -> word_mem tfibsegs m3 (sp0 - 24) vs1 ->
word_mem tfibsegs m3 (sp0 - 32) vs2 -> word_mem tfibsegs m3 (sp0 - 40) vs3 -> word_mem tfibsegs m3 (sp0 - 48) vs4 ->
word_mem tfibsegs m3 (sp0 - 56) vs5 -> word_mem tfibsegs m3 (sp0 - 64) vs6 -> word_mem tfibsegs m3 (sp0 - 72) vs7 ->
word_mem tfibsegs m3 (sp0 - 80) vs8 ->
getr regs 19 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 (sp0 - 2160) ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x458b4) m3 rom) (mkst regs' (v_jalr (Z_to_bv 64 va) 0) m3 rom) /\
getr regs' 10 = Z_to_bv 64 p /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = Z_to_bv 64 va /\
getr regs' 8 = Z_to_bv 64 vs0 /\ getr regs' 9 = Z_to_bv 64 vs1 /\ getr regs' 18 = Z_to_bv 64 vs2 /\
getr regs' 19 = Z_to_bv 64 vs3 /\ getr regs' 20 = Z_to_bv 64 vs4 /\ getr regs' 21 = Z_to_bv 64 vs5 /\
getr regs' 22 = Z_to_bv 64 vs6 /\ getr regs' 23 = Z_to_bv 64 vs7 /\ getr regs' 24 = Z_to_bv 64 vs8 /\
(forall r : bv 5, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 9%bv -> r <> 10%bv -> r <> 18%bv -> r <> 19%bv ->
r <> 20%bv -> r <> 21%bv -> r <> 22%bv -> r <> 23%bv -> r <> 24%bv -> getr regs' r = getr regs r).
Proof.
intros m3 regs p V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 H19 H2.
destruct (word_mem_ld tfibsegs m3 _ _ V0 ltac:(lia) ltac:(lia)) as (b0 & R0 & L0).
destruct (word_mem_ld tfibsegs m3 _ _ V1 ltac:(lia) ltac:(lia)) as (b1 & R1 & L1).
destruct (word_mem_ld tfibsegs m3 _ _ V2 ltac:(lia) ltac:(lia)) as (b2 & R2 & L2).
destruct (word_mem_ld tfibsegs m3 _ _ V3 ltac:(lia) ltac:(lia)) as (b3 & R3 & L3).
destruct (word_mem_ld tfibsegs m3 _ _ V4 ltac:(lia) ltac:(lia)) as (b4 & R4 & L4).
destruct (word_mem_ld tfibsegs m3 _ _ V5 ltac:(lia) ltac:(lia)) as (b5 & R5 & L5).
destruct (word_mem_ld tfibsegs m3 _ _ V6 ltac:(lia) ltac:(lia)) as (b6 & R6 & L6).
destruct (word_mem_ld tfibsegs m3 _ _ V7 ltac:(lia) ltac:(lia)) as (b7 & R7 & L7).
destruct (word_mem_ld tfibsegs m3 _ _ V8 ltac:(lia) ltac:(lia)) as (b8 & R8 & L8).
destruct (word_mem_ld tfibsegs m3 _ _ V9 ltac:(lia) ltac:(lia)) as (b9 & R9 & L9).
eexists. split.
- norm_pc.
sv S_45868 DS_45868 (Z_to_bv 64 p).
sv S_4586c DS_4586c (Z_to_bv 64 (sp0 - 2032)).
sdld S_45870 DS_45870 b0 (Z_to_bv 64 va) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 8)); [lia | exact R0]) ltac:(exact L0).
sdld S_45874 DS_45874 b1 (Z_to_bv 64 vs0) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 16)); [lia | exact R1]) ltac:(exact L1).
sdld S_45878 DS_45878 b2 (Z_to_bv 64 vs1) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 24)); [lia | exact R2]) ltac:(exact L2).
sdld S_4587c DS_4587c b3 (Z_to_bv 64 vs2) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 32)); [lia | exact R3]) ltac:(exact L3).
sdld S_45880 DS_45880 b4 (Z_to_bv 64 vs3) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 40)); [lia | exact R4]) ltac:(exact L4).
sdld S_45884 DS_45884 b5 (Z_to_bv 64 vs4) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 48)); [lia | exact R5]) ltac:(exact L5).
sdld S_45888 DS_45888 b6 (Z_to_bv 64 vs5) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 56)); [lia | exact R6]) ltac:(exact L6).
sdld S_4588c DS_4588c b7 (Z_to_bv 64 vs6) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 64)); [lia | exact R7]) ltac:(exact L7).
sdld S_45890 DS_45890 b8 (Z_to_bv 64 vs7) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 72)); [lia | exact R8]) ltac:(exact L8).
sdld S_45894 DS_45894 b9 (Z_to_bv 64 vs8) ltac:(addr_tac; apply (rdn_eqaddr _ _ (sp0 - 80)); [lia | exact R9]) ltac:(exact L9).
sv S_45898 DS_45898 (Z_to_bv 64 sp0).
stepret S_4589c DS_4589c.
apply mst_refl.
- split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
kept.
Qed.

Hypothesis V0 : word_mem tfibsegs m (sp0 - 8) va.
Hypothesis V1 : word_mem tfibsegs m (sp0 - 16) vs0.
Hypothesis V2 : word_mem tfibsegs m (sp0 - 24) vs1.
Hypothesis V3 : word_mem tfibsegs m (sp0 - 32) vs2.
Hypothesis V4 : word_mem tfibsegs m (sp0 - 40) vs3.
Hypothesis V5 : word_mem tfibsegs m (sp0 - 48) vs4.
Hypothesis V6 : word_mem tfibsegs m (sp0 - 56) vs5.
Hypothesis V7 : word_mem tfibsegs m (sp0 - 64) vs6.
Hypothesis V8 : word_mem tfibsegs m (sp0 - 72) vs7.
Hypothesis V9 : word_mem tfibsegs m (sp0 - 80) vs8.

(* a null block: no copy *)
Lemma snp_tail_null : forall regs,
getr regs 19 = Z_to_bv 64 0 -> getr regs 2 = Z_to_bv 64 (sp0 - 2160) ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x45898) m rom) (mkst regs' (v_jalr (Z_to_bv 64 va) 0) m rom) /\
getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = Z_to_bv 64 va /\
getr regs' 8 = Z_to_bv 64 vs0 /\ getr regs' 9 = Z_to_bv 64 vs1 /\ getr regs' 18 = Z_to_bv 64 vs2 /\
getr regs' 19 = Z_to_bv 64 vs3 /\ getr regs' 20 = Z_to_bv 64 vs4 /\ getr regs' 21 = Z_to_bv 64 vs5 /\
getr regs' 22 = Z_to_bv 64 vs6 /\ getr regs' 23 = Z_to_bv 64 vs7 /\ getr regs' 24 = Z_to_bv 64 vs8 /\
(forall r : bv 5, r = 3%bv \/ r = 4%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv -> getr regs' r = getr regs r).
Proof.
intros regs H19 H2.
destruct (snp_epi m regs 0 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 H19 H2) as (regs' & Hms & E).
exists regs'. split.
- norm_pc.
sdbt S_4584c DS_4584c ltac:(gr; rwH; rewrite branch_eq; vm_compute; reflexivity).
eapply msteps_trans; [apply (mst_refl_pc'' _ _ (Z_to_bv 64 0x458b4)); vm_compute; reflexivity | exact Hms].
- destruct E as (E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & K).
do 12 (split; [assumption|]).
intros r Hr. apply K; destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac.
Qed.

End e.
