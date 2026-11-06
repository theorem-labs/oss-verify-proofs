From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w YK0e YK0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a YO0c YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YE34.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN32 YN3h YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require Import RtDStrndupTbl RtDStrndupL RtDStrndupS RtDStrndupP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* plugin-hostd/fuzz_command's strndup entry on its ASan+UBSan image (fuzz_command.asan-ubsan; the walk of
   lib/A/Rt/RtDStrndupQ.v moved by the name-keyed A-to-B address map) from 0x428ec when the malloc body returned a block p: the call
   internal_memcpy(p, x, k) (0x428f0-0x428fc, RtDStrndupL.v cmd_imemcpy), s2 = p + k and the terminator p[k] = 0
   (0x42900-0x42904), then the epilogue (RtDStrndupP.v snp_epi). The context is RtDStrndupP.v's Section e. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (m rom : word -> option byte) (sp0 : Z).
Variables (va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : Z).
Hypothesis Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47.
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
Let snp_epi' := snp_epi rom sp0 va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 Hsp.
(* a block: internal_memcpy(p, x, k), then p[k] = 0 *)
Lemma snp_tail_copy : forall regs (x k p : Z) (buf : list byte),
0 < p -> p + k + 1 <= sp0 - 80 -> 0 < x -> x + k < 2 ^ 63 -> 0 <= k <= Z.of_nat (length buf) ->
(p + k + 1 <= x \/ x + k <= p) ->
(forall j, (j < Z.to_nat k)%nat -> rdn tfibsegs m (Z_to_bv 64 (x + Z.of_nat j)) 1 = Some [nth j buf NUL]) ->
(forall i, 0 <= i <= k -> present m (p + i)) ->
getr regs 19 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 x -> getr regs 18 = Z_to_bv 64 k ->
getr regs 2 = Z_to_bv 64 (sp0 - 2160) ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 0x428ec) m rom)
(mkst regs' (v_jalr (Z_to_bv 64 va) 0) (wbytes m (Z_to_bv 64 p) (firstn (Z.to_nat k) buf ++ [Z_to_bv 8 0])) rom) /\
getr regs' 10 = Z_to_bv 64 p /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = Z_to_bv 64 va /\
getr regs' 8 = Z_to_bv 64 vs0 /\ getr regs' 9 = Z_to_bv 64 vs1 /\ getr regs' 18 = Z_to_bv 64 vs2 /\
getr regs' 19 = Z_to_bv 64 vs3 /\ getr regs' 20 = Z_to_bv 64 vs4 /\ getr regs' 21 = Z_to_bv 64 vs5 /\
getr regs' 22 = Z_to_bv 64 vs6 /\ getr regs' 23 = Z_to_bv 64 vs7 /\ getr regs' 24 = Z_to_bv 64 vs8 /\
(forall r : bv 5, r = 3%bv \/ r = 4%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv -> getr regs' r = getr regs r).
Proof.
intros regs x k p buf Hp Hps Hx Hxk Hk Hdj Hrd Hpr H19 H9 H18 H2.
set (src := firstn (Z.to_nat k) buf).
assert (Lsrc : length src = Z.to_nat k) by (subst src; rewrite length_firstn; lia).
(* the call of internal_memcpy *)
set (regs1 := regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 x)) 12 (Z_to_bv 64 k)) 1 (Z_to_bv 64 0x42900)).
assert (Hms1 : msteps tfibsegs (mkst regs (Z_to_bv 64 0x428ec) m rom) (mkst regs1 (Z_to_bv 64 A_IMC) m rom)).
{ norm_pc.
sdbf S_4584c DS_4584c ltac:(gr; rwH; rewrite branch_eq; apply Z.eqb_neq; rewrite !u_Z2bv by lia; lia).
sv S_45850 DS_45850 (Z_to_bv 64 p).
sv S_45854 DS_45854 (Z_to_bv 64 x).
sv S_45858 DS_45858 (Z_to_bv 64 k).
stepj' S_4585c DS_4585c.
subst regs1. replace (v_addi 272636 4) with (Z_to_bv 64 0x42900 : word) by (apply bv_eq; vm_compute; reflexivity).
apply mst_refl_pc''. vm_compute. reflexivity. }
destruct (cmd_imemcpy src (Z_to_bv 64 p) (Z_to_bv 64 x) m rom regs1) as (regs2 & Hms2 & K2).
- subst regs1. gr. reflexivity.
- subst regs1. gr. reflexivity.
- subst regs1. gr. rewrite Lsrc, Z2Nat.id by lia. reflexivity.
- intros j Hj. rewrite u_Z2bv by lia. rewrite Lsrc in Hj. subst src. rewrite nth_firstn_lt by exact Hj. apply Hrd. exact Hj.
- intros i Hi. rewrite u_Z2bv by lia. apply Hpr. rewrite Lsrc in Hi. lia.
- rewrite !u_Z2bv by lia. rewrite Lsrc, Z2Nat.id by lia. lia.
- rewrite u_Z2bv by lia. rewrite Lsrc, Z2Nat.id by lia. lia.
- rewrite u_Z2bv by lia. rewrite Lsrc, Z2Nat.id by lia. lia.
- assert (E1 : getr regs1 1 = Z_to_bv 64 0x42900) by (subst regs1; gr; reflexivity).
rewrite E1 in Hms2. replace (v_jalr (Z_to_bv 64 0x42900) 0) with (Z_to_bv 64 0x42900 : word) in Hms2 by (apply bv_eq; vm_compute; reflexivity).
set (m1 := wbytes m (Z_to_bv 64 p) src) in *.
assert (K2' : forall r : bv 5, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs2 r = getr regs1 r)
by (intros r A1 A2 A3 A4; apply K2; assumption).
assert (P19 : getr regs2 19 = Z_to_bv 64 p) by (rewrite K2' by reg_neq_tac; subst regs1; gr; exact H19).
assert (P18 : getr regs2 18 = Z_to_bv 64 k) by (rewrite K2' by reg_neq_tac; subst regs1; gr; exact H18).
assert (P2 : getr regs2 2 = Z_to_bv 64 (sp0 - 2160)) by (rewrite K2' by reg_neq_tac; subst regs1; gr; exact H2).
(* the terminator *)
destruct (Hpr k ltac:(lia)) as [bk Hbk].
assert (Est : RiscvSemantics.store_ok tfibsegs m1 (Z_to_bv 64 (p + k)) 1%nat = true).
{ assert (E : m1 (Z_to_bv 64 (p + k)) = Some bk).
{ subst m1. rewrite wbytes_above; [exact Hbk|]. rewrite Lsrc, !u_Z2bv by lia. lia. }
cbn [RiscvSemantics.store_ok]. unfold wview. rewrite E. reflexivity. }
assert (Emem : wbytes m1 (Z_to_bv 64 (p + k)) [Z_to_bv 8 0] = wbytes m (Z_to_bv 64 p) (src ++ [Z_to_bv 8 0])).
{ subst m1. rewrite wbytes_app, Lsrc. rewrite addr_nat by (rewrite u_Z2bv by lia; lia). rewrite u_Z2bv by lia.
rewrite Z2Nat.id by lia. reflexivity. }
(* the ten saved words lie above the block, so the copy and the terminator keep them *)
assert (KEEPW : forall a v, sp0 - 80 <= a -> a + 8 <= sp0 -> word_mem tfibsegs m a v ->
word_mem tfibsegs (wbytes m (Z_to_bv 64 p) (src ++ [Z_to_bv 8 0])) a v).
{ intros a v Ha1 Ha2 Hw q Hq. rewrite <- (Hw q Hq). unfold YP09.mbyte. rewrite wbytes_above; [reflexivity|].
rewrite length_app, Lsrc. cbn [length]. rewrite !u_Z2bv by lia. lia. }
destruct (snp_epi' (wbytes m (Z_to_bv 64 p) (src ++ [Z_to_bv 8 0])) (regupd regs2 18 (Z_to_bv 64 (p + k))) p
(KEEPW (sp0 - 8) va ltac:(lia) ltac:(lia) V0) (KEEPW (sp0 - 16) vs0 ltac:(lia) ltac:(lia) V1) (KEEPW (sp0 - 24) vs1 ltac:(lia) ltac:(lia) V2)
(KEEPW (sp0 - 32) vs2 ltac:(lia) ltac:(lia) V3) (KEEPW (sp0 - 40) vs3 ltac:(lia) ltac:(lia) V4) (KEEPW (sp0 - 48) vs4 ltac:(lia) ltac:(lia) V5)
(KEEPW (sp0 - 56) vs5 ltac:(lia) ltac:(lia) V6) (KEEPW (sp0 - 64) vs6 ltac:(lia) ltac:(lia) V7) (KEEPW (sp0 - 72) vs7 ltac:(lia) ltac:(lia) V8)
(KEEPW (sp0 - 80) vs8 ltac:(lia) ltac:(lia) V9) ltac:(gr; exact P19) ltac:(gr; exact P2)) as (regs' & Hms4 & E).
exists regs'. split.
+ eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. norm_pc.
sdov S_45860 DS_45860 (Z_to_bv 64 (p + k)) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
sdsb S_45864 DS_45864 (p + k) ltac:(addr_tac; reflexivity) ltac:(gr; exact (sb_lbu (Z_to_bv 8 0))) Est.
rewrite Emem. eapply msteps_trans; [apply (mst_refl_pc'' _ _ (Z_to_bv 64 0x42908)); vm_compute; reflexivity | exact Hms4].
+ destruct E as (E10 & E2 & E1' & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & K).
do 12 (split; [assumption|]).
intros r Hr. rewrite K by (destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac). rewrite getr_other by (destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac).
rewrite K2' by (destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac). subst regs1.
rewrite !getr_other by (destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac). reflexivity.
Qed.

End e.
