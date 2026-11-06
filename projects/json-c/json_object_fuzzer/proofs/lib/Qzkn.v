(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QZDE QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qc8V Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qc8V.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QlKV.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma v_sltu_1A : forall x y : word, bv_unsigned x < bv_unsigned y -> v_sltu x y = Z_to_bv 64 1.
Proof. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [reflexivity|lia]. Qed.

Lemma lxor_bound64A : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as HL.
assert (Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
assert (Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
lia.
Qed.

Lemma usl_ret_bitsA cur : 0 <= cur < 2^64 ->
Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 cur)) 6566184))) + -1)))
(bv_unsigned (Z_to_bv 64 cur)))
= Z_to_bv 64 (usl_retA cur).
Proof.
intros Hc. unfold usl_retA, GLOBLOC_A, LC_GLOBAL_A. rewrite (unsigned_lit cur) by lia.
pose proof (lxor_bound64A cur 6566184 Hc ltac:(lia)) as XR.
destruct (Z.eqb_spec cur 6566184) as [->|NE]; [reflexivity|].
assert (NZ : Z.lxor cur 6566184 <> 0) by (intros E; apply Z.lxor_eq in E; lia).
rewrite v_sltu_1A by (rewrite !unsigned_lit by lia; lia).
change (bv_unsigned (Z_to_bv 64 1) + -1) with 0. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lor_0_l. reflexivity.
Qed.

Lemma b1_readA : forall m a b rest, bytes_at asegs m a (b :: rest) -> ov_read_bytes asegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros m a b rest H.
pose proof (bytes_at_read asegs m a (b :: rest) 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
cbv beta iota delta [Z.to_nat skipn firstn] in R. unfold wa in R. rewrite Z.add_0_r in R. exact R.
Qed.
Lemma cname_roA : forall m, mem_inv asegs m -> bytes_at asegs m CNAME_A [Z_to_bv 8 67; Z_to_bv 8 0].
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold CNAME_A; lia| unfold CNAME_A; cbn; lia| vm_compute; repeat split; reflexivity]. Qed.

Lemma nodup_app_disjZ : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; cbn; intros l2 x ND H1 H2; [exact H1|].
inversion ND as [|y' l' Hny Hnd]; subst.
destruct H1 as [-> | H1]; [apply Hny; apply in_or_app; right; exact H2 | exact (IH _ _ Hnd H1 H2)].
Qed.

Section LocA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma lm_blk_notin_LB : forall A LB LM FRS B m md d n k, HEAPAx A LB LM FRS B m md -> In (d, n) LM -> ~ In (d, k) LB.
Proof.
intros A LB LM FRS B m md d n k HP Hin Hc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND.
exact (nodup_app_disjZ _ _ d ND (in_map blk_addr _ _ Hc) (in_map blk_addr _ _ Hin)).
Qed.

Lemma lm_head_fresh : forall A LB LM FRS B m md r n k, HEAPAx A LB ((r, n) :: LM) FRS B m md -> ~ In (r, k) (LB ++ LM).
Proof.
intros A LB LM FRS B m md r n k HP Hin.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. cbn [map blk_addr fst] in ND.
apply (Permutation_NoDup (Permutation_sym (Permutation_middle _ _ _))) in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni. rewrite <- map_app. exact (in_map blk_addr _ _ Hin).
Qed.

Theorem errno_location_A_ok : errno_location_A_stmt.
Proof.
unfold errno_location_A_stmt, A_ERRNO_LOCATION. intros until m. intros TP. subst tp. unfold A_ERRNO, A_TP.
step. step. step. apply evt_done. reflexivity.
Qed.

Theorem uselocale_A_ok : uselocale_A_stmt.
Proof.
unfold uselocale_A_stmt, A_USELOCALE. intros until nw. intros LC Hcur Hnw TP MI. subst tp.
unfold LOCCELL_A, usl_newA, A_TP in *. change (6434400 - 48) with 6434352 in *.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(6434352, 6434352 + 8)] m) as MU.
step. step. step. step.
destruct (Z.eq_dec nw 0) as [->|NZ].
- step. if_truex. do 6 step. rewrite usl_ret_bitsA by lia.
apply evt_done. exists m. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact LC].
- step. if_falsex. rewrite (proj2 (Z.eqb_neq _ _) NZ). step. step.
destruct (Z.eq_dec nw (2^64 - 1)) as [->|NG].
+ if_falsex. step. stepz. do 6 step. rewrite usl_ret_bitsA by lia.
apply evt_done. exists m0. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold LC_GLOBAL_A, GLOBLOC_A. rewrite Z.eqb_refl. exact LC.
+ if_truex. stepz. do 6 step. rewrite usl_ret_bitsA by lia.
apply evt_done. eexists. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold LC_GLOBAL_A. rewrite (proj2 (Z.eqb_neq _ _) NG). exact LC.
Qed.

Theorem freelocale_A_ok : freelocale_A_stmt HIx.
Proof.
unfold freelocale_A_stmt, A_FREELOCALE, A_DUPLOCALE, A_NEWLOCALE. intros until errv. intros HP HIN ST LO LOS SPA HT ERR TP RA K.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heap_pres_refl A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
assert (HINX : In (d, n) (LB ++ LM)) by (apply in_or_app; right; exact HIN).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ d n HP HINX) as (Hn0 & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ d n HP HINX) as Himg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst tp. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 5 step.

do 22 step.
repeat match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end.
rewrite !(unsigned_lit d) by lia.
assert (X1 : forall k, 0 <= k < 2^64 -> k <> d -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor d k)) = Z_to_bv 64 1).
{ intros k Hk NE. pose proof (lxor_bound64A d k ltac:(lia) Hk). apply v_sltu_1A. rewrite !unsigned_lit by lia.
assert (Z.lxor d k <> 0) by (intros E; apply Z.lxor_eq in E; lia). lia. }
rewrite !X1 by lia. rewrite (v_sltu_1A (Z_to_bv 64 0) (Z_to_bv 64 d)) by (rewrite !unsigned_lit by lia; lia).
change (bv_unsigned (Z_to_bv 64 1)) with 1. cbn [Z.land].
change (Z.land 1 1) with 1. change (bv_unsigned (Z_to_bv 64 1)) with 1. change (Z.land 1 1) with 1.
step. if_falsex. do 4 step.
release_frame FR ST (bv_unsigned sp).
step.

alloc_callA (hiA_free2 A4L HIx) A4L HIx HP MU WM MI.
all: rewrite ?unsigned_lit by lia; cbn [uw_pre uw_ok uw_key uw_cost bB bD charge]; a4l_goal.
{ right. exists n. exact HIN. }
all: try eassumption; try reflexivity; try (unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
eapply K; [exact RS3| exact VM3| exact ST3| | exact ERR3| exact HP3].
eapply heap_pres_trans; [| exact HPR3].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU| exact WM|].
eapply (client_outsideA _ HIx); [exact HP| | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia| solve_clientWA A4L HIx HP].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact (in_lb_remove _ _ _ Hb)| right; exact Hb].
Qed.

Lemma seq_cases48A (P : nat -> Prop) : (forall k, (k < 48)%nat -> P k) <-> Forall P (seq 0 48).
Proof. rewrite Forall_forall. split; [intros H k Hk; apply H; apply in_seq in Hk; lia| intros H k Hk; apply H; apply in_seq; lia]. Qed.
Lemma globloc_romA : forall k, (k < 48)%nat -> seg_rom asegs (wa (GLOBLOC_A + Z.of_nat k)) <> None.
Proof. apply (proj2 (seq_cases48A _)). unfold GLOBLOC_A. repeat constructor; vm_compute; discriminate. Qed.
Lemma globloc_wA : forall k, (k < 48)%nat ->
match find_segment asegs (GLOBLOC_A + Z.of_nat k) 1 with
| Some seg => if seg_writable seg then segment_byte_at (seg_bytes seg) (Z.to_N (GLOBLOC_A + Z.of_nat k - Z.of_N (seg_base seg))) else None
| None => None end <> None.
Proof. apply (proj2 (seq_cases48A _)). unfold GLOBLOC_A. repeat constructor; vm_compute; discriminate. Qed.
Lemma globloc_anyA m : exists gl, rw_cells asegs m GLOBLOC_A [CB 48%nat gl].
Proof.
set (f := fun i : nat => match mrd asegs m (wa (GLOBLOC_A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
exists (map f (seq 0 48)).
assert (LEN : length (map f (seq 0 48)) = 48%nat) by (rewrite length_map, length_seq; reflexivity).
split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LEN| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [unfold GLOBLOC_A; lia|]. split; [rewrite LEN; unfold GLOBLOC_A; lia|].
intros i Hi. rewrite LEN in Hi. rewrite nth_error_map, (nth_error_seq 0 48 i) by lia. cbn [option_map Nat.add].
replace (i <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map].
subst f. cbv beta. destruct (mrd asegs m (wa (GLOBLOC_A + Z.of_nat i))) eqn:E; [reflexivity|].
exfalso. unfold mrd in E. destruct (m (wa (GLOBLOC_A + Z.of_nat i))); [discriminate|]. exact (globloc_romA i Hi E).
- split; [unfold GLOBLOC_A; lia|]. split; [unfold GLOBLOC_A; cbn; lia|]. cbn [cells_size csize Nat.add]. intros j Hj.
unfold wview. destruct (m (wa (GLOBLOC_A + j))); [discriminate|].
rewrite wa_unsigned by (unfold GLOBLOC_A; lia).
replace j with (Z.of_nat (Z.to_nat j)) by lia. apply globloc_wA. lia.
Qed.

Theorem duplocale_A_ok : duplocale_A_stmt HIx.
Proof.
unfold duplocale_A_stmt, A_FREELOCALE, A_DUPLOCALE, A_NEWLOCALE. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA LML BM K.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst tp. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 6 step. step.
alloc_callA (hiA_malloc2 A4L HIx) A4L HIx HP MU WM MI.
all: rewrite ?unsigned_lit by lia; cbn [uw_pre uw_ok uw_key uw_cost bB bD charge]; a4l_goal.
all: try eassumption; try reflexivity; try (unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
rewrite ?unsigned_lit in ST2, HPR2 by lia.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST ERR.
destruct OUT2 as [(-> & He & HP2) | (Hr & [bjunk BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex. do 3 step.
release_frame FR ST2 (bv_unsigned sp).
step.
evt_done5. eapply K; [| exact VM2| exact ST2| exact HPR| exact ERR2| left; split; [reflexivity| split; [exact He| exact HP2]]].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; right; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; right; left; reflexivity)) as Himg_r.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
destruct (globloc_anyA m2) as [gl GL]. unfold GLOBLOC_A in GL.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step. unfold LC_GLOBAL_A. if_falsex. step. step.
do 12 step.
do 3 step. release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. eapply K; [| exact VM2| exact ST2| | exact ERR2| right].
+ unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA _ HIx); [exact HP2 | | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
apply Forall_cons; [left; cbn; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists r, 48. cbn [fst snd]. split; [apply in_or_app; right; left; reflexivity|]. split; [| lia].
apply not_in_app3; [exact (lm_head_fresh _ _ _ _ _ _ _ r 48 48 HP2) | exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; right; left; reflexivity))].
+ split; [exact Hr|]. split.
* lazymatch type of BLK with rw_cells _ _ _ ?cs => exists (cells_bytes cs) end.
eapply (rw_cells_recast _ _ _ _ _ BLK); [| reflexivity| reflexivity].
cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length; [reflexivity|]. cbn [cells_wf cell_wf]. repeat split.
* eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU). solve_frameW_withA HP2.
Qed.

Lemma notin_lb_removeA : forall LB d n k, List.NoDup (map QCcH.blk_addr LB) -> In (d, n) LB -> ~ In (d, k) (lb_remove d LB).
Proof.
induction LB as [|[a sz] LB IH]; intros d n k ND Hin Hc; [exact Hin|].
cbn [map QCcH.blk_addr fst] in ND. inversion ND as [|x l Hna Hnd]; subst.
cbn [lb_remove QCcH.blk_addr fst] in Hc.
destruct (Z.eqb_spec a d) as [->|NE].
- apply Hna. apply in_map_iff. exists (d, k). split; [reflexivity| exact Hc].
- destruct Hc as [E|Hc]; [inversion E; subst; exact (NE eq_refl)|].
destruct Hin as [E|Hin]; [inversion E; subst; exact (NE eq_refl)|].
exact (IH d n k Hnd Hin Hc).
Qed.

Ltac nl_exit K r jk :=
stepz; stepz; stepz;
stepz; stepz; if_falsex; stepz;
lazymatch goal with | CAN2 : bytes_at asegs _ 6565536 (le8 _) |- _ =>
pose proof (le8_read asegs _ _ _ CAN2) as RD9; stepz; clear RD9 end;
stepz; stepz;
let KC := fresh "KC" in if_cases KC; [exfalso; rewrite bv_eqb_refl in KC; discriminate KC|];
stepz; do 6 stepz; stepz;
lazymatch goal with | FR : rw_cells asegs _ (bv_unsigned ?sp + -112) _, ST : stk asegs _ _ _ |- _ =>
release_frame FR ST (bv_unsigned sp) end;
stepz;
evt_done5;
eapply (K _ _ r jk).

Theorem newlocale_A_ok : newlocale_A_stmt HIx.
Proof.
unfold newlocale_A_stmt, A_FREELOCALE, A_DUPLOCALE, A_NEWLOCALE. intros until errv. intros HP HIN BLK LCK ST LO LOS SPA HT ERR TP RA K.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM.
assert (HINX : In (d, 48) (LB ++ LM)) by (apply in_or_app; right; exact HIN).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ d 48 HP HINX) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ d 48 HP HINX) as Himg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_l in ND.
pose proof (notin_lb_removeA LM d 48 48 ND HIN) as NLR. clear ND.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (g & CAN1 & CAN2 & CAN3). a4l.
pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL. cbn [hl_segs hl_libc hla_base A4L A4H Z.add] in NL.
pose proof (cname_roA m MI) as CN. unfold CNAME_A in CN.
unfold LOCALE_LOCK_A, CNAME_A in *. change (6434400 - 16) with 6434384 in CAN3.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m) as MU.

assert (HPRm : forall mx, munch [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m mx -> wmono asegs m mx ->
heap_pres A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx).
{ intros mx MUx WMx. eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx| exact WMx|].
eapply (client_outsideA _ HIx); [exact HP| | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|].
- intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact (in_lb_remove _ _ _ Hb)| right; exact Hb].
- apply Forall_cons; [left; cbn; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists d, 48. cbn [fst snd]. split; [exact HINX|]. split; [| lia].
intros Hc. apply in_app_or in Hc. destruct Hc as [Hc|Hc]; [exact (lm_blk_notin_LB _ _ _ _ _ _ _ d 48 48 HP HIN Hc)|].
apply in_app_or in Hc. destruct Hc as [Hc|Hc]; [exact (NLR Hc)|].
exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ d 48 HP HINX Hc). }
assert (HPm : forall mx, munch [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m mx -> wmono asegs m mx -> mem_inv asegs mx ->
HEAPAx A LB LM FRS B mx md).
{ intros mx MUx WMx MIx. eapply (heapA_client_frame A4L HIx); [exact HP | | exact WMx | exact MIx].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUx).
apply Forall_cons; [left; cbn; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists d, 48. cbn [fst snd]. split; [exact HINX| lia]. }
subst tp. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
destruct (rw_cells_CB_sizes asegs m [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat _ _ _ FR eq_refl)
as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & FR'). clear FR. rename FR' into FR.
do 7 stepz. do 3 stepz.
stepz. pose proof (le8_read asegs _ _ _ CAN1) as RD1. stepz. clear RD1.
pose proof (le8_read asegs _ _ _ CAN2) as RD2. stepz. clear RD2.
stepz.
stepz. stepz. stepz.

stepz. pose proof (b1_readA _ _ _ _ NL) as RD3. stepz. clear RD3.
replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
stepz. if_truex. stepz.

stepz. stepz. if_falsex. stepz. if_falsex.
stepz. stepz. stepz. stepz. stepz.
if_cases K0. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_truex. stepz. if_falsex. stepz. stepz. stepz. stepz.
carve_frame 384%nat ST.
destruct (rw_cells_CB_sizes asegs _ [272;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat _ _ _ FR0 eq_refl)
as (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & p14 & FR0'). clear FR0. rename FR0' into FR0.
do 14 stepz.
stepz. stepz. pose proof (le8_read asegs _ _ _ CAN1) as RD1. stepz. clear RD1.
pose proof (le8_read asegs _ _ _ CAN2) as RD2. stepz. clear RD2.
stepz.
pose proof (b1_readA _ _ _ _ CN) as RD3. stepz. clear RD3.
replace (zxb (Z_to_bv 8 67)) with (Z_to_bv 64 67) in * by (apply bv_eq; vm_compute; reflexivity).
stepz. stepz. if_falsex. stepz. stepz. if_truex.
stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (cname_roA mx ltac:(assumption)) as CNx; unfold CNAME_A in CNx;
pose proof (proj1 (bytes_at_app asegs mx 143520 [Z_to_bv 8 67] [Z_to_bv 8 0]) CNx) as [_ CN1] end.
pose proof (b1_readA _ _ _ _ CN1) as RD4. stepz.
replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) in * by (apply bv_eq; vm_compute; reflexivity).
stepz. stepz. if_truex.

stepz. stepz. stepz. stepz. stepz. stepz. if_falsex.
stepz. stepz. stepz. if_falsex.
stepz. stepz. stepz. if_falsex.
stepz. clear RD4 CN1 CNx. stepz. stepz. if_truex.

stepz. if_truex. stepz.
pose proof (le8_read asegs _ _ _ CAN2) as RD2. stepz. clear RD2. stepz. stepz.
if_cases KC. { exfalso. rewrite bv_eqb_refl in KC. discriminate KC. }
stepz. do 13 stepz. stepz.
release_frame FR0 ST (bv_unsigned sp + -112).
stepz.

stepz. stepz. stepz. if_falsex.

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K2. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K3. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K4. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K5. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. stepz. stepz. stepz.
stepz. if_falsex. stepz. stepz. if_falsex. stepz. stepz. stepz. if_falsex. stepz. if_falsex. stepz. if_falsex.

do 12 stepz.
stepz. stepz.
lazymatch type of BLK with rw_cells _ _ _ ?cs =>
nl_exit K d (cells_bytes cs); [| exact ST| apply HPRm; assumption| | exact LCK| exact ERR| apply HPm; assumption| left; reflexivity] end.
- unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists.
- eapply (rw_cells_recast _ _ _ _ _ BLK); [| reflexivity| reflexivity].
cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length; [reflexivity| cbn [cells_wf cell_wf]; repeat split].
Qed.
End LocA.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache QWxq_c1 QgoP QB1P Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QgoP.
Import Q7UD Qwm6.
Import QsKa.Mq1 QsKa.Mq0.
Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Module AF_F_strtol := QB1P.
Import Qwm6.Mq0 QlKV.Mqa.
Import ListNotations.
Open Scope Z_scope.

Ltac if_zxb b :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
replace c with b; [cbv iota | symmetry; cbv delta [zxb]; solve_condx]
end.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
apply Z.mod_small. lia.
Qed.

Lemma blank_test : forall c, 0 <= c < 256 -> bv_ltu (Z_to_bv 64 (c + -9)) (Z_to_bv 64 5) = ((9 <=? c) && (c <=? 13))%bool.
Proof.
intros c Hc. unfold bv_ltu. rewrite !unsigned_lit_wrap. change (5 mod 2 ^ 64) with 5.
destruct (Z_lt_le_dec c 9) as [Hlt | Hge].
- replace ((c + -9) mod 2 ^ 64) with (2 ^ 64 + c - 9) by (Z.div_mod_to_equations; lia).
replace (9 <=? c) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply Z.ltb_ge. lia.
- rewrite Z.mod_small by lia. replace (9 <=? c) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.leb_spec0 c 13); [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma shadow_outside_W : forall E lo hi s n a k,
app_mem E 8 -> alloc_ceiling <= lo -> 0 <= s -> s + n <= 2^47 -> 0 < n ->
shadow_span_lo A_SB s <= a -> a + k <= shadow_span_hi A_SB s n ->
disjoint_from [(E, E + 8); (A_TP - 164, A_TP - 160); (lo, hi)] a k.
Proof.
intros E lo hi s n a k APP LO Hs Hsn Hn Ha Hk.
pose proof (shadow_outside_stack A_SB s n lo hi a k ltac:(unfold A_SB; lia) Hs Hsn Hn LO Ha Hk) as [D _].
unfold shadow_span_lo, shadow_span_hi, A_SB in Ha, Hk. unfold app_mem, A_SB, A_HMB in APP. unfold A_TP.
assert ((s + n - 1) / 8 <= 2^44) by (Z.div_mod_to_equations; lia).
cbn. split; [| split; [| split; [exact D | exact I]]]; Z.div_mod_to_equations; lia.
Qed.

Lemma real_strtoll_specZ :
forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte) (str : list byte) (SP A E lo : Z) (e g ej : word),
0 <= SP < 2^64 -> 0 <= A < 2^64 -> 0 <= E < 2^64 ->
bytes_at asegs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells asegs m E [C8 ej] ->
rw_cells asegs m (0x622e60 - 164) [C4 e] ->
bytes_at asegs m 0xe6b80 (le8 (Z_to_bv 64 0x642ea0)) -> bytes_at asegs m 0x642ea0 (le8 g) ->
stk asegs m lo SP -> (0x645000 <= lo)%Z -> (lo <= SP - 368)%Z ->
(0x645000 <= E)%Z ->
(E + 8 <= SP - 368 \/ SP <= E)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 368 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= 0x622e60 - 164 \/ 0x622e60 - 160 <= A)%Z ->
mem_inv asegs m ->
evt asegs (fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (j : Z) (e' : word),
ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 0x622e60) x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(SP - 368, SP); (E, E + 8); (0x622e60 - 164, 0x622e60 - 160)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' E [C8 (Z_to_bv 64 (A + j))] /\ (0 <= j <= Z.of_nat (length str))%Z
/\ bytes_at asegs m' A (str ++ [b0])
/\ rw_cells asegs m' (0x622e60 - 164) [C4 e']
/\ stk asegs m' lo SP)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 0x622e60) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 E) (Z_to_bv 64 10) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xda7e8) fc None m (seg_rom asegs)).
Proof.
intros until ej. intros HSP HA HE STR NONUL AB EP ERR GOTF GF ST LO LOS ELO SEP1 SEP2 SEP3 SEP4 MI.
pose proof (AF_F_strtol.strtoll_spec ra (Z_to_bv 64 SP) gp (Z_to_bv 64 0x622e60) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 E) (Z_to_bv 64 10)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str SP A E lo e g ej) as X.
unfold AF_F_strtol.strtoll_entry, AF_F_strtol.GOT_GUARD, AF_F_strtol.GUARD in X.
rewrite (unsigned_lit SP), (unsigned_lit A), (unsigned_lit E) in X by lia.
eapply evt_mono; [eapply X; first [reflexivity | assumption | lia] |].
intros ms' P. unfold AF_F_strtol.strtox_post, AF_F_strtol.strtox_W in P. exact P.
Qed.

Lemma a4_rt_cells_not_errno : forall c, In c a4_rt_cells ->
fst c + Z.of_nat (length (snd c)) <= A_TP - 164 \/ A_TP - 160 <= fst c.
Proof.
intros c Hc. unfold A_TP. unfold a4_rt_cells, a4_rt_consts in Hc. cbn [app] in Hc.
repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; unfold A_GOT_SB, A_SB_CELL;
repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end; lia |]).
destruct Hc.
Qed.

Section IStrtoll.
Hypothesis OBL_REGION : region_is_poisoned_spec_U.

Lemma istrtoll_sound : istrtoll_spec_U.
Proof.
unfold istrtoll_spec_U.
intros until Q. intros UPA UPE RT APP APPE Ha0 Ha1 Ha2 Htp HA HAn Hl40 HE HEn STR NONUL EP ERR GOTF GF SEPE SEPA SEPAE SEPAR ST LO LOS SPA MI RA K.
subst a0 a1 a2 tp. word_range sp SPR. pose proof alloc_ceiling_ge as ACG.
pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB.
set (L := Z.of_nat (length str)) in *.

rt_cell RT 0xf07d8 as INITED. rt_cell RT 0xe5db0 as GOTCF. rt_cell RT 0xed315 as CF29. rt_cell RT 0xe7d80 as REALS.
rt_cell RT 0xe5da8 as GOTFL. rt_cell RT 0x18171d as F245. rt_cell RT 0xe5db8 as GOTSB. rt_cell RT 0xefaf8 as SBC.
apply ro_C8_of_bytes_at in GOTCF. apply ro_C8_of_bytes_at in REALS. apply ro_C8_of_bytes_at in GOTFL.
apply ro_C8_of_bytes_at in GOTSB. apply ro_C8_of_bytes_at in SBC.
apply ro_C1_of_bytes_at in INITED. apply ro_C1_of_bytes_at in CF29. apply ro_C1_of_bytes_at in F245.
assert (RO10400 : ro_cells asegs m 0x10460 [CB 8 (le8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa))]).
{ change 8%nat with (length (le8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa))).
apply (ro_cells_image asegs); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
stash STR.
pose proof (munch_refl [(E, E + 8); (A_TP - 164, A_TP - 160); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_ISTRTOLL. unfold A_TP in *. unfold A_GOT_GUARD, A_GUARD in GOTF, GF. carve_frame 48%nat ST.
step.
do 6 step.
step. step. step.
step.
eapply init_gate_spec; [assumption | assumption | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a0x a1x m1 MU1 WM1 MI1 ST1.
lazymatch type of MU1 with munch _ ?mc _ =>
transport_after_call asegs mc m1 MU1 WM1; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU1 WM1 end.
replace (ret_pc (Z_to_bv 64 0x573f0)) with (Z_to_bv 64 0x573f0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 5 step.
step. if_false.
do 2 step.
stepz.
do 4 step.
apply (proj1 (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 12297829382473034410)] _)) in FR as [EPL FR].
cbn [cells_size csize Nat.add] in FR. replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FR by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STR2 : bytes_at asegs mc A (str ++ [b0]))
by (pose proof STR as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia])
end.
(call real_strtoll_specZ); [lia | lia | lia | exact STR2 | exact NONUL | lia | exact EPL | exact ERR | exact GOTF | exact GF
| exact ST1 | lia | lia | lia | lia | lia | lia | lia | assumption |].
lazymatch goal with H1 : rw_cells _ ?mc (bv_unsigned sp + -48) [C8 (Z_to_bv 64 (A + ?jj))], H2 : 0 <= ?jj <= _,
H3 : rw_cells _ _ (6434400 - 164) [C4 ?ee], H4 : stk _ _ lo (bv_unsigned sp + -48) |- _ =>
rename H1 into EPL', H2 into Hj, H3 into ERR3, H4 into ST3, jj into j, ee into e1 end.
repeat match goal with H : bytes_at _ _ A (str ++ [b0]) |- _ => clear H end.
step.
do 7 step.

carve_frame 72%nat ST3.
do 12 stepz.
do 4 step.
step. if_falsex.
step.
step.
step. if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT2 : asan_rt_ok mc)
by (eapply asan_rt_ok_transport; [exact RT | exact MU | intros c Hc; pose proof (a4_rt_cells_in_img c Hc); pose proof (a4_rt_cells_not_errno c Hc);
unfold A_TP in *; cbn [disjoint_from]; repeat split; try lia; exact I]);
assert (UPE2 : unpoisoned asegs mc A_SB E 8)
by (eapply unpoisoned_transport; [exact UPE | exact MU | intros u w Hu Hw; eapply (shadow_outside_W E lo (bv_unsigned sp) E 8); try eassumption; lia]);
assert (UPA2 : unpoisoned asegs mc A_SB A (L + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros u w Hu Hw; eapply (shadow_outside_W E lo (bv_unsigned sp) A (L + 1)); try eassumption; lia])
end.
clear RT UPE UPA.

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mc _) =>
enough (MID1 : forall x0 x1 x5 x6 x7 : word,
evt asegs Q (MS (bvmap_set (Z_to_bv 5 10) x0 (bvmap_set (Z_to_bv 5 11) x1 (bvmap_set (Z_to_bv 5 15) x5
(bvmap_set (Z_to_bv 5 16) x6 (bvmap_set (Z_to_bv 5 17) x7 R)))))
F (Z_to_bv 64 0x61300) fc None mc (seg_rom asegs)))
end.
{ assert (Hh : E / 8 <= (E + 7) / 8 <= E / 8 + 1) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (E / 8 + A_SB) UPE2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((E + 7) / 8 + A_SB) UPE2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GE0 : forall i, 0 <= i -> E / 8 + i < (E + 7) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (E / 8 + 2147450880 + i)) 1 = Some [Z_to_bv 8 0]);
[ intros i Hi Hil; apply ov_read1_of_ro;
replace (E / 8 + 2147450880 + i) with ((E / 8 + i) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPE2); lia |];
assert (HRE : exists u, ov_read_bytes asegs mc (Z_to_bv 64 ((E + 7) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 u]
/\ (u = 0 \/ (0 < u < 8 /\ (E + 7) mod 8 < u)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPE2) as (u & Hro & Hu); replace (E + 8 - 1) with (E + 7) in Hro, Hu by lia;
exists u; split; [| exact Hu]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPE2 UPA2.
rt_cell RT2 0xe5db8 as GOTSB2. rt_cell RT2 0xefaf8 as SBC2. apply ro_C8_of_bytes_at in GOTSB2. apply ro_C8_of_bytes_at in SBC2.
do 3 step.
step.
do 2 step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + E / 8) with (E / 8 + 2147450880) by lia.
replace (2147450880 + (E + 7) / 8) with ((E + 7) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (E / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((E + 7) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply MID1. }
destruct HRE as (u & HR & Hu).
assert (Hu8 : 0 <= u < 128) by (destruct Hu as [->|(? & ?)]; lia).
clear V1c V2c.
step. rewrite (sxb_small u) by lia. clear HR.
step. rewrite (unsigned_lit (E + 7)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hu as [-> | (Hk & Hlast)].
+ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (E / 8) ((E + 7) / 8)) as [Heq1|Hne1].
* if_truex. step. step. if_true. apply MID1.
* if_falsex.
pose proof (GE0 0 ltac:(lia) ltac:(lia)) as HR. rewrite Z.add_0_r in HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step. if_falsex.
step. step. if_true. apply MID1.
+ rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 u)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((E + 7) mod 8)) (Z_to_bv 64 u)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (E / 8) ((E + 7) / 8)) as [Heq1|Hne1].
* if_truex. step. step. if_true. apply MID1.
* if_falsex.
pose proof (GE0 0 ltac:(lia) ltac:(lia)) as HR. rewrite Z.add_0_r in HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step. if_falsex.
step. step. if_true. apply MID1. }
intros y0 y1 y5 y6 y7.
step.
replace (v_sltiu (Z_to_bv 64 10) 1) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
step. step.
replace (v_sltiu (Z_to_bv 64 8) 35) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
step.
step. if_false.
step.

lazymatch type of FR0 with rw_cells _ _ ?fa0 ?fcs0 => lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
enough (EPI : forall (w z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z28 z29 z30 z31 : word)
(mc : word -> option byte) (e2 : word),
munch [(E, E + 8); (6434400 - 164, 6434400 - 160); (lo, bv_unsigned sp)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc E [C8 (Z_to_bv 64 (A + j))] -> rw_cells asegs mc (6434400 - 164) [C4 e2] ->
stk asegs mc lo (bv_unsigned sp + -120) -> rw_cells asegs mc fa0 fcs0 -> rw_cells asegs mc fa fcs ->
rw_cells asegs mc (bv_unsigned sp + -48) [C8 (Z_to_bv 64 (A + j))] ->
evt asegs Q (MS (mkR w (Z_to_bv 64 (bv_unsigned sp + -2192)) gp (Z_to_bv 64 6434400) z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17
z18 z19 z20 z21 z22 z23 s8 s9 s10 s11 z28 z29 z30 z31)
F (Z_to_bv 64 0x613f8) fc None mc (seg_rom asegs)))
end end.
2: { clear - STR K Hj SEPE SEPA SEPAE SEPAR LO LOS SPA RA SPR ACG HA HAn HE HEn STRB.
intros w z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z28 z29 z30 z31 mc e2 MU WM MI EPm ERRm ST FR0 FR EPL.
do 12 step.
replace (ret_pc (Z_to_bv 64 0x57444)) with (Z_to_bv 64 0x57444) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 8 step.
assert (STRm : bytes_at asegs mc A (str ++ [b0]))
by (pose proof STR as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
eapply K; [exact MU | exact WM | exact MI | exact EPm | exact Hj | exact STRm | exact ERRm |].
release_frame FR0 ST (bv_unsigned sp + -48). release_frame EPL ST (bv_unsigned sp + -40). release_frame FR ST (bv_unsigned sp). exact ST. }

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mc _) =>
enough (JOIN : forall (ea : Z) (q1 q2 q4 q5 : word), A <= ea <= A + L ->
evt asegs Q (MS (bvmap_set (Z_to_bv 5 11) q1 (bvmap_set (Z_to_bv 5 12) q2 (bvmap_set (Z_to_bv 5 13) (Z_to_bv 64 ea)
(bvmap_set (Z_to_bv 5 14) q4 (bvmap_set (Z_to_bv 5 15) q5 R)))))
F (Z_to_bv 64 0x61378) fc None mc (seg_rom asegs)))
end.
{ destruct (Z.eq_dec j 0) as [Hj0 | Hjn].
-
if_truex.
step. step. step. step.
lazymatch goal with |- evt _ _ (MS ?R1 _ _ _ _ ?mc _) =>
assert (STRw : bytes_at asegs mc A (str ++ [b0]))
by (pose proof STR as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]);
assert (WS : forall (cnt : nat) (pa : Z) (r4 r5 : word), Z.to_nat (A + L - pa) = cnt -> A <= pa <= A + L ->
evt asegs Q (MS (bvmap_set (Z_to_bv 5 13) (Z_to_bv 64 pa) (bvmap_set (Z_to_bv 5 14) r4 (bvmap_set (Z_to_bv 5 15) r5 R1)))
F (Z_to_bv 64 0x61354) fc None mc (seg_rom asegs)))
end.
{ clear EPI.
induction cnt as [cnt IH] using lt_wf_ind; intros pa r4 r5 Hcnt Hp.
assert (exists cp, nth_error (str ++ [b0]) (Z.to_nat (pa - A)) = Some cp) as (cp & Hcp).
{ destruct (nth_error (str ++ [b0]) (Z.to_nat (pa - A))) as [cp|] eqn:En; [exists cp; reflexivity|].
apply nth_error_None in En. rewrite length_app in En. cbn [length] in En. lia. }
pose proof (byte_range8 cp) as Rcp.
pose proof (cstr_nth_zero str (Z.to_nat (pa - A)) cp NONUL Hcp) as Zcp.
pose proof (u8ro_read asegs _ A (str ++ [b0]) (pa - A) cp _ STRw Hcp ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
step. clear RD.
cbv delta [zxb].
step.
step.
rewrite (blank_test (bv_unsigned cp)) by lia.
destruct ((9 <=? bv_unsigned cp) && (bv_unsigned cp <=? 13))%bool eqn:Hbl; cbv iota.
+ assert (bv_unsigned cp <> 0) by (apply andb_true_iff in Hbl as [H9 _]; apply Z.leb_le in H9; lia).
step.
apply (IH (Z.to_nat (A + L - (pa + 1))) ltac:(lia) (pa + 1)); lia.
+ step.
destruct (Z.eq_dec (bv_unsigned cp) 32) as [Hsp | Hnsp].
* if_truex. step. apply (IH (Z.to_nat (A + L - (pa + 1))) ltac:(lia) (pa + 1)); lia.
* if_falsex. step. step.
destruct (Z.eq_dec (bv_unsigned cp) 43) as [Hpl | Hnpl].
-- if_truex. step. apply (JOIN (pa + 1)); lia.
-- if_falsex. step. step.
destruct (Z.eq_dec (bv_unsigned cp) 45) as [Hmi | Hnmi].
++ if_falsex. step. apply (JOIN (pa + 1)); lia.
++ if_truex. apply (JOIN pa); lia. }
apply (WS (Z.to_nat (A + L - A)) A); lia.
- if_falsex. step. if_truex.
apply (JOIN (A + j)); lia. }

intros ea q1 q2 q4 q5 Hea.
do 3 step.
step. if_true.
step. step.
step. step.
rewrite (unsigned_lit ea), (unsigned_lit A) by lia. rewrite (unsigned_lit (ea - A + 1)) by lia. rewrite land_ones64_l by lia.
step. step. rewrite (unsigned_lit A) by lia. rewrite (lxor_ones64 A) by lia. if_falsex.
step. step. step.
replace (ea - A + -64) with ((ea - A + 1) + -65) by lia.
assert (UPAn : unpoisoned asegs m2 A_SB A (ea - A + 1)) by (eapply unpoisoned_sub_any; [exact UPA2 | lia | lia | lia]).
remember (ea - A + 1) as n eqn:En.
destruct (Z.le_gt_cases n 64) as [Hn64 | Hnbig].
+
rewrite (size_test_n n) by lia. cbv iota.
assert (Hg : A / 8 <= (A + n - 1) / 8 <= A / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (A / 8 + A_SB) UPAn ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((A + n - 1) / 8 + A_SB) UPAn ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
unfold A_SB in W1c, W2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GA0 : forall i, 0 <= i -> A / 8 + i < (A + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (A / 8 + 2147450880 + i)) 1 = Some [Z_to_bv 8 0]);
[ intros i Hi Hil; apply ov_read1_of_ro;
replace (A / 8 + 2147450880 + i) with ((A / 8 + i) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPAn); lia |];
assert (HRA : exists u, ov_read_bytes asegs mc (Z_to_bv 64 ((A + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 u]
/\ (u = 0 \/ (0 < u < 8 /\ (A + n - 1) mod 8 < u)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPAn) as (u & Hro & Hu); exists u; split; [| exact Hu]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
rt_cell RT2 0xe5db8 as GOTSB3. rt_cell RT2 0xefaf8 as SBC3. apply ro_C8_of_bytes_at in GOTSB3. apply ro_C8_of_bytes_at in SBC3.
clear UPA2 UPE2.
do 2 step.
step. replace (A + n) with (A + n - 1 + 1) by lia.
step.
step.
step. replace (A + n - 1 + 1 + -1) with (A + n - 1) by lia.
step. do 2 step. do 2 step.
sh_norm.
replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
replace (2147450880 + (A + n - 1) / 8) with ((A + n - 1) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (A / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((A + n - 1) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mc _) =>
assert (LOOPA : forall (Kn : nat) (i : Z) (p3 p4 : word),
Z.to_nat ((A + n - 1) / 8 - A / 8 - i) = Kn -> 0 <= i -> A / 8 + i < (A + n - 1) / 8 ->
evt asegs Q (MS (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (A / 8 + 2147450880 + i)) (bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0)
(bvmap_set (Z_to_bv 5 13) p3 (bvmap_set (Z_to_bv 5 14) p4 R))))
F (Z_to_bv 64 0x614b4) fc None mc (seg_rom asegs)))
end.
{ clear Hg W1c W2c HRA.
induction Kn as [|Kn IH]; intros i p3 p4 HK Hi Hig; [lia|].
pose proof (GA0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (A / 8 + i + 1) ((A + n - 1) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true.
eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL'].
- if_truex. replace (A / 8 + 2147450880 + i + 1) with (A / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL']. }

destruct HRA as (u & HR & Hu).
assert (Hu8 : 0 <= u < 128) by (destruct Hu as [->|(? & ?)]; lia).
clear W1c W2c.
step. rewrite (sxb_small u) by lia. clear HR.
step. rewrite (unsigned_lit (A + n - 1)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hu as [-> | (Hk & Hlast)].
* rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (A / 8) ((A + n - 1) / 8)) as [Heq1|Hne1].
-- if_truex. step. step. if_true.
eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL'].
-- if_falsex. replace (A / 8 + 2147450880) with (A / 8 + 2147450880 + 0) by lia.
apply (LOOPA (Z.to_nat ((A + n - 1) / 8 - A / 8 - 0)) 0); lia.
* rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 u)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((A + n - 1) mod 8)) (Z_to_bv 64 u)) by (rewrite !signed_lit by lia; clear Hg; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (A / 8) ((A + n - 1) / 8)) as [Heq1|Hne1].
-- if_truex. step. step. if_true.
eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL'].
-- if_falsex. replace (A / 8 + 2147450880) with (A / 8 + 2147450880 + 0) by lia.
apply (LOOPA (Z.to_nat ((A + n - 1) / 8 - A / 8 - 0)) 0); lia.
+
rewrite (size_test_big n) by lia. cbv iota.
assert (APPn : app_mem A n) by (specialize (APP ltac:(lia)); unfold app_mem in *; lia).
step. if_truex.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc1 _) =>
lazymatch goal with STc : stk asegs mc1 lo ?hi |- _ =>
destruct (stk_split asegs mc1 lo (bv_unsigned sp - 2192) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply (OBL_REGION _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A n lo);
[ exact UPAn | exact RT2 | exact APPn | lia
| rewrite unsigned_lit by lia; lia | reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| assumption | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros p0 p1 p2 o1 o2 o3 o4 o5 o6 o7 r3 r4 r5 r6 m3 MU3 WM3 MI3 ST1' UP3 RT3.
lazymatch type of MU3 with munch _ ?mc1 _ =>
transport_after_call asegs mc1 m3 MU3 WM3; try match goal with H : mem_inv asegs mc1 |- _ => clear H end end.
clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 0x614d8)) with (Z_to_bv 64 0x614d8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
eapply EPI; [exact MU | exact WM | exact MI3 | exact EP | exact ERR3 | eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR0 | exact FR | exact EPL'].
Qed.
End IStrtoll.
End RC__1.

Lemma istrtoll_sound_U {RC__ : Q6q3.RunConsts} : istrtoll_spec_U.
Proof. exact (istrtoll_sound Qw5U.Mq4.region_is_poisoned_sound_U). Qed.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qc8V.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QlKV.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma v_sltu_1A : forall x y : word, bv_unsigned x < bv_unsigned y -> v_sltu x y = Z_to_bv 64 1.
Proof. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [reflexivity|lia]. Qed.

Lemma lxor_bound64A : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as HL.
assert (Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
assert (Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
lia.
Qed.

Lemma usl_ret_bitsA cur : 0 <= cur < 2^64 ->
Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 cur)) 6576104))) + -1)))
(bv_unsigned (Z_to_bv 64 cur)))
= Z_to_bv 64 (usl_retA cur).
Proof.
intros Hc. unfold usl_retA, GLOBLOC_A, LC_GLOBAL_A. rewrite (unsigned_lit cur) by lia.
pose proof (lxor_bound64A cur 6576104 Hc ltac:(lia)) as XR.
destruct (Z.eqb_spec cur 6576104) as [->|NE]; [reflexivity|].
assert (NZ : Z.lxor cur 6576104 <> 0) by (intros E; apply Z.lxor_eq in E; lia).
rewrite v_sltu_1A by (rewrite !unsigned_lit by lia; lia).
change (bv_unsigned (Z_to_bv 64 1) + -1) with 0. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lor_0_l. reflexivity.
Qed.

Lemma b1_readA : forall m a b rest, bytes_at asegs m a (b :: rest) -> ov_read_bytes asegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros m a b rest H.
pose proof (bytes_at_read asegs m a (b :: rest) 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
cbv beta iota delta [Z.to_nat skipn firstn] in R. unfold wa in R. rewrite Z.add_0_r in R. exact R.
Qed.
Lemma cname_roA : forall m, mem_inv asegs m -> bytes_at asegs m CNAME_A [Z_to_bv 8 67; Z_to_bv 8 0].
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold CNAME_A; lia| unfold CNAME_A; cbn; lia| vm_compute; repeat split; reflexivity]. Qed.

Lemma nodup_app_disjZ : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; cbn; intros l2 x ND H1 H2; [exact H1|].
inversion ND as [|y' l' Hny Hnd]; subst.
destruct H1 as [-> | H1]; [apply Hny; apply in_or_app; right; exact H2 | exact (IH _ _ Hnd H1 H2)].
Qed.

Section LocA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma lm_blk_notin_LB : forall A LB LM FRS B m md d n k, HEAPAx A LB LM FRS B m md -> In (d, n) LM -> ~ In (d, k) LB.
Proof.
intros A LB LM FRS B m md d n k HP Hin Hc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND.
exact (nodup_app_disjZ _ _ d ND (in_map blk_addr _ _ Hc) (in_map blk_addr _ _ Hin)).
Qed.

Lemma lm_head_fresh : forall A LB LM FRS B m md r n k, HEAPAx A LB ((r, n) :: LM) FRS B m md -> ~ In (r, k) (LB ++ LM).
Proof.
intros A LB LM FRS B m md r n k HP Hin.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. cbn [map blk_addr fst] in ND.
apply (Permutation_NoDup (Permutation_sym (Permutation_middle _ _ _))) in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni. rewrite <- map_app. exact (in_map blk_addr _ _ Hin).
Qed.

Theorem errno_location_A_ok : errno_location_A_stmt.
Proof.
unfold errno_location_A_stmt, A_ERRNO_LOCATION. intros until m. intros TP. subst tp. unfold A_ERRNO, A_TP.
step. step. step. apply evt_done. reflexivity.
Qed.

Theorem uselocale_A_ok : uselocale_A_stmt.
Proof.
unfold uselocale_A_stmt, A_USELOCALE. intros until nw. intros LC Hcur Hnw TP MI. subst tp.
unfold LOCCELL_A, usl_newA, A_TP in *. change (6444320 - 48) with 6444272 in *.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(6444272, 6444272 + 8)] m) as MU.
step. step. step. step.
destruct (Z.eq_dec nw 0) as [->|NZ].
- step. if_truex. do 6 step. rewrite usl_ret_bitsA by lia.
apply evt_done. exists m. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact LC].
- step. if_falsex. rewrite (proj2 (Z.eqb_neq _ _) NZ). step. step.
destruct (Z.eq_dec nw (2^64 - 1)) as [->|NG].
+ if_falsex. step. stepz. do 6 step. rewrite usl_ret_bitsA by lia.
apply evt_done. exists m0. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold LC_GLOBAL_A, GLOBLOC_A. rewrite Z.eqb_refl. exact LC.
+ if_truex. stepz. do 6 step. rewrite usl_ret_bitsA by lia.
apply evt_done. eexists. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold LC_GLOBAL_A. rewrite (proj2 (Z.eqb_neq _ _) NG). exact LC.
Qed.

Theorem freelocale_A_ok : freelocale_A_stmt HIx.
Proof.
unfold freelocale_A_stmt, A_FREELOCALE, A_DUPLOCALE, A_NEWLOCALE. intros until errv. intros HP HIN ST LO LOS SPA HT ERR TP RA K.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heap_pres_refl A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
assert (HINX : In (d, n) (LB ++ LM)) by (apply in_or_app; right; exact HIN).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ d n HP HINX) as (Hn0 & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ d n HP HINX) as Himg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst tp. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 5 step.

do 22 step.
repeat match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end.
rewrite !(unsigned_lit d) by lia.
assert (X1 : forall k, 0 <= k < 2^64 -> k <> d -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor d k)) = Z_to_bv 64 1).
{ intros k Hk NE. pose proof (lxor_bound64A d k ltac:(lia) Hk). apply v_sltu_1A. rewrite !unsigned_lit by lia.
assert (Z.lxor d k <> 0) by (intros E; apply Z.lxor_eq in E; lia). lia. }
rewrite !X1 by lia. rewrite (v_sltu_1A (Z_to_bv 64 0) (Z_to_bv 64 d)) by (rewrite !unsigned_lit by lia; lia).
change (bv_unsigned (Z_to_bv 64 1)) with 1. cbn [Z.land].
change (Z.land 1 1) with 1. change (bv_unsigned (Z_to_bv 64 1)) with 1. change (Z.land 1 1) with 1.
step. if_falsex. do 4 step.
release_frame FR ST (bv_unsigned sp).
step.

alloc_callA (hiA_free2 A4L HIx) A4L HIx HP MU WM MI.
all: rewrite ?unsigned_lit by lia; cbn [uw_pre uw_ok uw_key uw_cost bB bD charge]; a4l_goal.
{ right. exists n. exact HIN. }
all: try eassumption; try reflexivity; try (unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
eapply K; [exact RS3| exact VM3| exact ST3| | exact ERR3| exact HP3].
eapply heap_pres_trans; [| exact HPR3].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU| exact WM|].
eapply (client_outsideA _ HIx); [exact HP| | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia| solve_clientWA A4L HIx HP].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact (in_lb_remove _ _ _ Hb)| right; exact Hb].
Qed.

Lemma seq_cases48A (P : nat -> Prop) : (forall k, (k < 48)%nat -> P k) <-> Forall P (seq 0 48).
Proof. rewrite Forall_forall. split; [intros H k Hk; apply H; apply in_seq in Hk; lia| intros H k Hk; apply H; apply in_seq; lia]. Qed.
Lemma globloc_romA : forall k, (k < 48)%nat -> seg_rom asegs (wa (GLOBLOC_A + Z.of_nat k)) <> None.
Proof. apply (proj2 (seq_cases48A _)). unfold GLOBLOC_A. repeat constructor; vm_compute; discriminate. Qed.
Lemma globloc_wA : forall k, (k < 48)%nat ->
match find_segment asegs (GLOBLOC_A + Z.of_nat k) 1 with
| Some seg => if seg_writable seg then segment_byte_at (seg_bytes seg) (Z.to_N (GLOBLOC_A + Z.of_nat k - Z.of_N (seg_base seg))) else None
| None => None end <> None.
Proof. apply (proj2 (seq_cases48A _)). unfold GLOBLOC_A. repeat constructor; vm_compute; discriminate. Qed.
Lemma globloc_anyA m : exists gl, rw_cells asegs m GLOBLOC_A [CB 48%nat gl].
Proof.
set (f := fun i : nat => match mrd asegs m (wa (GLOBLOC_A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
exists (map f (seq 0 48)).
assert (LEN : length (map f (seq 0 48)) = 48%nat) by (rewrite length_map, length_seq; reflexivity).
split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LEN| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [unfold GLOBLOC_A; lia|]. split; [rewrite LEN; unfold GLOBLOC_A; lia|].
intros i Hi. rewrite LEN in Hi. rewrite nth_error_map, (nth_error_seq 0 48 i) by lia. cbn [option_map Nat.add].
replace (i <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map].
subst f. cbv beta. destruct (mrd asegs m (wa (GLOBLOC_A + Z.of_nat i))) eqn:E; [reflexivity|].
exfalso. unfold mrd in E. destruct (m (wa (GLOBLOC_A + Z.of_nat i))); [discriminate|]. exact (globloc_romA i Hi E).
- split; [unfold GLOBLOC_A; lia|]. split; [unfold GLOBLOC_A; cbn; lia|]. cbn [cells_size csize Nat.add]. intros j Hj.
unfold wview. destruct (m (wa (GLOBLOC_A + j))); [discriminate|].
rewrite wa_unsigned by (unfold GLOBLOC_A; lia).
replace j with (Z.of_nat (Z.to_nat j)) by lia. apply globloc_wA. lia.
Qed.

Theorem duplocale_A_ok : duplocale_A_stmt HIx.
Proof.
unfold duplocale_A_stmt, A_FREELOCALE, A_DUPLOCALE, A_NEWLOCALE. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA LML BM K.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst tp. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
do 6 step. step.
alloc_callA (hiA_malloc2 A4L HIx) A4L HIx HP MU WM MI.
all: rewrite ?unsigned_lit by lia; cbn [uw_pre uw_ok uw_key uw_cost bB bD charge]; a4l_goal.
all: try eassumption; try reflexivity; try (unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
rewrite ?unsigned_lit in ST2, HPR2 by lia.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST ERR.
destruct OUT2 as [(-> & He & HP2) | (Hr & [bjunk BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex. do 3 step.
release_frame FR ST2 (bv_unsigned sp).
step.
evt_done5. eapply K; [| exact VM2| exact ST2| exact HPR| exact ERR2| left; split; [reflexivity| split; [exact He| exact HP2]]].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; right; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; right; left; reflexivity)) as Himg_r.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
destruct (globloc_anyA m2) as [gl GL]. unfold GLOBLOC_A in GL.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step. unfold LC_GLOBAL_A. if_falsex. step. step.
do 12 step.
do 3 step. release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. eapply K; [| exact VM2| exact ST2| | exact ERR2| right].
+ unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA _ HIx); [exact HP2 | | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
apply Forall_cons; [left; cbn; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists r, 48. cbn [fst snd]. split; [apply in_or_app; right; left; reflexivity|]. split; [| lia].
apply not_in_app3; [exact (lm_head_fresh _ _ _ _ _ _ _ r 48 48 HP2) | exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; right; left; reflexivity))].
+ split; [exact Hr|]. split.
* lazymatch type of BLK with rw_cells _ _ _ ?cs => exists (cells_bytes cs) end.
eapply (rw_cells_recast _ _ _ _ _ BLK); [| reflexivity| reflexivity].
cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length; [reflexivity|]. cbn [cells_wf cell_wf]. repeat split.
* eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU). solve_frameW_withA HP2.
Qed.

Lemma notin_lb_removeA : forall LB d n k, List.NoDup (map QCcH.blk_addr LB) -> In (d, n) LB -> ~ In (d, k) (lb_remove d LB).
Proof.
induction LB as [|[a sz] LB IH]; intros d n k ND Hin Hc; [exact Hin|].
cbn [map QCcH.blk_addr fst] in ND. inversion ND as [|x l Hna Hnd]; subst.
cbn [lb_remove QCcH.blk_addr fst] in Hc.
destruct (Z.eqb_spec a d) as [->|NE].
- apply Hna. apply in_map_iff. exists (d, k). split; [reflexivity| exact Hc].
- destruct Hc as [E|Hc]; [inversion E; subst; exact (NE eq_refl)|].
destruct Hin as [E|Hin]; [inversion E; subst; exact (NE eq_refl)|].
exact (IH d n k Hnd Hin Hc).
Qed.

Ltac nl_exit K r jk :=
stepz; stepz; stepz;
stepz; stepz; if_falsex; stepz;
lazymatch goal with | CAN2 : bytes_at asegs _ 6575456 (le8 _) |- _ =>
pose proof (le8_read asegs _ _ _ CAN2) as RD9; stepz; clear RD9 end;
stepz; stepz;
let KC := fresh "KC" in if_cases KC; [exfalso; rewrite bv_eqb_refl in KC; discriminate KC|];
stepz; do 6 stepz; stepz;
lazymatch goal with | FR : rw_cells asegs _ (bv_unsigned ?sp + -112) _, ST : stk asegs _ _ _ |- _ =>
release_frame FR ST (bv_unsigned sp) end;
stepz;
evt_done5;
eapply (K _ _ r jk).

Theorem newlocale_A_ok : newlocale_A_stmt HIx.
Proof.
unfold newlocale_A_stmt, A_FREELOCALE, A_DUPLOCALE, A_NEWLOCALE. intros until errv. intros HP HIN BLK LCK ST LO LOS SPA HT ERR TP RA K.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM.
assert (HINX : In (d, 48) (LB ++ LM)) by (apply in_or_app; right; exact HIN).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ d 48 HP HINX) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ d 48 HP HINX) as Himg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_l in ND.
pose proof (notin_lb_removeA LM d 48 48 ND HIN) as NLR. clear ND.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (g & CAN1 & CAN2 & CAN3). a4l.
pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL. cbn [hl_segs hl_libc hla_base A4L A4H Z.add] in NL.
pose proof (cname_roA m MI) as CN. unfold CNAME_A in CN.
unfold LOCALE_LOCK_A, CNAME_A in *. change (6444320 - 16) with 6444304 in CAN3.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m) as MU.

assert (HPRm : forall mx, munch [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m mx -> wmono asegs m mx ->
heap_pres A4H (LB ++ lb_remove d LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx).
{ intros mx MUx WMx. eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx| exact WMx|].
eapply (client_outsideA _ HIx); [exact HP| | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|].
- intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact (in_lb_remove _ _ _ Hb)| right; exact Hb].
- apply Forall_cons; [left; cbn; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists d, 48. cbn [fst snd]. split; [exact HINX|]. split; [| lia].
intros Hc. apply in_app_or in Hc. destruct Hc as [Hc|Hc]; [exact (lm_blk_notin_LB _ _ _ _ _ _ _ d 48 48 HP HIN Hc)|].
apply in_app_or in Hc. destruct Hc as [Hc|Hc]; [exact (NLR Hc)|].
exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ d 48 HP HINX Hc). }
assert (HPm : forall mx, munch [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m mx -> wmono asegs m mx -> mem_inv asegs mx ->
HEAPAx A LB LM FRS B mx md).
{ intros mx MUx WMx MIx. eapply (heapA_client_frame A4L HIx); [exact HP | | exact WMx | exact MIx].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUx).
apply Forall_cons; [left; cbn; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists d, 48. cbn [fst snd]. split; [exact HINX| lia]. }
subst tp. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
destruct (rw_cells_CB_sizes asegs m [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat _ _ _ FR eq_refl)
as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & FR'). clear FR. rename FR' into FR.
do 7 stepz. do 3 stepz.
stepz. pose proof (le8_read asegs _ _ _ CAN1) as RD1. stepz. clear RD1.
pose proof (le8_read asegs _ _ _ CAN2) as RD2. stepz. clear RD2.
stepz.
stepz. stepz. stepz.

stepz. pose proof (b1_readA _ _ _ _ NL) as RD3. stepz. clear RD3.
replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
stepz. if_truex. stepz.

stepz. stepz. if_falsex. stepz. if_falsex.
stepz. stepz. stepz. stepz. stepz.
if_cases K0. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_truex. stepz. if_falsex. stepz. stepz. stepz. stepz.
carve_frame 384%nat ST.
destruct (rw_cells_CB_sizes asegs _ [272;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat _ _ _ FR0 eq_refl)
as (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & p14 & FR0'). clear FR0. rename FR0' into FR0.
do 14 stepz.
stepz. stepz. pose proof (le8_read asegs _ _ _ CAN1) as RD1. stepz. clear RD1.
pose proof (le8_read asegs _ _ _ CAN2) as RD2. stepz. clear RD2.
stepz.
pose proof (b1_readA _ _ _ _ CN) as RD3. stepz. clear RD3.
replace (zxb (Z_to_bv 8 67)) with (Z_to_bv 64 67) in * by (apply bv_eq; vm_compute; reflexivity).
stepz. stepz. if_falsex. stepz. stepz. if_truex.
stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (cname_roA mx ltac:(assumption)) as CNx; unfold CNAME_A in CNx;
pose proof (proj1 (bytes_at_app asegs mx 143616 [Z_to_bv 8 67] [Z_to_bv 8 0]) CNx) as [_ CN1] end.
pose proof (b1_readA _ _ _ _ CN1) as RD4. stepz.
replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) in * by (apply bv_eq; vm_compute; reflexivity).
stepz. stepz. if_truex.

stepz. stepz. stepz. stepz. stepz. stepz. if_falsex.
stepz. stepz. stepz. if_falsex.
stepz. stepz. stepz. if_falsex.
stepz. clear RD4 CN1 CNx. stepz. stepz. if_truex.

stepz. if_truex. stepz.
pose proof (le8_read asegs _ _ _ CAN2) as RD2. stepz. clear RD2. stepz. stepz.
if_cases KC. { exfalso. rewrite bv_eqb_refl in KC. discriminate KC. }
stepz. do 13 stepz. stepz.
release_frame FR0 ST (bv_unsigned sp + -112).
stepz.

stepz. stepz. stepz. if_falsex.

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K2. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K3. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K4. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K5. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists. }

stepz. stepz. stepz. stepz. stepz.
stepz. if_falsex. stepz. stepz. if_falsex. stepz. stepz. stepz. if_falsex. stepz. if_falsex. stepz. if_falsex.

do 12 stepz.
stepz. stepz.
lazymatch type of BLK with rw_cells _ _ _ ?cs =>
nl_exit K d (cells_bytes cs); [| exact ST| apply HPRm; assumption| | exact LCK| exact ERR| apply HPm; assumption| left; reflexivity] end.
- unfold ret_state. cbn [hl_segs hla_base A4L A4H]. repeat eexists.
- eapply (rw_cells_recast _ _ _ _ _ BLK); [| reflexivity| reflexivity].
cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length; [reflexivity| cbn [cells_wf cell_wf]; repeat split].
Qed.
End LocA.

End RC__1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1sw_c2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Module AF_F_strtol := Q1sw_c2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj.
Import ListNotations.
Open Scope Z_scope.

Ltac if_zxb b :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
replace c with b; [cbv iota | symmetry; cbv delta [zxb]; solve_condx]
end.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
apply Z.mod_small. lia.
Qed.

Lemma blank_test : forall c, 0 <= c < 256 -> bv_ltu (Z_to_bv 64 (c + -9)) (Z_to_bv 64 5) = ((9 <=? c) && (c <=? 13))%bool.
Proof.
intros c Hc. unfold bv_ltu. rewrite !unsigned_lit_wrap. change (5 mod 2 ^ 64) with 5.
destruct (Z_lt_le_dec c 9) as [Hlt | Hge].
- replace ((c + -9) mod 2 ^ 64) with (2 ^ 64 + c - 9) by (Z.div_mod_to_equations; lia).
replace (9 <=? c) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply Z.ltb_ge. lia.
- rewrite Z.mod_small by lia. replace (9 <=? c) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.leb_spec0 c 13); [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma shadow_outside_W : forall E lo hi s n a k,
app_mem E 8 -> alloc_ceiling <= lo -> 0 <= s -> s + n <= 2^47 -> 0 < n ->
shadow_span_lo A_SB s <= a -> a + k <= shadow_span_hi A_SB s n ->
disjoint_from [(E, E + 8); (A_TP - 164, A_TP - 160); (lo, hi)] a k.
Proof.
intros E lo hi s n a k APP LO Hs Hsn Hn Ha Hk.
pose proof (shadow_outside_stack A_SB s n lo hi a k ltac:(unfold A_SB; lia) Hs Hsn Hn LO Ha Hk) as [D _].
unfold shadow_span_lo, shadow_span_hi, A_SB in Ha, Hk. unfold app_mem, A_SB, A_HMB in APP. unfold A_TP.
assert ((s + n - 1) / 8 <= 2^44) by (Z.div_mod_to_equations; lia).
cbn. split; [| split; [| split; [exact D | exact I]]]; Z.div_mod_to_equations; lia.
Qed.

Lemma real_strtoll_specZ :
forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte) (str : list byte) (SP A E lo : Z) (e g ej : word),
0 <= SP < 2^64 -> 0 <= A < 2^64 -> 0 <= E < 2^64 ->
bytes_at asegs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells asegs m E [C8 ej] ->
rw_cells asegs m (0x625520 - 164) [C4 e] ->
bytes_at asegs m 0xe8f90 (le8 (Z_to_bv 64 0x645560)) -> bytes_at asegs m 0x645560 (le8 g) ->
stk asegs m lo SP -> (0x647000 <= lo)%Z -> (lo <= SP - 368)%Z ->
(0x647000 <= E)%Z ->
(E + 8 <= SP - 368 \/ SP <= E)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 368 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= 0x625520 - 164 \/ 0x625520 - 160 <= A)%Z ->
mem_inv asegs m ->
evt asegs (fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (j : Z) (e' : word),
ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 0x625520) x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(SP - 368, SP); (E, E + 8); (0x625520 - 164, 0x625520 - 160)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' E [C8 (Z_to_bv 64 (A + j))] /\ (0 <= j <= Z.of_nat (length str))%Z
/\ bytes_at asegs m' A (str ++ [b0])
/\ rw_cells asegs m' (0x625520 - 164) [C4 e']
/\ stk asegs m' lo SP)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 0x625520) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 E) (Z_to_bv 64 10) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdceac) fc None m (seg_rom asegs)).
Proof.
intros until ej. intros HSP HA HE STR NONUL AB EP ERR GOTF GF ST LO LOS ELO SEP1 SEP2 SEP3 SEP4 MI.
pose proof (AF_F_strtol.strtoll_spec ra (Z_to_bv 64 SP) gp (Z_to_bv 64 0x625520) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 E) (Z_to_bv 64 10)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str SP A E lo e g ej) as X.
unfold AF_F_strtol.strtoll_entry, AF_F_strtol.GOT_GUARD, AF_F_strtol.GUARD in X.
rewrite (unsigned_lit SP), (unsigned_lit A), (unsigned_lit E) in X by lia.
eapply evt_mono; [eapply X; first [reflexivity | assumption | lia] |].
intros ms' P. unfold AF_F_strtol.strtox_post, AF_F_strtol.strtox_W in P. exact P.
Qed.

Lemma a4_rt_cells_not_errno : forall c, In c a4_rt_cells ->
fst c + Z.of_nat (length (snd c)) <= A_TP - 164 \/ A_TP - 160 <= fst c.
Proof.
intros c Hc. unfold A_TP. unfold a4_rt_cells, a4_rt_consts in Hc. cbn [app] in Hc.
repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; unfold A_GOT_SB, A_SB_CELL;
repeat match goal with |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end; lia |]).
destruct Hc.
Qed.

Section IStrtoll.
Hypothesis OBL_REGION : region_is_poisoned_spec_U.

Lemma istrtoll_sound : istrtoll_spec_U.
Proof.
unfold istrtoll_spec_U.
intros until Q. intros UPA UPE RT APP APPE Ha0 Ha1 Ha2 Htp HA HAn Hl40 HE HEn STR NONUL EP ERR GOTF GF SEPE SEPA SEPAE SEPAR ST LO LOS SPA MI RA K.
subst a0 a1 a2 tp. word_range sp SPR. pose proof alloc_ceiling_ge as ACG.
pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB.
set (L := Z.of_nat (length str)) in *.

rt_cell RT 0xf2e98 as INITED. rt_cell RT 0xe81b0 as GOTCF. rt_cell RT 0xef9d5 as CF29. rt_cell RT 0xea1a0 as REALS.
rt_cell RT 0xe81a8 as GOTFL. rt_cell RT 0x183ddd as F245. rt_cell RT 0xe81b8 as GOTSB. rt_cell RT 0xf21b8 as SBC.
apply ro_C8_of_bytes_at in GOTCF. apply ro_C8_of_bytes_at in REALS. apply ro_C8_of_bytes_at in GOTFL.
apply ro_C8_of_bytes_at in GOTSB. apply ro_C8_of_bytes_at in SBC.
apply ro_C1_of_bytes_at in INITED. apply ro_C1_of_bytes_at in CF29. apply ro_C1_of_bytes_at in F245.
assert (RO10400 : ro_cells asegs m 0x10480 [CB 8 (le8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa))]).
{ change 8%nat with (length (le8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa))).
apply (ro_cells_image asegs); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
stash STR.
pose proof (munch_refl [(E, E + 8); (A_TP - 164, A_TP - 160); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_ISTRTOLL. unfold A_TP in *. unfold A_GOT_GUARD, A_GUARD in GOTF, GF. carve_frame 48%nat ST.
bstep.
do 6 bstep.
bstep. bstep. bstep.
bstep.
eapply init_gate_spec; [assumption | assumption | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a0x a1x m1 MU1 WM1 MI1 ST1.
lazymatch type of MU1 with munch _ ?mc _ =>
transport_after_call asegs mc m1 MU1 WM1; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU1 WM1 end.
replace (ret_pc (Z_to_bv 64 0x577c8)) with (Z_to_bv 64 0x577c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 5 bstep.
bstep. if_false.
do 2 bstep.
bstepz.
do 4 bstep.
apply (proj1 (rw_cells_app asegs _ _ [C8 (Z_to_bv 64 12297829382473034410)] _)) in FR as [EPL FR].
cbn [cells_size csize Nat.add] in FR. replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FR by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STR2 : bytes_at asegs mc A (str ++ [b0]))
by (pose proof STR as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia])
end.
(call real_strtoll_specZ); [lia | lia | lia | exact STR2 | exact NONUL | lia | exact EPL | exact ERR | exact GOTF | exact GF
| exact ST1 | lia | lia | lia | lia | lia | lia | lia | assumption |].
lazymatch goal with H1 : rw_cells _ ?mc (bv_unsigned sp + -48) [C8 (Z_to_bv 64 (A + ?jj))], H2 : 0 <= ?jj <= _,
H3 : rw_cells _ _ (6444320 - 164) [C4 ?ee], H4 : stk _ _ lo (bv_unsigned sp + -48) |- _ =>
rename H1 into EPL', H2 into Hj, H3 into ERR3, H4 into ST3, jj into j, ee into e1 end.
repeat match goal with H : bytes_at _ _ A (str ++ [b0]) |- _ => clear H end.
bstep.
do 7 bstep.

carve_frame 72%nat ST3.
do 12 bstepz.
do 4 bstep.
bstep. if_falsex.
bstep.
bstep.
bstep. if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT2 : asan_rt_ok mc)
by (eapply asan_rt_ok_transport; [exact RT | exact MU | intros c Hc; pose proof (a4_rt_cells_in_img c Hc); pose proof (a4_rt_cells_not_errno c Hc);
unfold A_TP in *; cbn [disjoint_from]; repeat split; try lia; exact I]);
assert (UPE2 : unpoisoned asegs mc A_SB E 8)
by (eapply unpoisoned_transport; [exact UPE | exact MU | intros u w Hu Hw; eapply (shadow_outside_W E lo (bv_unsigned sp) E 8); try eassumption; lia]);
assert (UPA2 : unpoisoned asegs mc A_SB A (L + 1))
by (eapply unpoisoned_transport; [exact UPA | exact MU | intros u w Hu Hw; eapply (shadow_outside_W E lo (bv_unsigned sp) A (L + 1)); try eassumption; lia])
end.
clear RT UPE UPA.

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mc _) =>
enough (MID1 : forall x0 x1 x5 x6 x7 : word,
evt asegs Q (MS (bvmap_set (Z_to_bv 5 10) x0 (bvmap_set (Z_to_bv 5 11) x1 (bvmap_set (Z_to_bv 5 15) x5
(bvmap_set (Z_to_bv 5 16) x6 (bvmap_set (Z_to_bv 5 17) x7 R)))))
F (Z_to_bv 64 0x616d8) fc None mc (seg_rom asegs)))
end.
{ assert (Hh : E / 8 <= (E + 7) / 8 <= E / 8 + 1) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (E / 8 + A_SB) UPE2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((E + 7) / 8 + A_SB) UPE2 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GE0 : forall i, 0 <= i -> E / 8 + i < (E + 7) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (E / 8 + 2147450880 + i)) 1 = Some [Z_to_bv 8 0]);
[ intros i Hi Hil; apply ov_read1_of_ro;
replace (E / 8 + 2147450880 + i) with ((E / 8 + i) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPE2); lia |];
assert (HRE : exists u, ov_read_bytes asegs mc (Z_to_bv 64 ((E + 7) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 u]
/\ (u = 0 \/ (0 < u < 8 /\ (E + 7) mod 8 < u)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPE2) as (u & Hro & Hu); replace (E + 8 - 1) with (E + 7) in Hro, Hu by lia;
exists u; split; [| exact Hu]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPE2 UPA2.
rt_cell RT2 0xe81b8 as GOTSB2. rt_cell RT2 0xf21b8 as SBC2. apply ro_C8_of_bytes_at in GOTSB2. apply ro_C8_of_bytes_at in SBC2.
do 3 bstep.
bstep.
do 2 bstep. do 2 bstep. do 2 bstep.
sh_norm.
replace (2147450880 + E / 8) with (E / 8 + 2147450880) by lia.
replace (2147450880 + (E + 7) / 8) with ((E + 7) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (E / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((E + 7) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 bstep. bstep.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply MID1. }
destruct HRE as (u & HR & Hu).
assert (Hu8 : 0 <= u < 128) by (destruct Hu as [->|(? & ?)]; lia).
clear V1c V2c.
bstep. rewrite (sxb_small u) by lia. clear HR.
bstep. rewrite (unsigned_lit (E + 7)) by lia. rewrite land7_mod8 by lia.
bstep. bstep. bstep. bstep.
destruct Hu as [-> | (Hk & Hlast)].
+ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
bstep.
destruct (Z.eq_dec (E / 8) ((E + 7) / 8)) as [Heq1|Hne1].
* if_truex. bstep. bstep. if_true. apply MID1.
* if_falsex.
pose proof (GE0 0 ltac:(lia) ltac:(lia)) as HR. rewrite Z.add_0_r in HR.
bstep. rewrite ?zxb_zero. clear HR.
bstep. bstep. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
bstep. if_falsex.
bstep. bstep. if_true. apply MID1.
+ rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 u)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((E + 7) mod 8)) (Z_to_bv 64 u)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
bstep.
destruct (Z.eq_dec (E / 8) ((E + 7) / 8)) as [Heq1|Hne1].
* if_truex. bstep. bstep. if_true. apply MID1.
* if_falsex.
pose proof (GE0 0 ltac:(lia) ltac:(lia)) as HR. rewrite Z.add_0_r in HR.
bstep. rewrite ?zxb_zero. clear HR.
bstep. bstep. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
bstep. if_falsex.
bstep. bstep. if_true. apply MID1. }
intros y0 y1 y5 y6 y7.
bstep.
replace (v_sltiu (Z_to_bv 64 10) 1) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
bstep. bstep.
replace (v_sltiu (Z_to_bv 64 8) 35) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
bstep.
bstep. if_false.
bstep.

lazymatch type of FR0 with rw_cells _ _ ?fa0 ?fcs0 => lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
enough (EPI : forall (w z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z28 z29 z30 z31 : word)
(mc : word -> option byte) (e2 : word),
munch [(E, E + 8); (6444320 - 164, 6444320 - 160); (lo, bv_unsigned sp)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc E [C8 (Z_to_bv 64 (A + j))] -> rw_cells asegs mc (6444320 - 164) [C4 e2] ->
stk asegs mc lo (bv_unsigned sp + -120) -> rw_cells asegs mc fa0 fcs0 -> rw_cells asegs mc fa fcs ->
rw_cells asegs mc (bv_unsigned sp + -48) [C8 (Z_to_bv 64 (A + j))] ->
evt asegs Q (MS (mkR w (Z_to_bv 64 (bv_unsigned sp + -2192)) gp (Z_to_bv 64 6444320) z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17
z18 z19 z20 z21 z22 z23 s8 s9 s10 s11 z28 z29 z30 z31)
F (Z_to_bv 64 0x617d0) fc None mc (seg_rom asegs)))
end end.
2: { clear - STR K Hj SEPE SEPA SEPAE SEPAR LO LOS SPA RA SPR ACG HA HAn HE HEn STRB.
intros w z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z28 z29 z30 z31 mc e2 MU WM MI EPm ERRm ST FR0 FR EPL.
do 12 bstep.
replace (ret_pc (Z_to_bv 64 0x5781c)) with (Z_to_bv 64 0x5781c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 8 bstep.
assert (STRm : bytes_at asegs mc A (str ++ [b0]))
by (pose proof STR as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
eapply K; [exact MU | exact WM | exact MI | exact EPm | exact Hj | exact STRm | exact ERRm |].
release_frame FR0 ST (bv_unsigned sp + -48). release_frame EPL ST (bv_unsigned sp + -40). release_frame FR ST (bv_unsigned sp). exact ST. }

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mc _) =>
enough (JOIN : forall (ea : Z) (q1 q2 q4 q5 : word), A <= ea <= A + L ->
evt asegs Q (MS (bvmap_set (Z_to_bv 5 11) q1 (bvmap_set (Z_to_bv 5 12) q2 (bvmap_set (Z_to_bv 5 13) (Z_to_bv 64 ea)
(bvmap_set (Z_to_bv 5 14) q4 (bvmap_set (Z_to_bv 5 15) q5 R)))))
F (Z_to_bv 64 0x61750) fc None mc (seg_rom asegs)))
end.
{ destruct (Z.eq_dec j 0) as [Hj0 | Hjn].
-
if_truex.
bstep. bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS ?R1 _ _ _ _ ?mc _) =>
assert (STRw : bytes_at asegs mc A (str ++ [b0]))
by (pose proof STR as S0; unstash S0; eapply bytes_at_transport; [exact S0 | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]);
assert (WS : forall (cnt : nat) (pa : Z) (r4 r5 : word), Z.to_nat (A + L - pa) = cnt -> A <= pa <= A + L ->
evt asegs Q (MS (bvmap_set (Z_to_bv 5 13) (Z_to_bv 64 pa) (bvmap_set (Z_to_bv 5 14) r4 (bvmap_set (Z_to_bv 5 15) r5 R1)))
F (Z_to_bv 64 0x6172c) fc None mc (seg_rom asegs)))
end.
{ clear EPI.
induction cnt as [cnt IH] using lt_wf_ind; intros pa r4 r5 Hcnt Hp.
assert (exists cp, nth_error (str ++ [b0]) (Z.to_nat (pa - A)) = Some cp) as (cp & Hcp).
{ destruct (nth_error (str ++ [b0]) (Z.to_nat (pa - A))) as [cp|] eqn:En; [exists cp; reflexivity|].
apply nth_error_None in En. rewrite length_app in En. cbn [length] in En. lia. }
pose proof (byte_range8 cp) as Rcp.
pose proof (cstr_nth_zero str (Z.to_nat (pa - A)) cp NONUL Hcp) as Zcp.
pose proof (u8ro_read asegs _ A (str ++ [b0]) (pa - A) cp _ STRw Hcp ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
bstep. clear RD.
cbv delta [zxb].
bstep.
bstep.
rewrite (blank_test (bv_unsigned cp)) by lia.
destruct ((9 <=? bv_unsigned cp) && (bv_unsigned cp <=? 13))%bool eqn:Hbl; cbv iota.
+ assert (bv_unsigned cp <> 0) by (apply andb_true_iff in Hbl as [H9 _]; apply Z.leb_le in H9; lia).
bstep.
apply (IH (Z.to_nat (A + L - (pa + 1))) ltac:(lia) (pa + 1)); lia.
+ bstep.
destruct (Z.eq_dec (bv_unsigned cp) 32) as [Hsp | Hnsp].
* if_truex. bstep. apply (IH (Z.to_nat (A + L - (pa + 1))) ltac:(lia) (pa + 1)); lia.
* if_falsex. bstep. bstep.
destruct (Z.eq_dec (bv_unsigned cp) 43) as [Hpl | Hnpl].
-- if_truex. bstep. apply (JOIN (pa + 1)); lia.
-- if_falsex. bstep. bstep.
destruct (Z.eq_dec (bv_unsigned cp) 45) as [Hmi | Hnmi].
++ if_falsex. bstep. apply (JOIN (pa + 1)); lia.
++ if_truex. apply (JOIN pa); lia. }
apply (WS (Z.to_nat (A + L - A)) A); lia.
- if_falsex. bstep. if_truex.
apply (JOIN (A + j)); lia. }

intros ea q1 q2 q4 q5 Hea.
do 3 bstep.
bstep. if_true.
bstep. bstep.
bstep. bstep.
rewrite (unsigned_lit ea), (unsigned_lit A) by lia. rewrite (unsigned_lit (ea - A + 1)) by lia. rewrite land_ones64_l by lia.
bstep. bstep. rewrite (unsigned_lit A) by lia. rewrite (lxor_ones64 A) by lia. if_falsex.
bstep. bstep. bstep.
replace (ea - A + -64) with ((ea - A + 1) + -65) by lia.
assert (UPAn : unpoisoned asegs m2 A_SB A (ea - A + 1)) by (eapply unpoisoned_sub_any; [exact UPA2 | lia | lia | lia]).
remember (ea - A + 1) as n eqn:En.
destruct (Z.le_gt_cases n 64) as [Hn64 | Hnbig].
+
rewrite (size_test_n n) by lia. cbv iota.
assert (Hg : A / 8 <= (A + n - 1) / 8 <= A / 8 + 8) by (Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (A / 8 + A_SB) UPAn ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((A + n - 1) / 8 + A_SB) UPAn ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
unfold A_SB in W1c, W2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GA0 : forall i, 0 <= i -> A / 8 + i < (A + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (A / 8 + 2147450880 + i)) 1 = Some [Z_to_bv 8 0]);
[ intros i Hi Hil; apply ov_read1_of_ro;
replace (A / 8 + 2147450880 + i) with ((A / 8 + i) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPAn); lia |];
assert (HRA : exists u, ov_read_bytes asegs mc (Z_to_bv 64 ((A + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 u]
/\ (u = 0 \/ (0 < u < 8 /\ (A + n - 1) mod 8 < u)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPAn) as (u & Hro & Hu); exists u; split; [| exact Hu]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
rt_cell RT2 0xe81b8 as GOTSB3. rt_cell RT2 0xf21b8 as SBC3. apply ro_C8_of_bytes_at in GOTSB3. apply ro_C8_of_bytes_at in SBC3.
clear UPA2 UPE2.
do 2 bstep.
bstep. replace (A + n) with (A + n - 1 + 1) by lia.
bstep.
bstep.
bstep. replace (A + n - 1 + 1 + -1) with (A + n - 1) by lia.
bstep. do 2 bstep. do 2 bstep.
sh_norm.
replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
replace (2147450880 + (A + n - 1) / 8) with ((A + n - 1) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (A / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((A + n - 1) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 bstep. bstep.

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mc _) =>
assert (LOOPA : forall (Kn : nat) (i : Z) (p3 p4 : word),
Z.to_nat ((A + n - 1) / 8 - A / 8 - i) = Kn -> 0 <= i -> A / 8 + i < (A + n - 1) / 8 ->
evt asegs Q (MS (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (A / 8 + 2147450880 + i)) (bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0)
(bvmap_set (Z_to_bv 5 13) p3 (bvmap_set (Z_to_bv 5 14) p4 R))))
F (Z_to_bv 64 0x6188c) fc None mc (seg_rom asegs)))
end.
{ clear Hg W1c W2c HRA.
induction Kn as [|Kn IH]; intros i p3 p4 HK Hi Hig; [lia|].
pose proof (GA0 i Hi Hig) as HR.
bstep. rewrite ?zxb_zero. clear HR.
bstep. bstep. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
bstep.
destruct (Z.eq_dec (A / 8 + i + 1) ((A + n - 1) / 8)) as [Heq|Hne].
- if_falsex. bstep. bstep. if_true.
eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL'].
- if_truex. replace (A / 8 + 2147450880 + i + 1) with (A / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
bstep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL']. }

destruct HRA as (u & HR & Hu).
assert (Hu8 : 0 <= u < 128) by (destruct Hu as [->|(? & ?)]; lia).
clear W1c W2c.
bstep. rewrite (sxb_small u) by lia. clear HR.
bstep. rewrite (unsigned_lit (A + n - 1)) by lia. rewrite land7_mod8 by lia.
bstep. bstep. bstep. bstep.
destruct Hu as [-> | (Hk & Hlast)].
* rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
bstep.
destruct (Z.eq_dec (A / 8) ((A + n - 1) / 8)) as [Heq1|Hne1].
-- if_truex. bstep. bstep. if_true.
eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL'].
-- if_falsex. replace (A / 8 + 2147450880) with (A / 8 + 2147450880 + 0) by lia.
apply (LOOPA (Z.to_nat ((A + n - 1) / 8 - A / 8 - 0)) 0); lia.
* rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 u)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((A + n - 1) mod 8)) (Z_to_bv 64 u)) by (rewrite !signed_lit by lia; clear Hg; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
bstep.
destruct (Z.eq_dec (A / 8) ((A + n - 1) / 8)) as [Heq1|Hne1].
-- if_truex. bstep. bstep. if_true.
eapply EPI; [exact MU | exact WM | assumption | exact EP | exact ERR3 | exact ST3 | exact FR0 | exact FR | exact EPL'].
-- if_falsex. replace (A / 8 + 2147450880) with (A / 8 + 2147450880 + 0) by lia.
apply (LOOPA (Z.to_nat ((A + n - 1) / 8 - A / 8 - 0)) 0); lia.
+
rewrite (size_test_big n) by lia. cbv iota.
assert (APPn : app_mem A n) by (specialize (APP ltac:(lia)); unfold app_mem in *; lia).
bstep. if_truex.
bstep. bstep.
bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc1 _) =>
lazymatch goal with STc : stk asegs mc1 lo ?hi |- _ =>
destruct (stk_split asegs mc1 lo (bv_unsigned sp - 2192) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply (OBL_REGION _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A n lo);
[ exact UPAn | exact RT2 | exact APPn | lia
| rewrite unsigned_lit by lia; lia | reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| assumption | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros p0 p1 p2 o1 o2 o3 o4 o5 o6 o7 r3 r4 r5 r6 m3 MU3 WM3 MI3 ST1' UP3 RT3.
lazymatch type of MU3 with munch _ ?mc1 _ =>
transport_after_call asegs mc1 m3 MU3 WM3; try match goal with H : mem_inv asegs mc1 |- _ => clear H end end.
clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 0x618b0)) with (Z_to_bv 64 0x618b0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
bstep. if_true.
eapply EPI; [exact MU | exact WM | exact MI3 | exact EP | exact ERR3 | eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR0 | exact FR | exact EPL'].
Qed.
End IStrtoll.
End RC__1.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma istrtoll_sound_U {RC__ : Q6q3.RunConsts} : istrtoll_spec_U.
Proof. exact (istrtoll_sound Qw5U.region_is_poisoned_sound_U). Qed.
