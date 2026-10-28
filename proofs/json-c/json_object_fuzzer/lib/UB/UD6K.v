(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3CA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3CA.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma v_sltu_1 : forall x y : word, bv_unsigned x < bv_unsigned y -> v_sltu x y = Z_to_bv 64 1.
Proof. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [reflexivity|klia]. Qed.
#[using="Type"] Lemma v_sltu_0 : forall x y : word, bv_unsigned y <= bv_unsigned x -> v_sltu x y = Z_to_bv 64 0.
Proof. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [klia|reflexivity]. Qed.
#[using="Type"] Lemma lor_ones64_l : forall x, 0 <= x < 2^64 -> Z.lor 18446744073709551615 x = 18446744073709551615.
Proof. intros x Hx. rewrite Z.lor_comm. change 18446744073709551615 with (Z.ones 64). apply Z.lor_ones_low; [klia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; klia|]. apply Z.log2_lt_pow2; klia. Qed.
#[using="Type"] Lemma lxor_bound64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; klia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [klia|].
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); klia|].
pose proof (Z.log2_lxor a b ltac:(klia) ltac:(klia)) as HL.
assert (Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; klia| apply Z.log2_lt_pow2; klia]).
assert (Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; klia| apply Z.log2_lt_pow2; klia]).
klia.
Qed.

#[using="Type"] Lemma usl_ret_bits cur : 0 <= cur < 2^64 ->
Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 cur)) 622280))) + -1)))
(bv_unsigned (Z_to_bv 64 cur)))
= Z_to_bv 64 (usl_ret cur).
Proof.
intros Hc. unfold usl_ret, GLOBLOC, LC_GLOBAL. rewrite (unsigned_lit cur) by klia.
pose proof (lxor_bound64 cur 622280 Hc ltac:(klia)) as XR.
destruct (Z.eqb_spec cur 622280) as [->|NE]; [reflexivity|].
assert (NZ : Z.lxor cur 622280 <> 0) by (intros E; apply Z.lxor_eq in E; klia).
rewrite v_sltu_1 by (rewrite !unsigned_lit by klia; klia).
change (bv_unsigned (Z_to_bv 64 1) + -1) with 0. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lor_0_l. reflexivity.
Qed.

#[using="Type"] Lemma b1_read : forall m a b rest, bytes_at rsegs m a (b :: rest) -> ov_read_bytes rsegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros m a b rest H.
pose proof (bytes_at_read rsegs m a (b :: rest) 0 1 H ltac:(klia) ltac:(cbn; klia)) as R.
cbv beta iota delta [Z.to_nat skipn firstn] in R. unfold wa in R. rewrite Z.add_0_r in R. exact R.
Qed.
#[using="Type"] Lemma cname_ro : forall m, mem_inv rsegs m -> bytes_at rsegs m CNAME [Z_to_bv 8 67; Z_to_bv 8 0].
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold CNAME; klia| unfold CNAME; cbn; klia| vm_compute; repeat split; reflexivity]. Qed.

Section Loc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

#[using="Type"] Theorem errno_location_ok : errno_location_stmt.
Proof.
unfold errno_location_stmt. intros until m. intros TP. subst tp.
step. step. step. apply evt_done. reflexivity.
Qed.

#[using="Type"] Theorem uselocale_ok : uselocale_stmt.
Proof.
unfold uselocale_stmt. intros until nw. intros LC Hcur Hnw TP MI. subst tp.
unfold_consts. unfold LOCCELL, usl_new in *. change (490496 - 48) with 490448 in *.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(490448, 490448 + 8)] m) as MU.
step. step. step. step.
destruct (Z.eq_dec nw 0) as [->|NZ].
- step. if_truex. do 6 step. rewrite usl_ret_bits by klia.
apply evt_done. exists m. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact LC].
- step. if_falsex. rewrite (proj2 (Z.eqb_neq _ _) NZ). step. step.
destruct (Z.eq_dec nw (2^64 - 1)) as [->|NG].
+ if_falsex. step. stepz. do 6 step. rewrite usl_ret_bits by klia.
apply evt_done. exists m0. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold LC_GLOBAL, GLOBLOC. rewrite Z.eqb_refl. exact LC.
+ if_truex. stepz. do 6 step. rewrite usl_ret_bits by klia.
apply evt_done. eexists. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold LC_GLOBAL. rewrite (proj2 (Z.eqb_neq _ _) NG). exact LC.
Qed.

#[using="Type"] Theorem freelocale_ok : freelocale_stmt HIx.
Proof.
unfold freelocale_stmt. intros until errv. intros HP HIN ST LO LOS SPA HT ERR TP RA K.
unfold_consts. cbn [hl_stack S4L] in LOS. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L (lb_remove d LB) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (heap_blk S4L HIx _ _ _ _ d n HP HIN) as (Hn0 & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ d n HP HIN) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold_consts.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 16%nat ST.
do 5 step.

do 22 step.
repeat match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end.
rewrite !(unsigned_lit d) by klia.
assert (X1 : forall k, 0 <= k < 2^64 -> k <> d -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor d k)) = Z_to_bv 64 1).
{ intros k Hk NE. pose proof (lxor_bound64 d k ltac:(klia) Hk). apply v_sltu_1. rewrite !unsigned_lit by klia.
assert (Z.lxor d k <> 0) by (intros E; apply Z.lxor_eq in E; klia). klia. }
rewrite !X1 by klia. rewrite (v_sltu_1 (Z_to_bv 64 0) (Z_to_bv 64 d)) by (rewrite !unsigned_lit by klia; klia).
change (bv_unsigned (Z_to_bv 64 1)) with 1. cbn [Z.land].
change (Z.land 1 1) with 1. change (bv_unsigned (Z_to_bv 64 1)) with 1. change (Z.land 1 1) with 1.
step. if_falsex. do 4 step.
release_frame FR ST (bv_unsigned sp).
step.

alloc_call (hi_free2 S4L HIx) S4L HIx HP MU WM MI.
{ right. exists n. exact HIN. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3.
eapply K; [exact RS3| exact VM3| exact ST3| | exact ERR3| exact HP3].
eapply heap_pres_trans; [| exact HPR3].
eapply (heap_pres_of_munch S4L (lb_remove d LB) (bv_unsigned sp)); [exact MU| exact WM|].
eapply (client_outside S4L HIx); [exact HP| intros b Hb; exact (in_lb_remove _ _ _ Hb)| unfold_consts; klia| solve_clientW S4L HIx HP].
Qed.

#[using="Type"] Lemma seq_cases48 (P : nat -> Prop) : (forall k, (k < 48)%nat -> P k) <-> Forall P (seq 0 48).
Proof. rewrite Forall_forall. split; [intros H k Hk; apply H; apply in_seq in Hk; klia| intros H k Hk; apply H; apply in_seq; klia]. Qed.
#[using="Type"] Lemma globloc_rom : forall k, (k < 48)%nat -> seg_rom rsegs (wa (GLOBLOC + Z.of_nat k)) <> None.
Proof. apply (proj2 (seq_cases48 _)). unfold GLOBLOC. repeat constructor; vm_compute; discriminate. Qed.
#[using="Type"] Lemma globloc_w : forall k, (k < 48)%nat ->
match find_segment rsegs (GLOBLOC + Z.of_nat k) 1 with
| Some seg => if seg_writable seg then segment_byte_at (seg_bytes seg) (Z.to_N (GLOBLOC + Z.of_nat k - Z.of_N (seg_base seg))) else None
| None => None end <> None.
Proof. apply (proj2 (seq_cases48 _)). unfold GLOBLOC. repeat constructor; vm_compute; discriminate. Qed.
#[using="Type"] Lemma globloc_any m : exists gl, rw_cells rsegs m GLOBLOC [CB 48%nat gl].
Proof.
set (f := fun i : nat => match mrd rsegs m (wa (GLOBLOC + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
exists (map f (seq 0 48)).
assert (LEN : length (map f (seq 0 48)) = 48%nat) by (rewrite length_map, length_seq; reflexivity).
split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LEN| exact I].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [unfold GLOBLOC; klia|]. split; [rewrite LEN; unfold GLOBLOC; klia|].
intros i Hi. rewrite LEN in Hi. rewrite nth_error_map, (nth_error_seq 0 48 i) by klia. cbn [option_map Nat.add].
replace (i <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map].
subst f. cbv beta. destruct (mrd rsegs m (wa (GLOBLOC + Z.of_nat i))) eqn:E; [reflexivity|].
exfalso. unfold mrd in E. destruct (m (wa (GLOBLOC + Z.of_nat i))); [discriminate|]. exact (globloc_rom i Hi E).
- split; [unfold GLOBLOC; klia|]. split; [unfold GLOBLOC; cbn; klia|]. cbn [cells_size csize Nat.add]. intros j Hj.
unfold wview. destruct (m (wa (GLOBLOC + j))); [discriminate|].
rewrite wa_unsigned by (unfold GLOBLOC; klia).
replace j with (Z.of_nat (Z.to_nat j)) by klia. apply globloc_w. klia.
Qed.

#[using="Type"] Theorem duplocale_ok : duplocale_stmt HIx.
Proof.
unfold duplocale_stmt. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA K.
unfold_consts. cbn [hl_stack S4L] in LOS. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 16%nat ST.
do 6 step. step.
alloc_call (hi_malloc2 S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?unsigned_lit in ST2, HPR2 by klia.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; klia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST ERR.
destruct OUT2 as [(-> & He & HP2) | (Hr & [bjunk BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_truex. do 3 step.
release_frame FR ST2 (bv_unsigned sp).
step.
apply evt_RZ_done. eapply K; [| exact VM2| exact ST2| exact HPR| exact ERR2| left; split; [reflexivity| split; [exact He| exact HP2]]].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
destruct (globloc_any m2) as [gl GL]. unfold GLOBLOC in GL.
reenter MOK2.
step. if_falsex. step. step. unfold LC_GLOBAL. if_falsex. step. step.
do 12 step.
do 3 step. release_frame FR ST2 (bv_unsigned sp). step.
apply evt_RZ_done. eapply K; [| exact VM2| exact ST2| | exact ERR2| right].
+ unfold ret_state. cbn [hl_segs S4L]. repeat eexists.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; right; exact Hb | clia | solve_clientW S4L HIx HP2].
+ split; [exact Hr|]. split.
* lazymatch type of BLK with rw_cells _ _ _ ?cs => exists (cells_bytes cs) end.
eapply (rw_cells_recast _ _ _ _ _ BLK); [| reflexivity| reflexivity].
cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length; [reflexivity|]. cbn [cells_wf cell_wf]. repeat split.
* eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU). solve_frameW.
Qed.

#[using="Type"] Lemma notin_lb_remove : forall LB d n k, List.NoDup (map QCcH.blk_addr LB) -> In (d, n) LB -> ~ In (d, k) (lb_remove d LB).
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
lazymatch goal with | CAN2 : bytes_at rsegs _ 622192 (le8 _) |- _ =>
pose proof (le8_read rsegs _ _ _ CAN2) as RD9; stepz; clear RD9 end;
stepz; stepz;
let KC := fresh "KC" in if_cases KC; [exfalso; rewrite bv_eqb_refl in KC; discriminate KC|];
stepz; do 6 stepz; stepz;
lazymatch goal with | FR : rw_cells rsegs _ (bv_unsigned ?sp + -112) _, ST : stk rsegs _ _ _ |- _ =>
release_frame FR ST (bv_unsigned sp) end;
stepz;
apply evt_RZ_done;
eapply (K _ _ r jk).

#[using="Type"] Theorem newlocale_ok : newlocale_stmt HIx.
Proof.
unfold newlocale_stmt. intros until errv. intros HP HIN BLK LCK ST LO LOS SPA HT ERR TP RA K.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (heap_blk S4L HIx _ _ _ _ d 48 HP HIN) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ d 48 HP HIN) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
pose proof (notin_lb_remove LB d 48 48 ND HIN) as NLR. clear ND.
destruct (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & CAN3). cbn [hl_segs hl_got_guard hl_guard hl_tp S4L] in CAN1, CAN2, CAN3.
pose proof (heap_need_locks S4L HIx _ _ _ _ HP) as NL. cbn [hl_segs hl_libc S4L Z.add] in NL.
pose proof (cname_ro m MI) as CN. unfold CNAME in CN.
unfold LOCALE_LOCK, CNAME in *. unfold_consts.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m) as MU.

assert (HPRm : forall mx, munch [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m mx -> wmono rsegs m mx ->
heap_pres S4L (lb_remove d LB) (bv_unsigned sp) m mx).
{ intros mx MUx WMx. eapply (heap_pres_of_munch S4L (lb_remove d LB) (bv_unsigned sp)); [exact MUx| exact WMx|].
eapply (client_outside S4L HIx); [exact HP| intros b Hb; exact (in_lb_remove _ _ _ Hb)| unfold_consts; klia|].
apply Forall_cons; [left; cbn; unfold_consts; klia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists d, 48. cbn [fst snd]. split; [exact HIN|]. split; [exact NLR| klia]. }
assert (HPm : forall mx, munch [(bv_unsigned sp - 496, bv_unsigned sp); (d, d + 48)] m mx -> wmono rsegs m mx -> mem_inv rsegs mx ->
HEAPx A LB mx md).
{ intros mx MUx WMx MIx. eapply (heap_frame S4L HIx); [exact HP | | exact WMx | exact MIx].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MUx).
apply Forall_cons; [left; cbn; unfold_consts; klia|]. apply Forall_cons; [| apply Forall_nil].
right; left. exists d, 48. cbn [fst snd]. split; [exact HIN| klia]. }
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 112%nat ST.
destruct (rw_cells_CB_sizes rsegs m [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat _ _ _ FR eq_refl)
as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & FR'). clear FR. rename FR' into FR.
do 7 stepz. do 3 stepz.
stepz. pose proof (le8_read rsegs _ _ _ CAN1) as RD1. stepz. clear RD1.
pose proof (le8_read rsegs _ _ _ CAN2) as RD2. stepz. clear RD2.
stepz.
stepz. stepz. stepz.

stepz. pose proof (b1_read _ _ _ _ NL) as RD3. stepz. clear RD3.
replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
stepz. if_truex. stepz.

stepz. stepz. if_falsex. stepz. if_falsex.
stepz. stepz. stepz. stepz. stepz.
if_cases K0. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists. }

stepz. stepz. if_truex. stepz. if_falsex. stepz. stepz. stepz. stepz.
carve_frame 384%nat ST.
destruct (rw_cells_CB_sizes rsegs _ [272;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat _ _ _ FR0 eq_refl)
as (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & p14 & FR0'). clear FR0. rename FR0' into FR0.
do 14 stepz.
stepz. stepz. pose proof (le8_read rsegs _ _ _ CAN1) as RD1. stepz. clear RD1.
pose proof (le8_read rsegs _ _ _ CAN2) as RD2. stepz. clear RD2.
stepz.
pose proof (b1_read _ _ _ _ CN) as RD3. stepz. clear RD3.
replace (zxb (Z_to_bv 8 67)) with (Z_to_bv 64 67) in * by (apply bv_eq; vm_compute; reflexivity).
stepz. stepz. if_falsex. stepz. stepz. if_truex.
stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (cname_ro mx ltac:(assumption)) as CNx; unfold CNAME in CNx;
pose proof (proj1 (bytes_at_app rsegs mx 74650 [Z_to_bv 8 67] [Z_to_bv 8 0]) CNx) as [_ CN1] end.
pose proof (b1_read _ _ _ _ CN1) as RD4. stepz.
replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) in * by (apply bv_eq; vm_compute; reflexivity).
stepz. stepz. if_truex.

stepz. stepz. stepz. stepz. stepz. stepz. if_falsex.
stepz. stepz. stepz. if_falsex.
stepz. stepz. stepz. if_falsex.
stepz. clear RD4 CN1 CNx. stepz. stepz. if_truex.

stepz. if_truex. stepz.
pose proof (le8_read rsegs _ _ _ CAN2) as RD2. stepz. clear RD2. stepz. stepz.
if_cases KC. { exfalso. rewrite bv_eqb_refl in KC. discriminate KC. }
stepz. do 13 stepz. stepz.
release_frame FR0 ST (bv_unsigned sp + -112).
stepz.

stepz. stepz. stepz. if_falsex.

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K2. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K3. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K4. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists. }

stepz. stepz. if_falsex. stepz. if_falsex. stepz. stepz. stepz. stepz. stepz.
if_cases K5. { stepz. nl_exit K 0 junk; [| exact ST| apply HPRm; assumption| exact BLK| exact LCK| exact ERR| apply HPm; assumption| right; reflexivity].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists. }

stepz. stepz. stepz. stepz. stepz.
stepz. if_falsex. stepz. stepz. if_falsex. stepz. stepz. stepz. if_falsex. stepz. if_falsex. stepz. if_falsex.

do 12 stepz.
stepz. stepz.
lazymatch type of BLK with rw_cells _ _ _ ?cs =>
nl_exit K d (cells_bytes cs); [| exact ST| apply HPRm; assumption| | exact LCK| exact ERR| apply HPm; assumption| left; reflexivity] end.
- unfold ret_state. cbn [hl_segs S4L]. repeat eexists.
- eapply (rw_cells_recast _ _ _ _ _ BLK); [| reflexivity| reflexivity].
cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length; [reflexivity| cbn [cells_wf cell_wf]; repeat split].
Qed.
End Loc.

End RC__1.
