(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULAQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULAQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgTW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgTW.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrIB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udgq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udgq.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition DC_ENTRY_P : Z := 0x26d6c.
Definition REC_P : Z := 112.
Definition DC_C : Z := 10528.
Definition dc_stk (d : Z) : Z := REC_P + DC_C + REC_P * d.

Definition LASTERR_P : Z := 0x28f40.
Definition LASTERR_BUF_P : Z := 0x76fbc.
Definition LASTERR_FMT_P : Z := 0x120dc.
Definition LASTERR_STK : Z := 80 + 5856.
Definition set_last_err_spec_P : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (canary : word),
a0 = Z_to_bv 64 LASTERR_FMT_P ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - LASTERR_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^63 ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (LASTERR_BUF_P, LASTERR_BUF_P + 256)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp) /\ fsaved F F' /\ frm0 fc')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 LASTERR_P) fc None m (seg_rom rsegs)).

#[using="Type"] Lemma rwc_eq : forall segs m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. intros segs m A A' cs H <-. exact H. Qed.

#[using="Type"] Lemma hi_top_bound2 : forall L (HIx : heap_iface L) A LB m md, HEAP L HIx A LB m md -> hi_top L HIx + 8 <= 2^64.
Proof.
intros L HIx A LB m md HP. destruct (heap_auxv L HIx _ _ _ _ HP) as (aw & keys & (_ & _ & _ & _ & B) & LE).
pose proof (bytes_at_bound _ _ _ _ B) as X. rewrite length_le8 in X. lia.
Qed.

#[using="Type"] Lemma got_read : forall m, exists bs : list byte, ov_read_bytes rsegs m (Z_to_bv 64 0x658c8) 8 = Some bs.
Proof.
intros m.
assert (E : forall k : nat, (k < 8)%nat -> exists b, mrd rsegs m (wa (0x658c8 + Z.of_nat k)) = Some b).
{ intros k Hk. unfold mrd. destruct (m (wa (0x658c8 + Z.of_nat k))) as [b|]; [exists b; reflexivity|].
do 8 (destruct k as [|k]; [vm_compute; eexists; reflexivity|]). lia. }
destruct (E 0%nat ltac:(lia)) as [b0 E0]. destruct (E 1%nat ltac:(lia)) as [b1 E1]. destruct (E 2%nat ltac:(lia)) as [b2 E2]. destruct (E 3%nat ltac:(lia)) as [b3 E3].
destruct (E 4%nat ltac:(lia)) as [b4 E4]. destruct (E 5%nat ltac:(lia)) as [b5 E5]. destruct (E 6%nat ltac:(lia)) as [b6 E6]. destruct (E 7%nat ltac:(lia)) as [b7 E7].
assert (BY : bytes_at rsegs m 0x658c8 [b0;b1;b2;b3;b4;b5;b6;b7]).
{ split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. do 8 (destruct i as [|i]; [assumption|]). lia. }
exists [b0;b1;b2;b3;b4;b5;b6;b7].
pose proof (bytes_at_read rsegs m 0x658c8 _ 0 8 BY ltac:(lia) ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R.
unfold wa in R. exact R.
Qed.

#[using="Type"] Lemma presxD_of_munch_x : forall L D LB SP W m m',
munch W m m' -> wmono (hl_segs L) m m' ->
(forall a, 0 <= a < 2^64 -> client_addrx L (hl_volatile L) LB SP a -> ~ (D <= a < D + 8) -> outside W a) ->
heap_presxD L D LB SP m m'.
Proof.
intros L D LB SP W m m' MU WM HW a Ha Hc Hd. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.

Section DcDefs.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

Definition fres (m : word -> option byte) (CBS : list blk) (q : Z) : Prop :=
(q = 0 /\ CBS = [])
\/ (q <> 0 /\ exists s, jval rsegs S4F s m CBS q 1)
\/ jroot_rep S4L S4F (JRdblx (fn_ud_to_json_string S4F)) m CBS q.

Definition dc_res (r : jroot) (BS LB : list blk) (D : Z) (m' : word -> option byte) (md' : Model) (rv : Z) : Prop :=
(rv = 0 /\ exists (A' : AS S4L HIx) (d : jroot) q CBS REM,
copy_of r d /\ q <> 0 /\ rw_cells rsegs m' D [C8 (wz q)] /\ jroot_rep S4L S4F d m' CBS q /\
HEAPx A' (BS ++ CBS ++ REM ++ LB) m' md')
\/ (rv = 2^64 - 1 /\ exists (A' : AS S4L HIx) q CBS REM,
rw_cells rsegs m' D [C8 (wz q)] /\ fres m' CBS q /\ HEAPx A' (BS ++ CBS ++ REM ++ LB) m' md').

Definition dcopy_spec (r : jroot) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (lo p D : Z) (errv : word),
HEAPx A (BS ++ LB) m md -> jroot_rep S4L S4F r m BS p -> r <> JRnull -> jc_glob_P m ->
rw_cells rsegs m D [C8 (wz 0)] -> bv_unsigned sp <= D -> D + 8 <= hi_top S4L HIx -> D mod 8 = 0 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - dc_stk (rdepth r) ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> tp = wz 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p -> a4 = wz D -> a5 = wz SH_ENTRY_P ->
(forall ms' md' m' rv,
jf_postD S4L D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz DC_ENTRY_P) fc None m (seg_rom rsegs)) md) T.
End DcDefs.

Section DcP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis LASTERR : set_last_err_spec_P.
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis NEWOBJ : jo_new_object_P HIx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stk (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Definition dc_frame (m : word -> option byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition dc_cell (m : word -> option byte) (cj : list byte) : Prop := rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 cj].

Definition dc_inv (mc : word -> option byte) (mdc : Model) : Prop :=
model_vm_only md0 mdc /\ heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mc /\
stk rsegs mc lo (bv_unsigned sp + -80) /\ dc_frame mc /\ jc_glob_P mc.

#[using="RC__ HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS lo p D T LOS NN JR0 Kont"] Lemma rdepth_nonneg : 0 <= rdepth r.
Proof. destruct r; cbn [rdepth]; try lia. apply sdepth_nonneg. Qed.

#[using="fc p LO LOS SPD NN JR0 Kont"] Lemma dc_epi :
forall (x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (rv : Z) (errc : word) (cj : list byte),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
dc_res HIx r BS LB D mc mdc rv ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 x8 x9 (wz rv) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26f54) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until cj. intros (VM & PRES & ST & FR & G) FS FRM1 CELL ERR RES.
unfold dc_frame in FR. unfold dc_cell in CELL. unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
assert (HPX : exists A' CBS REM, HEAPx A' (BS ++ CBS ++ REM ++ LB) mc mdc).
{ destruct RES as [(_ & A' & d & q & CBS & REM & _ & _ & _ & _ & HP) | (_ & A' & q & CBS & REM & _ & _ & HP)]; exists A', CBS, REM; exact HP. }
destruct HPX as (A' & CBS0 & REM0 & HP).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash RES. stash G.
apply rz_evt; [exact MOK|].
do 11 bstep.
apply evt_RZ_done. unstash RES. unstash G.
eapply (Kont _ mdc mc rv).
- unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [exact FS | intros _; exact FRM1] |].
split; [exact VM|].
split.
{ assert (FALL : rw_cells rsegs mc (bv_unsigned sp + -80) ([CB 8 cj] ++ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact CELL|]. cbn [cells_size csize Nat.add].
eapply (rwc_eq rsegs); [exact FR | lia]. }
cbn [app] in FALL. release_frame FALL ST (bv_unsigned sp). exact ST. }
split; [exact PRES | eexists; exact ERR].
- exact G.
- eapply jroot_rep_agree; [exact JR0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [exact PRES | exact HP | incl_tac | incl_tac | clia].
- exact RES.
Qed.

Definition dc_regs (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 (wz p) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6.

#[using="fc LO LOS SPD NN JR0 Kont"] Lemma dc_ret0 :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (d : jroot) (q : Z) (CBS REM : list blk) (errc : word) (cj : list byte),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
HEAPx A (BS ++ CBS ++ REM ++ LB) mc mdc ->
copy_of r d -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> jroot_rep S4L S4F d mc CBS q ->
realizes rsegs (mkCfg (MS (dc_regs x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6)
F1 (wz 0x26eec) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until cj. intros INV FS FRM1 CELL ERR HP CO Hq DC JD. pose proof INV as (VM & PRES & ST & FR & G).
unfold dc_regs. unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash JD. stash G.
apply rz_evt; [exact MOK|].
bstep. bstep.
apply evt_RZ_done. unstash JD. unstash G.
eapply dc_epi; [exact INV | exact FS | exact FRM1 | exact CELL | exact ERR |].
left. split; [reflexivity|]. exists A, d, q, CBS, REM. repeat (split; [assumption|]). exact HP.
Qed.

#[using="fc r LO LOS SPD NN JR0 Kont"] Lemma dc_failr :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q : Z) (CBS REM : list blk) (errc : word) (cj : list byte),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
HEAPx A (BS ++ CBS ++ REM ++ LB) mc mdc ->
rw_cells rsegs mc D [C8 (wz q)] -> fres mc CBS q ->
realizes rsegs (mkCfg (MS (dc_regs x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6)
F1 (wz 0x26f50) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until cj. intros INV FS FRM1 CELL ERR HP DC FRES. pose proof INV as (VM & PRES & ST & FR & G).
unfold dc_regs. unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash FRES. stash G.
apply rz_evt; [exact MOK|].
bstep.
apply evt_RZ_done. unstash FRES. unstash G.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply dc_epi; [exact INV | exact FS | exact FRM1 | exact CELL | exact ERR |].
right. split; [reflexivity|]. exists A, q, CBS, REM. split; [exact DC|]. split; [exact FRES | exact HP].
Qed.

#[using="PUT PUTX fc r LO LOS SPA HT SPD DAL NN JR0 Kont"] Lemma dc_fail :
forall (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q qc : Z) (sq : jshape) (CBS CBSc REM : list blk) (errc : word) (cj : list byte),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
HEAPx A (CBSc ++ BS ++ CBS ++ REM ++ LB) mc mdc ->
rw_cells rsegs mc D [C8 (wz q)] -> q <> 0 -> jval rsegs S4F sq mc CBS q 1 ->
fres mc CBSc qc ->
realizes rsegs (mkCfg (MS (dc_regs x1 t0 t1 t2 x9 (wz qc) a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 t3 t4 t5 t6)
F1 (wz 0x26f4c) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until cj. intros INV FS FRM1 CELL ERR HP DC Hq JQ FRES. pose proof INV as (VM & PRES & ST & FR & G).
unfold dc_regs. unfold dc_frame in FR. unfold dc_cell in CELL. unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash FRES. stash G. stash JQ.
apply rz_evt; [exact MOK|].
bstep.
unstash FRES. unstash G. unstash JQ.

assert (AFTER : forall ms3 md3 m3 (A3 : AS S4L HIx) (rr : word),
ret_statew S4L (wz 0x26f50) (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) (wz p) x9 (wz SH_ENTRY_P) x19 x20 x21 x22 x23 s8 s9 s10 s11 F1 fc1 rr m3 ms3 ->
model_vm_only mdc md3 -> stk rsegs m3 lo (bv_unsigned sp + -80) ->
heap_pres S4L (BS ++ CBS ++ REM ++ LB) (bv_unsigned sp + -80) mc m3 ->
(exists e3, rw_cells rsegs m3 (0x77c00 - 164) [C4 e3]) ->
HEAPx A3 (BS ++ CBS ++ REM ++ LB) m3 md3 ->
realizes rsegs (mkCfg ms3 md3) T).
{ intros ms3 md3 m3 A3 rr RS3 VM3 ST3 HPR3 [e3 ERR3] HP3.
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp S4L] in *.
pose proof PRES as PRES3. extend_presD_call PRES3 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in CELL; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
pose proof (jc_glob_P_pres _ _ _ _ HPR3 G) as G3.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
pose proof (wmono_refl rsegs m3) as WM3. pose proof (munch_refl [] m3) as MU3.
apply rz_evt; [exact MOK3|].
replace (ret_pc (wz 0x26f50)) with (wz 0x26f50) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
apply evt_RZ_done.
eapply dc_failr with (CBS := CBS) (REM := REM);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]]
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1 | exact CELL | exact ERR3 | exact HP3 | exact DC | ].
right; left. split; [exact Hq|]. exists sq. eapply jval_agree; [exact JQ | | ].
- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | apply incl_refl].
- incl_tac. }
apply evt_RZ_done.
destruct FRES as [(-> & ->) | [(Hqc & sc & JC) | XD]].
-
eapply (PUT) with (s := None) (BS := []) (p := 0) (rc := 1) (LB := BS ++ CBS ++ REM ++ LB) (lo := lo);
[ cbn [app]; exact HP | split; reflexivity | reflexivity | .. ]; try alloc_side.
{ unfold put_stk_P. rewrite ?unsigned_lit by lia. lia. }
intros ms3 md3 (m3 & A3 & rr & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3). cbn [hl_segs hl_tp S4L] in *.
destruct OUT3 as [[_ HP3] | (s' & ES & _)]; [| discriminate ES].
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
eapply AFTER; [exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exists errc; exact ERR3 | exact HP3].
-
eapply (PUT) with (s := Some sc) (BS := CBSc) (p := qc) (rc := 1) (LB := BS ++ CBS ++ REM ++ LB) (lo := lo);
[ exact HP | split; [exact Hqc | split; [lia | exact JC]] | reflexivity | .. ]; try alloc_side.
{ unfold put_stk_P. rewrite ?unsigned_lit by lia. lia. }
intros ms3 md3 (m3 & A3 & rr & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3). cbn [hl_segs hl_tp S4L] in *.
destruct OUT3 as [[_ HP3] | (s' & _ & R2 & _)]; [| lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
eapply AFTER; [exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exists errc; exact ERR3 | exact HP3].
-
pose proof PUTX as PX. unfold jo_put_xleaf_stmt in PX.
eapply PX with (BS := CBSc) (LB := BS ++ CBS ++ REM ++ LB) (lo := lo) (r := JRdblx (fn_ud_to_json_string S4F)); clear PX;
[ | exact XD | exact I | reflexivity | ].
{ unfold jf_pre. cbn [hl_segs hl_tp S4L]. rewrite !(unsigned_lit (bv_unsigned sp + -80)) by lia.
split; [exact HP|]. split; [exact ST|]. split; [clia|]. split; [unfold put_stk_P; lia|].
split; [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity|]. split; [clia|].
split; [exact ERR|]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
intros ms3 md3 m3 rv3 (RS3 & VM3 & ST3 & HPR3 & ERR3') RV ERR3 [A3 HP3]. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
eapply AFTER; [exact RS3 | exact VM3 | exact ST3 | exact HPR3 | exists errc; exact ERR3 | exact HP3].
Qed.

#[using="fc LO LOS SPA HT SPD DHI DAL NN JR0 Kont"] Lemma dc_tail0 :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (d : jroot) (q np ty tojs pb : Z) (CBS REM : list blk) (errc : word) (cj : list byte),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
HEAPx A (BS ++ CBS ++ REM ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc p (jhdr_cells ty 1 tojs pb 0 0) ->
copy_of r d -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> jroot_rep S4L S4F d mc CBS q ->
realizes rsegs (mkCfg (MS (dc_regs x1 t0 t1 t2 (wz D) a0 a1 a2 a3 a4 a5 a6 a7 (wz 1) x20 x21 x22 x23 t3 t4 t5 t6)
F1 (wz 0x26ee4) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until cj. intros INV FS FRM1 CELL ERR HP INp Hnp SRC CO Hq DC JD. pose proof INV as (VM & PRES & ST & FR & G).
unfold dc_regs. unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB. clear HT63 RA.
assert (INp1 : In (p, np) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash JD. stash G. stash CO.
apply rz_evt; [exact MOK|].
bstep. bstep. if_true. bstep. bstep. bstep. if_false. bstep. bstep. if_true.
unstash JD. unstash G. unstash CO.
apply evt_RZ_done.
eapply dc_ret0; [exact INV | exact FS | exact FRM1 | exact CELL | exact ERR | exact HP | exact CO | exact Hq | exact DC | exact JD].
Qed.

#[using="LASTERR HT63 fc LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont"] Lemma dc_tail_ud :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q pb ud udn : Z) (uds : list byte) (bits bits' : word) (REM : list blk) (errc : word) (cj : list byte),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
HEAPx A (BS ++ [(q, 48)] ++ REM ++ LB) mc mdc -> In (p, 48) BS -> In (ud, udn) BS -> udn <= 2^31 ->
rw_cells rsegs mc p (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string S4F) pb (fn_free_userdata S4F) ud ++ [C8 bits]) ->
cstr rsegs mc ud udn uds ->
r = JRtree (Sdouble true) ->
q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] ->
rw_cells rsegs mc q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string S4F) 0 0 0 ++ [C8 bits']) ->
realizes rsegs (mkCfg (MS (dc_regs x1 t0 t1 t2 (wz D) a0 a1 a2 a3 a4 a5 a6 a7 (wz 1) x20 x21 x22 x23 t3 t4 t5 t6)
F1 (wz 0x26ee4) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until cj. intros INV FS FRM1 CELL ERR HP INp INu UDN SRC CS Er Hq DC QX. pose proof INV as (VM & PRES & ST & FR & G).
unfold dc_regs. unfold dc_frame in FR. unfold dc_cell in CELL. unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
assert (INp1 : In (p, 48) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
assert (INu1 : In (ud, udn) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; left; exact INu).
assert (INq1 : In (q, 48) (BS ++ [(q, 48)] ++ REM ++ LB)) by (apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p 48 HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HP INq1) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 48 HP INq1) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
destruct (key_string HIx _ _ _ _ _ _ _ HP INu1 CS) as (slack & USTR & UPAD & UNN & Hual & HUL & Hulo & Huhi & USL).
pose proof (heap_blk_img S4L HIx _ _ _ _ ud udn HP INu1) as Huimg. cbn [hl_img_lo hl_img_hi S4L] in Huimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi, Huhi.
assert (Hqp : q <> p) by (intros ->; exact (nodup_mid_notin BS [(p, 48)] (REM ++ LB) p 48 48 (heap_blk_nodup S4L HIx _ _ _ _ HP) ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact INp))).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 48 p 48 HP INq1 INp1 Hqp) as Hdqp.
unfold jhdr_cells in SRC, QX. cbn [app] in SRC, QX.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash G. stash CS. stash USTR. stash Hpimg. stash Huimg.
apply rz_evt; [exact MOK|].
bstep. bstep. if_true. bstep. bstep. bstep. if_truex.
bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => destruct (got_read mx) as [gbs GOT] end.
bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SDUP : forall a2' : word,
evt rsegs (RZ rsegs mdc T)
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz q) (wz ud) (wz (fn_ud_to_json_string S4F)) a2' a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F1 (wz 0x26f80) fc1 None mx (seg_rom rsegs))) end.
2:{ bstep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
- apply SDUP.
- bstep. bstep. bstep. if_true. apply SDUP. }
intros a2'. clear GOT.
bstep.

unstash USTR.
apply evt_RZ_done.
eapply (strdup_cps HIx) with (LB := BS ++ [(q, 48)] ++ REM ++ LB) (lo := lo) (str := uds) (slack := slack);
[ heap_now S4L HIx HP MU WM MI
| rewrite unsigned_lit by lia; exact USTR | exact UNN | rewrite unsigned_lit by lia; exact UPAD
| rewrite !unsigned_lit by lia; eapply client_range_block; [exact INu1 | lia | lia]
| rewrite !unsigned_lit by lia; left; lia | lia | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r2 & e4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & STR4 & OUT4). open_ret RS4. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR4 by lia.
extend_presD_call PRES HPR4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in CELL; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in QX; [| eapply client_range_block; [exact INq1 | lia | cbn; lia]]. cbn [hl_segs S4L] in QX.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR4 G) as G4. clear G.
unstash CS. assert (CS4 : cstr rsegs m4 ud udn uds).
{ eapply (cstr_agree rsegs); [exact CS | | exact INu1 | lia]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | apply incl_refl]. }
clear CS MU WM MI ST.
destruct OUT4 as [(-> & HP4) | (Hr2 & NEW & HP4)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m4) as WM. pose proof (munch_refl [] m4) as MU.
pose proof (heap_canary S4L HIx _ _ _ _ HP4) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_tp S4L] in CAN1, CAN2.
pose proof (ssp_cells_of_bytes_at m4 g CAN1 CAN2) as SSP. clear CAN1 CAN2.
stash G4. stash CS4.
reenter MOK4.
bstep. if_true. bstep. bstep. bstep.

eapply evt_cut.
{ eapply (LASTERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 lo g);
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
[ reflexivity | exact ST4 | clia | unfold LASTERR_STK; lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | lia | exact SSP | exact MI | apply FRM1 ]. }
cbv beta. intros ms5 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F5 & fc5 & m5 & -> & MU5 & WM5 & MI5 & ST5 & FS5 & FRM5).
unfold LASTERR_BUF_P in MU5. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in MU5 by lia.
unstash Hpimg. unstash Huimg. unstash G4.
apply (fun HX => rw_cells_transport rsegs _ m4 m5 _ _ HX MU5 WM5) in FR; [| cbn; lia].
apply (fun HX => rw_cells_transport rsegs _ m4 m5 _ _ HX MU5 WM5) in CELL; [| cbn; lia].
apply (fun HX => rw_cells_transport rsegs _ m4 m5 _ _ HX MU5 WM5) in DC; [| cbn; lia].
apply (fun HX => rw_cells_transport rsegs _ m4 m5 _ _ HX MU5 WM5) in QX; [| cbn; lia].
apply (fun HX => rw_cells_transport rsegs _ m4 m5 _ _ HX MU5 WM5) in ERR4; [| cbn; lia].
assert (HP5 : HEAPx A4 (BS ++ [(q, 48)] ++ REM ++ LB) m5 md4).
{ eapply (heap_frame S4L HIx); [exact HP4 | | exact WM5 | exact MI5].
intros a Ha Hna Hns. apply MU5. rewrite wa_unsigned by lia. cbn. split; [| split; [| exact I]].
- intros Hin. apply Hna. split; [left; clia | pose proof (hi_top_hi S4L HIx); clia].
- intros Hin. apply Hna. split; [right; left; cbn; unfold s4_client_static; lia | pose proof (hi_top_hi S4L HIx); clia]. }
assert (G5 : jc_glob_P m5).
{ eapply jc_glob_P_munch; [exact G4 | exact MU5 | exact WM5 |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia. }
assert (PRES5 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m5).
{ eapply presxD_trans; [exact PRES|]. eapply (presxD_of_munch_x S4L); [exact MU5 | exact WM5 |].
intros a Ha Hc Hd. cbn. split; [| split; [| exact I]].
- destruct Hc as [Hc | [[Hc _] | (b & Hb & Hr)]]; [lia | pose proof (hl_static_in_img S4L a Hc); cbn in *; clia |].
destruct b as [ba bn]. cbn in Hr. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP4 ltac:(apply in_app_or in Hb; destruct Hb as [Hb|Hb]; in_find Hb)) as (_ & _ & _ & Hbhi & _). clia.
- destruct Hc as [Hc | [[Hc Hx] | (b & Hb & Hr)]]; [lia | intros Hin; apply Hx; cbn; unfold s4_volatile; lia |].
destruct b as [ba bn]. cbn in Hr. pose proof (heap_blk_img S4L HIx _ _ _ _ ba bn HP4 ltac:(apply in_app_or in Hb; destruct Hb as [Hb|Hb]; in_find Hb)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg. lia. }
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST5 by lia.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
clear MU WM MI. pose proof (wmono_refl rsegs m5) as WM. pose proof (munch_refl [] m5) as MU. rename MI5 into MI.
replace (ret_pc (wz 0x26fac)) with (wz 0x26fac) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
bstep.
apply evt_RZ_done.
eapply dc_failr with (CBS := [(q, 48)]) (REM := REM);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM4] | split; [exact PRES5 | split; [exact ST5 | split; [exact FR | exact G5]]]]
| eapply fsaved_trans; [exact FS | exact FS5] | exact FRM5 | exact CELL | exact ERR4 | exact HP5 | exact DC | ].
right; right. apply (xdbl_transient_jroot S4L S4F) with (bits := bits'). { exact Hq. } unfold jhdr_cells. cbn [app]. exact QX.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as (_ & Hral & Hrlo & Hrhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
assert (Hrq : r2 <> q) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP4 INq1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 _ q 48 HP4 ltac:(left; reflexivity) ltac:(right; exact INq1) Hrq) as Hdrq.
pose proof (wmono_refl rsegs m4) as WM. pose proof (munch_refl [(q, q + 48)] m4) as MU.
stash G4. stash CS4. stash NEW.
reenter MOK4.
bstep. if_falsex. bstep. bstep. bstep. bstep. bstep. bstep.
unstash G4. unstash CS4. unstash NEW.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP6 : HEAPx A4 ((r2, Z.of_nat (length uds) + 1) :: BS ++ [(q, 48)] ++ REM ++ LB) mx md4) by
(eapply (heap_frame S4L HIx); [exact HP4 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP4 MU);
apply Forall_cons; [cbn [fst snd]; right; left; exists q, 48; split; [right; exact INq1 | lia] | apply Forall_nil]);
assert (G6 : jc_glob_P mx) by
(eapply jc_glob_P_outside; [exact G4 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia)
end.
assert (NIq : ~ In (q, 48) (BS ++ LB)).
{ intros Hin. apply (nodup_mid_notin BS [(q, 48)] (REM ++ LB) q 48 48 (heap_blk_nodup S4L HIx _ _ _ _ HP) ltac:(left; reflexivity)).
apply in_app_or in Hin; destruct Hin as [Hin|Hin]; in_find Hin. }
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => assert (PRES6 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mx) end.
{ eapply presxD_trans; [exact PRES|]. apply pres_presxD. eapply (heap_pres_of_munch S4L (BS ++ LB) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP4 | incl_tac | clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, 48; split; [right; exact INq1 | split; [exact NIq | lia]] | apply Forall_nil]. }
clear PRES. rename PRES6 into PRES.
eapply dc_epi;
[ split; [eapply model_vm_only_trans; [exact VM | exact VM4] | split; [exact PRES | split; [exact ST4 | split; [exact FR | exact G6]]]]
| exact FS | exact FRM1 | exact CELL | exact ERR4 | ].
left. split; [reflexivity|]. exists A4, (JRtree (Sdouble true)), q, [(q, 48); (r2, Z.of_nat (length uds) + 1)], REM.
split; [subst r; cbn [copy_of]; eexists; split; [reflexivity | cbn; lia] |].
split; [exact Hq|]. split; [exact DC|]. split.
+ cbn [jroot_rep]. split; [exact Hq|].
exists 0, [], [(q, 48); (r2, Z.of_nat (length uds) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists bits', r2, (Z.of_nat (length uds) + 1), uds. split; [reflexivity|]. split; [destruct CS4 as (L1 & _); lia|]. split.
* unfold jhdr_cells. cbn [app fn_ud_to_json_string fn_free_userdata S4F]. exact QX.
* split; [lia|]. split; [exact (proj1 (proj2 CS4))|]. exists []. rewrite app_nil_r.
eapply (rw_cells_transport rsegs); [exact NEW | exact MU | exact WM | cbn; lia].
+ eapply (heap_perm S4L HIx); [exact HP6 | perm].
Qed.

#[using="NEWOBJ LO LOS SPA HT FRM0 SPD DHI DAL NN JR0 Kont"] Lemma dc_b0 :
forall (t0 t1 t2 a1 a2 a3 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (errv : word),
HEAPx A (BS ++ LB) m0 md0 -> jc_glob_P m0 -> rw_cells rsegs m0 D [C8 (wz 0)] -> stk rsegs m0 lo (bv_unsigned sp) ->
rw_cells rsegs m0 (0x77c00 - 164) [C4 errv] ->
(forall (x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A' : AS S4L HIx) (q : Z) (CBS : list blk) (cj : list byte) (e : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj -> rw_cells rsegs mc (0x77c00 - 164) [C4 e] ->
HEAPx A' (BS ++ CBS ++ LB) mc mdc -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> scopy S4L S4F r mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0' t1' t2' (wz p) (wz D) (wz 0) a1' a2' a3' a4' a5' a6' a7'
(wz SH_ENTRY_P) (wz 1) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F1 (wz 0x26db4) fc1 None mc (seg_rom rsegs)) mdc) T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (wz 0x77c00) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) (wz SH_ENTRY_P) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz DC_ENTRY_P) fc None m0 (seg_rom rsegs)) md0) T.
Proof.
intros until errv. intros HP G DC ST ERR K1.
unfold dc_stk, REC_P, DC_C in LOS. pose proof rdepth_nonneg as RD0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
destruct (jroot_rep_root_in S4L S4F r m0 BS p JR0 NN) as (np & INp & Hnp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m0) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
stash G.
apply rz_evt; [exact MOK|]. unfold DC_ENTRY_P.
carve_frame 80%nat ST.
do 13 bstep. bstep.
unstash G.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPc : HEAPx A (BS ++ LB) mx md0) by heap_now S4L HIx HP MU WM MI;
assert (Gc : jc_glob_P mx) by (eapply jc_glob_P_outside; [exact G | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia);
assert (AGc : agree_on rsegs (BS ++ LB) m0 mx) by
(eapply (agree_of_munch rsegs); [exact MU | exact WM |]; intros b k Hb; cbn;
pose proof (heap_blk S4L HIx _ _ _ _ b k HP Hb) as (_ & _ & _ & Hbhi & _); unfold_consts; lia);
assert (PRESc : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mx) by
(eapply presxD_of_munch; [exact MU | exact WM |]; intros b Hb Hc Hd;
eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HP | intros bb Hbb; exact Hbb | clia | solve_clientW S4L HIx HP | exact Hb | exact Hc])
end.
pose proof (jroot_rep_agree S4L S4F _ _ _ _ _ _ JR0 AGc ltac:(incl_tac)) as JRc.

apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR as X. destruct X as [CELL FR2]. cbn [cells_size csize Nat.add] in FR2. clear FR.
replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp + -72) in FR2 by lia.
clear MU WM MI.
apply evt_RZ_done.
replace (ret_pc (wz SH_ENTRY_P)) with (wz SH_ENTRY_P) by (symmetry; apply ret_pc_even; [unfold SH_ENTRY_P; lia|reflexivity]).
pose proof (shallow_P HIx NEWOBJ) as SH. unfold shallow_stmt in SH.
eapply SH with (LB := LB) (BS := BS) (lo := lo) (r := r); clear SH;
[ exact HPc | exact JRc | exact NN | exact Gc | exact DC | rewrite unsigned_lit by lia; lia | exact DHI | exact DAL
| rewrite unsigned_lit by lia; exact ST | clia | rewrite unsigned_lit by lia; unfold SH_STK_P; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | rewrite unsigned_lit by lia; reflexivity | reflexivity | reflexivity | ].
intros ms2 md2 m2 rv (RS2 & VM2 & ST2 & HPR2 & [e2 ERR2]) G2 JR2 RES2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hl_volatile S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR2 by lia.
assert (PRES2 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m2).
{ eapply presxD_trans; [exact PRESc|]. eapply presxD_weaken; [exact HPR2 | lia | apply incl_refl]. }
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR2) in CELL; [| left; cbn; lia | cbn; lia].
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR2; [| left; cbn; lia | cbn; lia].
cbn [hl_segs S4L] in CELL, FR2.
destruct RES2 as [(-> & A2 & q & CBS & Hq & DC2 & SC & HP2) | (-> & A2 & DC2 & HP2)]; cbn [hl_segs S4L] in DC2.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [] m2) as MU.
stash SC. stash G2.
reenter MOK2.
bstep. if_falsex. bstep. ub_skip.
unstash SC. unstash G2.
apply evt_RZ_done.
eapply K1; [ split; [exact VM2 | split; [exact PRES2 | split; [exact ST2 | split; [exact FR2 | exact G2]]]]
| exact FS2 | apply FRM2; exact FRM0 | exact CELL | exact ERR2 | exact HP2 | exact Hq | exact DC2 | exact SC ].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
change (490496 - 164) with 490332 in ERR2.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [(490332, 490336)] m2) as MU.
stash G2.
reenter MOK2.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bstep. if_true. bstep. bstep. bstep. bstep. bstep. bstepz. bstep.
unstash G2.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP3 : HEAPx A2 (BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI;
assert (G3 : jc_glob_P mx) by (eapply jc_glob_P_munch; [exact G2 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia);
assert (PRES3 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mx) by
(eapply presxD_trans; [exact PRES2|]; eapply presxD_of_munch; [exact MU | exact WM |]; intros b Hb Hc Hd;
eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HP2 | intros bb Hbb; exact Hbb | clia | solve_clientW S4L HIx HP2 | exact Hb | exact Hc])
end.
eapply dc_failr with (CBS := []) (REM := []);
[ split; [exact VM2 | split; [exact PRES3 | split; [exact ST2 | split; [exact FR2 | exact G3]]]]
| exact FS2 | apply FRM2; exact FRM0 | exact CELL | | cbn [app]; exact HP3 | exact DC2 | left; split; reflexivity ].
eassumption.
Qed.
End DcP.

End RC__1.
