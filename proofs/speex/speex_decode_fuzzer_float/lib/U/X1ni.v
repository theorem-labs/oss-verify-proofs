(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1kx X1el X1ec. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1nc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma lb_remove_app : forall (p : bptr) L1 L2, lb_remove p (L1 ++ L2) = lb_remove p L1 ++ lb_remove p L2.
Proof.
intros p L1 L2. induction L1 as [|b L1 IH]; [reflexivity|]. cbn [app]. rewrite !lb_remove_cons, IH.
destruct (bptr_eqb (blk_id b) p); reflexivity.
Qed.

Definition A_sb_destroy_direct : Z := 0x2e62c.
Definition sbd_site_pc (k : nat) : Z := 0x2e650 + 8 * Z.of_nat k.

Definition sbd_site_addr (a : sb_addrs) (k : nat) : Z := nth k [a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a] 0.

Definition sbd_inv {RCEIL : RunCeiling} (k : nat) (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (S : Z)
(sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xra : word) (F : bvmap 5 word) (fc : bv 32)
(LBk LBr : list block) (lo AB : Z) (m0 : mem) (st0 : PState)
(st : PState) (ms : machine_state) : Prop :=
exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (errv : word),
ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 S) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (sbd_site_pc k)) fc None m (seg_rom rsegs)
/\ RHEAP st (((sbd_blk s, S, SBSTATE_SIZEOF) :: LBk) ++ LBr) m
/\ rw_cells rsegs m S (SBCELLS s a OUT j)
/\ rw_cells rsegs m (bv_unsigned sp + -16) [C8 xs0; C8 xra]
/\ rw_cells rsegs m (errno_addr tp) [C4 errv]
/\ rauxv_ok m AB /\ stk rsegs m lo (bv_unsigned sp + -16) /\ mem_inv rsegs m
/\ rheap_pres LBr (bv_unsigned sp) m0 m
/\ ps_so st = ps_so st0.

Section SITES.
Context {RCEIL : RunCeiling}.
Variables (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (S : Z).
Variables (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xra : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LBr : list block) (lo AB : Z) (m0 : mem) (st0 : PState).
Hypothesis SB : bv_unsigned sp <= AB.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 16 - RFREE_STACK.
Hypothesis TPE : tp = Z_to_bv 64 RATP.
Hypothesis SPOS : 0 < S /\ S + 160 < 2^63.

Local Notation INV := (fun k LBk => sbd_inv k s a OUT j S sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xra F fc LBk LBr lo AB m0 st0).

#[using="SB CLO LO TPE"] Lemma sbd_free_site : forall (k : nat) (ob : option bptr) (nk : Z) (LBk : list block) st ms,
(k < 8)%nat ->
match ob with None => sbd_site_addr a k = 0 | Some b => In (b, sbd_site_addr a k, nk) LBk end ->
INV k LBk st ms ->
implM rsegs (free_opt raw_free ob) st
(fun _ st' ms' => INV (Datatypes.S k) (match ob with None => LBk | Some b => lb_remove b LBk end) st' ms')
ms.
Proof.
intros k ob nk LBk st ms Hk Hob sfH_; first [ sf_destruct 28%nat sfH_ as ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m errv -> HEAP X FR ERR AUX ST MI HP PSO | sf_fb; destruct sfH_ as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & errv & -> & HEAP & X & FR & ERR & AUX & ST & MI & HP & PSO) ].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv. unfold RFREE_STACK in LO.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
unfold sb_cells in X.

eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR (Z_to_bv 64 (sbd_site_pc (Datatypes.S k))) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 S) s1
(Z_to_bv 64 (sbd_site_addr a k)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs))).
{ unfold sbd_site_pc, sbd_site_addr.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [ | | | | | | | | exfalso; lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add];
step; step; apply evt_done; reflexivity. }
cbv beta. intros ms1 ->.
destruct ob as [b|].
-
eapply implM_mono.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m st _ b (sbd_site_addr a k) nk lo AB _ HEAP).
- right. apply in_app_iff. left. exact Hob.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CLO.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERR.
- exact MI.
- exact TPE.
- reflexivity. }
cbv beta. intros [] st' ms' PF. first [ sf_destruct 25%nat PF as z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 m' -> MI' ST' ERR' AUX' HP' PSF' PSO' HEAP' | sf_fb; destruct PF as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & PSF' & PSO' & HEAP') ].
rewrite unsigned_lit in ST' by lia. rewrite unsigned_lit in HP' by lia. rewrite ret_pc_even by (unfold sbd_site_pc; lia).
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP) as ND.

assert (INb : In (b, sbd_site_addr a k, nk) (((sbd_blk s, S, SBSTATE_SIZEOF) :: LBk) ++ LBr)) by (right; apply in_app_iff; left; exact Hob).
assert (NS : sbd_blk s <> b).
{ intros E. cbn [map app] in ND. apply (proj1 (List.NoDup_cons_iff _ _)) in ND. destruct ND as [NI _]. apply NI. cbn. rewrite E.
rewrite map_app. apply in_app_iff. left. apply (in_map blk_id) in Hob. exact Hob. }
assert (NR : forall b', In b' LBr -> blk_id b' <> b).
{ intros b' Hb' E. cbn [map app] in ND. apply (proj1 (List.NoDup_cons_iff _ _)) in ND. destruct ND as [_ ND]. rewrite map_app in ND.
eapply (NoDup_app_in_neq _ _ _ _ ND); [apply (in_map blk_id) in Hob; exact Hob| apply in_map; exact Hb'| cbn; symmetry; exact E]. }
assert (PR : Permutation (lb_remove b (((sbd_blk s, S, SBSTATE_SIZEOF) :: LBk) ++ LBr)) (((sbd_blk s, S, SBSTATE_SIZEOF) :: lb_remove b LBk) ++ LBr)).
{ cbn [app]. rewrite lb_remove_cons. cbn [blk_id fst snd]. rewrite (bptr_eqb_neq _ _ NS). apply perm_skip.
rewrite lb_remove_app. rewrite (lb_remove_notin b LBr); [apply Permutation_refl|].
intros Hin. apply in_map_iff in Hin. destruct Hin as (b' & E & Hb'). exact (NR b' Hb' E). }
unfold sbd_inv. first [ unshelve sf_eexists 18%nat; [ exact ((Z_to_bv 64 (sbd_site_pc (Datatypes.S k)))) | exact (z0) | exact (z1) | exact (z2) | exact (za0) | exact (za1) | exact (za2) | exact (za3) | exact (za4) | exact (za5) | exact (za6) | exact (za7) | exact (z3) | exact (z4) | exact (z5) | exact (z6) | exact (m') | exact (errv) | ] | sf_fb; exists (Z_to_bv 64 (sbd_site_pc (Datatypes.S k))), z0, z1, z2, za0, za1, za2, za3, za4, za5, za6, za7, z3, z4, z5, z6, m', errv ].
split; [reflexivity|]. split; [eapply RHEAP_perm; [exact HEAP'| exact PR]|].
split.
{ unfold sb_cells. eapply rheap_pres_rw_cells; [exact HP'| exact X|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF).
split; [apply in_lb_remove_keep; [left; reflexivity| cbn [blk_id fst snd]; exact NS]|]. cbn [blk_addr blk_size fst snd]. rewrite sb_cells_size. unfold SBSTATE_SIZEOF. lia. }
split; [eapply rheap_pres_rw_cells; [exact HP'| exact FR| left; cbn; lia]|].
split; [exact ERR'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact MI'|].
split; [| rewrite PSO'; exact PSO].
eapply rheap_pres_trans; [exact HP|]. eapply rheap_pres_weaken; [exact HP'| lia|].
intros b' Hb'. apply in_lb_remove_keep; [apply in_app_iff; right; exact Hb'| exact (NR b' Hb')].
-
cbn [free_opt]. apply implM_ret.
eapply evt_mono. { eapply (rfree_null_spec). rewrite Hob. reflexivity. }
cbv beta. intros ms' ->. rewrite ret_pc_even by (unfold sbd_site_pc; lia).
unfold sbd_inv. first [ unshelve sf_eexists 18%nat; [ exact ((Z_to_bv 64 (sbd_site_pc (Datatypes.S k)))) | exact (t0) | exact (t1) | exact (t2) | exact ((Z_to_bv 64 (sbd_site_addr a k))) | exact (a1) | exact (a2) | exact (a3) | exact (a4) | exact (a5) | exact (a6) | exact (a7) | exact (t3) | exact (t4) | exact (t5) | exact (t6) | exact (m) | exact (errv) | ] | sf_fb; exists (Z_to_bv 64 (sbd_site_pc (Datatypes.S k))), t0, t1, t2, (Z_to_bv 64 (sbd_site_addr a k)), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m, errv ].
split; [reflexivity|]. split; [exact HEAP|]. split; [unfold sb_cells; exact X|]. split; [exact FR|].
split; [rewrite ETP; unfold RERRNO; exact ERR|]. split; [exact AUX|]. split; [exact ST|]. split; [exact MI|]. split; [exact HP| exact PSO].
Qed.
End SITES.

Definition sbd_sizes (s : sbd_state bptr) : list Z := [256; 256; 4 * sbd_subframeSize s; 32; 32; 16; 16; 64].
Definition sbd_addrs (a : sb_addrs) : list Z := [a_g0 a; a_g1 a; a_exc a; a_oq a; a_iq a; a_pg a; a_er a; a_msp a].
Fixpoint present (obs : list (option bptr)) (addrs sizes : list Z) : list block :=
match obs, addrs, sizes with
| Some b :: o', ad :: ad', n :: n' => (b, ad, n) :: present o' ad' n'
| None :: o', _ :: ad', _ :: n' => present o' ad' n'
| _, _, _ => []
end.

Lemma present_drop_site : forall obs addrs sizes k,
length obs = 8%nat -> length addrs = 8%nat -> length sizes = 8%nat -> (k < 8)%nat ->
List.NoDup (map blk_id (present (skipn k obs) (skipn k addrs) (skipn k sizes))) ->
match nth k obs None with
| None => present (skipn (S k) obs) (skipn (S k) addrs) (skipn (S k) sizes) = present (skipn k obs) (skipn k addrs) (skipn k sizes)
| Some b => In (b, nth k addrs 0, nth k sizes 0) (present (skipn k obs) (skipn k addrs) (skipn k sizes))
/\ lb_remove b (present (skipn k obs) (skipn k addrs) (skipn k sizes)) = present (skipn (S k) obs) (skipn (S k) addrs) (skipn (S k) sizes)
end.
Proof.
intros obs addrs sizes k LO LA LS Hk ND.
assert (G : forall (l : list (option bptr)) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l).
{ clear. intros l. induction l as [|x l IH]; intros k d H; [cbn in H; lia|]. destruct k; [reflexivity|]. cbn. apply IH. cbn in H. lia. }
assert (GZ : forall (l : list Z) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l).
{ clear. intros l. induction l as [|x l IH]; intros k d H; [cbn in H; lia|]. destruct k; [reflexivity|]. cbn. apply IH. cbn in H. lia. }
rewrite (G obs k None), (GZ addrs k 0), (GZ sizes k 0) in ND |- * by lia.
destruct (nth k obs None) as [b|]; cbn [present].
- split; [left; reflexivity|]. rewrite lb_remove_cons. cbn [blk_id fst snd]. rewrite bptr_eqb_refl'. apply lb_remove_notin.
cbn [present map] in ND. apply (proj1 (List.NoDup_cons_iff _ _)) in ND. exact (proj1 ND).
- reflexivity.
Qed.

Lemma skipn_cons_nth {A} (l : list A) : forall k x r d, x :: r = skipn k l -> x = nth k l d /\ r = skipn (S k) l.
Proof.
induction l as [|y l IH]; intros k x r d E.
- destruct k; cbn in E; discriminate E.
- destruct k as [|k]; cbn in E.
+ inversion E; subst. split; reflexivity.
+ destruct (IH k x r d E) as [E1 E2]. split; [exact E1|]. rewrite E2. reflexivity.
Qed.

Fixpoint frees_from {B} (l : list (option bptr)) (tail : M PState B) : M PState B :=
match l with [] => tail | o :: l' => free_opt raw_free o ;;; frees_from l' tail end.

Definition sbdp_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(st0 : PState) (LBr : list block) (AB lo : Z) (m0 : mem) (st' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rheap_pres LBr (bv_unsigned sp) m0 m'
/\ ps_so st' = ps_so st0
/\ RHEAP st' LBr m'.

Theorem rdes_sb_partial {RCEIL : RunCeiling} :
forall (s : sbd_state bptr) (a : sb_addrs) (OUT STEREO : Z) (j : sb_junk) (S : Z) (low : dec_state bptr)
(LBL LB LBr : list block) (o0 o1 o2 o3 o4 o5 o6 o7 : option bptr)
(st : PState) (lo AB : Z) (errv : word) {B} (K : M PState B) (Q : B -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
let obs := [o0; o1; o2; o3; o4; o5; o6; o7] in
let PRES := present obs (sbd_addrs a) (sbd_sizes s) in
(forall k, (k < 8)%nat -> nth k obs None = None -> sbd_site_addr a k = 0) ->
RHEAP st LB m -> Permutation LB (LBL ++ ((sbd_blk s, S, SBSTATE_SIZEOF) :: PRES) ++ LBr) ->
DREP OUT STEREO m (a_low a) low LBL -> (dec_depth low <= 3)%nat -> (sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) ->
rw_cells rsegs m S (SBCELLS s a OUT j) -> rtables_pristine m ->
rauxv_ok m AB -> bv_unsigned sp <= AB ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - (16 + des_depth low) ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc -> tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 S ->
(forall st' ms', sbdp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LBr AB lo m st' ms' -> implM rsegs K st' Q ms') ->
implM rsegs (speex_decoder_destroy raw_free low ;;;
free_opt raw_free o0 ;;; free_opt raw_free o1 ;;; free_opt raw_free o2 ;;; free_opt raw_free o3 ;;;
free_opt raw_free o4 ;;; free_opt raw_free o5 ;;; free_opt raw_free o6 ;;; free_opt raw_free o7 ;;;
raw_free (sbd_blk s) ;;; K) st Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sb_destroy_direct) fc None m (seg_rom rsegs)).
Proof.
intros s a OUT STEREO j S low LBL LB LBr o0 o1 o2 o3 o4 o5 o6 o7 st lo AB errv B K Q
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
cbv zeta. intros NULLS HEAP PERM RL DEPTH Imo X TP AUX SB ST CLO LO ERR MI FRM TPE -> HK.
set (PRES := present [o0; o1; o2; o3; o4; o5; o6; o7] (sbd_addrs a) (sbd_sizes s)) in *.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
assert (CDP : RFREE_STACK <= des_depth low) by (clear; induction low; cbn; unfold RFREE_STACK in *; lia). unfold RFREE_STACK in CDP.
assert (INL : forall b, In b (LBL ++ ((sbd_blk s, S, SBSTATE_SIZEOF) :: PRES) ++ LBr) -> In b LB) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
assert (INS : In (sbd_blk s, S, SBSTATE_SIZEOF) LB) by (apply INL; apply in_app_iff; right; left; reflexivity).
pose proof (RHEAP_block_range_proof _ _ _ _ HEAP INS) as BRS. unfold blk_addr, blk_size, SBSTATE_SIZEOF in BRS. cbn [fst snd] in BRS.
first [ sf_destruct 5%nat BRS as S0 S16 _ SCE SIMG | sf_fb; destruct BRS as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE.
unfold sb_cells in X.

pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
carve_frame 16%nat ST.
eapply (implM_evt rsegs _ _ _ (fun ms1 => exists m1,
ms1 = MS (mkR (Z_to_bv 64 0x2e650) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 S) s1
(Z_to_bv 64 (a_low a)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_destroy) fc None m1 (seg_rom rsegs)
/\ rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -16))).
{ unfold A_sb_destroy_direct. zstep. des_walk 0x1cf48.
apply evt_done; eexists; (split; [reflexivity|]); (split; [eassumption|]); (split; [exact MU0|]); (split; [exact WM0|]); split; assumption. }
clear MU0 WM0. cbv beta. intros ms1 sfH_; first [ sf_destruct 7%nat sfH_ as m1 -> FRa MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (m1 & -> & FRa & MU1 & WM1 & MI1 & ST1) ].
assert (HEAP1 : RHEAP st LB m1).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn [fst]. lia. }
assert (AUX1 : rauxv_ok m1 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (ERR1 : rw_cells rsegs m1 316332 [C4 errv]).
{ eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. split; [lia| exact I]. }
assert (TP1 : rtables_pristine m1).
{ eapply rtables_pristine_munch; [exact TP| exact MU1|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. split; [lia| exact I]. }
assert (X1 : rw_cells rsegs m1 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rw_cells_transport; [exact X| exact MU1| exact WM1|]. cbn. split; [lia| exact I]. }
assert (RL1 : DREP OUT STEREO m1 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL| exact MU1| exact WM1|]. intros b x Hb Hx.
assert (HbL : In b LB) by (apply INL; apply in_app_iff; left; exact Hb).
first [ pose proof (RHEAP_block_range_proof _ _ _ _ HEAP HbL) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ _ HEAP HbL) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. cbn. split; [lia| exact I]. }
clear X RL ERR TP.

eapply implM_bind.
{ eapply (rdes_all low OUT STEREO (a_low a) LBL LB (((sbd_blk s, S, SBSTATE_SIZEOF) :: PRES) ++ LBr) st lo AB errv); try reflexivity.
- exact HEAP1.
- exact PERM.
- exact RL1.
- exact TP1.
- exact AUX1.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST1.
- exact CLO.
- rewrite unsigned_lit by lia. lia.
- rewrite ETP. unfold RERRNO. exact ERR1.
- exact MI1.
- exact FRM.
- exact TPE. }
cbv beta. intros [] s1' ms2 sfH_; first [ sf_destruct 28%nat sfH_ as x0 x1 x2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x3 x4 x5 x6 F1 fc1 m2 errv1 -> FRM1 MI2 ST2 ERR2 AUX2 HP2 PSO2 HEAP2 | sf_fb; destruct sfH_ as (x0 & x1 & x2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & x3 & x4 & x5 & x6 & F1 & fc1 & m2 & errv1 & -> & FRM1 & MI2 & ST2 & ERR2 & AUX2 & HP2 & PSO2 & HEAP2) ].
rewrite unsigned_lit in ST2 by lia. rewrite unsigned_lit in HP2 by lia. rewrite ret_pc_even by lia.
assert (X2 : rw_cells rsegs m2 S (SBCELLS s a OUT j)).
{ eapply rheap_pres_rw_cells; [exact HP2| exact X1|]. right; right. exists (sbd_blk s, S, SBSTATE_SIZEOF). split; [apply in_app_iff; left; left; reflexivity|].
unfold blk_addr, blk_size, SBSTATE_SIZEOF. cbn [fst snd]. rewrite sb_cells_size. lia. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP2| exact FRa| left; cbn; lia]).
assert (HPacc2 : rheap_pres LBr (bv_unsigned sp) m m2).
{ eapply rheap_pres_trans.
- eapply (rheap_pres_of_munch LBr (bv_unsigned sp) _ m m1 MU1 WM1). intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
first [ pose proof (RHEAP_block_range_proof _ _ _ b HEAP ltac:(apply INL; apply in_app_iff; right; right; apply in_app_iff; right; exact Hb)) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ b HEAP ltac:(apply INL; apply in_app_iff; right; right; apply in_app_iff; right; exact Hb)) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. unfold in_block in Hab. lia.
- eapply rheap_pres_weaken; [exact HP2| lia| intros b Hb; apply in_app_iff; right; exact Hb]. }

assert (I0 : sbd_inv 0 s a OUT j S sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 ra F1 fc1 PRES LBr lo AB m st s1'
(MS (mkR (Z_to_bv 64 190032) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x0 x1 x2 (Z_to_bv 64 S) s1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
F1 (Z_to_bv 64 190032) fc1 None m2 (seg_rom rsegs))).
{ unfold sbd_inv. sf_eexists 16%nat. exists m2, errv1. split; [reflexivity|]. split; [exact HEAP2|]. split; [exact X2|]. split; [exact FR2|].
split; [exact ERR2|]. split; [exact AUX2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact HPacc2| exact PSO2]. }
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND2.
clear HEAP HEAP1 AUX AUX1 ERR1 ERR2 MI MI1 ST ST1 FRa FR2 X1 X2 MU1 WM1 TP1 RL1 HP2 AUX2 MI2 ST2.

assert (SITES : forall (l : list (option bptr)) (k : nat) st1 ms1,
l = skipn k [o0; o1; o2; o3; o4; o5; o6; o7] -> (k + length l = 8)%nat ->
sbd_inv k s a OUT j S sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 ra F1 fc1
(present l (skipn k (sbd_addrs a)) (skipn k (sbd_sizes s))) LBr lo AB m st st1 ms1 ->
implM rsegs (frees_from l (raw_free (sbd_blk s) ;;; K)) st1 Q ms1).
{ induction l as [|o l IHl]; intros k st1 ms1 El Hk Ik.
-
cbn [frees_from]. cbn [length] in Hk. rewrite Nat.add_0_r in Hk. subst k.
first [ sf_destruct 28%nat Ik as zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 mk errk -> HEAPk Xk FRk ERRk AUXk STk MIk HPk PSOk | sf_fb; destruct Ik as (zra & z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & mk & errk & -> & HEAPk & Xk & FRk & ERRk & AUXk & STk & MIk & HPk & PSOk) ].
cbn [present skipn] in HEAPk.
rewrite ETP in ERRk. unfold RERRNO in ERRk.
eapply (implM_evt rsegs _ _ _ (fun ms => ms = _)). { unfold sbd_site_pc. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add]. step. step. step. step. step. apply evt_done. reflexivity. }
cbv beta. intros ms_fin ->. rewrite ?unsigned_lit by lia.
release_frame FRk STk (bv_unsigned sp).
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAPk) as NDk.
eapply implM_bind.
{ eapply (rfree_spec_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk st1 _ (sbd_blk s) S SBSTATE_SIZEOF lo AB _ HEAPk).
- left. reflexivity.
- exact AUXk.
- first [exact SB | rewrite Z_to_bv_bv_unsigned; exact SB | idtac "SBFIX"].
- first [exact STk | idtac "STFIX"].
- exact CLO.
- unfold RFREE_STACK. lia.
- rewrite ETP. unfold RERRNO. exact ERRk.
- exact MIk.
- exact TPE.
- reflexivity. }
cbv beta. intros [] st2 ms3 PF. first [ sf_destruct 25%nat PF as q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 m3 -> MI3 ST3 ERR3 AUX3 HP3 PSF3 PSO3 HEAP3 | sf_fb; destruct PF as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & PSF3 & PSO3 & HEAP3) ].
apply HK. unfold sbdp_post.
apply (RHEAP_perm _ _ LBr) in HEAP3.
2:{ apply (lb_remove_perm_of _ (sbd_blk s, S, SBSTATE_SIZEOF)); [| exact NDk]. cbn [app]. apply Permutation_refl. }
sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F1) | exact (fc1) | exact (m3) | exact (errk) | ] | sf_fb; exists F1, fc1, m3, errk ].
split; [reflexivity|]. split; [exact FRM1|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
split.
{ eapply rheap_pres_trans; [exact HPk|]. eapply rheap_pres_weaken; [exact HP3| lia|]. intros b Hb. apply in_lb_remove_keep; [right; exact Hb|].
apply not_eq_sym. eapply (NoDup_app_in_neq (map blk_id [(sbd_blk s, S, SBSTATE_SIZEOF)]) (map blk_id LBr)); [| left; reflexivity| apply in_map; exact Hb].
rewrite <- map_app. exact NDk. }
split; [rewrite PSO3; exact PSOk| exact HEAP3].
-
cbn [frees_from]. cbn [length] in Hk.
assert (Hk8 : (k < 8)%nat) by lia.
pose proof Ik as sfP_; first [ sf_destruct 21%nat sfP_ as zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 mk errk Ems HEAPk _ | sf_fb; destruct sfP_ as (zra & z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & mk & errk & Ems & HEAPk & _) ].
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAPk) as NDk. cbn [map app] in NDk. apply (proj1 (List.NoDup_cons_iff _ _)) in NDk. destruct NDk as [_ NDk].
rewrite map_app in NDk. apply List.NoDup_app_remove_r in NDk.
destruct (skipn_cons_nth _ _ _ _ None El) as [EO El'].
pose proof (present_drop_site [o0; o1; o2; o3; o4; o5; o6; o7] (sbd_addrs a) (sbd_sizes s) k eq_refl eq_refl eq_refl Hk8) as PD.
rewrite <- El in PD. specialize (PD NDk). rewrite El in PD.
subst o. revert Ik PD El. destruct (nth k [o0; o1; o2; o3; o4; o5; o6; o7] None) as [b|] eqn:EN; intros Ik PD El.
+ destruct PD as [PIN PE]. eapply implM_bind.
{ eapply (sbd_free_site s a OUT j S sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 ra F1 fc1 LBr lo AB m st SB CLO ltac:(unfold RFREE_STACK; lia) TPE
k (Some b) (nth k (sbd_sizes s) 0) _ st1 ms1 Hk8).
- cbn beta iota. rewrite <- El in PIN. exact PIN.
- exact Ik. }
cbv beta. intros [] st2 ms2' Ik1. apply (IHl (Datatypes.S k)); [exact El'| lia|]. rewrite <- El in PE. rewrite El' at 1. rewrite <- PE. exact Ik1.
+ eapply implM_bind.
{ eapply (sbd_free_site s a OUT j S sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 ra F1 fc1 LBr lo AB m st SB CLO ltac:(unfold RFREE_STACK; lia) TPE
k None (nth k (sbd_sizes s) 0) _ st1 ms1 Hk8).
- cbn beta iota. apply NULLS; [exact Hk8| exact EN].
- exact Ik. }
cbv beta. intros [] st2 ms2' Ik1. apply (IHl (Datatypes.S k)); [exact El'| lia|]. rewrite <- El in PD. rewrite El' at 1. rewrite PD. exact Ik1. }
change (free_opt raw_free o0 ;;; free_opt raw_free o1 ;;; free_opt raw_free o2 ;;; free_opt raw_free o3 ;;;
free_opt raw_free o4 ;;; free_opt raw_free o5 ;;; free_opt raw_free o6 ;;; free_opt raw_free o7 ;;; raw_free (sbd_blk s) ;;; K)
with (frees_from [o0; o1; o2; o3; o4; o5; o6; o7] (raw_free (sbd_blk s) ;;; K)).
eapply (SITES _ 0%nat); [reflexivity| reflexivity| exact I0].
Qed.
