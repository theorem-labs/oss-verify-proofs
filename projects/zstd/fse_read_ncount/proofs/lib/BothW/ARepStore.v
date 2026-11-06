(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit ARepFrame
AKit AModelFacts F_aalloc2 F_aalloc F_amalloc_icpt F_amalloc_arep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation Wn sp t c AB UB PGE n nodes store :=
([(sp - 4096, sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792); (t + 2800, t + 3169);
(UB - 16, UB + n); (AB, AB + 16); (shad UB, PGE);
(ADEPOT_LO, ADEPOT_HI); (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).
Section CANSEC1. Context {rc : runConstT}.
Section Kinds.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
Definition kfacts : Prop :=
(ATOP <= lo /\ lo <= sp - 4096)
/\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)
/\ (1 <= c <= 16)
/\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
/\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
/\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
/\ shad AB + ssz <= 17594333495296)
/\ (sclr nodes 1048576 /\ 6254592 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6254592 <= store /\ store + 8388608 <= ATOP)
/\ (sclr ctx 65536 /\ 6254592 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfacts.
End Kinds.
Definition bnew (c k n : Z) (p : aptr) (b1 ctx : Z) : xbusy := mkXBusy c k n (BLive p) b1 ctx.
Definition xfast (X : aconc) (c k n : Z) (p : aptr) (b1 ctx : Z) : aconc :=
mkAConc (fun c' => if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c')
(bnew c k n p b1 ctx :: x_busy X).
#[using="Type"] Lemma xfast_busy_of : forall X c k n p b1 ctx c' k',
busy_of (xfast X c k n p b1 ctx) c' k' = if (c =? c') && (k =? k') then Some (bnew c k n p b1 ctx) else busy_of X c' k'.
Proof. intros. unfold xfast, busy_of. cbn. destruct ((c =? c') && (k =? k')); reflexivity. Qed.
#[using="Type"] Lemma xfast_busy_slots : forall X c k n p b1 ctx c',
busy_slots (xfast X c k n p b1 ctx) c' = (if c =? c' then [k] else []) ++ busy_slots X c'.
Proof. intros. unfold xfast, busy_slots. cbn. destruct (c =? c'); reflexivity. Qed.
#[using="Type"] Lemma xfast_cls : forall X c k n p b1 ctx c',
x_cls (xfast X c k n p b1 ctx) c' = if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c'.
Proof. reflexivity. Qed.
#[using="Type"] Lemma awf_fast : forall L st X c k n cnt b1 ctx,
awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = cnt -> 0 < cnt ->
nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None ->
1 <= n <= AREQMAX -> rounded_size n + rz_size n <= size_of_class c -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
awf L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx).
Proof.
intros L st X c k n cnt b1 ctx WF HC CNT POS NK NB N FIT B1 AT1 CTX.
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
pose proof (st_fast_fields st c n cnt) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
{ apply cache_split_last. rewrite <- NK. f_equal. clear -LENC CNT. Local Ltac2 Set LiaHints.tbl := fun () => "0080=25091863719.630153082410.130463143846.740508011410.359308665200.459314971621.259321100262.663020087909.600000:00;00I00L00S00V00d012S3CNT4LENCSS3CNT3POS4LENCS1FS2NE2EQS1FS3CNT3POS4LENCS3CNT3POS4CNTB".
lia. }
assert (LRL : Z.of_nat (length (removelast (xc_cache (x_cls X c)))) = cnt - 1).
{ rewrite length_removelast; [clear -LENC CNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC CNT POS. lia. }
assert (PNE : forall p ch, a_live st !! p = Some ch -> p <> a_next st).
{ intros p ch Hp E. pose proof (FRESH p ch Hp) as F. subst p. clear -F. lia. }
unfold awf. rewrite E1, E2, E6, E7.
split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
split.
{
intros c' HC'. rewrite st_fast_cls, st_fast_max_count, st_fast_ndist, xfast_cls, xfast_busy_slots.
destruct (Z.eqb_spec c' c) as [->|NE].
- rewrite Z.eqb_refl. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count cls_set_count app].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [exact LENF|]. split; [exact LRL|]. split; [clear -CNTB CNT POS; lia|].
rewrite CACHE in ND, RANGE. rewrite <- !app_assoc in ND, RANGE. cbn [app] in ND, RANGE.
split; [exact ND | exact RANGE].
- destruct (Z.eqb_spec c c') as [EQ|_]; [exfalso; clear -EQ NE; lia|]. cbn [app].
destruct (PERC c' HC') as (B1' & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
cbv zeta. repeat lazymatch goal with |- _ /\ _ => split end.
all: first [exact B1' | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact BLENF | exact BLENC | exact BCNTB | exact BND | exact BRANGE
| exact (proj1 B1') | exact (proj2 B1') | exact (proj1 B6) | exact (proj2 B6) | exact (proj1 BCNTB) | exact (proj2 BCNTB)
| match goal with |- ?G => idtac "PERC-LEFT" G end]. }
split.
{ intros c' HC'. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; [exfalso; exact (HC' HC)| exact (OUTC c' HC')]. }
split.
{
intros b [<-|Hb].
- cbn. split; [exact HC|]. split; [exact N|]. split; [exact FIT|]. split; [exact B1|]. split; [exact AT1|]. split; [exact CTX|]. apply lookup_insert_eq.
- destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [p| |]; [| exact M | exact M].
destruct M as (M1 & M2 & M3 & M3' & M4 & M5). split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M3'|]. split; [exact M4|].
rewrite lookup_insert_ne by (symmetry; eapply PNE; exact M5). exact M5. }
split.
{
intros p c0 n0 Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
- rewrite lookup_insert_eq in Hp. injection Hp as <- <-. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. auto.
- rewrite lookup_insert_ne in Hp by congruence. destruct (LIVE p c0 n0 Hp) as (b & Hb & R). exists b. split; [right; exact Hb| exact R]. }
split.
{ intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [clear; lia|].
rewrite lookup_insert_ne in Hp by congruence. pose proof (FRESH p ch Hp) as F. clear -F. lia. }
intros b0 b2 [<-|H0] [<-|H2] EQ [p Hp]; [reflexivity| exfalso | exfalso | exact (UNIQ b0 b2 H0 H2 EQ (ex_intro _ p Hp))].
- cbn in EQ. destruct (BUSY b2 H2) as [_ M]. rewrite <- EQ in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (PNE _ _ M5 eq_refl).
- cbn in EQ. destruct (BUSY b0 H0) as [_ M]. rewrite EQ in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (PNE _ _ M5 eq_refl).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablocks_fast : forall L st X LB c k n cnt b1 ctx,
awf L st X -> ablocks L st X LB ->
ablocks L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx) (HB (a_next st) (aslot_addr L c k + rz_size n) n :: LB).
Proof.
intros L st X LB c k n cnt b1 ctx WF (BH & BF & NDI & NDL).
destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
{ intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
- destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
- exact (FRESH _ _ Lp). }
split; [| split; [| split]].
- intros p A n' [E|Hin].
+ injection E as <- <- <-. left. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. unfold xb_user, xb_alloc. cbn. auto.
+ destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms & Lp & R)].
* left. exists b. split; [right; exact Hb| exact R].
* right. exists mb, ms. split; [| exact R]. pose proof (st_fast_fields st c n cnt) as (_ & _ & _ & _ & _ & E6 & _). rewrite E6.
rewrite lookup_insert_ne; [exact Lp|]. intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59314971621.2000003S1F".
lia.
- intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
- cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
- constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition unbx {P : Prop} (b : boxed P) : P := match b with Box _ p => p end.
#[using="Type"] Lemma arng_fast : forall L RNG st X c n cnt, awf L st X -> arng L RNG st -> arng L RNG (st_fast st c n cnt).
Proof.
intros L RNG st X c n cnt WF (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RC & RPA & RSC & RPSH).
destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
pose proof (st_fast_fields st c n cnt) as (_ & _ & E3 & _ & _ & E6 & _ & E8 & _ & E10 & _).
unfold arng. repeat (split; [assumption|]). split; [| split].
- intros c' Hc'. pose proof (st_fast_counters st c n cnt c') as (E1 & E2 & _ & E4 & E5). cbv zeta. rewrite E1, E4. exact (RC c' Hc').
- rewrite E3. exact RPA.
- split; [| exact RPSH]. eapply RSEC_perm; [apply Permutation_sym; eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [| exact E6| exact E8| exact E10]| exact RSC].
destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59314971621.2000003S1F".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
End S.
End CANSEC1.
