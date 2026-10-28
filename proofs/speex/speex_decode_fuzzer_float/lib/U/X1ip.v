(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0om X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1ik X1ij X1im.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition OGG_REALLOC_STACK : Z := 8256.

Lemma lxor_ones63 : forall a, 0 <= a < 2^63 -> Z.lxor a 9223372036854775807 = 9223372036854775807 - a.
Proof.
intros a Ha.
assert (E : 9223372036854775807 - a = (Z.lnot a) mod 2^63).
{ unfold Z.lnot. apply Z.mod_unique with (q := -1); [left; lia| lia]. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. change 9223372036854775807 with (Z.ones 63).
destruct (Z.lt_ge_cases i 63).
- rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. apply xorb_true_r.
- rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia. rewrite xorb_false_r.
apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|].
apply Z.lt_le_trans with 63; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma stream_blocks_newbody : forall LB (os : stream_st bptr) Bd L Gv pb q Bd' n' bs',
stream_blocks LB os Bd L Gv -> os_body_data os = Some pb ->
List.NoDup (q :: map blk_id (lb_remove pb LB)) ->
stream_blocks ((q, Bd', n') :: lb_remove pb LB)
(set_blocks os (Some q) bs' (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os)) Bd' L Gv.
Proof.
intros LB os Bd L Gv pb q Bd' n' bs' SB Hpb ND.
apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
first [ sf_destruct 6%nat SB as SB1 SB2 SB3 D12 D13 D23 | sf_fb; destruct SB as (SB1 & SB2 & SB3 & D12 & D13 & D23) ]. unfold stream_blocks. destruct os; cbn in *. subst.
split; [exists n'; left; reflexivity|].
split. { destruct os_lacing_vals as [p2|]; [| exact SB2]. destruct SB2 as [n2 IN2]. exists n2. right.
apply lb_remove_keep; [exact IN2| cbn; intros EQ; eapply D12; [reflexivity| reflexivity| symmetry; exact EQ]]. }
split. { destruct os_granule_vals as [p3|]; [| exact SB3]. destruct SB3 as [n3 IN3]. exists n3. right.
apply lb_remove_keep; [exact IN3| cbn; intros EQ; eapply D13; [reflexivity| reflexivity| symmetry; exact EQ]]. }
split. { intros p q' Hp -> ->. injection Hp as ->. apply NI. destruct SB2 as [n2 IN2].
apply (in_map_blk_id (q', L, n2)). apply lb_remove_keep; [exact IN2| cbn; intros EQ; eapply D12; [reflexivity| reflexivity| symmetry; exact EQ]]. }
split. { intros p q' Hp -> ->. injection Hp as ->. apply NI. destruct SB3 as [n3 IN3].
apply (in_map_blk_id (q', Gv, n3)). apply lb_remove_keep; [exact IN3| cbn; intros EQ; eapply D13; [reflexivity| reflexivity| symmetry; exact EQ]]. }
exact D23.
Qed.

Section EXP.
Context {RCEIL : RunCeiling}.
Variable rhdr_known : PState -> bptr -> Prop.
Hypothesis rhdr_known_indep : forall s s' p, rhdr_known s p -> rhdr_known s' p.

Definition ogg_realloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (oldbytes : list byte) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rw_cells rsegs m' A [CB (Z.to_nat old) oldbytes] /\ rhdr_known s' p
| Some q => exists A' junk,
a0 = Z_to_bv 64 A' /\ rblock_range A' n
/\ RHEAP s' ((q, A', n) :: lb_remove p LB) m'
/\ rw_cells rsegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n old)) oldbytes ++ junk)]
/\ rhdr_known s' q /\ (q = p -> A' = A)
end.

Definition ogg_realloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbytes : list byte),
RHEAP s LB m -> In (p, A, old) LB -> rhdr_known s p -> 1024 <= n ->
rw_cells rsegs m A [CB (Z.to_nat old) oldbytes] ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - OGG_REALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
implM rsegs (raw_realloc p n) s
(ogg_realloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbytes m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_realloc) fc None m (seg_rom rsegs)).

Hypothesis HR : ogg_realloc_stmt.
Hypothesis HF : rfree_stmt.

#[using="HR"] Lemma realloc_site : forall {R} (k : option bptr -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (p : bptr) (A old n SP RA SA lo B : Z) (errv : word) (oldbytes : list byte)
(fcs scs : list cell)
(gp tp : word) (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> In (p, A, old) LB -> rhdr_known s p -> rw_cells rsegs m A [CB (Z.to_nat old) oldbytes] ->
rauxv_ok m B -> SP <= B -> 0 <= SP < 2^64 -> 1024 <= n ->
stk rsegs m lo SP -> alloc_ceiling <= lo -> lo <= SP - OGG_REALLOC_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
0 <= n < MMAP_THRESHOLD -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
rw_cells rsegs m SP fcs -> rw_cells rsegs m SA scs -> SP <= SA ->
(forall (m' : mem) (s' : PState) (r : option bptr) (errv' : word) (y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rauxv_ok m' B -> stk rsegs m' lo SP ->
rw_cells rsegs m' 316332 [C4 errv'] -> mem_inv rsegs m' ->
rheap_pres (lb_remove p LB) SP m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' SP fcs -> rw_cells rsegs m' SA scs ->
match r with
| None => va0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rw_cells rsegs m' A [CB (Z.to_nat old) oldbytes] /\ rhdr_known s' p
| Some q => exists A' junk, va0 = Z_to_bv 64 A' /\ rblock_range A' n /\ RHEAP s' ((q, A', n) :: lb_remove p LB) m'
/\ rw_cells rsegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n old)) oldbytes ++ junk)]
/\ rhdr_known s' q /\ (q = p -> A' = A)
end ->
implM rsegs (k r) s' Q
(MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp y5 y6 y7 x8 x9 va0 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 RA) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (raw_realloc p n) k) s Q
(MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 A) (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 A_realloc) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP HIN HK BLK AUX SPB SP0 HBIG ST CEIL LO ERR MI TP Hn HRA HRA2 FR OS LE K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold OGG_REALLOC_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. pose proof (rw_cells_bound _ _ _ _ OS) as OB.
eapply implM_bind.
{ unfold ogg_realloc_stmt in HR.
eapply HR with (s := s) (LB := LB) (p := p) (A := A) (old := old) (n := n) (lo := lo) (B := B) (errv := errv) (oldbytes := oldbytes).
- exact HP.
- exact HIN.
- exact HK.
- exact HBIG.
- exact BLK.
- exact AUX.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold OGG_REALLOC_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity.
- reflexivity.
- exact Hn. }
cbv beta. intros r ps ms PO.
first [ sf_destruct 26%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ERR' AUX' HPR FA SO RES | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & RES) ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
rewrite (ret_pc_even RA) by assumption.
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
Qed.

Definition body_expand_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (os : stream_st bptr) (pb : bptr) (needed A Bd L Gv lo B : Z) (hdr bodybytes : list byte) (m : mem)
(r : Z * stream_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fst r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with (rc, os') =>
(rc = 0 /\ exists (q : bptr) (Bd' : Z) (junk : list byte) (LB' : list block),
os' = set_blocks os (Some q) (os_body_storage os') (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os)
/\ os_body_storage os <= os_body_storage os' /\ os_body_fill os + needed <= os_body_storage os'
/\ RHEAP s' LB' m' /\ (forall b, In b (lb_remove pb LB) -> In b LB')
/\ In (q, Bd', os_body_storage os') LB' /\ stream_blocks LB' os' Bd' L Gv /\ rhdr_known s' q
/\ (forall b, In b LB -> blk_id b <> pb -> blk_id b <> q)
/\ rblock_range Bd' (os_body_storage os')
/\ cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 408)] (lb_remove pb LB) (bv_unsigned sp) m m'
/\ rw_cells rsegs m' A (stream_cells Bd' L Gv hdr os')
/\ rw_cells rsegs m' Bd' [CB (Z.to_nat (os_body_storage os')) (bodybytes ++ junk)]
/\ Permutation LB' ((q, Bd', os_body_storage os') :: lb_remove pb LB))
\/ (rc = -1 /\ os' = stream_zero /\ RHEAP s' (stream_clear_LB LB os) m'
/\ cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 408)] (stream_clear_LB LB os) (bv_unsigned sp) m m'
/\ rw_cells rsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero))
end.

#[using="HR HF"] Lemma os_body_expand_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (os : stream_st bptr) (pb : bptr) (needed A Bd L Gv lo B : Z) (hdr bodybytes : list byte) (errv : word),
RHEAP s LB m -> stream_blocks LB os Bd L Gv -> length hdr = 284%nat ->
os_body_data os = Some pb -> In (pb, Bd, os_body_storage os) LB -> rhdr_known s pb ->
rw_cells rsegs m Bd [CB (Z.to_nat (os_body_storage os)) bodybytes] ->
0 <= needed < 2^62 -> 0 <= os_body_storage os < 2^62 -> 0 <= os_body_fill os < 2^63 ->
os_body_fill os <= os_body_storage os ->
(os_body_storage os - needed <= os_body_fill os -> os_body_storage os + needed + 1024 < MMAP_THRESHOLD) ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - OGG_REALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 needed -> rw_cells rsegs m A (stream_cells Bd L Gv hdr os) ->
implM rsegs (os_body_expand raw_realloc raw_free os needed) s
(body_expand_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB os pb needed A Bd L Gv lo B hdr bodybytes m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP SB HL Hpb HIN HK BLK Hnd Hbs Hbf Hfs Hbound AUX SPB SPA AB ST CEIL LO ERR MI TP -> -> OS.
unfold A_os_body_expand. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold OGG_REALLOC_STACK in LO.
pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as SB1 SB2 SB3 D12 D13 D23 | sf_fb; destruct sfP_ as (SB1 & SB2 & SB3 & D12 & D13 & D23) ].
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (RHEAP_block_range_proof _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR.
first [ sf_destruct 5%nat BR as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct BR as (BR1 & BR2 & BR3 & BR4 & BR5) ].
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold os_body_expand. unfold implM. iprefix.
carve_frame 32%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. if_cases CN1; zify_cond CN1; rewrite !zb_signed_small in CN1 by lia.

2:{ replace (os_body_fill os <? os_body_storage os - needed) with true by (symmetry; apply Z.ltb_lt; lia).

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
apply evt_done. cbv beta iota. apply impl_ret_ok. apply evt_done. cbn [fst snd].
unfold body_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split; [reflexivity|]. split; [reflexivity|].
cbn [fst snd]. left. split; [reflexivity|]. first [ unshelve sf_eexists 4%nat; [ exact (pb) | exact (Bd) | exact ((@nil byte)) | exact (LB) | ] | sf_fb; exists pb, Bd, (@nil byte), LB ].
split. { rewrite <- Hpb. destruct os; reflexivity. }
split; [lia|]. split; [lia|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split; [intros b Hb; eapply lb_remove_sub; exact Hb|].
split; [exact HIN|]. split; [exact SB|]. split; [exact HK|].
split; [intros b _ NE; exact NE|].
split; [exact (conj BR1 (conj BR2 (conj BR3 (conj BR4 BR5))))|].
split. { apply cmod_of_munch; [exact MU| exact WM]. }
split; [exact OS|]. split; [rewrite app_nil_r; exact BLK|].
cbn [os_body_storage set_blocks]. apply perm_hd_lbr; [exact (RHEAP_blocks_nodup_proof _ _ _ HP)| exact HIN]. }

replace (os_body_fill os <? os_body_storage os - needed) with false by (symmetry; apply Z.ltb_ge; lia).
specialize (Hbound ltac:(lia)). unfold MMAP_THRESHOLD in Hbound.

zstep. zstep. zstep. zstep. if_cases CN2; zify_cond CN2.
all: rewrite lxor_ones63 in CN2 by lia; rewrite !zb_signed_small in CN2 by lia.
2:{ exfalso. lia. }
replace (LONG_MAX - needed <? os_body_storage os) with false by (symmetry; apply Z.ltb_ge; unfold LONG_MAX; lia).
rewrite Hpb.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
replace (os_body_storage os + needed + 2^63 <? 18446744073709550591) with true by (symmetry; apply Z.ltb_lt; lia).
replace (os_body_storage os + needed <? LONG_MAX - 1024) with true by (symmetry; apply Z.ltb_lt; unfold LONG_MAX; lia).
change (Z.b2z true ≪ 10) with 1024. rewrite Z.mul_1_r.
set (n' := os_body_storage os + needed + 1024).
assert (Hn' : os_body_storage os + needed + 1024 <= n' < MMAP_THRESHOLD) by (subst n'; unfold MMAP_THRESHOLD; lia).
pose proof BLK as BLK0. destruct BLK0 as [[[LENb _] _] _].

zstep. apply evt_done.
eapply (realloc_site _ _ s LB pb Bd (os_body_storage os) n' (bv_unsigned sp + -32) 0x3036c A lo B errv bodybytes _ _ gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact BLK | exact OS | exact FR | exact ERR]
| |- In _ _ => exact HIN
| |- rhdr_known _ _ => exact HK
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- _ mod 2 = 0 => reflexivity
| |- forall m', _ => idtac
| |- _ => try (unfold OGG_REALLOC_STACK, MMAP_THRESHOLD in *; lia)
end.
clear AUX ST ERR MI FR OS. rename MU into MU0. rename WM into WM0.
intros m2 s2' r errv2 y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AUX ST ERR MI HPR FA2 SO2 FR OS RES.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 408)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
destruct r as [q|].
-
first [ sf_destruct 8%nat RES as Bd' junk2 -> BRq HP2 BLK2 HKq SAME | sf_fb; destruct RES as (Bd' & junk2 & -> & BRq & HP2 & BLK2 & HKq & SAME) ].
pose proof BRq as sfP_; first [ sf_destruct 5%nat sfP_ as Q1 Q2 Q3 Q4 Q5 | sf_fb; destruct sfP_ as (Q1 & Q2 & Q3 & Q4 & Q5) ]. unfold alloc_ceiling in Q4.
rewrite Z.min_r in BLK2 by lia. rewrite <- LENb, firstn_all in BLK2.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP2) as ND. cbn [map blk_id fst] in ND.
unfold implM. iprefix.

zstep. if_cases CN3; zify_cond CN3; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN3 by lia; [exfalso; lia|].
zstep. lstep. lstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
apply evt_done. cbv beta iota. apply impl_ret_ok. apply evt_done. cbn [fst snd].
unfold body_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split; [exact FA2|]. split; [exact SO2|].
left. split; [reflexivity|]. first [ unshelve sf_eexists 4%nat; [ exact (q) | exact (Bd') | exact (junk2) | exact (((q, Bd', n') :: lb_remove pb LB)) | ] | sf_fb; exists q, Bd', junk2, ((q, Bd', n') :: lb_remove pb LB) ].
split; [reflexivity|].
split; [cbn; lia|]. split; [cbn; lia|].
split. { eapply RHEAP_frame_proof; [exact HP2| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split; [intros b Hb; right; exact Hb|].
split; [left; reflexivity|].
split; [apply (stream_blocks_newbody LB os Bd L Gv pb); [exact SB| exact Hpb| exact ND]|].
split; [exact HKq|].
split. { intros b Hb NE E. pose proof ND as NDc. apply List.NoDup_cons_iff in NDc. destruct NDc as [NI _]. apply NI. rewrite <- E.
apply in_map_blk_id. apply lb_remove_keep; [exact Hb| exact NE]. }
split; [exact BRq|].
split. { eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR| lia| intros b Hb; exact Hb| intros x Hx; exact Hx]|].
apply cmod_of_munch; [exact MU| exact WM]. }
split; [exact OS|]. split; [exact BLK2|]. cbn [os_body_storage set_blocks]. apply Permutation_refl.
-
first [ sf_destruct 4%nat RES as -> HP2 BLK2 HK2 | sf_fb; destruct RES as (-> & HP2 & BLK2 & HK2) ].
unfold implM. iprefix.
zstep. if_cases CN3; zify_cond CN3; [| exfalso; apply CN3; reflexivity].

zstep. zstep. apply evt_done. cbv beta iota. eapply implM_bind.
{ lazymatch goal with OSx : rw_cells rsegs ?mx A _ |- _ =>
eapply (ogg_stream_clear_spec HF) with (s := s2') (LB := LB) (os := os) (A := A) (Bd := Bd) (L := L) (Gv := Gv) (hdr := hdr);
[ eapply RHEAP_frame_proof; [exact HP2| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| exact SB
| exact HL
| eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| lia
| rewrite unsigned_lit by lia; exact ST
| exact CEIL
| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR
| exact MI
| exact TP
| reflexivity
| exact OSx ] end. }
clear AUX ST ERR MI. rename MU into MU1. rename WM into WM1.
intros osr ps4 ms4 PO.
first [ sf_destruct 26%nat PO as q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 m5 -> MI5 ST ERR AUX CMc FA4 SO4 HP5 -> OSZ | sf_fb; destruct PO as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m5 & -> & MI5 & ST & ERR & AUX & CMc & FA4 & SO4 & HP5 & -> & OSZ) ].
rewrite unsigned_lit in ST, CMc by lia.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
repeat match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -32) _ |- _ =>
apply (cmod_rw_cells _ _ _ _ _ _ _ CMc) in FRx; [| left; cbn; lia| cbn; lia] end.
apply implM_ret.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -32) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
zstep.
assert (SUB3 : forall b, In b (stream_clear_LB LB os) -> In b LB) by (intros bq Hbq; unfold stream_clear_LB in Hbq; do 3 apply lb_remove_opt_sub in Hbq; exact Hbq).
apply evt_done. unfold body_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split; [exact AUX|].
split; [congruence|]. split; [congruence|].
right. split; [reflexivity|]. split; [reflexivity|]. split; [exact HP5|].
split. { eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR| lia| | intros x Hx; exact Hx]|].
{ intros b Hb. unfold stream_clear_LB in Hb. rewrite Hpb in Hb. do 2 apply lb_remove_opt_sub in Hb. exact Hb. }
eapply cmod_trans; [eapply cmod_of_munch; [exact MU1| exact WM1]|].
eapply (cmod_weaken [(A, A + 408)] _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[ eapply (cmod_drop_low (bv_unsigned sp + -32 - 16) (bv_unsigned sp + -32)); [exact CMc| lia| lia|];
intros bq Hbq; left;
pose proof (RHEAP_block_range_proof _ _ _ _ HP2 (SUB3 bq Hbq)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ X4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & X4 & _) ]; unfold alloc_ceiling in X4; lia
| lia | intros b Hb; exact Hb | intros xq Hxq; cbn in Hxq |- *; tauto ]. }
exact OSZ.
Qed.
End EXP.
