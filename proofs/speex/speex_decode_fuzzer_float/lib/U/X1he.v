(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it X1j2 X1iv X1iw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg X1hc X1hd X1gt X1gp X1h8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma perm_ins3f : forall (P S L : list block) (a b d : block),
Permutation L (P ++ S) -> Permutation (a :: b :: d :: L) (P ++ a :: b :: d :: S).
Proof.
intros P S L a b d H.
apply Permutation_trans with (l' := a :: b :: d :: (P ++ S)); [repeat apply perm_skip; exact H|].
apply Permutation_cons_app. apply Permutation_cons_app. apply Permutation_cons_app. apply Permutation_refl.
Qed.

Lemma nodup_ids_mid_ne : forall (l1 : list block) (b : block) (l2 : list block) (b' : block),
List.NoDup (map blk_id (l1 ++ b :: l2)) -> In b' l1 \/ In b' l2 -> blk_id b' <> blk_id b.
Proof.
intros l1 b l2 b' ND H. destruct b as [[p A] n].
pose proof (X1gy.nodup_ids_app_mid l1 p A n l2 ND) as [N1 N2]. cbn. destruct H as [H|H]; [exact (N1 _ H)| exact (N2 _ H)].
Qed.

Lemma nodup_ids_app_ne : forall (l1 l2 : list block) b1 b2,
List.NoDup (map blk_id (l1 ++ l2)) -> In b1 l1 -> In b2 l2 -> blk_id b1 <> blk_id b2.
Proof.
intros l1 l2 b1 b2 ND H1 H2 E. rewrite map_app in ND.
eapply (nodup_app_disj _ _ (blk_id b1) ND); [apply in_map; exact H1| rewrite E; apply in_map; exact H2].
Qed.

Lemma owned_perm_stream : forall (c : hcx) x h L,
Permutation L (owned x h ++ x_LB0 c) ->
Permutation L (stream_blks x h ++ ((opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h)) ++ x_LB0 c)
++ ((match h_st h with Some _ => a_LBD x | None => [] end) ++ [(sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))]))).
Proof.
intros c x h L H. eapply Permutation_trans; [exact H|]. unfold owned, stream_blks.
rewrite <- !app_assoc.
match goal with |- Permutation (?D ++ [?b] ++ ?R) _ => rewrite (app_assoc D [b] R) end.
eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Lemma stream_rep_pagein {RCEIL : RunCeiling} : forall m c xa h3 (pb' pl' pg' : bptr),
hstream_ok (h_os h3) -> stream_fields_ok (h_os h3) ->
os_body_data (h_os h3) = Some pb' -> os_lacing_vals (h_os h3) = Some pl' -> os_granule_vals (h_os h3) = Some pg' ->
rw_cells rsegs m (aOS c) (stream_cells (a_Bd xa) (a_L xa) (a_Gv xa) (a_hdr xa) (h_os h3)) -> length (a_hdr xa) = 284%nat ->
stream_arrays m (h_os h3) (a_Bd xa) (a_L xa) (a_Gv xa) (a_body xa) (a_lws xa) (a_gws xa) ->
a_nB xa = os_body_storage (h_os h3) -> a_nL xa = os_lacing_storage (h_os h3) * 4 -> a_nG xa = os_lacing_storage (h_os h3) * 8 ->
rblock_range (a_Bd xa) (a_nB xa) -> rblock_range (a_L xa) (a_nL xa) -> rblock_range (a_Gv xa) (a_nG xa) ->
stream_rep m c xa h3.
Proof.
intros m c xa h3 pb' pl' pg' HS FOK EB EL EG OS LH ARR NB NL NG RB RL RG.
first [ sf_destruct 12%nat HS as SINV BINV LOK GOK S1 S2 E1 E2 E3 G1 G2 G3 | sf_fb; destruct HS as (SINV & BINV & LOK & GOK & S1 & S2 & E1 & E2 & E3 & G1 & G2 & G3) ].
first [ sf_destruct 8%nat ARR as UB BLEN [BP1 BP2] UL LPRE LLEN UG GLEN | sf_fb; destruct ARR as (UB & BLEN & [BP1 BP2] & UL & LPRE & LLEN & UG & GLEN) ].
pose proof RB as sfP_; first [ sf_destruct 5%nat sfP_ as RB1 RB2 RB3 RB4 RB5 | sf_fb; destruct sfP_ as (RB1 & RB2 & RB3 & RB4 & RB5) ]. pose proof RL as sfP_; first [ sf_destruct 5%nat sfP_ as RL1 RL2 RL3 RL4 RL5 | sf_fb; destruct sfP_ as (RL1 & RL2 & RL3 & RL4 & RL5) ]. pose proof RG as sfP_; first [ sf_destruct 5%nat sfP_ as RG1 RG2 RG3 RG4 RG5 | sf_fb; destruct sfP_ as (RG1 & RG2 & RG3 & RG4 & RG5) ].
unfold stream_rep.
split; [exact OS|]. split; [exact LH|]. split; [exact FOK|]. split; [exact SINV|]. split; [exact BINV|]. split; [exact LOK|]. split; [exact GOK|].
split; [exact UL|]. split; [exact UG|]. split; [exact UB|]. split; [exact LPRE|]. split; [exact LLEN|]. split; [exact GLEN|]. split; [exact BLEN|].
split; [exact BP1|]. split; [exact BP2|]. split; [exact NB|]. split; [lia|]. split; [lia|].
rewrite EB, EL, EG. split; [split; [discriminate| lia]|]. split; [split; [discriminate| lia]|]. split; [split; [discriminate| lia]|].
split; [intros _; exact RB|]. split; [intros _; exact RL|]. split; [intros _; exact RG|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [intros; discriminate|]. split; [intros; discriminate|]. split; [intros; discriminate|].
split; [intros _; apply G1; rewrite EB; discriminate|]. split; [intros _; apply G2; rewrite EL; discriminate|].
left. repeat split; discriminate.
Qed.

Section PAGE4.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RTK : rheap_top_known_stmt.
Hypothesis OPAGEIN : ogg_stream_pagein_stmt2.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PGP := (PGP dec_rep c).
Notation PGG := (PGG dec_rep c).

#[using="DRF RHF RBR RND RTK OPAGEIN CX"] Lemma page_pagein : forall (Q : outcome bptr -> PState -> machine_state -> Prop) fuel' (h0 h : hstate bptr) og st ms,
PGP h og st ms -> h_oy h = h_oy h0 ->
(forall h3 st3 ms3, PGG h3 og st3 ms3 -> h_oy h3 = h_oy h -> h_bytes_remaining h3 = h_bytes_remaining h ->
implM rsegs (page_restP fuel' (page_header (h_oy h0) og) h3) st3 Q ms3) ->
implM rsegs (X1qx.mbind (ogg_stream_pagein raw_realloc raw_free (h_os h) (page_header (h_oy h0) og) (page_body (h_oy h0) og))
(fun x => let '(r, os) := x in page_restP fuel' (page_header (h_oy h0) og) (set_ogg h (h_oy h) os))) st Q ms.
Proof.
intros Q fuel' h0 h og st ms PG EOY K. rewrite <- !EOY in K. rewrite <- !EOY. clear h0 EOY.
first [ sf_destruct 34%nat PG as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 s3w s5w s8w OP -> FRM SI1 HRX LOK POK NN PB | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & s3w & s5w & s8w & OP & -> & FRM & SI1 & HRX & LOK & POK & NN & PB) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HRX as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKO) _ _ (stb & STB) OSP (OPK & OPS) (OG & OGS) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKO) & _ & _ & (stb & STB) & OSP & (OPK & OPS) & (OG & OGS) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold hbudget, hconsumed, hpend in BUD.
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
pose proof (RND _ _ _ HP) as ND.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (pay_range RBR c _ _ _ CX HP HL0) as PRANGE.
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT. rewrite ED in DAT. first [ sf_destruct 4%nat DAT as -> _ _ -> | sf_fb; destruct DAT as (-> & _ & _ & ->) ]. auto. }
pose proof (page_hs _ _ _ _ _ _ SY SYI POK NN) as sfP_; first [ sf_destruct 11%nat sfP_ as HS HBS LHS LBS EHS EBS HL27 NSEG PG0 PGE BL0 | sf_fb; destruct sfP_ as (HS & HBS & LHS & LBS & EHS & EBS & HL27 & NSEG & PG0 & PGE & BL0) ].
destruct (sy_data (h_oy h)) as [psy|] eqn:ESY; [| exfalso; exact (NN eq_refl)].
destruct (SYBLK ltac:(congruence)) as [(SB1 & SB2 & SB3 & SB4 & SB5) SB6].
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes x))) in *.
set (bs := firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) (a_sybytes x))) in *.
pose proof (page_ok_pagein_pre _ _ SYI POK) as PRE. cbv zeta in PRE. first [ sf_destruct 7%nat PRE as LACB _ ZSLE ZLB ZLH HDRB BODB | sf_fb; destruct PRE as (LACB & _ & ZSLE & ZLB & ZLH & HDRB & BODB) ].
pose proof (page_ok_body_len _ _ SYI POK) as (ZSEQ & _ & _).
pose proof OSP as OSP0. unfold os_piece in OSP. rewrite SI1 in OSP. cbn [Z.eqb] in OSP.
pose proof OSP as sfP_; first [ sf_destruct 34%nat sfP_ as OS LH FOK SINV BINV LOK' GOK UL UG UB W1 L1 L2 L3 PB1 PB2 N1 N2 N3 Z1 Z2 Z3 R1 R2 R3 C1 C2 C3 E1 E2 E3 G1 G2 G3 | sf_fb; destruct sfP_ as (OS & LH & FOK & SINV & BINV & LOK' & GOK & UL & UG & UB & W1 & L1 & L2 & L3 & PB1 & PB2 & N1 & N2 & N3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & C1 & C2 & C3 & E1 & E2 & E3 & G1 & G2 & G3) ].
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as Fa Fb Fc Fd Fe Ff Fg Fh Fi Fj Fk Fl | sf_fb; destruct sfP_ as (Fa & Fb & Fc & Fd & Fe & Ff & Fg & Fh & Fi & Fj & Fk & Fl) ]. unfold int31 in Fd, Fe, Ff, Fg, Fh, Fi, Fj.
pose proof (u8arr_bound _ _ _ _ UB) as BDB.
unfold low_cells, wz in LOW.
pose proof (munch_refl [(aLOW c - 144, aLOW c)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR. change (id (bytes_at rsegs m (x_P c) (to_bytes (x_payload c)))) in PAY.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
rewrite <- EHS, <- EBS.
destruct (os_body_data (h_os h)) as [pb|] eqn:EBD.
2:{
destruct G3 as [[G _]|EOS]; [exfalso; exact (G eq_refl)|].
pose proof (proj1 Z1 eq_refl) as EB0. rewrite EB0 in OS.
clear MU WM. unfold id in ERR, PAY.
eapply implM_bind.
{ eapply (ogg_stream_pagein_null_implM) with (lo := x_lo c) (A := aOS c) (L := a_L x) (Gv := a_Gv x) (G := aOG c) (Dsy := a_D x) (og := og) (shdr := a_hdr x);
rewrite ?(unsigned_lit (aLOW c)) by plia;
first [ exact EBD | exact LH | exact FOK | exact OS | exact OG | exact HS | exact MI | exact ST | plia ]. }
cbv beta. intros [r os'] st1 ms1 (ER & -> & PO). inversion ER; subst r os'. clear ER.
first [ sf_destruct 23%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 -> MU WM MI1 ST1 OS1 OG1 HS1 | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & -> & MU & WM & MI1 & ST1 & OS1 & OG1 & HS1) ].
rewrite ?(unsigned_lit (aLOW c)) in MU by plia. rewrite ?(unsigned_lit (aLOW c)) in ST1 by plia.
replace (ret_pc (Z_to_bv 64 0x1c290)) with (Z_to_bv 64 0x1c290) by (symmetry; rpc).
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
clear OS OG HS ST MI. clear PAY.   xportx AG side1c.
assert (HG1 : hglob c x h st m1).
{ eapply hglob_frame_lo; [exact RHF| exact RBR| exact CX| exact HG| exact MU| exact WM| | exact MI1| exact ST1].
apply Forall_cons; [cbn; plia| apply Forall_nil]. }
set (h3 := set_ogg h (h_oy h) (h_os h)). rewrite EHS.
apply (K h3); [| reflexivity| reflexivity].
unfold X1hg.PGG. do 16 eexists. exists F, fc, m1, x, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM|]. split; [exact SI1|].
split.
{ split; [exists j16, jsk, lk; split; [exact LOW| exact LKO]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [exact OSP0|].
split; [split; [exact OPK| exact OPS]|]. split; [split; [exact OG1| exact OGS]|].
split; [exact SY|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|]. split; [exact HG1|].
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h3 set_ogg].
repeat (split; [assumption|]). split; [intros _; split; [unfold rblock_range; repeat split; assumption| exact SB6]|].
repeat (split; [assumption|]).
destruct PB as (cold & PB'). unfold hbudget, hconsumed, hpend in PB' |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining h3 set_ogg] in PB' |- *.
repeat split; plia. }
split; [exact LOK|]. split; [exact POK|]. split; [rewrite ESY; discriminate|]. cbn [h_os h3 set_ogg]. rewrite EOS. reflexivity. }

destruct G3 as [(_ & GL & GG)|EOS]. 2:{ exfalso. rewrite EOS in EBD. cbv in EBD. discriminate. }
destruct (os_lacing_vals (h_os h)) as [pl|] eqn:ELV; [| exfalso; exact (GL eq_refl)].
destruct (os_granule_vals (h_os h)) as [pg|] eqn:EGV; [| exfalso; exact (GG eq_refl)].
pose proof (owned_perm_stream c x h _ PERM) as PERMS. pose proof PERMS as PERMS0.
pose proof (stream_blocks_of c m x h _ _ OSP ND PERMS) as SBL.
pose proof (perm_stream_clear (a_LB x) x h _ ND PERMS0) as KPERM.
unfold stream_clear_LB in KPERM. rewrite EBD, ELV, EGV in KPERM. cbn [lb_remove_opt] in KPERM. rewrite ESY in KPERM.
unfold stream_blks in PERMS. rewrite EBD, ELV, EGV, ESY in PERMS. cbn [opt_blk app] in PERMS.
pose proof (nodup_ids_perm _ _ PERMS ND) as NDS.
assert (INb : In (pb, a_Bd x, os_body_storage (h_os h)) (a_LB x)).
{ rewrite <- N1. eapply Permutation_in; [apply Permutation_sym; exact PERMS|]. left. reflexivity. }
assert (INl : In (pl, a_L x, os_lacing_storage (h_os h) * 4) (a_LB x)).
{ replace (os_lacing_storage (h_os h) * 4) with (a_nL x) by plia. eapply Permutation_in; [apply Permutation_sym; exact PERMS|]. right; left. reflexivity. }
assert (INg : In (pg, a_Gv x, os_lacing_storage (h_os h) * 8) (a_LB x)).
{ replace (os_lacing_storage (h_os h) * 8) with (a_nG x) by plia. eapply Permutation_in; [apply Permutation_sym; exact PERMS|]. right; right; left. reflexivity. }
assert (INs : In (psy, a_D x, sy_storage (h_oy h)) (a_LB x)).
{ eapply Permutation_in; [apply Permutation_sym; exact PERMS|]. right; right; right; left. reflexivity. }
assert (NEs : psy <> pb /\ psy <> pl /\ psy <> pg).
{ cbn in NDS. inversion NDS as [|i1 k1 NI1 ND1]; subst. inversion ND1 as [|i2 k2 NI2 ND2]; subst. inversion ND2 as [|i3 k3 NI3 ND3]; subst.
repeat split; intros E; subst psy; [apply NI1; right; right; left; reflexivity| apply NI2; right; left; reflexivity| apply NI3; left; reflexivity]. }
destruct NEs as (NEb & NEl & NEg).
specialize (G1 ltac:(discriminate)). specialize (G2 ltac:(discriminate)).

assert (LENH : length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat) by (apply Nat2Z.inj; rewrite Nat2Z.inj_add, Z2Nat.id by plia; plia).
assert (HSUM : zsum (lacing_of (ubytes hs)) <= pg_body_len og) by (rewrite EHS; plia).
destruct PB as (cold & PB'). unfold hconsumed, hpend in PB'.
assert (HBL : (os_lacing_storage (h_os h) + znth (ubytes hs) 26 + 33) * 8 < MMAP_THRESHOLD) by (unfold MMAP_THRESHOLD, MAX_FUZZ_SIZE in *; plia).
assert (HBB : os_body_storage (h_os h) + pg_body_len og + 1024 < MMAP_THRESHOLD) by (unfold MMAP_THRESHOLD, MAX_FUZZ_SIZE in *; plia).
assert (ARRS : stream_arrays m (h_os h) (a_Bd x) (a_L x) (a_Gv x) (a_body x) (a_lws x) (a_gws x)).
{ split; [exact UB|]. split; [exact L3|]. split; [split; [exact PB1| exact PB2]|]. split; [exact UL|]. split; [exact W1|].
split; [exact L1|]. split; [exact UG| exact L2]. }
assert (HSOK : hstream_ok (h_os h)).
{ split; [exact SINV|]. split; [exact BINV|]. split; [exact LOK'|]. split; [exact GOK|]. split; [plia|]. split; [plia|].
rewrite EBD, ELV, EGV. split; [intros; discriminate|]. split; [intros; discriminate|]. split; [intros; discriminate|].
split; [intros _; exact G1|]. split; [intros _; exact G2|]. left. repeat split; discriminate. }
pose proof HDRB as HDRB'. rewrite <- EHS in HDRB'. pose proof BODB as BODB'. rewrite <- EBS in BODB'.
assert (H27 : 27 <= zlength (ubytes hs)) by (unfold zlength; rewrite length_ubytes; plia).
assert (ZLH' : zlength (ubytes hs) = 27 + znth (ubytes hs) 26) by (unfold zlength; rewrite length_ubytes; plia).
assert (ZSEQ' : zsum (lacing_of (ubytes hs)) = zlength (ubytes bs)) by (rewrite EHS, EBS; exact ZSEQ).
clear MU WM. unfold id in ERR, PAY.
eapply implM_bind.
{ eapply implM_leaves.
eapply OPAGEIN with (LB := a_LB x) (pb := pb) (pl := pl) (pg := pg) (psy := psy) (A := aOS c) (G := aOG c) (Dsy := a_D x)
(nsy := sy_storage (h_oy h)) (Bd := a_Bd x) (L := a_L x) (Gv := a_Gv x) (lo := x_lo c) (B := x_AB c) (og := og)
(shdr := a_hdr x) (bodybytes := a_body x) (lws := a_lws x) (gws := a_gws x) (errv := errv);
rewrite ?(unsigned_lit (aLOW c)) by plia;
first [ exact HP | exact SBL | exact EBD | exact ELV | exact EGV | exact INb | exact INl | exact INg | exact INs
| exact NEb | exact NEl | exact NEg | exact OS | exact LH | exact ARRS | exact FOK | exact SINV | exact BINV | exact LOK'
| exact OG | exact HS | exact HBS | exact LENH | exact LHS | exact LBS | exact HSUM | exact HBL | exact HBB
| exact AUX | exact ST | exact MI | reflexivity | plia
| eapply RTK; [exact HP| eassumption| unfold RBIG; plia]
| unfold RATP; rewrite unsigned_lit by plia; exact ERR
| unfold OGG_REALLOC_STACK; plia ]. }
cbv beta. intros [r os'] st1 ms1 [PO LEAF].
pose proof (pagein_leaf_proof _ _ _ _ _ _ _ _ _ _ _ HSOK HDRB' H27 (proj1 NSEG) ZLH' ZSEQ' BODB' LEAF) as sfP_; first [ sf_destruct 7%nat sfP_ as _ HSOK' _ LF' BF' LS' BS' | sf_fb; destruct sfP_ as (_ & HSOK' & _ & LF' & BF' & LS' & BS') ].
pose proof (pagein_leaf_returned _ _ _ _ _ _ _ _ _ _ _ HSOK HDRB' H27 (proj1 NSEG) ZLH' ZSEQ' BODB' LEAF) as RET0.
clear LEAF.
first [ sf_destruct 32%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 errv1 LB1 -> MI1 ST1 ERR1 AUX1 EFA ESO HP1 HLB CM OG1 HS1 HBS1 RR CASES | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & errv1 & LB1 & -> & MI1 & ST1 & ERR1 & AUX1 & EFA & ESO & HP1 & HLB & CM & OG1 & HS1 & HBS1 & RR & CASES) ].
cbn [fst snd] in RR, CASES.
rewrite ?(unsigned_lit (aLOW c)) in ST1 by plia. rewrite ?(unsigned_lit (aLOW c)) in CM by plia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by plia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c290)) with (Z_to_bv 64 0x1c290) by (symmetry; rpc).
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.
pose proof (RND _ _ _ HP1) as ND1.
set (kept := lb_remove pg (lb_remove pl (lb_remove pb (a_LB x)))) in *.

assert (OWNK : forall bb, In bb ((psy, a_D x, sy_storage (h_oy h)) :: x_LB0 c ++ (match h_st h with Some _ => a_LBD x | None => [] end)
++ [(sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))]) ->
In bb kept /\ forall a, blk_addr bb <= a < blk_addr bb + blk_size bb ->
rclient_addr kept (hsp c) a /\ outside [(aOS c, aOS c + 408)] a).
{ intros bb Hbb.
assert (I2 : In bb (a_LB x)). { eapply Permutation_in; [apply Permutation_sym; exact PERMS|]. cbn [app]. right; right; right. exact Hbb. }
lazymatch type of NDS with List.NoDup (map blk_id (?k1 :: ?k2 :: ?k3 :: ?rest)) =>
pose proof (NDS : List.NoDup (map blk_id ([k1; k2; k3] ++ rest))) as NDS3 end.
assert (NE : forall bk, In bk [(pb, a_Bd x, a_nB x); (pl, a_L x, a_nL x); (pg, a_Gv x, a_nG x)] -> blk_id bk <> blk_id bb)
by (intros bk Hk; exact (nodup_ids_app_ne _ _ bk bb NDS3 Hk Hbb)).
assert (IK : In bb kept).
{ subst kept. apply lb_remove_keep; [apply lb_remove_keep; [apply lb_remove_keep; [exact I2|]|]|].
- intros E. apply (NE (pb, a_Bd x, a_nB x)); [left; reflexivity| cbn; symmetry; exact E].
- intros E. apply (NE (pl, a_L x, a_nL x)); [right; left; reflexivity| cbn; symmetry; exact E].
- intros E. apply (NE (pg, a_Gv x, a_nG x)); [right; right; left; reflexivity| cbn; symmetry; exact E]. }
split; [exact IK|]. intros a Ha. pose proof (RBR _ _ _ _ HP I2) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4.
split; [right; right; exists bb; split; [exact IK| exact Ha]| cbn [outside fst snd]; plia]. }
clear OS UL UG UB ST MI AUX ERR.
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). apply (OWNK bb); [| exact Ra]. right. rewrite !in_app_iff.
unfold dec_piece in DEC. destruct (h_st h); [right; left; exact Hbb| destruct DEC as [_ E']; rewrite E' in Hbb; destruct Hbb]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1c|].
2:{ intros a Ha. apply (OWNK (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))); [| cbn; exact Ha]. right. rewrite !in_app_iff. right; right. left. reflexivity. }
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1c]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. rewrite ESY in DAT |- *.
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. apply (OWNK (psy, a_D x, sy_storage (h_oy h))); [left; reflexivity| cbn; plia]. }
clear SYC DAT SY.
eapply (pay_keep c _ _ _ CX AG) in PAY.
2:{ intros NE' IN a' Ha'. apply (OWNK (x_pb c, x_P c, zlength (x_payload c))); [right; apply in_app_iff; left; exact IN| cbn; exact Ha']. }
clear HBS HS.   xport AG side1c.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- split; [left; plia| cbn [outside fst snd]; plia].
- split; [right; left; exact Hc| cbn [outside fst snd]; unfold ralloc_static, RLIBC, RCTX in Hc; plia].
- apply (OWNK bb); [right; apply in_app_iff; left; exact Hbb| exact Rbb]. }
assert (HLK : forall b, In b (x_LB0 c) -> In b kept).
{ intros b Hb. apply (proj1 (OWNK b ltac:(right; apply in_app_iff; left; exact Hb))). }
rewrite EHS. set (h3 := set_ogg h (h_oy h) os').

assert (FINISH : forall xa, a_S xa = a_S x -> a_D xa = a_D x -> a_LB xa = LB1 -> a_Dc xa = a_Dc x -> a_sybytes xa = a_sybytes x -> a_LBD xa = a_LBD x ->
stream_rep m1 c xa h3 -> Permutation LB1 (owned xa h3 ++ x_LB0 c) ->
os_lacing_fill (h_os h3) <= os_lacing_fill (h_os h) + znth (ubytes hs) 26 + 1 ->
os_body_fill (h_os h3) <= os_body_fill (h_os h) + zlength (ubytes bs) ->
os_lacing_storage (h_os h3) <= Z.max (os_lacing_storage (h_os h)) (os_lacing_fill (h_os h) + 2 * (znth (ubytes hs) 26 + 1) + 32) ->
os_body_storage (h_os h3) <= Z.max (os_body_storage (h_os h)) (os_body_fill (h_os h) + 2 * zlength (ubytes bs) + 1024) ->
PGG h3 og st1 (MS (mkR (Z_to_bv 64 0x1c290) (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y0 y1 y2 (Z_to_bv 64 (h_last_granule h))
(Z_to_bv 64 brem0) (wz r) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (a_S x)) s3w (Z_to_bv 64 (h_extra_headers h)) s5w (Z_to_bv 64 (h_eos h))
(Z_to_bv 64 (h_packet_count h)) s8w (Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 (h_channels h)) y3 y4 y5 y6)
F (Z_to_bv 64 0x1c290) fc None m1 (seg_rom rsegs))).
{ intros xa XS XD XLB XDc XSB XLBD SR PERM1 B1 B2 B3 B4.
unfold X1hg.PGG. do 16 eexists. exists F, fc, m1, xa, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; rewrite XS; reflexivity|]. split; [exact FRM|]. split; [exact SI1|].
split.
{ split; [exists j16, jsk, lk; split; [exact LOW| exact LKO]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [unfold os_piece; cbn [h_stream_init h3 set_ogg]; rewrite SI1; cbn [Z.eqb]; exact SR|].
split; [split; [exact OPK| exact OPS]|]. split; [rewrite XD; split; [exact OG1| exact OGS]|].
split; [rewrite XD, XSB; exact SY1|]. split; [rewrite XDc; exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|].
split; [unfold dec_piece in DEC |- *; cbn [h_st h3 set_ogg]; rewrite XS, XLBD; exact DEC|].
split.
{ split; [rewrite XLB; exact HP1|]. split; [rewrite XLB; exact PERM1|].
split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|]. split; [exists errv1; exact ERR1|]. split; [exact AUX1|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact PE1| cbn; congruence]. }
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os h3 set_ogg] in B1, B2, B3, B4 |- *.
rewrite XD, XSB, XDc. split; [exact SYOK|]. split; [exact BOK|]. split; [exact OWN|].
split; [intros _; split; [unfold rblock_range; repeat split; assumption| exact SB6]|]. split; [exact SYLEN|].
repeat (split; [assumption|]).
pose proof SINV as (LR1 & LR2 & _). pose proof SR as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ (LR3 & LR4 & _) _ | sf_fb; destruct sfP_ as (_ & _ & _ & (LR3 & LR4 & _) & _) ]. cbn [h_os h3 set_ogg] in LR3, LR4.
unfold MAX_FUZZ_SIZE in L4K.
unfold hbudget, hconsumed, hpend. cbn [h_packet_count h_oy h_os h_bytes_remaining h3 set_ogg]. unfold zlength in B2, B4. rewrite length_ubytes in B2, B4. plia. }
split; [exact LOK|]. split; [exact POK|]. split; [cbn [h_oy h3 set_ogg]; rewrite ESY; discriminate|]. cbn [h_os h3 set_ogg]. exact RET0. }
destruct CASES as [(Bd' & L' & Gv' & pb' & pl' & pg' & body' & lws' & gws' & EB' & EL' & EG' & INb' & INl' & INg' & RKb & RKl & RKg & SBL' & FOK' & OS' & ARR' & PLB)
| (EOS' & OS' & PLB)].
-
set (xa := hax_stream x LB1 Bd' L' Gv' (os_body_storage os') (os_lacing_storage os' * 4) (os_lacing_storage os' * 8) (a_hdr x) lws' gws' body').
pose proof (RBR _ _ _ _ HP1 INb') as RB'. pose proof (RBR _ _ _ _ HP1 INl') as RL'. pose proof (RBR _ _ _ _ HP1 INg') as RG'. cbn [blk_addr blk_size fst snd] in RB', RL', RG'.
apply (K h3); [| reflexivity| reflexivity].
apply (FINISH xa); try reflexivity.
+ eapply (stream_rep_pagein m1 c xa h3 pb' pl' pg'); try assumption; try reflexivity; exact LH.
+ unfold owned. cbn [h_st h_bits h_os h_oy h3 set_ogg a_LBD a_Dc a_Bd a_L a_Gv a_nB a_nL a_nG a_D a_LB xa hax_stream].
rewrite EB', EL', EG', ESY. cbn [opt_blk].
rewrite <- !app_assoc. lazymatch goal with |- Permutation _ (?D ++ [?b] ++ ?Y) => rewrite (app_assoc D [b] Y) end.
eapply Permutation_trans; [exact PLB|]. apply perm_ins3f.
eapply Permutation_trans; [exact KPERM|]. apply Permutation_app_comm.
+ exact (proj2 LF'). + exact (proj2 BF'). + exact LS'. + exact BS'.
-
subst os'.
set (xa := hax_stream x LB1 0 0 0 0 0 0 zero_hdr [] [] []).
apply (K h3); [| reflexivity| reflexivity].
apply (FINISH xa); try reflexivity.
+ eapply (stream_rep_zero m1 c xa h3); try reflexivity; exact OS'.
+ unfold owned. cbn [h_st h_bits h_os h_oy h3 set_ogg a_LBD a_Dc a_Bd a_L a_Gv a_nB a_nL a_nG a_D a_LB xa hax_stream stream_zero os_body_data os_lacing_vals os_granule_vals].
rewrite ESY. change (opt_blk None 0 0) with (@nil block). cbn [opt_blk app].
eapply Permutation_trans; [exact PLB|]. eapply Permutation_trans; [exact KPERM|].
eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. cbn [opt_blk app]. apply Permutation_refl.
+ exact (proj2 LF'). + exact (proj2 BF'). + exact LS'. + exact BS'.
Qed.
End PAGE4.
