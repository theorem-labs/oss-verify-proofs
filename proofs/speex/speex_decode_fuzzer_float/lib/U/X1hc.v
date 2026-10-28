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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il X1im X1is X1ip X1iq X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition hax_stream (x : hax) (LB : list block) (Bd L Gv nB nL nG : Z) (hdr : list byte) (lws gws : list word) (body : list byte) : hax :=
HAX LB (a_D x) (a_sybytes x) Bd L Gv nB nL nG hdr lws gws body (a_Dc x) (a_S x) (a_LBD x).

Lemma u8arr_nil' : forall m A, 0 <= A <= 2^64 -> u8arr rsegs m A [].
Proof. intros m A HA. split; (split; [lia|]; split; [cbn; lia|]); cbn; intros; lia. Qed.
Lemma u32arr_nil : forall m A, 0 <= A <= 2^64 -> u32arr rsegs m A [].
Proof. intros m A HA. split; (split; [lia|]; split; [cbn; lia|]); cbn; intros; lia. Qed.
Lemma u64arr_nil : forall m A, 0 <= A <= 2^64 -> u64arr rsegs m A [].
Proof. intros m A HA. split; (split; [lia|]; split; [cbn; lia|]); cbn; intros; lia. Qed.

Lemma s32_range : forall v, -2^31 <= s32 v < 2^31.
Proof. intros v. unfold s32. pose proof (Z.mod_pos_bound (v + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma stream_rep_zero {RCEIL : RunCeiling} : forall m c x h,
h_os h = stream_zero -> a_Bd x = 0 -> a_L x = 0 -> a_Gv x = 0 -> a_nB x = 0 -> a_nL x = 0 -> a_nG x = 0 ->
a_hdr x = zero_hdr -> a_lws x = [] -> a_gws x = [] -> a_body x = [] ->
rw_cells rsegs m (aOS c) (stream_cells 0 0 0 zero_hdr stream_zero) -> stream_rep m c x h.
Proof.
intros m c x h Eos E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 OS. unfold stream_rep. rewrite Eos, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
split; [exact OS|]. split; [unfold zero_hdr; apply repeat_length|].
split; [unfold stream_fields_ok, int31; cbn; repeat split; lia|]. split; [apply stream_zero_inv|]. split; [apply stream_zero_body_inv|].
split; [apply Forall_nil|]. split; [apply Forall_nil|].
split; [apply u32arr_nil; lia|]. split; [apply u64arr_nil; lia|]. split; [apply u8arr_nil'; lia|].
unfold wpre, alloc_ceiling. cbn.
repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
all: try (split; intros; first [reflexivity| lia| exfalso; congruence]).
all: try (intros; first [reflexivity| lia| exfalso; congruence]).
right. reflexivity.
Qed.

Lemma stream_rep_init {RCEIL : RunCeiling} : forall m c x h (pb pl pg : bptr) ser,
h_os h = init_os (Some pb) (Some pl) (Some pg) ser -> -2^31 <= ser < 2^31 ->
a_nB x = 16384 -> a_nL x = 4096 -> a_nG x = 8192 -> a_hdr x = zero_hdr ->
rblock_range (a_Bd x) 16384 -> rblock_range (a_L x) 4096 -> rblock_range (a_Gv x) 8192 ->
rw_cells rsegs m (aOS c) (stream_cells (a_Bd x) (a_L x) (a_Gv x) zero_hdr (h_os h)) ->
u8arr rsegs m (a_Bd x) (a_body x) -> length (a_body x) = 16384%nat ->
u32arr rsegs m (a_L x) (a_lws x) -> length (a_lws x) = 1024%nat ->
u64arr rsegs m (a_Gv x) (a_gws x) -> length (a_gws x) = 1024%nat ->
stream_rep m c x h.
Proof.
intros m c x h pb pl pg ser Eos SER E4 E5 E6 E7 RB RL RG OS AB LB AL LL AG LG.
unfold stream_rep. rewrite Eos in OS |- *. rewrite E4, E5, E6, E7 in *.
unfold rblock_range in RB, RL, RG.
split; [exact OS|]. split; [unfold zero_hdr; apply repeat_length|].
split; [unfold stream_fields_ok, int31, init_os; cbn; repeat split; lia|].
split; [unfold stream_inv, init_os, zlength; cbn; repeat split; lia|].
split; [unfold body_inv, init_os, zlength; cbn; repeat split; try lia; apply Forall_nil|].
split; [apply Forall_nil|]. split; [apply Forall_nil|].
split; [exact AL|]. split; [exact AG|]. split; [exact AB|].
unfold wpre, rblock_range, init_os. cbn -[Z.add Z.mul Z.le Z.lt alloc_ceiling Z.of_nat]. rewrite LB, LL, LG.
change (Z.of_nat 16384%nat) with 16384. change (Z.of_nat 1024%nat) with 1024.
repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
all: try (split; intros; first [discriminate| lia]).
all: try (intros; first [discriminate| lia]).
left. repeat split; discriminate.
Qed.

Lemma perm_ins3 : forall (P S L : list block) (a b d : block),
Permutation L (P ++ S) -> Permutation (d :: b :: a :: L) (P ++ a :: b :: d :: S).
Proof.
intros P S L a b d H.
apply Permutation_trans with (l' := d :: b :: a :: (P ++ S)); [repeat apply perm_skip; exact H|].
apply Permutation_trans with (l' := P ++ d :: b :: a :: S).
{ apply Permutation_cons_app. apply Permutation_cons_app. apply Permutation_cons_app. apply Permutation_refl. }
apply Permutation_app_head.
apply Permutation_trans with (l' := b :: d :: a :: S); [apply perm_swap|].
apply Permutation_trans with (l' := b :: a :: d :: S); [apply perm_skip; apply perm_swap|].
apply perm_swap.
Qed.

Section PAGE2.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RMALLOC : rmalloc_stmt.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis OSINIT : ogg_stream_init_stmt2.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PGB := (PGB dec_rep c).
Notation PGS := (PGS dec_rep c).

#[using="DRF RBR RND OSINIT CX"] Lemma page_sinit : forall (Q : outcome bptr -> PState -> machine_state -> Prop) fuel' h og st ms,
PGB h og st ms ->
(forall h1 st1 ms1, PGS h1 og st1 ms1 -> h_oy h1 = h_oy h -> h_bytes_remaining h1 = h_bytes_remaining h ->
implM rsegs (page_rest2P fuel' (h_oy h) og h1) st1 Q ms1) ->
implM rsegs (page_bodyP fuel' h og) st Q ms.
Proof.
intros Q fuel' h og st ms PG K.
first [ sf_destruct 32%nat PG as x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 s0w s3w s8w OP -> FRM HRX LOK POK NN PB | sf_fb; destruct PG as (x1 & t0 & t1 & t2 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & s0w & s3w & s8w & OP & -> & FRM & HRX & LOK & POK & NN & PB) ].
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
pose proof (page_hs _ _ _ _ _ _ SY SYI POK NN) as sfP_; first [ sf_destruct 11%nat sfP_ as HS HBS LHS LBS EHS EBS HL27 NSEG PG0 PGE BL0 | sf_fb; destruct sfP_ as (HS & HBS & LHS & LBS & EHS & EBS & HL27 & NSEG & PG0 & PGE & BL0) ].
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes x))) in *.
set (bs := firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) (a_sybytes x))) in *.
pose proof (s32_range (le32_at (page_header (h_oy h) og) 14)) as SERR.
change (s32 (le32_at (page_header (h_oy h) og) 14)) with (ogg_page_serialno (page_header (h_oy h) og)) in SERR.
set (serial := ogg_page_serialno (page_header (h_oy h) og)) in *.
unfold page_bodyP. cbv zeta. fold serial.
unfold low_cells, wz in LOW.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. zstep. if_cases K1; zify_cond K1.
-
assert (E1 : h_stream_init h = 1) by (destruct SIR as [E|E]; rewrite E in K1; cbv in K1; [discriminate| exact E]).
rewrite E1. cbn [Z.eqb].
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply implM_retb. apply K; [| reflexivity| reflexivity].
unfold X1hg.PGS. do 16 eexists. exists F, fc, m, x, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM|]. split; [exact E1|]. split; [exact HRX|].
split; [exact LOK|]. split; [exact POK|]. split; [exact NN| exact PB].
-
assert (E0 : h_stream_init h = 0) by (destruct SIR as [E|E]; [exact E| rewrite E in K1; cbv in K1; exfalso; apply K1; reflexivity]).
rewrite E0. cbn [Z.eqb].
unfold os_piece in OSP. rewrite E0 in OSP. cbn [Z.eqb] in OSP. first [ sf_destruct 5%nat OSP as [osj OSJ] EOS XB XL XG | sf_fb; destruct OSP as ([osj OSJ] & EOS & XB & XL & XG) ].

zstep. zstep.
callx (eapply ogg_page_serialno_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
rewrite EHS in POST. fold serial in POST. subst x4. unfold wz.

zstep. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply implM_bind_assoc. change (id (rw_cells rsegs m RERRNO [C4 errv])) in ERR.
eapply implM_bind.
{ eapply OSINIT with (A := aOS c) (lo := x_lo c) (B := x_AB c) (LB := a_LB x) (serialno := serial) (junk := osj);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP | exact AUX | exact ST | exact MI | exact OSJ | reflexivity | lia
| unfold id in ERR; unfold RATP; rewrite unsigned_lit by lia; exact ERR
| unfold RMALLOC_STACK; lia ]. }
cbv beta. intros [rc os'] st1 ms1 PO.
first [ sf_destruct 28%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 errv1 LB1 -> MI1 ST1 ERR1 AUX1 CM EFA ESO HP1 HLB CASES | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & errv1 & LB1 & -> & MI1 & ST1 & ERR1 & AUX1 & CM & EFA & ESO & HP1 & HLB & CASES) ].
cbn [fst snd] in CASES.
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in CM by lia.
unfold RATP in ERR1. rewrite ?unsigned_lit in ERR1 by lia. change (0x4d450 + -164) with RERRNO in ERR1.
replace (ret_pc (Z_to_bv 64 0x1c260)) with (Z_to_bv 64 0x1c260) by (symmetry; rpc).
pose proof (agree_of_cmod _ _ _ _ _ CM) as AG.
pose proof (RND _ _ _ HP1) as ND1.

assert (OWNL : forall bb, In bb (owned x h ++ x_LB0 c) -> forall a, blk_addr bb <= a < blk_addr bb + blk_size bb ->
rclient_addr (a_LB x) (hsp c) a /\ outside [(aLOW c - 48, aLOW c); (aOS c, aOS c + 408)] a).
{ intros bb Hbb a Ha. assert (I2 : In bb (a_LB x)) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hbb]).
pose proof (RBR _ _ _ _ HP I2) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4.
split; [right; right; exists bb; split; [exact I2| exact Ha]| cbn [outside fst snd]; lia]. }
clear OSJ ST MI AUX ERR.
eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG) in DEC.
2:{ intros a (bb & Hbb & Ra). apply (OWNL bb); [| exact Ra]. unfold owned. rewrite !in_app_iff.
unfold dec_piece in DEC. destruct (h_st h); [left; left; exact Hbb| destruct DEC as [_ E']; rewrite E' in Hbb; destruct Hbb]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1|].
2:{ intros a Ha. apply (OWNL (sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))); [| cbn; exact Ha].
unfold owned. rewrite !in_app_iff. cbn. clear. tauto. }
pose proof SY as sfP_; first [ sf_destruct 4%nat sfP_ as SYC SYF DAT SYSEP | sf_fb; destruct sfP_ as (SYC & SYF & DAT & SYSEP) ].
assert (SY1 : sync_rep m1 (aOY c) (a_D x) (h_oy h) (a_sybytes x)).
{ split; [eapply rw_cells_agree; [exact AG| exact SYC| side1]|]. split; [exact SYF|]. split; [| exact SYSEP].
unfold sync_data in DAT |- *. destruct (sy_data (h_oy h)) as [p|] eqn:ED; [| exact DAT].
first [ sf_destruct 5%nat DAT as D1 ARR D3 D4 D5 | sf_fb; destruct DAT as (D1 & ARR & D3 & D4 & D5) ]. split; [exact D1|]. split; [| auto].
eapply u8arr_agree; [exact AG| exact ARR|]. intros a Ha. apply (OWNL (p, a_D x, sy_storage (h_oy h))); [| cbn; lia].
unfold owned. rewrite ED. rewrite !in_app_iff. cbn. clear. tauto. }
clear SYC DAT SY.
eapply (pay_keep c _ _ _ CX AG) in PAY.
2:{ intros NE IN a Ha. apply (OWNL (x_pb c, x_P c, zlength (x_payload c))); [apply in_app_iff; right; exact IN| cbn; exact Ha]. }
clear HBS HS.   xport AG side1.
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. cbn beta. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- split; [left; lia| cbn [outside fst snd]; lia].
- split; [right; left; exact Hc| cbn [outside fst snd]; unfold ralloc_static, RLIBC, RCTX in Hc; lia].
- apply (OWNL bb); [apply in_app_iff; right; exact Hbb| exact Rbb]. }

apply implM_retb. apply K; [| reflexivity| reflexivity].

assert (PERM0 : Permutation (a_LB x) ((match h_st h with Some _ => a_LBD x | None => [] end ++ [(sb_chars (h_bits h), a_Dc x, sb_buf_size (h_bits h))])
++ (opt_blk (sy_data (h_oy h)) (a_D x) (sy_storage (h_oy h)) ++ x_LB0 c))).
{ unfold owned in PERM. rewrite EOS in PERM. cbn [os_body_data os_lacing_vals os_granule_vals stream_zero opt_blk app] in PERM.
rewrite <- !app_assoc in PERM. rewrite <- !app_assoc. exact PERM. }
destruct CASES as [(-> & pb & pl & pg & Bd & L & Gv & jb & jl & jg & -> & -> & RBb & RBl & RBg & OS1 & BLKb & BLKl & BLKg) | (-> & -> & PLB & OS1)].
+
change (rw_cells rsegs m1 L [CB 4096 (u32s [] ++ jl)]) in BLKl.
destruct (chunk_u32arr m1 L [] jl 1024 _ BLKl eq_refl ltac:(lia) ltac:(cbn; lia)) as (lws & AL & LL). cbn [app] in AL, LL.
change (rw_cells rsegs m1 Gv [CB 8192 (u64s [] ++ jg)]) in BLKg.
destruct (chunk_u64arr m1 Gv [] jg 1024 _ BLKg eq_refl ltac:(lia) ltac:(cbn; lia)) as (gws & AGW & LG). cbn [app] in AGW, LG.
pose proof (rw_cells_bound _ _ _ _ BLKb) as BB. cbn [cells_size csize Nat.add] in BB.
pose proof BLKb as [[WFB _] _]. cbn [cells_wf cell_wf] in WFB. destruct WFB as [LJB _]. apply u8arr_of_rw_cells in BLKb.
set (xa := hax_stream x ((pg, Gv, 8192) :: (pl, L, 4096) :: (pb, Bd, 16384) :: a_LB x) Bd L Gv 16384 4096 8192 zero_hdr lws gws jb).
set (ha := set_stream_init h (init_os (Some pb) (Some pl) (Some pg) serial)).
assert (SR1 : stream_rep m1 c xa ha).
{ eapply (stream_rep_init m1 c xa ha pb pl pg serial); try reflexivity; try assumption.
- unfold zlength in LL. cbn [a_lws xa hax_stream]. lia.
- cbn [a_gws xa hax_stream]. lia. }
unfold X1hg.PGS. do 16 eexists. exists F, fc, m1, xa, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM|]. split; [reflexivity|].
split.
{ split; [exists j16, jsk, lk; split; [exact LOW| exact LKO]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [unfold os_piece; cbn [h_stream_init ha set_stream_init Z.eqb]; exact SR1|].
split; [split; [exact OPK| exact OPS]|]. split; [split; [exact OG| exact OGS]|].
split; [exact SY1|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|].
split.
{ split; [exact HP1|]. split.
{ unfold owned. cbn [h_st h_bits h_os h_oy ha set_stream_init a_LBD a_Dc a_Bd a_L a_Gv a_nB a_nL a_nG a_D a_LB xa hax_stream init_os os_body_data os_lacing_vals os_granule_vals].
change (opt_blk (Some pb) Bd 16384) with [(pb, Bd, 16384)]. change (opt_blk (Some pl) L 4096) with [(pl, L, 4096)].
change (opt_blk (Some pg) Gv 8192) with [(pg, Gv, 8192)].
rewrite <- !app_assoc. lazymatch goal with |- Permutation _ (?D ++ [?b] ++ ?Y) => rewrite (app_assoc D [b] Y) end.
apply perm_ins3. exact PERM0. }
split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|]. split; [exists errv1; exact ERR1|]. split; [exact AUX1|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact PE1| cbn; congruence]. }
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os ha set_stream_init a_D a_sybytes a_Dc xa hax_stream].
split; [exact SYOK|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact SYBLK|]. split; [exact SYLEN|].
split; [exact BBR|]. split; [exact BSZ|]. split; [exact FS|]. split; [exact GFS|]. split; [exact NFR|]. split; [exact CHR|].
split; [exact RTR|]. split; [exact EXR|]. split; [exact SSR|]. split; [exact PCR|]. split; [exact LGR|]. split; [right; reflexivity|].
split; [exact EOR|]. split; [exact BRR|]. split; [exact L4K|]. split; [exact STR|].
unfold hbudget, hconsumed, hpend. cbn [h_packet_count h_oy h_os h_bytes_remaining ha set_stream_init init_os os_lacing_fill os_lacing_returned os_body_fill os_lacing_storage os_body_storage]. lia. }
split; [exact LOK|]. split; [exact POK|]. split; [exact NN|].
destruct PB as (cold & PB'). exists cold. rewrite EOS in PB'. unfold hconsumed, hpend in PB' |- *.
cbn [h_packet_count h_oy h_os h_bytes_remaining ha set_stream_init init_os stream_zero os_lacing_fill os_lacing_returned os_body_fill os_lacing_storage os_body_storage] in PB' |- *. lia.
+
set (xa := hax_stream x LB1 0 0 0 0 0 0 zero_hdr [] [] []).
set (ha := set_stream_init h stream_zero).
assert (SR1 : stream_rep m1 c xa ha) by (eapply (stream_rep_zero m1 c xa ha); try reflexivity; exact OS1).
unfold X1hg.PGS. do 16 eexists. exists F, fc, m1, xa, nbr, brem0. do 3 eexists. exists OP.
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM|]. split; [reflexivity|].
split.
{ split; [exists j16, jsk, lk; split; [exact LOW| exact LKO]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists stb; exact STB|].
split; [unfold os_piece; cbn [h_stream_init ha set_stream_init Z.eqb]; exact SR1|].
split; [split; [exact OPK| exact OPS]|]. split; [split; [exact OG| exact OGS]|].
split; [exact SY1|]. split; [exact BI|]. split; [exists pad; exact FSZ|]. split; [exists outb; split; [exact OUT| exact LOUT]|].
split; [exists hij; exact HI|]. split; [exact SAV|]. split; [exact DEC|].
split.
{ split; [exact HP1|]. split.
{ unfold owned. cbn [h_st h_bits h_os h_oy ha set_stream_init a_LBD a_Dc a_Bd a_L a_Gv a_nB a_nL a_nG a_D a_LB xa hax_stream stream_zero os_body_data os_lacing_vals os_granule_vals].
change (opt_blk None 0 0) with (@nil block). cbn [app].
eapply Permutation_trans; [exact PLB|]. rewrite <- !app_assoc in PERM0 |- *. cbn [app] in PERM0 |- *. exact PERM0. }
split; [exact PAY|]. split; [exact TP|]. split; [exact SEW|]. split; [exists errv1; exact ERR1|]. split; [exact AUX1|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact PE1| cbn; congruence]. }
unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os ha set_stream_init a_D a_sybytes a_Dc xa hax_stream].
split; [exact SYOK|]. split; [exact BOK|]. split; [exact OWN|]. split; [exact SYBLK|]. split; [exact SYLEN|].
split; [exact BBR|]. split; [exact BSZ|]. split; [exact FS|]. split; [exact GFS|]. split; [exact NFR|]. split; [exact CHR|].
split; [exact RTR|]. split; [exact EXR|]. split; [exact SSR|]. split; [exact PCR|]. split; [exact LGR|]. split; [right; reflexivity|].
split; [exact EOR|]. split; [exact BRR|]. split; [exact L4K|]. split; [exact STR|].
unfold hbudget, hconsumed, hpend. cbn [h_packet_count h_oy h_os h_bytes_remaining ha set_stream_init stream_zero os_lacing_fill os_lacing_returned os_body_fill os_lacing_storage os_body_storage]. lia. }
split; [exact LOK|]. split; [exact POK|]. split; [exact NN|].
destruct PB as (cold & PB'). exists cold. rewrite EOS in PB'. unfold hconsumed, hpend in PB' |- *.
cbn [h_packet_count h_oy h_os h_bytes_remaining ha set_stream_init stream_zero os_lacing_fill os_lacing_returned os_body_fill os_lacing_storage os_body_storage] in PB' |- *. lia.
Qed.
End PAGE2.
