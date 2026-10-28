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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h9 X1gy X1hg X1hf X1hh X1hi X1gz.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition FRC {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (pc : Z) (a0c : word -> Prop) (g : hstate bptr) (j : Z) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 pno skip : Z) (s8w : word),
ms = MS (hregs c g (a_S x) (wz (pno + 1)) (wz skip) (wz (h_speex_serialno g)) (wz 2147483647) s8w (wz (h_nframes g - j))
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom rsegs)
/\ a0c a0
/\ frm0 fc /\ h_stream_init g = 1 /\ h_packet_count g <> 0
/\ hrep dec_rep c x g st m (C8 (wz nbr)) (C8 (wz brem0)) /\ low_ok g nbr brem0
/\ -2^31 <= skip < 2^31 /\ 0 <= pno <= h_packet_count g /\ (s8w = wz 0 \/ (s8w = wz 1 /\ skip < 0))
/\ h_packet_count g + 1 + (os_lacing_fill (h_os g) - os_lacing_returned (h_os g)) <= 162 * hconsumed c g.
Notation FR dec_rep c g j := (FRC dec_rep c 0x1c46c (fun _ => True) g j).
Notation FRr dec_rep c g j ret := (FRC dec_rep c 0x1c47c (fun a0 => a0 = wz ret) g j).

Lemma rheap_ssp0 {RCEIL : RunCeiling} : forall s LB m, RHEAP s LB m -> ssp_cells m run_canary.
Proof.
intros s LB m sfH_; first [ sf_destruct 6%nat sfH_ as st LB0 _ _ MR _ | sf_fb; destruct sfH_ as (st & LB0 & _ & _ & MR & _) ]. first [ sf_destruct 4%nat MR as _ _ G _ | sf_fb; destruct MR as (_ & _ & G & _) ]. first [ sf_destruct 5%nat G as _ _ _ G4 G5 | sf_fb; destruct G as (_ & _ & _ & G4 & G5) ].
unfold ssp_cells, got_ssp, ssp_guard. split; [exact G4| exact G5].
Qed.

Lemma zbv_sub_modl : forall x y, Z_to_bv 64 (x mod 18446744073709551616 - y) = Z_to_bv 64 (x - y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
Lemma swrap32_sub_modl : forall x y, bv_swrap 32 (x mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof.
intros x y.
change (bv_swrap 32 (x mod 18446744073709551616 - y)) with ((x mod 18446744073709551616 - y + 2147483648) mod 4294967296 - 2147483648).
change (bv_swrap 32 (x - y)) with ((x - y + 2147483648) mod 4294967296 - 2147483648). f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x mod 18446744073709551616 - y + 2147483648) with (x mod 18446744073709551616 + (2147483648 - y)) by lia.
replace (x - y + 2147483648) with (x + (2147483648 - y)) by lia.
rewrite (Zplus_mod (x mod 18446744073709551616)), (Zplus_mod x).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 x) by (lia || exact D). reflexivity.
Qed.

Ltac lts_false :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if bv_lts ?a ?b then _ else _) _ _ _ _) =>
replace (bv_lts a b) with false by (symmetry; unfold bv_lts; rewrite ?zb_signed_small by lia; apply Z.ltb_ge; lia); cbv iota
end.
Ltac nrm := rewrite ?X1c8.land_W64; nswrap.
Ltac ntk := zstep; rewrite ?Z.add_opp_r; if_false_z.
Ltac blk_z K := zstep; if_true_z; apply K.
Ltac blk_n K :=
zstep; if_false_z;
zstep; zstep; nrm; ntk; zstep; nrm;
zstep; zstep; nrm; ntk; zstep; nrm;
zstep; zstep; nrm; ntk;
zstep; zstep; nrm; ntk;
zstep; zstep; nrm;
zstep; zstep; rewrite ?X1c8.land_W64, ?zbv_sub_modl, ?swrap32_sub_modl; nswrap; ntk; apply K.

Lemma low_lk_c4 : forall m A j16 (w10 w18 : word) jsk (w30 w38 w40 : word) L (wr : word),
rw_cells rsegs m A [CB 16 j16; C8 w10; C8 w18; CB 16 jsk; C8 w30; C8 w38; C8 w40; CB 4 (le4 (wz L)); C4 wr] ->
rw_cells rsegs m A [CB 16 j16; C8 w10; C8 w18; CB 16 jsk; C8 w30; C8 w38; C8 w40; C4 (wz L); C4 wr].
Proof.
intros m A j16 w10 w18 jsk w30 w38 w40 L wr H. pose proof H as [[WF _] _]. cbn in WF.
eapply X0pw.rw_cells_recast; [exact H| | reflexivity| reflexivity].
cbn. cbn in WF. repeat split; try reflexivity; tauto.
Qed.

Lemma dead_block : forall (Q : machine_state -> Prop) (x1 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (HSP skip L fs nf jd : Z) (j16 jsk pad : list byte) (w10 w18 w30 w38 w40 wr : word),
mem_inv rsegs m ->
rw_cells rsegs m HSP [CB 16 j16; C8 w10; C8 w18; CB 16 jsk; C8 w30; C8 w38; C8 w40; CB 4 (le4 (wz L)); C4 wr] ->
rw_cells rsegs m (HSP + 672) [CB 4 pad; C4 (wz fs)] ->
0 <= HSP -> HSP + 8832 < 2^63 ->
0 <= L <= 1342177280 -> 0 <= fs <= 640 -> 1 <= nf <= 10 -> 0 <= jd < nf -> -2^31 <= skip < 2^31 ->
(s8 = wz 0 \/ (s8 = wz 1 /\ skip < 0)) ->
(forall b0 b1 b2 b3, evt rsegs Q (MS (mkR x1 (wz HSP) gp tp t0 t1 t2 s0 (wz skip) b0 b1 b2 b3 a4 a5 a6 a7
s2 s3 s4 (wz 2147483647) s6 s7 s8 (wz nf) (wz jd) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1c544) fc None m (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR x1 (wz HSP) gp tp t0 t1 t2 s0 (wz skip) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 (wz 2147483647) s6 s7 s8 (wz nf) (wz jd) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1c4a8) fc None m (seg_rom rsegs)).
Proof.
intros until w40. intros wr MI LOW FSZ H0 H1 LR FS NF JD SK S8 K.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. apply low_lk_c4 in LOW.
unfold wz in *.
assert (PB1 : 0 <= nf * fs <= 6400) by nia.
assert (PB2 : 0 <= jd * fs <= nf * fs - fs) by nia.
zstep. rewrite sx32_small by (unfold X1nj.int31; lia).
zstep. zstep. rewrite swrap32_small by lia. ntk.
zstep. nswrap.
zstep. if_cases BG; zify_cond BG.
{ apply K. }
rewrite !zb_signed_small in BG by lia.
zstep. rewrite sx32_small by (unfold X1nj.int31; lia).
zstep.
destruct S8 as [-> | [-> SN]].
- zstep. if_cases B1; [blk_z K|]. zstep. if_cases B2; [blk_z K|]. zstep. if_cases B3; [blk_z K|].
  apply Bool.negb_false_iff in B3. unfold bv_lts in B3. rewrite !zb_signed_small in B3 by lia. apply Z.ltb_lt in B3. rename B3 into SP.
  zstep. zstep. nswrap. ntk. zstep. nswrap. zstep. zstep. nswrap. ntk. zstep. apply K.
- zstep. if_cases B1; [blk_n K|]. zstep. if_cases B2; [blk_n K|]. zstep.
  replace (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 skip)) with false by (symmetry; unfold bv_lts; rewrite !zb_signed_small by lia; apply Z.ltb_ge; lia).
  cbn [negb]. cbv iota. blk_n K.
Qed.

Lemma loop_tail : forall (Q : machine_state -> Prop) (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (nf jd : Z),
1 <= nf <= 10 -> 0 <= jd < nf ->
(jd + 1 < nf -> evt rsegs Q (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (wz (jd + 1)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (wz nf) (wz (jd + 1)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1c46c) fc None m (seg_rom rsegs))) ->
(jd + 1 = nf -> evt rsegs Q (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (wz (jd + 1)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (wz nf) (wz (jd + 1)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1c554) fc None m (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (wz nf) (wz jd) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1c544) fc None m (seg_rom rsegs)).
Proof.
intros until jd. intros NF JD KL KX.
unfold wz in *.
zstep. nswrap. zstep. lts_false. zstep. zstep. if_cases BL; zify_cond BL.
- apply KL. lia.
- apply KX. lia.
Qed.

Section DEC.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DECODE : rspx_decode_stmt dec_rep.
Hypothesis DSTEREO : rspx_decode_stereo_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PKE := (PKE dec_rep c).
Notation h_decodeP := (h_decode io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Notation decode_loopP := (decode_loop io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).

#[using="DECODE RHF RBR RND RBD CX"] Lemma decode_call : forall g j d st ms,
FR dec_rep c g j st ms -> h_st g = Some d ->
implM rsegs (h_decodeP d (h_bits g)) st
(fun r st' ms' => let '(ret, d', b') := r in
st' = st /\ -2 <= ret <= 0 /\ sb_chars b' = sb_chars (h_bits g) /\ sb_buf_size b' = sb_buf_size (h_bits g)
/\ FRr dec_rep c (set_bits_st g b' (Some d') (h_eos g)) j ret st ms') ms.
Proof.
intros g j d st ms FX ESt.
first [ sf_destruct 36%nat FX as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 pno skip s8w -> _ FRM SI1 NZ HR LOK SKR PNR S8R BUD' | sf_fb; destruct FX as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & pno & skip & s8w & -> & _ & FRM & SI1 & NZ & HR & LOK & SKR & PNR & S8R & BUD') ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
unfold dec_piece in DEC. rewrite ESt in DEC. destruct DEC as (DR & SB & BRD).
assert (HLo : forall b, In b (owned x g) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (INLBD : forall b, In b (a_LBD x) -> In b (a_LB x)).
{ intros b Hb. apply HLo. unfold owned. rewrite ESt. apply in_app_iff. left. exact Hb. }
assert (INBITS : In (sb_chars (h_bits g), a_Dc x, sb_buf_size (h_bits g)) (a_LB x)).
{ apply HLo. unfold owned. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
pose proof (rheap_ssp0 _ _ _ HP) as SSP.
assert (LBDNE : forall x0, In x0 (a_LBD x) -> blk_id x0 <> sb_chars (h_bits g)).
{ pose proof (nodup_ids_perm _ _ PERM (RND _ _ _ HP)) as NDO. unfold owned in NDO. rewrite ESt, <- app_assoc, map_app in NDO.
intros x0 Hx0 E. eapply (nodup_app_disj _ _ (blk_id x0) NDO); [apply in_map; exact Hx0| rewrite E; left; reflexivity]. }
unfold low_cells, wz in LOW.
lazymatch goal with |- implM _ _ _ ?Q _ => set (QQ := Q) end.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st QQ msx) end.
eapply implM_mono.
{ eapply DECODE with (LB := a_LB x) (STEREO := aSTEREO c) (S := a_S x) (LBD := a_LBD x) (BITS := aBITS c) (Dc := a_Dc x)
(OUT := aOUT c) (lo := x_lo c) (outb := outb) (stb := stb) (canary := run_canary);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact DR | exact HP | exact INLBD | exact BI | exact BOK | exact OWN | exact INBITS | exact OUT | exact LOUT | exact STB
| exact TP | exact SEW | exact SSP | exact ST | exact MI | exact FRM | reflexivity | exact LBDNE
| apply (align_of_usp (usp c)); [exact SP16| lia| reflexivity]
| unfold HOUT_BYTES, DECODE_STACK, alloc_ceiling in *; lia ]. }
cbv beta. intros [[ret d'] b'] st' ms' PO.
first [ sf_destruct 37%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F' fc' m' outb' stb' -> RET FRM' MU WM MI' ST' DR' BI' BOK' EOW ECH EBS OUT' LOUT' STB' SEW' -> | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & m' & outb' & stb' & -> & RET & FRM' & MU & WM & MI' & ST' & DR' & BI' & BOK' & EOW & ECH & EBS & OUT' & LOUT' & STB' & SEW' & ->) ].
rewrite ?(unsigned_lit (aLOW c)) in ST' by lia. rewrite ?(unsigned_lit (aLOW c)) in MU by lia.
replace (ret_pc (Z_to_bv 64 0x1c47c)) with (Z_to_bv 64 0x1c47c) by (symmetry; rpc).
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
pose proof (RND _ _ _ HP) as ND.
set (g' := set_bits_st g b' (Some d') (h_eos g)).

set (rest := [(sb_chars (h_bits g), a_Dc x, sb_buf_size (h_bits g))] ++ stream_blks x g ++ opt_blk (sy_data (h_oy g)) (a_D x) (sy_storage (h_oy g))).
assert (PERM2 : Permutation (a_LB x) ((a_LBD x ++ rest) ++ x_LB0 c)).
{ unfold owned in PERM. rewrite ESt in PERM. unfold rest, stream_blks. rewrite <- !app_assoc. rewrite <- !app_assoc in PERM. exact PERM. }
assert (OTHERS : forall a, in_block rest a -> forall b, In b (a_LBD x) -> ~ (blk_addr b <= a < blk_addr b + blk_size b)).
{ intros a (bb & Hbb & Ra) b Hb. pose proof (owned_apart RBD st m x (a_LBD x) rest (x_LB0 c) b bb HP ND PERM2 Hb Hbb). lia. }
assert (RREST : forall bb, In bb rest -> rblock_range (blk_addr bb) (blk_size bb)).
{ intros bb Hbb. apply (RBR _ _ _ _ HP). eapply Permutation_in; [apply Permutation_sym; exact PERM2|].
apply in_app_iff. left. apply in_app_iff. right. exact Hbb. }

assert (OW : forall a,
(aLOW c <= a < aSTEREO c \/ aSTEREO c + 24 <= a < aBITS c \/ aBITS c + 48 <= a < aOUT c \/ aOUT c + HOUT_BYTES <= a < usp c
\/ in_block rest a) ->
outside ((x_lo c, aLOW c) :: (aBITS c, aBITS c + 48) :: (aOUT c, aOUT c + HOUT_BYTES) :: (aSTEREO c, aSTEREO c + 24)
:: (250128, 250128 + 232) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) (a_LBD x)) a).
{ intros a Ha. unfold HOUT_BYTES in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Hin]]]].
1-4: cbn [outside]; repeat (split; [lia|]); apply outside_blocks; intros b Hb; pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; lia.
pose proof Hin as (bb & Hbb & Ra). pose proof (RREST bb Hbb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ R4 R5 | sf_fb; destruct sfP_ as (_ & _ & _ & R4 & R5) ]. unfold alloc_ceiling in R4.
cbn [outside]. repeat (split; [lia|]). apply outside_blocks. intros b Hb. exact (OTHERS a Hin b Hb). }

destruct (hglob_munch RHF RBR RND RBD c x g st m m' _ CX HG MU WM MI' ST' SEW') as [HG1 _].
{ unfold hfoot_ok. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; unfold HOUT_BYTES; lia|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; reflexivity|].
apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb).
right; right. exists b. split; [unfold owned; rewrite ESt; apply in_app_iff; left; exact Hb| cbn; lia]. }
unfold QQ. split; [reflexivity|]. split; [exact RET|]. split; [exact ECH|]. split; [exact EBS|].
unfold FRC. sf_eexists 16%nat. first [ unshelve sf_eexists 9%nat; [ exact (F') | exact (fc') | exact (m') | exact (x) | exact (nbr) | exact (brem0) | exact (pno) | exact (skip) | exact (s8w) | ] | sf_fb; exists F', fc', m', x, nbr, brem0, pno, skip, s8w ].
split; [unfold hregs, wz, g'; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers set_bits_st]; reflexivity|].
split; [reflexivity|]. split; [exact FRM'|]. split; [exact SI1|]. split; [exact NZ|].
split.
{
split. { exists j16, jsk, lk. split; [| unfold lk_ok, g' in LKOK |- *; cbn [h_st set_bits_st]; intros _; apply LKOK; rewrite ESt; discriminate].
unfold low_cells, wz. cbn [h_extra_headers h_granule_frame_size h_rate h_last_granule g' set_bits_st].
eapply rw_cells_agree; [exact AG| exact LOW| intros a Ha; apply OW; cbn in Ha; lia]. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists stb'; exact STB'|].
split. { eapply (os_piece_agree2 _ _ _ _ _ _ AG); [unfold g'; unfold os_piece in OSP |- *; cbn [h_stream_init h_os set_bits_st]; exact OSP| |].
- intros a Ha. apply OW. lia.
- intros a Ha. apply OW. right; right; right; right. unfold rest. apply in_block_app_r. apply in_block_app_l.
unfold g' in Ha. unfold stream_blks in Ha |- *. cbn [h_os set_bits_st] in Ha. exact Ha. }
split. { exists opj. eapply rw_cells_agree; [exact AG| exact OP| intros a Ha; apply OW; cbn in Ha; lia]. }
split. { exists ogj. eapply rw_cells_agree; [exact AG| exact OG| intros a Ha; apply OW; cbn in Ha; lia]. }
split. { unfold g'. cbn [h_oy set_bits_st]. eapply (sync_rep_agree _ _ _ _ _ _ _ AG SY); [intros a Ha; apply OW; lia|].
intros a Ha. apply OW. right; right; right; right. unfold rest. apply in_block_app_r. apply in_block_app_r.
first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy g)) as [q|]; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
exists (q, a_D x, sy_storage (h_oy g)). split; [left; reflexivity|]. cbn. rewrite <- SYLEN. lia. }
split; [unfold g'; cbn [h_bits set_bits_st]; exact BI'|].
split. { exists pad. unfold fsz_cells, g'. cbn [h_frame_size set_bits_st]. eapply rw_cells_agree; [exact AG| exact FSZ| intros a Ha; apply OW; cbn in Ha; lia]. }
split; [exists outb'; split; [exact OUT'| exact LOUT']|].
split. { exists hij. eapply rw_cells_agree; [exact AG| exact HI| intros a Ha; apply OW; cbn in Ha; unfold HOUT_BYTES; lia]. }
split. { eapply rw_cells_agree; [exact AG| exact SAV| intros a Ha; apply OW; cbn in Ha; unfold HOUT_BYTES; lia]. }
split. { unfold dec_piece, g'. cbn [h_st set_bits_st]. split; [exact DR'|]. split; [exact SB| exact BRD]. }
split. { unfold g'. unfold hglob, owned in HG1 |- *. cbn [h_st h_bits h_os h_oy set_bits_st]. rewrite ESt in HG1. rewrite ECH, EBS. exact HG1. }
unfold hpure, g'. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os set_bits_st].
rewrite EOW, EBS. split; [exact SYOK|]. split; [exact BOK'|]. repeat (split; [assumption|]).
unfold hbudget, hconsumed, hpend in BUD |- *. cbn [h_packet_count h_oy h_os h_bytes_remaining set_bits_st]. exact BUD. }
split; [unfold low_ok, g' in LOK |- *; cbn [h_bytes_remaining set_bits_st]; exact LOK|].
split; [exact SKR|]. split; [unfold g'; cbn [h_packet_count set_bits_st]; exact PNR|]. split; [exact S8R|].
unfold g'. unfold hconsumed, hpend in BUD' |- *. cbn [h_packet_count h_os h_oy h_bytes_remaining set_bits_st]. exact BUD'.
Qed.

#[using="DRF DSTEREO RHF RBR RND RBD CX"] Lemma frame_rest : forall {B} g j ret d st ms (KK : dec_state bptr * bits_st bptr -> M PState B) (Q : B -> PState -> machine_state -> Prop),
FRr dec_rep c g j ret st ms -> h_st g = Some d -> -2 <= ret <= 0 -> 1 <= j <= h_nframes g ->
(forall st' ms', PKE g st' ms' -> implM rsegs (KK (d, h_bits g)) st' Q ms') ->
(forall ms', FR dec_rep c g (j - 1) st ms' -> 2 <= j ->
implM rsegs (X1qx.mbind (decode_loopP (Z.to_nat (j - 1)) d (h_bits g)) KK) st Q ms') ->
implM rsegs (X1qx.mbind
(if (ret =? -1) || (ret =? -2) then X1qx.mret (d, h_bits g)
else X1qx.mbind (bits_remaining_M (h_bits g))
(fun rem => if rem <? 0 then X1qx.mret (d, h_bits g) else decode_loopP (Z.to_nat (j - 1)) d (h_bits g)))
KK) st Q ms.
Proof.
intros B g j ret d st ms KK Q FX ESt RET HJ KEXIT KNEXT.
first [ sf_destruct 36%nat FX as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 pno skip s8w -> -> FRM SI1 NZ HR LOK SKR PNR S8R BUD' | sf_fb; destruct FX as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & pno & skip & s8w & -> & -> & FRM & SI1 & NZ & HR & LOK & SKR & PNR & S8R & BUD') ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) _ _ (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & _ & _ & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
assert (EOSB : 0 <= h_eos g <= 1) by lia.

assert (REMR : -1 <= speex_bits_remaining (h_bits g) < 2^62).
{ pose proof BOK as sfP_; first [ sf_destruct 7%nat sfP_ as Bl B1 Bn Bc Bb Bp Bo | sf_fb; destruct sfP_ as (Bl & B1 & Bn & Bc & Bb & Bp & Bo) ]. pose proof BBR as sfP_; first [ sf_destruct 5%nat sfP_ as R1 _ R3 R4 _ | sf_fb; destruct sfP_ as (R1 & _ & R3 & R4 & _) ]. unfold alloc_ceiling in R4.
unfold speex_bits_remaining, bits_pos in *. destruct (negb (sb_overflow (h_bits g) =? 0)); lia. }

assert (EXIT : forall j2 ms2, FRC dec_rep c 0x1c554 (fun _ => True) g j2 st ms2 -> implM rsegs (KK (d, h_bits g)) st Q ms2).
{ intros j2 ms2 FX2.
first [ sf_destruct 36%nat FX2 as z1 u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 x2 nbr2 brem2 pno2 skip2 s8w2 -> _ FRM2 _ _ HR2 LOK2 _ PNR2 _ BUD2 | sf_fb; destruct FX2 as (z1 & u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & x2 & nbr2 & brem2 & pno2 & skip2 & s8w2 & -> & _ & FRM2 & _ & _ & HR2 & LOK2 & _ & PNR2 & _ & BUD2) ].
unfold implM. iprefix. unfold hregs, wz.
zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply KEXIT.
unfold X1hi.PKE. sf_eexists 16%nat. first [ unshelve sf_eexists 11%nat; [ exact (F2) | exact (fc2) | exact (m2) | exact (x2) | exact ((pno2 + 1)) | exact (nbr2) | exact (brem2) | exact ((Z_to_bv 64 (pno2 + 1))) | exact ((Z_to_bv 64 2147483647)) | exact (s8w2) | exact ((Z_to_bv 64 (h_nframes g - j2))) | ] | sf_fb; exists F2, fc2, m2, x2, (pno2 + 1), nbr2, brem2, (Z_to_bv 64 (pno2 + 1)), (Z_to_bv 64 2147483647), s8w2, (Z_to_bv 64 (h_nframes g - j2)) ].
split; [unfold hregs, wz; reflexivity|]. split; [exact FRM2|]. split; [exact SI1|]. split; [exact NZ|].
split; [lia|]. split; [exact HR2|]. split; [exact LOK2| exact BUD2]. }

assert (JOIN2 : forall ms2, FRC dec_rep c 0x1c4a8 (fun _ => True) g j st ms2 ->
implM rsegs (X1qx.mbind (decode_loopP (Z.to_nat (j - 1)) d (h_bits g)) KK) st Q ms2).
{ intros ms2 FX2.
first [ sf_destruct 36%nat FX2 as z1 u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 x2 nbr2 brem2 pno2 skip2 s8w2 -> _ FRM2 _ _ HR2 LOK2 SKR2 PNR2 S8R2 BUD2 | sf_fb; destruct FX2 as (z1 & u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & x2 & nbr2 & brem2 & pno2 & skip2 & s8w2 & -> & _ & FRM2 & _ & _ & HR2 & LOK2 & SKR2 & PNR2 & S8R2 & BUD2) ].
pose proof HR2 as sfP_; first [ sf_destruct 16%nat sfP_ as (j16' & jsk' & lk' & LOW2 & LKOK2) _ _ _ _ _ _ _ _ (pad' & FSZ2) _ _ _ _ HG2 PURE2 | sf_fb; destruct sfP_ as ((j16' & jsk' & lk' & LOW2 & LKOK2) & _ & _ & _ & _ & _ & _ & _ & _ & (pad' & FSZ2) & _ & _ & _ & _ & HG2 & PURE2) ].
pose proof HG2 as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ MI2 _ _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & MI2 & _ & _ & _) ].
destruct (LKOK2 ltac:(rewrite ESt; discriminate)) as (L & -> & LR).
unfold low_cells in LOW2. unfold fsz_cells in FSZ2.
replace (bv_unsigned (x_sp c) + -8160) with (bv_unsigned (x_sp c) + -8832 + 672) in FSZ2 by lia.
unfold implM. iprefix. unfold hregs.
eapply dead_block; [exact MI2| exact LOW2| exact FSZ2| lia| lia| lia| lia| lia| lia| exact SKR2| exact S8R2|].
intros b0 b1 b2 b3.
eapply loop_tail; [lia| lia| |].
- intros LT.
apply evt_done. apply KNEXT; [| lia].
unfold FRC. sf_eexists 16%nat. first [ unshelve sf_eexists 9%nat; [ exact (F2) | exact (fc2) | exact (m2) | exact (x2) | exact (nbr2) | exact (brem2) | exact (pno2) | exact (skip2) | exact (s8w2) | ] | sf_fb; exists F2, fc2, m2, x2, nbr2, brem2, pno2, skip2, s8w2 ].
split; [unfold hregs; replace (h_nframes g - (j - 1)) with (h_nframes g - j + 1) by lia; reflexivity|].
split; [exact I|]. split; [exact FRM2|]. split; [exact SI1|]. split; [exact NZ|].
split; [exact HR2|]. split; [exact LOK2|]. split; [exact SKR2|]. split; [exact PNR2|]. split; [exact S8R2| exact BUD2].
- intros EQ.
replace (j - 1) with 0 by lia. cbn [Z.to_nat decode_loop].
apply evt_done. apply implM_retb. apply (EXIT (j - 1)).
unfold FRC. sf_eexists 16%nat. first [ unshelve sf_eexists 9%nat; [ exact (F2) | exact (fc2) | exact (m2) | exact (x2) | exact (nbr2) | exact (brem2) | exact (pno2) | exact (skip2) | exact (s8w2) | ] | sf_fb; exists F2, fc2, m2, x2, nbr2, brem2, pno2, skip2, s8w2 ].
split; [unfold hregs; replace (h_nframes g - (j - 1)) with (h_nframes g - j + 1) by lia; reflexivity|].
split; [exact I|]. split; [exact FRM2|]. split; [exact SI1|]. split; [exact NZ|].
split; [exact HR2|]. split; [exact LOK2|]. split; [exact SKR2|]. split; [exact PNR2|]. split; [exact S8R2| exact BUD2]. }

assert (FX0 : forall pc0 mx, hrep dec_rep c x g st mx (C8 (wz nbr)) (C8 (wz brem0)) ->
forall (y1 v0 v1 v2 b0 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 : word) Fx fcx, frm0 fcx ->
FRC dec_rep c pc0 (fun _ => True) g j st
(MS (hregs c g (a_S x) (wz (pno + 1)) (wz skip) (wz (h_speex_serialno g)) (wz 2147483647) s8w (wz (h_nframes g - j))
y1 v0 v1 v2 b0 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6) Fx (wz pc0) fcx None mx (seg_rom rsegs))).
{ intros pc0 mx HRx y1 v0 v1 v2 b0 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 Fx fcx FRMx.
unfold FRC. sf_eexists 16%nat. first [ unshelve sf_eexists 9%nat; [ exact (Fx) | exact (fcx) | exact (mx) | exact (x) | exact (nbr) | exact (brem0) | exact (pno) | exact (skip) | exact (s8w) | ] | sf_fb; exists Fx, fcx, mx, x, nbr, brem0, pno, skip, s8w ].
split; [reflexivity|]. split; [exact I|]. split; [exact FRMx|]. split; [exact SI1|]. split; [exact NZ|].
split; [exact HRx|]. split; [exact LOK|]. split; [exact SKR|]. split; [exact PNR|]. split; [exact S8R| exact BUD']. }

unfold implM. iprefix. unfold hregs, wz.

assert (R3 : ret = 0 \/ ret = -1 \/ ret = -2) by lia.
zstep. zstep. if_cases B1.
-
assert (RT : (ret =? -1) || (ret =? -2) = true).
{ destruct R3 as [->|[->| ->]]; [| reflexivity| reflexivity]. exfalso. revert B1. vm_compute. discriminate. }
rewrite RT. apply evt_done. apply implM_retb. apply (EXIT j).
lazymatch goal with |- FRC _ _ _ _ _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ ?r28 ?r29 ?r30 ?r31) ?Fx _ ?fcx _ ?mx _) =>
exact (FX0 0x1c554 mx HR r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 Fx fcx FRM) end.
- assert (R0 : ret = 0).
{ destruct R3 as [->|[->| ->]]; [reflexivity| |]; exfalso; revert B1; vm_compute; discriminate. }
subst ret. cbn [Z.eqb orb].
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
apply implM_bind_assoc. apply implM_retb. cbv beta.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold implM. iprefix.

unfold low_cells, wz in LOW.
zstep. zstep.
callx (eapply (X1g6.speex_bits_remaining_spec (aBITS c) (a_Dc x) (h_bits g)); [exact BI| exact BOK| exact MI]).
lazymatch type of PC with ?v = _ => subst v end. clear POST.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mR end.
lazymatch goal with H : mem_inv _ mR |- _ => rename H into MIR end.
assert (HRR : hrep dec_rep c x g st mR (C8 (Z_to_bv 64 nbr)) (C8 (Z_to_bv 64 brem0))).
{ eapply (hrep_after_stackcall dec_rep DRF RHF RBR RND RBD c x g st m mR); [exact CX| exact HR| | exact WM| exact MIR| exact ST| exact OUT| exact LOUT| exact STB].
eapply munch_weaken; [| exact MU]. intros a _. exact I. }

zstep. if_cases B2; scond B2.
+
replace (speex_bits_remaining (h_bits g) <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
apply evt_done. apply implM_retb. apply (EXIT j).
lazymatch goal with |- FRC _ _ _ _ _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ ?r28 ?r29 ?r30 ?r31) ?Fx _ ?fcx _ ?mx _) =>
exact (FX0 0x1c554 mx HRR r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 Fx fcx FRM) end.
+ replace (speex_bits_remaining (h_bits g) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).

zstep. zstep. if_cases B3.
*
apply evt_done. apply JOIN2.
lazymatch goal with |- FRC _ _ _ _ _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ ?r28 ?r29 ?r30 ?r31) ?Fx _ ?fcx _ ?mx _) =>
exact (FX0 0x1c4a8 mx HRR r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 Fx fcx FRM) end.
*
assert (CH2 : h_channels g = 2).
{ first [apply Bool.negb_false_iff in B3| idtac]. rewrite zbv_eqb_signed in B3 by lia. apply (proj1 (Z.eqb_eq _ _)) in B3. exact B3. }
clear MU WM HR.

unfold fsz_cells in FSZ.
zstep. rewrite sx32_small by (unfold X1nj.int31; lia). zstep. zstep. zstep.
eapply evt_cut.
{ eapply DSTEREO with (OUT := aOUT c) (STEREO := aSTEREO c) (lo := x_lo c) (frame_size := h_frame_size g) (outb := outb) (stb := stb);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact OUT | exact LOUT | exact STB | exact ST | exact MIR | exact FRM | reflexivity
| unfold HOUT_BYTES, DECODE_STEREO_STACK, alloc_ceiling in *; lia ]. }
cbv beta. intros ms3 PO.
first [ sf_destruct 29%nat PO as r0 r1 r2 q0 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 F3 fc3 m3 outb3 stb3 -> FRM3 MU3 WM3 MI3 ST3 OUT3 LOUT3 STB3 | sf_fb; destruct PO as (r0 & r1 & r2 & q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & r3 & r4 & r5 & r6 & F3 & fc3 & m3 & outb3 & stb3 & -> & FRM3 & MU3 & WM3 & MI3 & ST3 & OUT3 & LOUT3 & STB3) ].
rewrite ?(unsigned_lit (aLOW c)) in MU3 by lia. rewrite ?(unsigned_lit (aLOW c)) in ST3 by lia.
replace (ret_pc (Z_to_bv 64 0x1c4a8)) with (Z_to_bv 64 0x1c4a8) by (symmetry; rpc).
assert (HR3 : hrep dec_rep c x g st m3 (C8 (Z_to_bv 64 nbr)) (C8 (Z_to_bv 64 brem0))).
{ eapply (hrep_after_stackcall dec_rep DRF RHF RBR RND RBD c x g st mR m3); [exact CX| exact HRR| exact MU3| exact WM3| exact MI3| exact ST3| exact OUT3| unfold HOUT_BYTES in LOUT3; exact LOUT3| exact STB3]. }
apply evt_done. apply JOIN2.
lazymatch goal with |- FRC _ _ _ _ _ _ _ (MS (mkR ?r1 _ _ _ ?r5 ?r6 ?r7 _ _ ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 _ _ _ _ _ _ _ _ _ _ ?r28 ?r29 ?r30 ?r31) ?Fx _ ?fcx _ ?mx _) =>
exact (FX0 0x1c4a8 mx HR3 r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 Fx fcx FRM3) end.
Qed.
End DEC.
