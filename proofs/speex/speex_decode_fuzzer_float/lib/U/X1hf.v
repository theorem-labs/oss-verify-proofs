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

Lemma s64_range' : forall v, -2^63 <= s64 v < 2^63.
Proof. intros v. unfold s64. pose proof (Z.mod_pos_bound (v + 2^63) (2^64) ltac:(lia)). lia. Qed.

Lemma count_lt255_bound : forall l, 0 <= count_lt255 l <= zlength l.
Proof.
induction l as [|v l IH]; [unfold zlength; cbn; lia|]. cbn [count_lt255]. rewrite zlength_cons.
destruct (v <? 255); lia.
Qed.
Lemma ogg_page_packets_range : forall hdr, 0 <= znth hdr 26 <= 255 -> 0 <= ogg_page_packets hdr <= 255.
Proof.
intros hdr Hn. unfold ogg_page_packets. pose proof (count_lt255_bound (zslice 27 (znth hdr 26) hdr)).
unfold zslice in *. pose proof (zlength_ztake_le_n (znth hdr 26) (zdrop 27 hdr) ltac:(lia)). lia.
Qed.

Lemma sgn64_pos : forall p, -2^63 <= p < 2^63 ->
((0 <? Z.land p 18446744073709551615) && (Z.land p 18446744073709551615 <? 9223372036854775808) = true <-> 0 < p).
Proof.
intros p Hp. rewrite land_ones64.
destruct (Z_lt_le_dec p 0).
- rewrite <- (Z.mod_add p 1 (2^64)) by lia. rewrite Z.mod_small by lia.
split; [| lia]. intros H. apply andb_prop in H. destruct H as [_ H]. apply Z.ltb_lt in H. lia.
- rewrite Z.mod_small by lia. rewrite Bool.andb_true_iff, !Z.ltb_lt. lia.
Qed.
Lemma sgn64_pos_t : forall p, -2^63 <= p < 2^63 ->
(0 <? Z.land p 18446744073709551615) && (Z.land p 18446744073709551615 <? 9223372036854775808) = true -> 0 < p.
Proof. intros p Hp H. apply (proj1 (sgn64_pos p Hp) H). Qed.
Lemma sgn64_pos_f : forall p, -2^63 <= p < 2^63 ->
(0 <? Z.land p 18446744073709551615) && (Z.land p 18446744073709551615 <? 9223372036854775808) = false -> p <= 0.
Proof. intros p Hp H. destruct (Z_lt_le_dec 0 p); [| lia]. apply (proj2 (sgn64_pos p Hp)) in l. rewrite l in H. discriminate. Qed.

Lemma land64_of_signed : forall p, -2^63 <= p < 2^63 ->
(0 <= p -> Z.land p 18446744073709551615 = p) /\ (p < 0 -> Z.land p 18446744073709551615 = p + 2^64).
Proof.
intros p Hp. rewrite land_ones64. split; intros H.
- apply Z.mod_small. lia.
- rewrite <- (Z.mod_add p 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac unsign p HP :=
let L := fresh "L" in pose proof (land64_of_signed p HP) as L;
first [ rewrite (proj1 L) in * by plia | rewrite (proj2 L) in * by plia
| let Hn := fresh "Hn" in let Hq := fresh "Hq" in
destruct (Z_lt_le_dec p 0) as [Hn|Hq]; [rewrite (proj2 L Hn) in * | rewrite (proj1 L Hq) in *] ];
clear L.

Definition C640 : Z := 14411518807585587.
Lemma c640_eq : C640 = Z.quot 9223372036854775807 640.
Proof. reflexivity. Qed.

Ltac scond K :=
unfold bv_lts, bv_ltu, bv_eqb in K;
rewrite ?zb_signed_small in K by plia;
rewrite ?unsigned_lit in K by plia;
lazymatch type of K with
| negb ?x = true => apply (proj1 (Bool.negb_true_iff x)) in K
| negb ?x = false => apply (proj1 (Bool.negb_false_iff x)) in K
| _ => idtac
end;
lazymatch type of K with
| (?a <? ?b) = true => apply (proj1 (Z.ltb_lt a b)) in K
| (?a <? ?b) = false => apply (proj1 (Z.ltb_ge a b)) in K
| (?a =? ?b) = true => apply (proj1 (Z.eqb_eq a b)) in K
| (?a =? ?b) = false => apply (proj1 (Z.eqb_neq a b)) in K
| (?a <=? ?b) = true => apply (proj1 (Z.leb_le a b)) in K
| (?a <=? ?b) = false => apply (proj1 (Z.leb_gt a b)) in K
| _ => idtac
end.

Lemma zbv_sub_land : forall x y, Z_to_bv 64 (x + - Z.land y 18446744073709551615) = Z_to_bv 64 (x - y).
Proof.
intros x y. apply Z_to_bv_eqm. rewrite land_ones64.
replace (x + - (y mod 2^64)) with (x - y mod 2^64) by lia. apply Zminus_mod_idemp_r.
Qed.
Lemma zbv_neg_land : forall y, Z_to_bv 64 (- Z.land y 18446744073709551615) = Z_to_bv 64 (- y).
Proof.
intros y. apply Z_to_bv_eqm. rewrite land_ones64.
replace (- (y mod 2^64)) with (0 - y mod 2^64) by lia. rewrite Zminus_mod_idemp_r. f_equal.
Qed.
Lemma zbv_eqb_signed : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
intros a b Ha Hb. rewrite bv_eqb_Z, !Z_to_bv_unsigned.
change (bv_wrap 64 a) with (a mod 2^64). change (bv_wrap 64 b) with (b mod 2^64).
destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
apply Z.eqb_neq. intros E. apply NE. rewrite <- !land_ones64 in E. apply land64_inj_signed in E; lia.
Qed.

Lemma v_div_small : forall x y, -2^63 <= x < 2^63 -> 0 < y < 2^63 ->
v_div (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.quot x y).
Proof.
intros x y Hx Hy. unfold v_div. rewrite unsigned_lit by lia.
replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold zsig. rewrite !zb_signed_small by lia. reflexivity.
Qed.

Lemma swrap32_u64_plus1 : forall e, -2^31 <= e -> e + 1 < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 e) + 1) = e + 1.
Proof.
intros e H1 H2. rewrite Z_to_bv_unsigned. change (bv_wrap 64 e) with (e mod 2^64).
rewrite X1nj.swrap32_mod64_plus. apply X1nj.swrap32_small. lia.
Qed.

Lemma swrap32_land64_plus1 : forall e, -2^31 <= e -> e + 1 < 2^31 -> bv_swrap 32 (Z.land e 18446744073709551615 + 1) = e + 1.
Proof.
intros e H1 H2. rewrite land_ones64. rewrite X1nj.swrap32_mod64_plus. apply X1nj.swrap32_small. lia.
Qed.

Lemma s32_range' : forall v, -2^31 <= s32 v < 2^31.
Proof. intros v. unfold s32. pose proof (Z.mod_pos_bound (v + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma hrep_regran {RCEIL : RunCeiling} : forall dec_rep c x h st m m' cn cb cn' cb' j16 jsk lk pg sk,
  dec_rep_frame_stmt dec_rep -> rheap_frame_stmt -> rheap_block_range_stmt -> hcx_ok c ->
  hrep dec_rep c x h st m cn cb ->
  munch [(aLOW c, aLOW c + 80)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  rw_cells rsegs m' (aLOW c) (low_cells c (set_granule h pg sk) j16 cn' cb' jsk lk) -> lk_ok h lk ->
  csize cn' = 8%nat -> csize cb' = 8%nat -> -2^63 <= pg < 2^63 ->
  hrep dec_rep c x (set_granule h pg sk) st m' cn' cb'.
Proof.
intros dec_rep c x h st m m' cn cb cn' cb' j16 jsk lk pg sk DRF RHF RBR CX HR MU WM MI LOW' LKO E1 E2 PG.
destruct HR as (_ & _ & _ & (stb & STB) & OSP & (opj & OPK) & (ogj & OGJ) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE).
assert (PURE' : hpure c x (set_granule h pg sk)).
{ destruct PURE as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD).
  unfold hpure. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
  h_packet_count h_last_granule h_stream_init h_eos h_bytes_remaining h_st h_os set_granule].
  do 15 (split; [assumption|]). split; [exact PG|]. do 5 (split; [assumption|]). exact BUD. }
pose proof CX as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB). unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof PURE as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & _).
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (ST' : stk rsegs m' (x_lo c) (hsp c)).
{ destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _). eapply stk_transport_disjoint; [| exact MU| exact WM|]; [exact ST|]. cbn. lia. }
assert (HG' : hglob c x h st m').
{ eapply hglob_frame; [exact RHF| exact RBR| exact CX| exact HG| exact MU| exact WM| | exact MI| exact ST'].
  unfold in_frame. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
unfold hrep. cbn [h_oy h_bits h_frame_size h_granule_frame_size h_nframes h_channels h_rate h_extra_headers h_speex_serialno
h_packet_count h_last_granule h_skip_samples h_stream_init h_eos h_bytes_remaining h_st h_os set_granule].
split; [exists j16, jsk, lk; split; [exact LOW'| exact LKO]|]. split; [exact E1|]. split; [exact E2|].
split. { exists stb. eapply rw_cells_agree; [exact AG| exact STB| side1]. }
split. { eapply os_piece_agree; [exact AG| exact OSP| side1| intros a Ha; cbn; unfold alloc_ceiling in Ha; lia]. }
split. { exists opj. eapply rw_cells_agree; [exact AG| exact OPK| side1]. }
split. { exists ogj. eapply rw_cells_agree; [exact AG| exact OGJ| side1]. }
split. { eapply sync_rep_agree; [exact AG| exact SY| side1|].
  intros a Ha. cbn. destruct (sy_data (h_oy h)) eqn:ED.
  - destruct (SYBLK ltac:(congruence)) as [(_ & _ & _ & B4 & _) _]. rewrite ?SYLEN in Ha. unfold alloc_ceiling in B4. lia.
  - destruct SY as (_ & _ & DAT & _). unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (_ & Eb & _). rewrite ?Eb, <- ?SYLEN in Ha. cbn in Ha. lia. }
split. { eapply bits_rep_agree; [exact AG| exact BI| exact BOK| side1|]. intros a Ha. cbn. destruct BBR as (_ & _ & _ & B4 & _). unfold alloc_ceiling in B4. lia. }
split. { exists pad. eapply rw_cells_agree; [exact AG| exact FSZ| unfold fsz_cells; side1]. }
split. { exists outb. split; [| exact LOUT]. eapply u8arr_agree; [exact AG| exact OUT|]. intros a Ha. cbn. lia. }
split. { exists hij. eapply rw_cells_agree; [exact AG| exact HI| side1]. }
split. { eapply rw_cells_agree; [exact AG| exact SAV| unfold sav_cells; side1]. }
split. { eapply dec_piece_agree; [exact DRF| exact AG| exact DEC|]. intros a Ha. cbn. unfold alloc_ceiling in Ha. lia. }
split; [exact HG'| exact PURE'].
Qed.

Section PAGE5.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation PGG := (PGG dec_rep c).
Notation PK := (PK dec_rep c).
Notation KREST fuel' := (fun o : outcome bptr => match o with
| Returned => X1qx.mret Returned
| Cont h5 => page_loopP fuel' h5 end).

#[using="DRF RHF RBR CX"] Lemma pg_join_pk : forall (Q : outcome bptr -> PState -> machine_state -> Prop) fuel' h st x m m' cn cb
(j16 jsk lk : list byte) (pg skip nbr brem0 : Z)
(x1 t0 t1 t2 s0w s1w s3w s5w s8w a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(forall h4 st4 ms4, PK h4 st4 ms4 -> h_oy h4 = h_oy h -> h_bytes_remaining h4 = h_bytes_remaining h ->
implM rsegs (X1qx.mbind (packet_loopP (packet_fuel (h_os h4)) h4 0) (KREST fuel')) st4 Q ms4) ->
frm0 fc -> h_stream_init h = 1 -> h_eos h = 0 -> os_body_returned (h_os h) = 0 ->
hrep dec_rep c x h st m cn cb -> low_ok h nbr brem0 ->
munch [(aLOW c, aLOW c + 80)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
rw_cells rsegs m' (aLOW c) (low_cells c (set_granule h pg skip) j16 (C8 (wz nbr)) (C8 (wz brem0)) jsk lk) -> lk_ok h lk ->
-2^63 <= pg < 2^63 ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((X1qx.mbind (packet_loopP (packet_fuel (h_os (set_granule h pg skip))) (set_granule h pg skip) 0) (KREST fuel')) st)
(epost (fun p ms2 => Q (fst p) (snd p) ms2)) ms1)
(MS (hregs c h (a_S x) s0w s1w s3w s5w s8w (wz (h_speex_serialno h)) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c3b8) fc None m' (seg_rom rsegs)).
Proof.
intros Q fuel' h st x m m' cn cb j16 jsk lk pg skip nbr brem0 x1 t0 t1 t2 s0w s1w s3w s5w s8w a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc
KP FRM SI E0 OBR HR LOK MU WM MI LOW LKO PGR.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
pose proof PURE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCR & _).
pose proof CX as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB). unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof LOW as [[WF0 _] _]. unfold low_cells in WF0. cbn in WF0.
unfold low_cells, wz in LOW. unfold hregs, wz.
zstep. zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => set (m2 := mx) in * end. clearbody m2.
assert (LOW2 : rw_cells rsegs m2 (aLOW c) (low_cells c (set_granule h pg skip) j16 (C8 (wz nbr)) (C8 (wz brem0)) (le8 a0 ++ le8 a3) lk)).
{ unfold low_cells, wz. eapply X0pw.rw_cells_recast; [exact LOW| | cbn; rewrite <- ?app_assoc; reflexivity| reflexivity].
  cbn. rewrite ?length_app, ?length_le8. cbn in WF0 |- *. repeat split; try reflexivity; try tauto; lia. }
pose proof (hrep_regran dec_rep c x h st m m2 cn cb (C8 (wz nbr)) (C8 (wz brem0)) j16 (le8 a0 ++ le8 a3) lk pg skip
DRF RHF RBR CX HR MU WM MI LOW2 LKO eq_refl eq_refl PGR) as HR2.
apply KP; [| reflexivity| reflexivity].
unfold X1hg.PK. exists x1, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m2, x, nbr, brem0, 0, s0w, s3w, s5w, s8w.
split; [unfold hregs, wz, A_PKT; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers set_granule]; reflexivity|].
split; [exact FRM|]. cbn [h_stream_init h_eos h_packet_count h_os set_granule]. split; [exact SI|]. split; [exact E0|]. split; [exact HR2|].
split; [unfold low_ok in *; cbn [h_bytes_remaining set_granule]; exact LOK|].
split; [lia| intros _; exact OBR].
Qed.

#[using="DRF RHF RBR CX"] Lemma pg_join_cln : forall (Q : outcome bptr -> PState -> machine_state -> Prop) h st x m m' cn cb cn' cb'
(j16 jsk lk : list byte) (pg skip : Z)
(x1 t0 t1 t2 s0w s1w s3w s4w s5w s6w s7w s8w s9w s10w s11w a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(forall h' st' ms', CLN dec_rep c h' st' ms' ->
implM rsegs (X1qx.mbind (cleanupP h') (fun _ => X1qx.mret Returned)) st' Q ms') ->
frm0 fc -> h_stream_init h = 1 ->
hrep dec_rep c x h st m cn cb ->
munch [(aLOW c, aLOW c + 80)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
rw_cells rsegs m' (aLOW c) (low_cells c (set_granule h pg skip) j16 cn' cb' jsk lk) -> lk_ok h lk ->
csize cn' = 8%nat -> csize cb' = 8%nat -> -2^63 <= pg < 2^63 ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (cleanupP h) (fun _ => X1qx.mret Returned)) st)
(epost (fun p ms2 => Q (fst p) (snd p) ms2)) ms1)
(MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 s0w s1w a0 a1 a2 a3 a4 a5 a6 a7
(wz (a_S x)) s3w s4w s5w s6w s7w s8w s9w s10w s11w t3 t4 t5 t6)
F (wz 0x1c778) fc None m' (seg_rom rsegs)).
Proof.
intros Q h st x m m' cn cb cn' cb' j16 jsk lk pg skip x1 t0 t1 t2 s0w s1w s3w s4w s5w s6w s7w s8w s9w s10w s11w a0 a1 a2 a3 a4 a5 a6 a7
t3 t4 t5 t6 F fc KC FRM SI HR MU WM MI LOW LKO E1 E2 PGR.
pose proof (hrep_regran dec_rep c x h st m m' cn cb cn' cb' j16 jsk lk pg skip DRF RHF RBR CX HR MU WM MI LOW LKO E1 E2 PGR) as HR2.
clear HR MU WM LOW.
pose proof CX as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB). unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
unfold wz.
do 5 zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
change (cleanupP h) with (cleanupP (set_granule h pg skip)).
apply KC. unfold CLN. sf_eexists 23%nat. exists F, fc, m', x, cn', cb'.
split; [cbn [h_stream_init set_granule]; rewrite SI; reflexivity|]. split; [exact FRM| exact HR2].
Qed.

#[using="Type"] Lemma granule_step_sel : forall fs gfs nf lg pg nbp eos,
(if (nbp * gfs * nf <? pg - lg) || (INT64_MAX ÷ 640 - nbp * gfs * nf <? - (pg - lg)) || (INT64_MAX ÷ 640 <? nbp * gfs * nf - (pg - lg)) then None
else if s32 (fs * (nbp * gfs * nf - (pg - lg)) ÷ gfs) =? INT_MIN then None
else Some (if negb (eos =? 0) then - s32 (fs * (nbp * gfs * nf - (pg - lg)) ÷ gfs) else s32 (fs * (nbp * gfs * nf - (pg - lg)) ÷ gfs)))
= match granule_sel fs gfs nf lg pg nbp with None => None | Some skip => Some (if negb (eos =? 0) then - skip else skip) end.
Proof.
intros fs gfs nf lg pg nbp eos. unfold granule_sel. cbv zeta.
destruct (_ || _ || _); [reflexivity|]. destruct (s32 _ =? INT_MIN); reflexivity.
Qed.

#[using="DRF RHF RBR CX"] Lemma page_granule : forall (Q : outcome bptr -> PState -> machine_state -> Prop) fuel' h og st ms,
PGG h og st ms ->
(forall h' st' ms', CLN dec_rep c h' st' ms' ->
implM rsegs (X1qx.mbind (cleanupP h') (fun _ => X1qx.mret Returned)) st' Q ms') ->
(forall h4 st4 ms4, PK h4 st4 ms4 -> h_oy h4 = h_oy h -> h_bytes_remaining h4 = h_bytes_remaining h ->
implM rsegs (X1qx.mbind (packet_loopP (packet_fuel (h_os h4)) h4 0) (KREST fuel')) st4 Q ms4) ->
(forall h4 st4 ms4, PGN dec_rep c h4 st4 ms4 -> h_oy h4 = h_oy h -> h_bytes_remaining h4 = h_bytes_remaining h ->
implM rsegs (page_loopP fuel' h4) st4 Q ms4) ->
implM rsegs (page_restP fuel' (page_header (h_oy h) og) h) st Q ms.
Proof.
intros Q fuel' h og st ms PG KC KP KN.
destruct PG as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & s3w & s5w & s8w & OP & -> & FRM & SI1 & HRX & LOK & POK & NN & OBR).
pose proof CX as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB).
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HRX as ((j16 & jsk & lk & LOW & LKO) & C1 & C2 & _ & _ & _ & (OG & OGS) & SY & _ & (pad & FSZ) & _ & _ & _ & _ & HG & PURE).
pose proof HG as (_ & _ & _ & _ & _ & _ & _ & MI & _).
pose proof PURE as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD).
pose proof SYOK as (SYI2 & SYST & SYNUL). pose proof SYI2 as [SYI _].
assert (EOSB : 0 <= h_eos h <= 1) by lia. assert (SIB : 0 <= h_stream_init h <= 1) by lia.
assert (NUL : sy_data (h_oy h) = None -> a_D x = 0 /\ sy_storage (h_oy h) = 0).
{ intros ED. destruct SY as (_ & _ & DAT & _). unfold sync_data in DAT. rewrite ED in DAT. destruct DAT as (-> & _ & _ & ->). auto. }
assert (SYR : a_D x + sy_storage (h_oy h) <= alloc_ceiling /\ 0 <= a_D x).
{ destruct (sy_data (h_oy h)) eqn:ED.
- destruct (SYBLK ltac:(congruence)) as [(B1 & _ & _ & B4 & _) _]. lia.
- destruct (NUL eq_refl) as [-> ->]. unfold alloc_ceiling. lia. }
destruct SYR as [SYR D0].
pose proof (page_hs _ _ _ _ _ _ SY SYI POK NN) as (HS & HBS & LHS & LBS & EHS & EBS & HL27 & NSEG & PG0 & PGE & BL0).
set (hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) (a_sybytes x))) in *.
unfold page_restP, granule_step.
remember (ogg_page_granulepos (page_header (h_oy h) og)) as pgr eqn:Epgr.
remember (ogg_page_packets (page_header (h_oy h) og)) as pnp eqn:Epnp.
remember (ogg_page_eos (page_header (h_oy h) og)) as peos eqn:Epeos.
assert (PGR : -2^63 <= pgr < 2^63) by (rewrite Epgr; apply s64_range').
assert (PNPR : 0 <= pnp <= 255) by (rewrite Epnp, <- EHS; apply ogg_page_packets_range; exact NSEG).
unfold low_cells, wz in LOW. unfold fsz_cells, wz in FSZ.
pose proof (munch_refl [(aLOW c, aLOW c + 80)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold implM. iprefix. unfold hregs, wz.

zstep. zstep.
callx (eapply ogg_page_granulepos_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
rewrite EHS, <- Epgr in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.
zstep.

zstep. zstep.
callx (eapply ogg_page_packets_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| lia| exact MI]).
rewrite EHS, <- Epnp in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.
zstep.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in *; clearbody m1 end.
assert (PGNJ : forall (skip : Z) (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y28 y29 y30 y31 : word),
h_eos h = 1 ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs)
((X1qx.mbind (packet_loopP (packet_fuel (h_os (set_granule h pgr skip))) (set_granule h pgr skip) 0) (KREST fuel')) st)
(epost (fun p ms2 => Q (fst p) (snd p) ms2)) ms1)
(MS (hregs c h (a_S x) y8 (wz brem0) y19 y21 y24 (wz (h_speex_serialno h)) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)
F (wz 0x1c710) fc None m1 (seg_rom rsegs))).
{ intros skip y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y28 y29 y30 y31 E1.
  assert (LOWg : rw_cells rsegs m1 (aLOW c) (low_cells c (set_granule h pgr skip) j16 (C8 (wz nbr)) (C8 (wz brem0)) jsk lk))
    by (unfold low_cells, wz; exact LOW).
  pose proof (hrep_regran dec_rep c x h st m m1 _ _ (C8 (wz nbr)) (C8 (wz brem0)) j16 jsk lk pgr skip
    DRF RHF RBR CX (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX) MU WM MI LOWg LKO eq_refl eq_refl PGR) as HR4.
  apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm st Q msx) end.
  unfold packet_fuel. cbn [packet_loop]. cbn [h_eos set_granule]. rewrite E1. cbn [Z.eqb negb].
  apply implM_retb. apply KN; [| reflexivity| reflexivity].
  unfold PGN. exists y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, F, fc, m1, x, nbr, brem0, y8, y19, y21, y24.
  split; [unfold hregs, wz, A_PAGEN; cbn [h_nframes h_last_granule h_packet_count h_speex_serialno h_channels h_eos h_stream_init h_extra_headers set_granule]; reflexivity|].
  split; [exact FRM|]. split; [exact SI1|]. split; [exact HR4| unfold low_ok in *; cbn [h_bytes_remaining set_granule]; exact LOK]. }

zstep. if_cases BA; scond BA.
-
replace (0 <? pgr) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
zstep. zstep. zstep. if_cases BB; scond BB.
+
replace (pgr <? -1) with true by (symmetry; apply Z.ltb_lt; lia).
eapply (pg_join_cln Q h st x m m1 _ _ _ _ j16 jsk lk pgr 0); [exact KC| exact FRM| exact SI1| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| reflexivity| reflexivity| exact PGR].
+ replace (pgr <? -1) with false by (symmetry; apply Z.ltb_ge; lia).
zstep. zstep. if_cases BS; scond BS.
*
apply PGNJ; lia.
* eapply (pg_join_pk Q fuel' h st x m m1 _ _ j16 jsk lk pgr); [exact KP| exact FRM| exact SI1| lia| exact OBR| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact LOK| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| exact PGR].
-
replace (0 <? pgr) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
zstep. rewrite sx32_small by (unfold X1nj.int31; lia). zstep. if_cases BC; scond BC.
+
replace (h_frame_size h =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
replace (pgr <? -1) with false by (symmetry; apply Z.ltb_ge; lia).
zstep. zstep. zstep. if_cases BB; scond BB; [exfalso; lia|].
zstep. zstep. if_cases BS; scond BS.
*
apply PGNJ; lia.
* eapply (pg_join_pk Q fuel' h st x m m1 _ _ j16 jsk lk pgr); [exact KP| exact FRM| exact SI1| lia| exact OBR| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact LOK| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| exact PGR].
+ replace (h_frame_size h =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
destruct ((0 <? h_last_granule h) || (pgr <? INT64_MAX + h_last_granule h)) eqn:CND; cbn [orb].
*
assert (CNDP : 0 < h_last_granule h \/ pgr < INT64_MAX + h_last_granule h).
{ apply Bool.orb_true_iff in CND. destruct CND as [K|K]; [left; apply Z.ltb_lt; exact K| right; apply Z.ltb_lt; exact K]. }
lazymatch goal with |- evt ?sg ?P (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 _ _ ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20 ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) ?FF _ ?fcc ?rv ?mm ?ro) =>
  assert (GBLK : forall a1w a2w : word, evt sg P (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 a1w a2w r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) FF (Z_to_bv 64 0x1c2d0) fcc rv mm ro)) end.
{ intros a1w a2w. rewrite granule_step_sel.
  destruct (granule_sel (h_frame_size h) (h_granule_frame_size h) (h_nframes h) (h_last_granule h) pgr pnp) as [skip|] eqn:GS.
  - eapply granule_arith; [plia| plia| exact LOW| exact MI| exact PNPR| lia| exact GFS| exact NFR| lia| exact LGR| exact CNDP| intros GN; rewrite GS in GN; discriminate| ].
    intros skip' GS' y10 y11 y12 y13 y14 y15. rewrite GS in GS'. injection GS' as <-.
    zstep. zstep.
    callx (eapply ogg_page_eos_spec with (G := aOG c) (D := a_D x) (og := og) (hs := hs); [reflexivity| exact OG| exact HS| lia| exact MI]).
    rewrite EHS, <- Epeos in POST. lazymatch type of POST with ?v = _ => subst v end. unfold wz.
    zstep. if_cases BE; scond BE.
    + zstep. zstep. zstep. zstep. if_cases BS; scond BS.
      * eapply (pg_join_pk Q fuel' h st x m m1 _ _ j16 jsk lk pgr); [exact KP| exact FRM| exact SI1| lia| exact OBR| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact LOK| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| exact PGR].
      * zstep. apply PGNJ; lia.
    + zstep. zstep. zstep. zstep. if_cases BS; scond BS.
      * eapply (pg_join_pk Q fuel' h st x m m1 _ _ j16 jsk lk pgr); [exact KP| exact FRM| exact SI1| lia| exact OBR| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact LOK| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| exact PGR].
      * zstep. apply PGNJ; lia.
  - eapply granule_arith; [plia| plia| exact LOW| exact MI| exact PNPR| lia| exact GFS| exact NFR| lia| exact LGR| exact CNDP| | intros skip' GS'; rewrite GS in GS'; discriminate].
    intros _ y8 y10 y11 y12 y13 y14 y15.
    eapply (pg_join_cln Q h st x m m1 _ _ _ _ j16 jsk lk pgr 0); [exact KC| exact FRM| exact SI1| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| reflexivity| reflexivity| exact PGR]. }
zstep. if_cases BD; scond BD; [apply GBLK|].
zstep. zstep. zstep. zstep. zstep. if_cases BF; scond BF; [exfalso; unfold INT64_MAX in *; lia| apply GBLK].
* replace (pgr <? -1) with false by (symmetry; apply Z.ltb_ge; lia).
apply Bool.orb_false_iff in CND. destruct CND as [CN1 CN2]. apply Z.ltb_ge in CN1. apply Z.ltb_ge in CN2.
zstep. if_cases BD; scond BD; [exfalso; lia|].
zstep. zstep. zstep. zstep. zstep. if_cases BF; scond BF; [|exfalso; unfold INT64_MAX in *; lia].
zstep. zstep. if_cases BS; scond BS.
--
apply PGNJ; lia.
-- eapply (pg_join_pk Q fuel' h st x m m1 _ _ j16 jsk lk pgr); [exact KP| exact FRM| exact SI1| lia| exact OBR| exact (hrepx_hrep _ _ _ _ _ _ _ _ _ _ HRX)| exact LOK| exact MU| exact WM| exact MI| unfold low_cells, wz; exact LOW| exact LKO| exact PGR].
Qed.
End PAGE5.
