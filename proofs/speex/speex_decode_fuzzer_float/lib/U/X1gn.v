(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1il X1im X1ip X1in X1ja X1iu X1j8 X1j4 X1j9 X1it.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section H0.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis RCAL : bits_calloc_stmt.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation POSTQ := (fun (r : Z) st ms => harness_post (x_ra c) (x_sp c) (x_gp c) tpv (x_s0 c) (x_s1 c) (x_s2 c) (x_s3 c) (x_s4 c) (x_s5 c)
(x_s6 c) (x_s7 c) (x_s8 c) (x_s9 c) (x_s10 c) (x_s11 c) (x_st0 c) (x_LB0 c) (x_AB c) (x_lo c) (x_m0 c) r st ms).

#[using="CX"] Lemma ret0 : forall (st : PState) (LBc : list block) (x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (errv : word),
frm0 fc -> RHEAP st LBc m -> Permutation LBc (x_LB0 c) ->
stk rsegs m (x_lo c) (aSAV c) -> rw_cells rsegs m (aSAV c) (sav_cells c) ->
rw_cells rsegs m RERRNO [C4 errv] -> rauxv_ok m (x_AB c) -> mem_inv rsegs m -> stderr_wfile m ->
pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m -> ps_so st = ps_so (x_st0 c) ->
evt rsegs (POSTQ 0 st)
(MS (mkR x1 (wz (hsp c)) (x_gp c) tpv t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz A_RET0) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros FRM HP PERM ST SAV ERR AUX MI SEW PE SO.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
unfold sav_cells in SAV. unfold A_RET0, wz.
zstep. zstep. zstep. zstep.
do 13 zstep. zstep. zstep.
apply evt_done. unfold harness_post.
release_frame SAV ST (usp c).
sf_eexists 14%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (m) | exact (errv) | ] | sf_fb; exists F, fc, m, errv ]. split; [reflexivity|].
split; [lia|]. split; [exact FRM|]. split; [exact MI|]. split; [exact ST|].
split; [rewrite unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR|].
split; [exact AUX|]. split; [exact PE|]. split; [eapply RHEAP_perm; [exact HP| exact PERM]|]. split; [exact SEW| exact SO].
Qed.

Definition h0 (bits : bits_st bptr) : hstate bptr :=
mkH ogg_sync_init stream_zero bits None 0 0 0 0 2 0 (-1) 0 0 (-1) 0 0 (zlength (x_payload c)).

Notation HK := (fun (ob : option (bits_st bptr)) =>
match ob with
| None => X1qx.munr
| Some bits =>
X1qx.mbind (chunk_loop raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning
bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M
(chunk_fuel (zlength (x_payload c))) (x_payload c) (h0 bits))
(fun o => match o with
| Returned => X1qx.mret 0
| Cont h => X1qx.mbind (cleanup raw_free (St:=PState) h) (fun _ => X1qx.mret 0) end)
end).

#[using="Type"] Lemma fuzz_one_eq : fuzz_one (x_payload c) =
if MAX_FUZZ_SIZE <? zlength (x_payload c) then X1qx.mret 0
else X1qx.mbind (speex_bits_init raw_calloc) HK.
Proof. reflexivity. Qed.

#[using="RCAL RFREE RHF RBR CX"] Lemma h0_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (errv : word),
(forall h st ms, CUTC dec_rep c h st ms -> h = h0 (h_bits h) ->
implM rsegs (HK (Some (h_bits h))) st POSTQ ms) ->
RHEAP (x_st0 c) (x_LB0 c) (x_m0 c) ->
bytes_at rsegs (x_m0 c) (x_P c) (to_bytes (x_payload c)) ->
rtables_pristine (x_m0 c) -> stderr_wfile (x_m0 c) -> rauxv_ok (x_m0 c) (x_AB c) ->
stk rsegs (x_m0 c) (x_lo c) (usp c) ->
rw_cells rsegs (x_m0 c) RERRNO [C4 errv] -> mem_inv rsegs (x_m0 c) -> frm0 fc ->
implM rsegs (fuzz_one (x_payload c)) (x_st0 c) POSTQ
(MS (mkR (x_ra c) (x_sp c) (x_gp c) tpv t0 t1 t2 (x_s0 c) (x_s1 c) (wz (x_P c)) (wz (zlength (x_payload c))) a2 a3 a4 a5 a6 a7
(x_s2 c) (x_s3 c) (x_s4 c) (x_s5 c) (x_s6 c) (x_s7 c) (x_s8 c) (x_s9 c) (x_s10 c) (x_s11 c) t3 t4 t5 t6)
F (wz RFUZZ_ENTRY) fc None (x_m0 c) (seg_rom rsegs)).
Proof.
intros until errv. intros KONT HP PAY TP SEW AUX ST ERR MI FRM.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (bytes_at_bound _ _ _ _ PAY) as PB. rewrite to_bytes_length in PB.
pose proof (pay_range RBR c _ _ _ CX HP ltac:(auto)) as PRANGE.
rewrite fuzz_one_eq. unfold RFUZZ_ENTRY, wz.
pose proof (munch_refl [(usp c + -8832, usp c)] (x_m0 c)) as MU. pose proof (wmono_refl rsegs (x_m0 c)) as WM.
change (id (bytes_at rsegs (x_m0 c) (x_P c) (to_bytes (x_payload c)))) in PAY.
change (id (rw_cells rsegs (x_m0 c) RERRNO [C4 errv])) in ERR.
unfold implM. iprefix.
zstep.

carve_frame 104%nat ST. rename FR into SAV.
carve_frame 48%nat ST. rename FR into HI.
destruct (stk_carve_u8 _ _ _ 5968 ST ltac:(lia) ltac:(lia)) as [ST' (j9c & OUT2 & L9c)]. clear ST. rename ST' into ST.
replace (usp c + -152 - 5968) with (usp c + -6120) in ST, OUT2 by lia.
carve_frame 8%nat ST. rename FR into PROBE.
destruct (stk_carve_u8 _ _ _ 2024 ST ltac:(lia) ltac:(lia)) as [ST' (j9a & OUT1 & L9a)]. clear ST. rename ST' into ST.
replace (usp c + -6128 - 2024) with (usp c + -8152) in ST, OUT1 by lia.
carve_frame 8%nat ST. rename FR into FSZ.
carve_frame 48%nat ST. rename FR into BIJ.
carve_frame 32%nat ST. rename FR into OYJ.
carve_frame 32%nat ST. rename FR into OGJ.
carve_frame 48%nat ST. rename FR into OPK.
carve_frame 408%nat ST. rename FR into OSJ.
carve_frame 24%nat ST. rename FR into STB.
carve_frame 80%nat ST. rename FR into LOW.

do 13 zstep.

zstep. zstep. replace (usp c + -2032 + - (4096)) with (usp c + -6128) by lia.
lstep. zstep. zstep.
destruct (out_merge _ _ _ _ _ _ _ OUT1 L9a PROBE OUT2 L9c ltac:(lia) ltac:(lia)) as (outb & OUT & LOUT). clear OUT1 OUT2 PROBE L9a L9c j9a j9c.

zstep. zstep. lstep. do 8 zstep. lstep. lstep. lstep. lstep.

zstep.
if_cases K; zify_cond K; rewrite land64 in K by (unfold zlength in *; lia).
{
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm (x_st0 c) POSTQ msx) end.
replace (MAX_FUZZ_SIZE <? zlength (x_payload c)) with true by (symmetry; apply Z.ltb_lt; unfold MAX_FUZZ_SIZE; lia).
apply implM_ret.
release_frame LOW ST (aSTEREO c). release_frame STB ST (aOS c). release_frame OSJ ST (aOP c). release_frame OPK ST (aOG c).
release_frame OGJ ST (aOY c). release_frame OYJ ST (aBITS c). release_frame BIJ ST (aFSZ c). release_frame FSZ ST (aOUT c).
apply rw_cells_of_u8arr in OUT. release_frame OUT ST (aCBK c). release_frame HI ST (aSAV c).
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ERR.
eapply ret0; [exact FRM| | apply Permutation_refl| exact ST| exact SAV| | | exact MI | | | reflexivity].
- eapply RHF; [exact HP| exact MU| exact WM|]. apply Forall_cons; [|apply Forall_nil]. left. cbn [fst]. lia.
- eapply rw_cells_agree; [exact AG| exact ERR| side1].
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil].
- eapply stderr_wfile_agree; [exact AG| side1| exact SEW].
- eapply (pres_except_frame RBR c _ _ _ _ _ _ CX HP); [auto| apply pres_except_refl| exact AG|].
apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }

replace (MAX_FUZZ_SIZE <? zlength (x_payload c)) with false by (symmetry; apply Z.ltb_ge; unfold MAX_FUZZ_SIZE; lia).
zstep. zstep.
callx (eapply ogg_sync_init_spec with (A := aOY c); [reflexivity| lia| exact OYJ| assumption]).
rename POST into SY.

zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm (x_st0 c) POSTQ msx) end.

lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => set (mA := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold id in ERR, PAY.
assert (HP1 : RHEAP (x_st0 c) (x_LB0 c) mA).
{ eapply RHF; [exact HP| exact MU| exact WM|]. apply Forall_cons; [|apply Forall_nil]. left. cbn [fst]. lia. }
assert (ERR1 : rw_cells rsegs mA RERRNO [C4 errv]) by (eapply rw_cells_agree; [exact AG| exact ERR| side1]).
assert (AUX1 : rauxv_ok mA (x_AB c)).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
assert (SEW1 : stderr_wfile mA) by (eapply stderr_wfile_agree; [exact AG| side1| exact SEW]).
assert (TP1 : rtables_pristine mA) by (eapply rtables_pristine_agree; [exact AG| side1| exact TP]).
assert (PE1 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) mA).
{ eapply (pres_except_frame RBR c _ _ _ _ _ _ CX HP); [auto| apply pres_except_refl| exact AG|]. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
assert (PAY1 : bytes_at rsegs mA (x_P c) (to_bytes (x_payload c))) by (eapply (pay_keep c _ _ _ CX AG PAY); intros NE IN; side1).
lazymatch goal with MIx : mem_inv rsegs mA |- _ => rename MIx into MIA end.
clearbody mA. clear AG MU WM HP ERR AUX SEW TP PAY.
eapply implM_bind.
{ eapply implM_leaves.
eapply (speex_bits_init_spec RCAL RHF RBR) with (A := aBITS c) (lo := x_lo c) (B := x_AB c) (LB := x_LB0 c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ exact HP1 | exact AUX1 | exact ST | exact MIA | exact BIJ | reflexivity | lia
| unfold RATP; rewrite unsigned_lit by lia; exact ERR1
| unfold BITS_INIT_STACK, BITS_CALLOC_STACK; lia
| clear - SP16; Z.div_mod_to_equations; lia ]. }
cbv beta. intros ob st1 ms1 [PO LEAF].
first [ sf_destruct 26%nat PO as y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 m1 errv1 -> MI1 ST1 ERR2 AUX2 PEc EFA ESO RES | sf_fb; destruct PO as (y0 & y1 & y2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m1 & errv1 & -> & MI1 & ST1 & ERR2 & AUX2 & PEc & EFA & ESO & RES) ].
rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia. rewrite ?(unsigned_lit (aLOW c)) in PEc by lia.
unfold RATP in ERR2. rewrite ?unsigned_lit in ERR2 by lia. change (0x4d450 + -164) with RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 0x1c1c4)) with (Z_to_bv 64 0x1c1c4) by (symmetry; rpc).
pose proof (agree_of_pres_except _ _ _ _ PEc) as AG. clear BIJ ERR1. xport AG side1.
assert (PE2 : pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m1).
{ eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP1); [auto| exact PE1| exact AG|]. intros a Hc Hout Hx. cbn beta. split; [| cbn; lia].
eapply hclient_mono; [| exact Hc]. auto. }
clear AG PE1 HP1 AUX1 MIA.
destruct ob as [bits|].
-
first [ sf_destruct 6%nat RES as Dc HP2 BR SMALL BREP BOK | sf_fb; destruct RES as (Dc & HP2 & BR & SMALL & BREP & BOK) ].
pose proof (bits_init_leaf _ _ _ LEAF) as (OWN & BSZ & _).
set (X := HAX ((sb_chars bits, Dc, 2000) :: x_LB0 c) 0 [] 0 0 0 0 0 0 [] [] [] [] Dc 0 []).
assert (HG : hglob c X (h0 bits) st1 m1).
{ split; [exact HP2|]. split. { unfold owned, X, h0; cbn. rewrite BSZ. apply Permutation_refl. }
split; [exact PAY1|]. split; [exact TP1|]. split; [exact SEW1|]. split; [exists errv1; exact ERR2|].
split; [exact AUX2|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PE2| exact ESO]. }
clear HP2 PAY1 TP1 SEW1 ERR2 AUX2 PE2.
pose proof (munch_refl [(aLOW c, aLOW c + 80)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
pose proof BREP as ((rj & Lrj & OBJ) & _ & SIDE). unfold bits_cells in OBJ.
pose proof SIDE as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ Dpos _ | sf_fb; destruct sfP_ as (_ & _ & Dpos & _) ].
unfold implM. iprefix.

clear OBJ.
lstep. zstep. zstep. lstep. do 6 zstep.
apply evt_done. apply (KONT (h0 bits) st1); [| reflexivity].

lazymatch goal with |- CUTC _ _ _ _ (MS _ _ _ _ _ ?mx _) => set (mB := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (HG' : hglob c X (h0 bits) st1 mB).
{ eapply (hglob_frame RHF RBR c X (h0 bits) st1 m1 mB); [exact CX| exact HG| exact MU| exact WM| | assumption| assumption].
unfold in_frame. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
xport AG side1. clear MU WM AG HG.
unfold CUTC. sf_eexists 16%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (mB) | exact (X) | ] | sf_fb; exists F, fc, mB, X ].
lazymatch goal with LOWx : rw_cells rsegs mB (aLOW c) [CB 48 ?ja; C8 _; C8 _; C8 _; CB 4 ?jl; C4 _] |- _ =>
apply (rw_cells_split_CB rsegs _ _ [] 48 ja _ [16; 8; 8; 16]%nat) in LOWx; [| reflexivity];
cbn [app mk_CB_cells] in LOWx;
do 5 eexists end.
split; [reflexivity|]. split; [exact FRM|].
unfold hrep.
split. { sf_eexists 3%nat. split; [unfold low_cells, h0; cbn [h_granule_frame_size h_last_granule h_rate]; eassumption|].
unfold lk_ok, h0; cbn [h_st]. intros HH; exfalso; apply HH; reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
split. { lazymatch goal with STBx : rw_cells rsegs mB (aSTEREO c) ?cs |- _ => destruct (rw_cells_forget rsegs mB (aSTEREO c) cs STBx) as [stb STB']; exists stb; exact STB' end. }
split. { unfold os_piece, h0; cbn. split; [eexists; eassumption|]. repeat split; reflexivity. }
split; [eexists; eassumption|]. split; [eexists; eassumption|].
split; [assumption|]. split; [assumption|].
split; [eexists; unfold fsz_cells, h0; cbn [h_frame_size]; eassumption|].
split; [eexists; split; eassumption|]. split; [eexists; eassumption|]. split; [assumption|].
split; [cbn; split; reflexivity|].
split; [exact HG'|].

unfold hpure, h0, X; cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow zlength alloc_ceiling rblock_range hsync_ok bits_ok].
rewrite ?OWN, ?BSZ.
split; [apply hsync_init_ok|]. split; [exact BOK|]. split; [reflexivity|]. split; [intros HH; exfalso; apply HH; reflexivity|].
split; [reflexivity|]. split; [exact BR|].
unfold MAX_FUZZ_SIZE, hbudget, hconsumed, hpend. cbn -[Z.le Z.lt Z.add Z.sub Z.mul Z.pow zlength].
repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity; unfold zlength; lia.
-
cbv beta iota. apply implM_unr.
Qed.
End H0.
