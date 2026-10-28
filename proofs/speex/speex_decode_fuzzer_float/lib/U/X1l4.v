(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1ka X1kd X1k9 X1l0 X1l1 X1l2 X1l3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd X1ei.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1oc X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.
Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section B4.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis EARGV : argv = [arg0; arg1].
Hypothesis HT : 0 < TID < 4194304.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FKP : rfree_keeps_ptr_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.

Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
Notation LO' := (LO sp0).
Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
Notation FRAME' mm := (exists pad, MFRAME sp0 argv mm pad S7 S6 S5 S4).
Notation RDINV' := (RDINV sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
Notation POSTLOOP' := (POSTLOOP sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
Ltac hyps := first [exact VSP | exact HCEIL | exact VARGV | exact VENVP | exact EARGV | exact HT | exact RHF | exact RND | exact RBD | exact RBR | exact MALLOC | exact FREE | exact FKP | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
(GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTG) x23 t3 t4 t5 t6 F fc mm).

Definition RDONE (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
(A cap P1v fd : Z) (DATA junk : list byte) (errv : word),
ms = RST 0x1bd84 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
/\ content = map bv_unsigned DATA
/\ BUF mm s bufp A cap DATA junk
/\ FRAME' mm /\ BASE' mm /\ ADP0 mm /\ rw_cells rsegs mm RERRNO [C4 errv] /\ frm0 fc /\ is_mkF F.

Definition POSTB (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
match r with
| RdExit => rat_exit 2 s ms
| RdDone b c => RDONE b c s ms
end.

#[using="Type"] Lemma implM_fold_ : forall {A} (c : @X1qx.M PState A) (s : PState) (Q : A -> PState -> machine_state -> Prop) (ms : machine_state),
implM rsegs c s Q ms -> impl rsegs (at_node rsegs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros A c s Q ms H. exact H. Qed.

#[using="arg0 VSP HCEIL VARGV VENVP EARGV HT RHF RND RBD MALLOC FREE FKP FPR FWX SWF FWR TOW"] Lemma main_read_all : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem) (stg : list byte),
FRAME' mm -> BASE' mm -> RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] mm -> ADP0 mm -> rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] -> frm0 fc -> is_mkF F ->
rw_cells rsegs mm RSTG [CB (Z.to_nat 65536) stg] ->
implM rsegs (read_all io_diag raw_malloc raw_free RSTAGE_ubsan (map bv_unsigned arg1)) (ps_init alloc_ceiling (reservedZ rsegs)) POSTB
(MS (mkR (Z_to_bv 64 0x310d0) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
(Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x1bc88) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bcb8) fc None mm (seg_rom rsegs)).
Proof.
intros until stg. intros FR BA HP0 CJ ERR FRM MKF SG.
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
pose proof BA as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST. unfold RERRNO in ERR. destruct FR as [pad FR]. unfold MFRAME in FR. unfold RSTG in SG.
pose proof VARGV as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ ARGLEN NONUL _ | sf_fb; destruct sfP_ as (_ & _ & ARGLEN & NONUL & _) ].

first [ pose proof (argv_cstring sp0 argv envp uid hw rnd mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia)) as sfP_; sf_destruct 7%nat sfP_ as P1v slack1 HP1 P1LO P1HI STR1 SLK1 | sf_fb; destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia)) as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1) ]. unfold str_base, struct_size, argc, envc in P1LO.
destruct (stack_pieces sp0 argv envp uid hw rnd mm IMG) as (_ & ARGVP & _).
assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
assert (STR1' : bytes_at rsegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
{ change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
pose proof (RHEAP_ssp _ _ _ HP0) as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
unfold read_all. unfold implM. iprefix.
pose proof (u64ro_read mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep.
remember READ_FUEL as rf eqn:Erf. clear Erf.
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm (ps_init alloc_ceiling (reservedZ rsegs)) POSTB msx) end.
replace (map (Z_to_bv 8) (map bv_unsigned arg1)) with arg1 by (symmetry; apply zbytes_map_unsigned').
eapply implM_bind.
{ eapply implM_of_enode.
eapply open_spec with (lo := usp0 - 8388608) (errv := Z_to_bv 64 0) (canary := run_canary);
[ rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST
| rewrite (unsigned_lit P1v) by lia; exact STR1'
| unfold RATP; rewrite (unsigned_lit 316496) by lia; exact ERR
| exact G1 | exact G2 | exact MI | reflexivity | exact A1NN | ..].
all: unfold RATP, X1gj.got_ssp, X1gj.ssp_guard; rewrite ?(unsigned_lit 316496) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; lia. }
cbv beta. intros r s' ms' [PO ->].
first [ sf_destruct 25%nat PO as u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 -> MUc WMc MI1 ST1 ERR1 _ _ _ FDR | sf_fb; destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR) ].
unfold RATP in MUc, ERR1. rewrite ?(unsigned_lit 316496) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit 316496) in ERR1 by lia. change (316496 + -164) with 316332 in MUc, ERR1.
transport_after_call rsegs mm m1 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x1bcc8)) with (Z_to_bv 64 0x1bcc8) by (symmetry; rpc).
assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 112, usp0 + -128); (316332, 316332 + 4)]).
{ unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (HP1' : RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] m1).
{ eapply (RHEAP_munchW sp0 VSP HCEIL RHF); [exact WOKW| exact MUc| exact WMc| | exact HP0]. intros iv [<-|[<-|[]]]; cbn [fst snd]; intros; lia. }
assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP HCEIL VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; first [exact ST1| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1]]).
assert (CJ1 : ADP0 m1) by (eapply (ADP0_munchW sp0 VSP HCEIL); [exact WOKW| exact MUc| exact WMc| exact CJ]).
clear MUc WMc BA WOKW CJ HP0 G1 G2. try clear ST. try clear MI. try clear RS. try clear AUX. try clear IMG. try clear SE. try clear SOF.
pose proof BA1 as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST.
unfold implM. iprefix.
destruct r as [e|fd]; cbn [open_ret open_errno] in *.
-
pose proof RS as sfP_; first [ sf_destruct 14%nat sfP_ as _ _ _ _ _ _ _ _ _ _ G28 GD0 _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _) ].
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm (ps_init alloc_ceiling (reservedZ rsegs)) POSTB msx) end.
cbn [io_diag].
eapply (fprintf_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP HCEIL HT RHF FPR FWX SWF (DCannotOpen (map bv_unsigned arg1)));
[| exact BA1| exact HP1'| reflexivity| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
unfold X1ei.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
split; [unfold X1oc.INT_MAX; lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
-
zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm (ps_init alloc_ceiling (reservedZ rsegs)) POSTB msx) end.
eapply implM_bind.
{ unfold rmalloc_stmt in MALLOC.
eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 316496) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
first [ exact HP1' | exact AUX | exact ST | exact ERR1 | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
cbv beta. intros r s1 ms1 PO.
first [ sf_destruct 26%nat PO as v0 v1 v2 ra0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 errv2 -> MI2 ST2 ERR2 AUX2 HPR FAE SOE RR | sf_fb; destruct PO as (v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR) ].
unfold RATP in ERR2. rewrite ?(unsigned_lit 316496) in ERR2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
change (316496 + -164) with 316332 in ERR2.
replace (ret_pc (Z_to_bv 64 0x1bcdc)) with (Z_to_bv 64 0x1bcdc) by (symmetry; rpc).
assert (BA2 : BASE' m2) by (eapply (BASE_heap_pres sp0 argv envp uid hw rnd TID); [exact BA1| exact HPR| exact MI2| unfold LO; first [exact ST2| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2]| exact AUX2]).
assert (CJ2 : ADP0 m2) by (eapply ADP0_heap_pres; [exact HPR| exact CJ1]).
assert (FR2 : MFRAME sp0 argv m2 pad S7 S6 S5 S4) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
assert (SG2 : rw_cells rsegs m2 RSTG [CB (Z.to_nat 65536) stg]).
{ unfold RSTG. eapply rheap_pres_rw_cells; [exact HPR| exact SG|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
clear FR ST MI RS AUX IMG SE SOF ERR1 SG.
pose proof BA2 as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST.
unfold implM. iprefix.
destruct r as [buf|].
2:{
destruct RR as [-> HEAP2].
pose proof RS as sfP_; first [ sf_destruct 14%nat sfP_ as _ _ _ _ _ _ _ _ _ _ G28 GD0 _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _) ].
zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 POSTB msx) end.
cbn [io_diag].
eapply (fwrite_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP HCEIL HT RHF FWR TOW);
[exact BA2| exact HEAP2| rewrite SOE; reflexivity| intros ms'' AE; apply implM_ret; apply evt_done; exact AE]. }
first [ sf_destruct 8%nat RR as A junk -> BR HEAP2 BLK HEXP _ | sf_fb; destruct RR as (A & junk & -> & BR & HEAP2 & BLK & HEXP & _) ].
specialize (HEXP ltac:(apply raddr_exposed_ge; unfold X0qc.RBIG; lia)).
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ].
zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.

zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
apply evt_done.

lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_fold_ tm s1 POSTB msx) end.
eapply implM_bind.
{ apply (rd_loop sp0 argv envp uid hw rnd arg0 arg1 TID S4 S5 S6 S7 S8 S9 S10 S11 VSP HCEIL VARGV VENVP EARGV HT RHF RND RBD MALLOC FREE FKP FPR FWX SWF FWR TOW rf fd P1v); [lia| exact HP1|].
unfold RDINV. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
exists 0x1bd14. sf_eexists 17%nat. first [ unshelve sf_eexists 7%nat; [ exact (F) | exact (fc) | exact (m2) | exact (A) | exact ([]) | exact (junk) | exact (errv2) | ] | sf_fb; exists F, fc, m2, A, [], junk, errv2 ].
split; [reflexivity|]. split; [unfold RDHEAD, zlength; cbn [length Z.of_nat]; left; split; [reflexivity| lia]|]. split; [reflexivity|].
split; [| split; [exists pad; exact FR2| split; [exact BA2| split; [exact CJ2| split; [exact ERR2| split; [exact FRM| split; [exact MKF| exists stg; exact SG2]]]]]]].
split; [exact HEAP2|]. split; [rewrite FAE; reflexivity|]. split; [rewrite SOE; reflexivity|]. split; [exact HEXP|]. cbn [length Z.of_nat Z.sub].
split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
- apply rw_cells_CB0. lia.
- unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR]. }
cbv beta. intros res s2 ms2 PO.
destruct res as [|b c]; cbn [POSTLOOP] in PO.
{ apply implM_ret. apply evt_done. exact PO. }

clear dependent m2.
first [ sf_destruct 34%nat PO as x1 w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 x23 F2 fc2 m3 A3 cap3 DATA3 junk3 errv3 -> HC3 BU3 FR3 BA3 CJ3 ERR3 FRM3 MKF3 | sf_fb; destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & x23 & F2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3 & errv3 & -> & HC3 & BU3 & FR3 & BA3 & CJ3 & ERR3 & FRM3 & MKF3) ].
pose proof BA3 as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST. unfold RERRNO in ERR3. destruct FR3 as [pad3 FR3]. unfold MFRAME in FR3.
pose proof BU3 as sfP_; first [ sf_destruct 8%nat sfP_ as P3 FA3 SO3 HA3 BLK3 CAP3 LEN3 BRR3 | sf_fb; destruct sfP_ as (P3 & FA3 & SO3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3) ].
pose proof BRR3 as sfP_; first [ sf_destruct 5%nat sfP_ as BQ1 BQ2 BQ3 BQ4 BQ5 | sf_fb; destruct sfP_ as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5) ].
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s2 POSTB msx) end.
eapply implM_bind.
{ eapply implM_of_enode.
eapply close_spec with (lo := usp0 - 8388608) (errv := errv3); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 316496) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
first [ exact ST | exact ERR3 | exact MI | lia ]. }
cbv beta. intros r3 s3 ms3 [PO ->].
first [ sf_destruct 21%nat PO as y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 m4 -> MUc WMc MI4 ST4 ERR4 | sf_fb; destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4) ].
unfold RATP in MUc, ERR4. rewrite ?(unsigned_lit 316496) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit 316496) in ERR4 by lia. change (316496 + -164) with 316332 in MUc, ERR4.
transport_after_call rsegs m3 m4 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x1bd84)) with (Z_to_bv 64 0x1bd84) by (symmetry; rpc).
assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 32, usp0 + -128); (316332, 316332 + 4)]).
{ unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (P4 : RHEAP s2 [(b, A3, cap3)] m4).
{ eapply (RHEAP_munchW sp0 VSP HCEIL RHF); [exact WOKW| exact MUc| exact WMc| | exact P3]. intros iv [<-|[<-|[]]]; cbn [fst snd]; intros; lia. }
assert (BA4 : BASE' m4) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP HCEIL VARGV VENVP); [exact BA3| exact WOKW| exact MUc| exact WMc| exact MI4| unfold LO; first [exact ST4| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST4]]).
assert (CJ4 : ADP0 m4) by (eapply (ADP0_munchW sp0 VSP HCEIL); [exact WOKW| exact MUc| exact WMc| exact CJ3]).
apply implM_ret. apply evt_done. cbn [POSTB]. unfold RDONE.
sf_eexists 17%nat. first [ unshelve sf_eexists 8%nat; [ exact (F2) | exact (fc2) | exact (m4) | exact (A3) | exact (cap3) | exact (P1v) | exact (fd) | exact (DATA3) | ] | sf_fb; exists F2, fc2, m4, A3, cap3, P1v, fd, DATA3 ]. exists junk3, (close_errno r3 errv3).
split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exists pad3; exact FR3| split; [exact BA4| split; [exact CJ4| split; [exact ERR4| split; [exact FRM3| exact MKF3]]]]]].
split; [exact P4|]. split; [exact FA3|]. split; [exact SO3|]. split; [exact HA3|]. split; [exact BLK3|]. split; [exact CAP3|]. split; [exact LEN3| exact BRR3].
Qed.
End B4.
