(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of pins_set's ASan walk (the prologue and the inlined
   record(), both arms), after the cgif_close walk of cgif_file_fuzzer (proofs/cgif/cgif_file_fuzzer/lib/A/ACh*.v
   at c8557374ad2e: AChc.v, the seed of a walk and its first straight run; ACh2.v, the step
   through a call and back) over fuzz_command's recorder. *)

(* `ps_seg_entry`: from pins_set's entry to record()'s join. The prologue saves the ten callee-saved registers
   into the 80-byte frame and loads g_rec.ncalls; record() then takes the slot g_rec.calls[ncalls] and stores
   ncalls + 1 (the table arm), or, when the table holds 16 calls, frees record.spill's arguments with
   rec_calls_free and takes record.spill (the spill arm). Each arm is one straight symbolic run: the call count's
   atom carries the arm's bounds, so the executor settles record()'s branch itself. The runs (`pse_run_table`,
   `pse_run_spill`) hand the facts of their final state to a continuation; `pse_table_join` and
   `pse_spill_call` turn those facts into `ps_jinv`, the invariant the rest of the walk starts from. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaNoChain PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3 pins_set_s4 pins_set_s5 pins_set_s6 pins_set_s7 pins_set_s8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* two readers that hold the same n-byte value agree on those n bytes *)
Lemma pse_aval_same : forall (rd rd' : reader) a n v, aval_mem rd a n v -> aval_mem rd' a n v ->
forall x, a <= x < a + Z.of_nat n -> rd' x = rd x.
Proof.
intros rd rd' a n v H H' x Hx.
assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H (Z.to_nat (x - a)) Hk), (H' (Z.to_nat (x - a)) Hk). reflexivity.
Qed.

Lemma pse_denot_off : forall E k v d, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff k d) = Z_to_bv 64 (v + d).
Proof. intros E k v d Hk Hv. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hv. reflexivity. Qed.

(* the slot address record()'s table arm computes (slli / slli / sub folded to one multiplication by the
   symbolic executor): g_rec + 16 + 56 * ncalls *)
Lemma pse_denot_slot : forall E n, ew E PS_N = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E PS_GREC = Z_to_bv 64 A_G_REC ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff PS_N 0) (SLit 56)) (SLit 16)) (SOff PS_GREC 0)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n HN Hn HG. cbn [sv_denot]. rewrite HN, HG.
assert (Hk : (Z.to_nat n < 17)%nat) by lia.
replace n with (Z.of_nat (Z.to_nat n)) by lia.
generalize (Z.to_nat n) Hk. clear n HN Hn Hk. intros k Hk.
do 17 (destruct k as [|k]; [apply bv_eq; vm_compute; reflexivity|]).
lia.
Qed.

(* membership in a short concrete list *)
Ltac pse_in := cbn [In]; repeat first [ solve [left; reflexivity] | right ].

(* a register of the final symbolic state, as the expected symbolic value e *)
Ltac pse_reg HS r e K :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as K; change (sr_get (ss_regs ss) r) with e in K
| st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg sg H E ss ms r HS) as K; change (sr_get (ss_regs ss) r) with e in K
end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma pse_denot_reg : forall (rg : bvmap 5 word) n c rf cd st k d (r : bv 5), Z.of_nat k = bv_unsigned r ->
sv_denot (ps_E0 rg n c rf cd st) (SOff k d) = Z_to_bv 64 (bv_unsigned (getr rg r) + d).
Proof. intros rg n c rf cd st k d r Hk. cbn [sv_denot]. rewrite (ps_E0_reg rg n c rf cd st k r Hk). reflexivity. Qed.

Lemma pse_denot_reg0 : forall (rg : bvmap 5 word) n c rf cd st k (r : bv 5), Z.of_nat k = bv_unsigned r ->
sv_denot (ps_E0 rg n c rf cd st) (SOff k 0) = getr rg r.
Proof.
intros rg n c rf cd st k r Hk. rewrite (pse_denot_reg rg n c rf cd st k 0 r Hk), Z.add_0_r, Z_to_bv_bv_unsigned.
reflexivity.
Qed.

(* the frame of saved registers both runs leave: the chunk at sp0 - 8 - 8 i holds the i-th register of
   ps_saved *)
Definition pse_eframe : list YP09.chunk :=
[YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
 YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
 YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
 YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
 YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Lemma pse_frame_slot : forall E (m : word -> option byte) (Wc : world SEGS) (rg : bvmap 5 word) sp cs od (k : nat) (r : bv 5),
region_ok SEGS E (mrestrict (w_H Wc) m) (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs) ->
bv_unsigned (ew E 2%nat) = sp ->
In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
ew E k = getr rg r ->
aval_mem (aview SEGS (w_H Wc) m) (sp + od) 8 (bv_unsigned (getr rg r)).
Proof.
intros E m Wc rg sp cs od k r HR Hsp Hin Hk.
pose proof (field_of_region_any E (mrestrict (w_H Wc) m) 2%nat sp cs (-80) 0 (-80) 0 od 8%N (SOff k 0)
  HR Hsp Hin ltac:(cbn; lia)) as HV.
cbn [sv_denot] in HV. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned, ps_pow8 in HV.
rewrite (Z.mod_small (bv_unsigned (getr rg r)) (2 ^ 64) (bv_unsigned_in_range 64 (getr rg r))) in HV.
exact (aval_mem_view SEGS (w_H Wc) m (sp + od) 8%nat _ HV).
Qed.

Lemma pse_eframe_ok : forall E (m : word -> option byte) (Wc : world SEGS) (rg : bvmap 5 word) sp,
region_ok SEGS E (mrestrict (w_H Wc) m) (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 pse_eframe) ->
bv_unsigned (ew E 2%nat) = sp ->
(forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rg r) ->
forall i r, nth_error ps_saved i = Some r ->
aval_mem (aview SEGS (w_H Wc) m) (sp - 8 - 8 * Z.of_nat i) 8 (bv_unsigned (getr rg (Z_to_bv 5 r))).
Proof.
intros E m Wc rg sp HR Hsp HE i r Hir.
assert (ONE : forall od (k : nat) z, In (YP09.mkChunk od (CVal 8 (SOff k 0))) pse_eframe ->
  Z.of_nat k = bv_unsigned (Z_to_bv 5 z) -> sp + od = sp - 8 - 8 * Z.of_nat i ->
  aval_mem (aview SEGS (w_H Wc) m) (sp - 8 - 8 * Z.of_nat i) 8 (bv_unsigned (getr rg (Z_to_bv 5 z)))).
{ intros od k z Hin Hk Hod. rewrite <- Hod.
  exact (pse_frame_slot E m Wc rg sp pse_eframe od k (Z_to_bv 5 z) HR Hsp Hin (HE k (Z_to_bv 5 z) Hk)). }
assert (Hi : (i < 10)%nat) by (change 10%nat with (length ps_saved); apply nth_error_Some; rewrite Hir; discriminate).
destruct i as [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]; [| | | | | | | | | | exfalso; lia];
  cbn [nth_error ps_saved] in Hir; injection Hir as <-.
- exact (ONE (-8) 1%nat 1 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-16) 8%nat 8 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-24) 9%nat 9 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-32) 18%nat 18 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-40) 19%nat 19 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-48) 20%nat 20 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-56) 21%nat 21 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-64) 22%nat 22 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-72) 23%nat 23 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
- exact (ONE (-80) 24%nat 24 ltac:(unfold pse_eframe; pse_in) ltac:(vm_compute; reflexivity) ltac:(lia)).
Qed.

(* the value of g_rec.ncalls a run leaves in its ncalls region *)
Lemma pse_ncalls_val : forall E (m : word -> option byte) (Wc : world SEGS) nv v,
region_ok SEGS E (mrestrict (w_H Wc) m) (ps_ncalls nv) ->
bv_unsigned (ew E PS_GREC) = A_G_REC ->
sv_denot E nv = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
aval_mem (aview SEGS (w_H Wc) m) (A_G_REC + OFF_NCALLS) 4 v.
Proof.
intros E m Wc nv v HR HG Hv Hv32.
pose proof (field_of_region_any E (mrestrict (w_H Wc) m) PS_GREC A_G_REC [YP09.mkChunk OFF_NCALLS (CVal 4 nv)]
  OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS 4%N nv HR HG (or_introl eq_refl)
  ltac:(cbn; lia)) as HV.
rewrite Hv, unsigned_lit_small, ps_pow4, Z.mod_small in HV by lia.
exact (aval_mem_view SEGS (w_H Wc) m (A_G_REC + OFF_NCALLS) 4%nat v HV).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TXSTRDUP : txstrdup_spec B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis TRCF : trec_calls_free_spec B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis TL : PALib B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

Lemma pse_E0_obj : forall (rg : bvmap 5 word) n c,
ew (ps_E0 rg n c 0 0 0) PS_GREC = Z_to_bv 64 A_G_REC /\ ew (ps_E0 rg n c 0 0 0) PS_SPILL = Z_to_bv 64 A_REC_SPILL.
Proof.
intros rg n c. assert (HEI : img_env VAL A_LIM (ps_E0 rg n c 0 0 0)) by (unfold ps_E0; apply Eimg_env).
split.
- rewrite (img_env_atomP _ PS_GREC HEI ltac:(unfold PS_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (ps_grec_val VOBJS).
  reflexivity.
- rewrite (img_env_atomP _ PS_SPILL HEI ltac:(unfold PS_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), (ps_spill_val VOBJS).
  reflexivity.
Qed.

(* a byte outside the frame and outside g_rec.ncalls is kept by an entry run *)
Lemma pse_kept_of : forall (rg : bvmap 5 word) n c nv (m m' : word -> option byte) (H : word -> bool) a,
frame_of (ps_E0 rg n c 0 0 0) (ps_rs0 nv) m m' -> 0 <= a < 2 ^ 64 ->
~ (spZ rg - 80 <= a < spZ rg) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros rg n c nv m m' H a HF Ha H1 H2.
destruct (pse_E0_obj rg n c) as [EG _].
assert (EGu : bv_unsigned (ew (ps_E0 rg n c 0 0 0) PS_GREC) = A_G_REC)
  by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E2u : bv_unsigned (ew (ps_E0 rg n c 0 0 0) 2%nat) = spZ rg)
  by (rewrite (ps_E0_reg rg n c 0 0 0 2%nat 2%bv eq_refl); reflexivity).
apply (ps_rd_frame (ps_E0 rg n c 0 0 0) (ps_rs0 nv) H m m' a HF Ha).
intros (r & Hin & Hr). unfold ps_rs0 in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi ps_stack got_regionP bcell_regionP ps_ncalls base_val] in Hr.
- rewrite E2u in Hr. lia.
- lia.
- lia.
- rewrite EGu in Hr. lia.
Qed.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HSU : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri.
Hypothesis HSF : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf files.
Hypothesis HSL : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pl layout.
Hypothesis HSV : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict.
Hypothesis HREPA : rec_repA B ly S (rdW W mem) R O.
Hypothesis HEV : st_nev S + EV_PINS_SET R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_PINS_SET R uri files layout verdict <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_PINS_SET MT R uri files layout verdict).
Hypothesis H10 : getr regs 10 = w64 pu.
Hypothesis H11 : getr regs 11 = w64 pf.
Hypothesis H12 : getr regs 12 = w64 pl.
Hypothesis H13 : getr regs 13 = w64 pv.

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation PTRS := (ps_ptrs pu pf pl pv uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation E0 := (ps_E0 regs (ps_n R) (ps_c R) 0 0 0).
#[local] Notation JCONT := (ps_jcont B MT ly S W regs mem md pu pf pl pv uri files layout verdict R O).

(* the facts the runs hand on: the frame of saved registers, the bytes the run kept, and the registers
   ps_jinv names *)
Definition pse_frame (Wc : world SEGS) memc : Prop :=
forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW Wc memc) (ps_sp0 regs - 8 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition pse_kept memc : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (ps_sp0 regs - 80 <= a < ps_sp0 regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memc a = rdW W mem a.
Definition pse_jregs (regsc : bvmap 5 word) : Prop :=
getr regsc 2 = w64 (ps_sp0 regs - 80) /\ getr regsc 3 = w64 (as_gp B) /\ getr regsc 4 = w64 (as_tp B) /\
getr regsc 8 = w64 (ps_c R) /\ getr regsc 22 = w64 A_G_REC /\ getr regsc 23 = w64 SB /\
getr regsc 21 = w64 pu /\ getr regsc 20 = w64 pf /\ getr regsc 19 = w64 pl /\ getr regsc 9 = w64 pv /\
(forall r, 25 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

Lemma pse_jinv_intro : forall lyc Sc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc k,
ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= rec_spill_frees R -> mo_le MT S Sc (rec_spill_frees R * mo_free MT) -> blocks_bytes Sc <= blocks_bytes S ->
pse_frame Wc memc -> (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
ps_rec0 B ly S R O lyc Sc Wc memc -> pse_jregs regsc ->
ps_jinv B MT ly S W regs mem md pu pf pl pv R O lyc Sc Wc regsc memc mdc k.
Proof.
intros lyc Sc Wc regsc memc mdc k H1 H2 H3 H4 H5 H6 H7 H8.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.

(* the registers a callee keeps keep pse_jregs *)
Lemma pse_jregs_pres : forall (rg rg' : bvmap 5 word), aregs_preserved rg rg' -> pse_jregs rg -> pse_jregs rg'.
Proof.
intros rg rg' HP (R2 & R3 & R4 & R8 & R22 & R23 & R21 & R20 & R19 & R9 & RHI).
assert (PR : forall r (b : bv 5), acallee_saved r -> b = Z_to_bv 5 r -> getr rg' b = getr rg b)
  by (intros r b Hr Hb; exact (ps_pres rg rg' r b HP Hr Hb)).
unfold pse_jregs.
rewrite (PR 2 2%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 3 3%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 4 4%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 8 8%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 22 22%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 23 23%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 21 21%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 20 20%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 19 19%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
rewrite (PR 9 9%bv ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R22|].
split; [exact R23|]. split; [exact R21|]. split; [exact R20|]. split; [exact R19|]. split; [exact R9|].
intros r Hr. rewrite (PR r (Z_to_bv 5 r) ltac:(unfold acallee_saved; lia) eq_refl). exact (RHI r Hr).
Qed.

(* the registers of a final state over the entry's environment, as pse_jregs *)
Lemma pse_jregs_of : forall n c (rg : bvmap 5 word),
getr rg 2 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 2 (-80)) ->
getr rg 3 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 3 0) ->
getr rg 4 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 4 0) ->
getr rg 8 = w64 (ps_c R) ->
getr rg 22 = sv_denot (ps_E0 regs n c 0 0 0) (SOff PS_GREC 0) ->
getr rg 23 = sv_denot (ps_E0 regs n c 0 0 0) (SOff PS_SB 0) ->
getr rg 21 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 10 0) ->
getr rg 20 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 11 0) ->
getr rg 19 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 12 0) ->
getr rg 9 = sv_denot (ps_E0 regs n c 0 0 0) (SOff 13 0) ->
getr rg (Z_to_bv 5 25) = sv_denot (ps_E0 regs n c 0 0 0) (SOff 25 0) ->
getr rg (Z_to_bv 5 26) = sv_denot (ps_E0 regs n c 0 0 0) (SOff 26 0) ->
getr rg (Z_to_bv 5 27) = sv_denot (ps_E0 regs n c 0 0 0) (SOff 27 0) ->
pse_jregs rg.
Proof.
intros n c rg K2 K3 K4 K8 K22 K23 K21 K20 K19 K9 K25 K26 K27.
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
destruct (ps_E0_extra regs n c 0 0 0) as (ESB & _).
destruct (pse_E0_obj regs n c) as [EG _].
unfold pse_jregs.
split; [rewrite K2, (pse_denot_reg regs n c 0 0 0 2 (-80) 2%bv eq_refl); unfold w64, ps_sp0, spZ; f_equal; lia|].
split; [rewrite K3, (pse_denot_reg0 regs n c 0 0 0 3 3%bv eq_refl); exact Hgp|].
split; [rewrite K4, (pse_denot_reg0 regs n c 0 0 0 4 4%bv eq_refl); exact Htp|].
split; [exact K8|].
split; [rewrite K22, (pse_denot_off _ PS_GREC A_G_REC 0 EG ltac:(unfold A_G_REC; lia)), Z.add_0_r; reflexivity|].
split; [rewrite K23, (pse_denot_off _ PS_SB SB 0 ESB ltac:(unfold SB; lia)), Z.add_0_r; reflexivity|].
split; [rewrite K21, (pse_denot_reg0 regs n c 0 0 0 10 10%bv eq_refl); exact H10|].
split; [rewrite K20, (pse_denot_reg0 regs n c 0 0 0 11 11%bv eq_refl); exact H11|].
split; [rewrite K19, (pse_denot_reg0 regs n c 0 0 0 12 12%bv eq_refl); exact H12|].
split; [rewrite K9, (pse_denot_reg0 regs n c 0 0 0 13 13%bv eq_refl); exact H13|].
intros r Hr. assert (Hr3 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr3 as [-> | [-> | ->]].
- rewrite K25. exact (pse_denot_reg0 regs n c 0 0 0 25 (Z_to_bv 5 25) eq_refl).
- rewrite K26. exact (pse_denot_reg0 regs n c 0 0 0 26 (Z_to_bv 5 26) eq_refl).
- rewrite K27. exact (pse_denot_reg0 regs n c 0 0 0 27 (Z_to_bv 5 27) eq_refl).
Qed.

(* the regions the entry runs may write: the frame, and g_rec.ncalls (a byte of g_rec, which the footprint names) *)
Lemma pse_awr0 : forall n c nv, awr_ok SEGS B (ps_E0 regs n c 0 0 0) (ps_rs0 nv) PINS_SET_STK (spZ regs) (ps_FP O)
  (ablocks B ly S) (ablocks B ly S) (frames S) ly [].
Proof.
intros n c nv. unfold ps_rs0.
destruct (pse_E0_obj regs n c) as [EG _].
assert (EGu : bv_unsigned (ew (ps_E0 regs n c 0 0 0) PS_GREC) = A_G_REC)
  by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (E2u : bv_unsigned (ew (ps_E0 regs n c 0 0 0) 2%nat) = spZ regs)
  by (rewrite (ps_E0_reg regs n c 0 0 0 2%nat 2%bv eq_refl); reflexivity).
assert (Hstkx : 80 <= PINS_SET_STK)
  by (unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ANSWER_CODE_STK, HAND_BACK_STK, ASTACK, ESTACK; lia).
apply (awr_ok_cons_stack SEGS B _ (ps_stack (-80) []) _ PINS_SET_STK (spZ regs) (ps_FP O) _ _ _ ly [] 2%nat eq_refl E2u).
- cbn [YP09.r_wlo ps_stack]. lia.
- cbn [YP09.r_whi ps_stack]. lia.
- apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo got_regionP]; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo bcell_regionP]; lia|].
  apply (awr_ok_cons_gen B _ (ps_ncalls nv) [] PINS_SET_STK (spZ regs) (ps_FP O) _ _ _ ly [] PS_GREC A_G_REC eq_refl EGu);
    [|exact (awr_ok_nil SEGS B _ PINS_SET_STK (spZ regs) (ps_FP O) _ _ _ ly [])].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi ps_ncalls] in Ha.
  apply (ps_awr_prog B HB cmd_prog_img). left. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia.
Qed.

(* --- the table arm (ncalls < 16): one run from the entry to record()'s join ------------------------------ *)
Lemma pse_run_table : ps_n R < 16 ->
(forall mem1 md1 (regs1 : bvmap 5 word),
  ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] ly S W mem1 md1 0 ->
  pse_kept mem1 -> pse_frame W mem1 ->
  aval_mem (rdW W mem1) (A_G_REC + OFF_NCALLS) 4 (ps_n R + 1) -> pse_jregs regs1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + PS_JOIN)) mem1 (seg_rom SEGS)) md1) POST) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + PS_ENTRY)) mem (seg_rom SEGS)) md) POST.
Proof.
intros Hlt HK.
pose proof HPRE as (HAR & _ & _ & _ & _ & _ & Hpres & _).
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp46 & Hsp16 & _).
unfold ps_sp0 in Hsp46, Hsp16.
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn16.
pose proof HREPA as (Q & HA & _).
pose proof HA as (_ & _ & _ & (_ & _ & HNC & _) & _).
assert (Hstkx : 80 <= PINS_SET_STK)
  by (unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ANSWER_CODE_STK, HAND_BACK_STK, ASTACK, ESTACK; lia).
destruct (ps_E0_extra regs (ps_n R) (ps_c R) 0 0 0) as (ESB & EN & EC & _).
destruct (pse_E0_obj regs (ps_n R) (ps_c R)) as [EG _].
assert (Hc : ps_c R = A_G_REC + OFF_CALLS + CALL_SIZE * ps_n R)
  by (unfold ps_c, ps_slot_of; rewrite (proj2 (Z.eqb_neq (ps_n R) 16) ltac:(lia)); reflexivity).
assert (HEI : img_env VAL A_LIM E0) by (unfold ps_E0; apply Eimg_env).
destruct (ps_entry_seed B TL HB VOBJS cmd_prog_writable ly S W mem md regs (ps_n R) (ps_c R) 0 0 0
  (SOff PS_N 0) 0 15 HAR Hsp46 Hsp16 Hn16 eq_refl ltac:(lia) ltac:(intros a Ha; apply Hpres; lia) HNC
  ltac:(rewrite (pse_denot_off _ PS_N (ps_n R) 0 EN ltac:(lia)), Z.add_0_r; reflexivity)) as [HS SHOK].
pose proof (ajournal_init SEGS B PINS_SET_STK (ps_FP O) ly S W regs mem md ch HPRE) as HJ.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PS_JOIN.
{ exact (pse_awr0 (ps_n R) (ps_c R) (SOff PS_N 0)). }
set (mdv1 := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv1.
assert (E2u : bv_unsigned (ew E0 2%nat) = spZ regs)
  by (rewrite (ps_E0_reg regs (ps_n R) (ps_c R) 0 0 0 2%nat 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E0 PS_GREC) = A_G_REC) by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 0%nat
  (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 pse_eframe) HS eq_refl) as HR0.
pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) ms) 3%nat (ps_ncalls (SOff PS_N 1)) HS eq_refl) as HR3.
cbn [ms_mem restrict] in HR0, HR3.
assert (FRM : pse_frame W (ms_mem ms))
  by exact (pse_eframe_ok E0 (ms_mem ms) W regs (spZ regs) HR0 E2u
             (fun k r Hk => ps_E0_reg regs (ps_n R) (ps_c R) 0 0 0 k r Hk)).
assert (NC1 : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (ps_n R + 1))
  by exact (pse_ncalls_val E0 (ms_mem ms) W (SOff PS_N 1) (ps_n R + 1) HR3 EGu
             (pse_denot_off E0 PS_N (ps_n R) 1 EN ltac:(lia)) ltac:(lia)).
assert (KEPT : pse_kept (ms_mem ms))
  by (intros a Ha H1 H2; exact (pse_kept_of regs (ps_n R) (ps_c R) (SOff PS_N 0) mem (ms_mem ms) (w_H W) a HF Ha H1 H2)).
pse_reg HS (2%bv : bv 5) (SOff 2 (-80)) K2.
pse_reg HS (3%bv : bv 5) (SOff 3 0) K3.
pse_reg HS (4%bv : bv 5) (SOff 4 0) K4.
pse_reg HS (8%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff PS_N 0) (SLit 56)) (SLit 16)) (SOff PS_GREC 0)) K8.
pse_reg HS (22%bv : bv 5) (SOff PS_GREC 0) K22.
pse_reg HS (23%bv : bv 5) (SOff PS_SB 0) K23.
pse_reg HS (21%bv : bv 5) (SOff 10 0) K21.
pse_reg HS (20%bv : bv 5) (SOff 11 0) K20.
pse_reg HS (19%bv : bv 5) (SOff 12 0) K19.
pse_reg HS (9%bv : bv 5) (SOff 13 0) K9.
pse_reg HS (Z_to_bv 5 25) (SOff 25 0) K25.
pse_reg HS (Z_to_bv 5 26) (SOff 26 0) K26.
pse_reg HS (Z_to_bv 5 27) (SOff 27 0) K27.
rewrite (pse_denot_slot E0 (ps_n R) EN ltac:(lia) EG), <- Hc in K8.
pose proof (pse_jregs_of (ps_n R) (ps_c R) (ms_regs ms) K2 K3 K4 K8 K22 K23 K21 K20 K19 K9 K25 K26 K27) as REGS.
rewrite (st_ok_pi_restrict_mkst (w_H W) E0 _ ms HS eq_refl). cbn [ss_pc].
clear HS SHOK HF HFr HG HR0 HR3 K2 K3 K4 K8 K22 K23 K21 K20 K19 K9 K25 K26 K27.
exact (HK (ms_mem ms) mdv1 (ms_regs ms) HJ KEPT FRM NC1 REGS).
Qed.

(* --- the spill arm (ncalls = 16): one run from the entry to the call of rec_calls_free -------------------- *)
Lemma pse_run_spill : ps_n R = 16 ->
(forall mem1 md1 (regs1 : bvmap 5 word),
  ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] ly S W mem1 md1 0 ->
  pse_kept mem1 -> pse_frame W mem1 ->
  aval_mem (rdW W mem1) (A_G_REC + OFF_NCALLS) 4 (ps_n R) ->
  getr regs1 1 = Z_to_bv 64 (BASE + PS_RET_RCF) -> getr regs1 10 = w64 A_REC_SPILL -> getr regs1 11 = w64 1 ->
  pse_jregs regs1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_rec_calls_free)) mem1 (seg_rom SEGS)) md1) POST) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + PS_ENTRY)) mem (seg_rom SEGS)) md) POST.
Proof.
intros E16 HK.
pose proof HPRE as (HAR & _ & _ & _ & _ & _ & Hpres & _).
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp46 & Hsp16 & _).
unfold ps_sp0 in Hsp46, Hsp16.
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn16.
pose proof HREPA as (Q & HA & _).
pose proof HA as (_ & _ & _ & (_ & _ & HNC & _) & _).
assert (Hstkx : 80 <= PINS_SET_STK)
  by (unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ANSWER_CODE_STK, HAND_BACK_STK, ASTACK, ESTACK; lia).
destruct (ps_E0_extra regs (ps_n R) (ps_c R) 0 0 0) as (ESB & EN & EC & _).
destruct (pse_E0_obj regs (ps_n R) (ps_c R)) as [EG ESP].
assert (Hcsp : ps_c R = A_REC_SPILL) by (unfold ps_c, ps_slot_of; rewrite E16; reflexivity).
assert (HSIG : pa_sigma CS_rec_calls_free = BASE + AF_rec_calls_free).
{ assert (Haf : cmd_af CS_rec_calls_free = AF_rec_calls_free) by (vm_compute; reflexivity).
  rewrite (SIGP CS_rec_calls_free ltac:(unfold cmd_prog_syms; pse_in)), Haf. reflexivity. }
assert (HEI : img_env VAL A_LIM E0) by (unfold ps_E0; apply Eimg_env).
destruct (ps_entry_seed B TL HB VOBJS cmd_prog_writable ly S W mem md regs (ps_n R) (ps_c R) 0 0 0
  (SLit 16) 16 16 HAR Hsp46 Hsp16 Hn16 eq_refl ltac:(lia) ltac:(intros a Ha; apply Hpres; lia) HNC
  ltac:(cbn [sv_denot]; rewrite E16; reflexivity)) as [HS SHOK].
pose proof (ajournal_init SEGS B PINS_SET_STK (ps_FP O) ly S W regs mem md ch HPRE) as HJ.
paj_run_tok RUN HS HJ SHOK Bspan.
{ exact (pse_awr0 (ps_n R) (ps_c R) (SLit 16)). }
set (mdv1 := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv1.
assert (E2u : bv_unsigned (ew E0 2%nat) = spZ regs)
  by (rewrite (ps_E0_reg regs (ps_n R) (ps_c R) 0 0 0 2%nat 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E0 PS_GREC) = A_G_REC) by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 0%nat
  (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 pse_eframe) HS eq_refl) as HR0.
pose proof (st_ok_region_nth E0 _ (restrict (w_H W) ms) 3%nat (ps_ncalls (SLit 16)) HS eq_refl) as HR3.
cbn [ms_mem restrict] in HR0, HR3.
assert (FRM : pse_frame W (ms_mem ms))
  by exact (pse_eframe_ok E0 (ms_mem ms) W regs (spZ regs) HR0 E2u
             (fun k r Hk => ps_E0_reg regs (ps_n R) (ps_c R) 0 0 0 k r Hk)).
assert (NC1 : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (ps_n R))
  by (rewrite E16; exact (pse_ncalls_val E0 (ms_mem ms) W (SLit 16) 16 HR3 EGu eq_refl ltac:(lia))).
assert (KEPT : pse_kept (ms_mem ms))
  by (intros a Ha H1 H2; exact (pse_kept_of regs (ps_n R) (ps_c R) (SLit 16) mem (ms_mem ms) (w_H W) a HF Ha H1 H2)).
pse_reg HS (1%bv : bv 5) (SOff 240 25460) K1.
pse_reg HS (2%bv : bv 5) (SOff 2 (-80)) K2.
pse_reg HS (3%bv : bv 5) (SOff 3 0) K3.
pse_reg HS (4%bv : bv 5) (SOff 4 0) K4.
pse_reg HS (8%bv : bv 5) (SOff PS_SPILL 0) K8.
pse_reg HS (10%bv : bv 5) (SOff PS_SPILL 0) K10.
pse_reg HS (11%bv : bv 5) (SLit 1) K11.
pse_reg HS (22%bv : bv 5) (SOff PS_GREC 0) K22.
pse_reg HS (23%bv : bv 5) (SOff PS_SB 0) K23.
pse_reg HS (21%bv : bv 5) (SOff 10 0) K21.
pse_reg HS (20%bv : bv 5) (SOff 11 0) K20.
pse_reg HS (19%bv : bv 5) (SOff 12 0) K19.
pse_reg HS (9%bv : bv 5) (SOff 13 0) K9.
pse_reg HS (Z_to_bv 5 25) (SOff 25 0) K25.
pse_reg HS (Z_to_bv 5 26) (SOff 26 0) K26.
pse_reg HS (Z_to_bv 5 27) (SOff 27 0) K27.
cbn [sv_denot] in K1. rewrite (img_env_codeptr E0 HEI 25460) in K1.
rewrite (pse_denot_off E0 PS_SPILL A_REC_SPILL 0 ESP ltac:(unfold A_REC_SPILL; lia)), Z.add_0_r, <- Hcsp in K8.
rewrite (pse_denot_off E0 PS_SPILL A_REC_SPILL 0 ESP ltac:(unfold A_REC_SPILL; lia)), Z.add_0_r in K10.
cbn [sv_denot] in K11.
pose proof (pse_jregs_of (ps_n R) (ps_c R) (ms_regs ms) K2 K3 K4 K8 K22 K23 K21 K20 K19 K9 K25 K26 K27) as REGS.
rewrite (st_ok_restrict_mkst SEGS (w_H W) E0 _ ms HS eq_refl). cbn [ss_pc setpc]. rewrite HSIG.
clear HS SHOK HF HFr HG HR0 HR3 K2 K3 K4 K8 K22 K23 K21 K20 K19 K9 K25 K26 K27.
exact (HK (ms_mem ms) mdv1 (ms_regs ms) HJ KEPT FRM NC1 K1 K10 K11 REGS).
Qed.

(* --- the table arm at record()'s join: ps_jinv with the entry's recorder, k = 0 --------------------------- *)
Lemma pse_table_join : JCONT -> ps_n R < 16 ->
forall mem1 md1 (regs1 : bvmap 5 word),
  ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] ly S W mem1 md1 0 ->
  pse_kept mem1 -> pse_frame W mem1 ->
  aval_mem (rdW W mem1) (A_G_REC + OFF_NCALLS) 4 (ps_n R + 1) -> pse_jregs regs1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + PS_JOIN)) mem1 (seg_rom SEGS)) md1) POST.
Proof.
intros HCONT Hlt mem1 md1 regs1 HJ1 KEPT FRM NC1 REGS.
pose proof HPRE as (HAR & _).
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp46 & _ & Hspc).
pose proof asan_consts as (C1 & _).
pose proof HREPA as (Q & HA & HO).
pose proof HA as (_ & _ & _ & _ & _ & _ & _ & (_ & HOA)).
assert (Hrsf : rec_spill_frees R = 0)
  by (unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt (length (r_calls R)) 16) ltac:(unfold ps_n in Hlt; lia));
      reflexivity).
assert (HREC : ps_rec0 B ly S R O ly S W mem1).
{ exists R, Q, (rdW W mem), (ablocks B ly S).
  split; [exact HA|]. split; [reflexivity|]. split; [intros A0; reflexivity|].
  split; [intros H16; exfalso; lia|].
  split.
  { intros x Hx.
    assert (Hb : 0 <= x < alloc_ceiling /\ ~ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4)).
    { destruct Hx as [(Hg & Hn) | [(Hs & _) | ([p n] & Hpn & Hx)]].
      - split; [unfold A_G_REC, REC_SIZE in *; lia|]. intros Hnc. apply Hn. split; [exact Hlt | left; exact Hnc].
      - unfold A_REC_SPILL, SC_SIZE, A_G_REC, OFF_NCALLS in *. lia.
      - cbn [fst snd] in Hx.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (lay_blocks_in _ _ _ _ _ _ HA (p, n) Hpn))
          as (_ & H4096 & Hcl & _ & _ & _ & Hn0).
        pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
        destruct (HOA (p, n) Hpn) as [D _]. cbn [fst snd] in D. unfold iv_apart in D.
        unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply KEPT; [lia | lia | exact (proj2 Hb)]. }
  split.
  { intros pn Hpn. pose proof (proj2 (HO pn) Hpn) as HpO.
    exact (conj (lay_blocks_in _ _ _ _ _ _ HA pn Hpn) (conj HpO (proj1 (ps_O_facts B ly S _ R O HREPA pn HpO)))). }
  split.
  { intros pn Hpn. destruct (in_dec recb_pair_dec pn O) as [HpO | HpO];
      [right; exact (proj1 (HO pn) HpO) | left; exact (conj Hpn HpO)]. }
  intros _. exact NC1. }
assert (MO : mo_le MT S S (rec_spill_frees R * mo_free MT))
  by (rewrite Hrsf, Z.mul_0_l; exact (mle_start MT S MTL)).
exact (HCONT PS_JOIN ly S W regs1 mem1 md1 0 (or_introl eq_refl)
  (pse_jinv_intro ly S W regs1 mem1 md1 0 HJ1 ltac:(lia) MO ltac:(lia) FRM (fun pn H _ => H) HREC REGS)).
Qed.

(* --- the spill arm: the call of rec_calls_free(&record.spill, 1), then ps_jinv at its return -------------- *)
Lemma pse_spill_call : JCONT -> ps_n R = 16 ->
forall mem1 md1 (regs1 : bvmap 5 word),
  ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] ly S W mem1 md1 0 ->
  pse_kept mem1 -> pse_frame W mem1 ->
  aval_mem (rdW W mem1) (A_G_REC + OFF_NCALLS) 4 (ps_n R) ->
  getr regs1 1 = Z_to_bv 64 (BASE + PS_RET_RCF) -> getr regs1 10 = w64 A_REC_SPILL -> getr regs1 11 = w64 1 ->
  pse_jregs regs1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_rec_calls_free)) mem1 (seg_rom SEGS)) md1) POST.
Proof.
intros HCONT E16 mem1 md1 regs1 HJ KEPT FRM NC1 K1 K10 K11 REGS.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp46 & Hsp16 & Hspc).
unfold ps_sp0 in Hsp46, Hsp16, Hspc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
pose proof HREPA as (Q & HA & HO).
pose proof HA as (_ & _ & _ & (_ & _ & HNC0 & _) & _).
pose proof REGS as (R2 & R3 & R4 & R8 & _).
assert (Hcsp : ps_c R = A_REC_SPILL) by (unfold ps_c, ps_slot_of; rewrite E16; reflexivity).
assert (Hlen16 : length (r_calls R) = 16%nat) by (unfold ps_n in E16; lia).
assert (Hrsf : rec_spill_frees R = Z.of_nat (length (snd (r_spill R))))
  by (unfold rec_spill_frees; rewrite Hlen16; reflexivity).
assert (Hstkx : REC_CALLS_FREE_STK + 80 <= PINS_SET_STK)
  by (unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ANSWER_CODE_STK, HAND_BACK_STK, ASTACK, ESTACK; lia).
assert (Hrcf0 : 0 <= REC_CALLS_FREE_STK) by (unfold REC_CALLS_FREE_STK, ASTACK; lia).
assert (Hsp1 : spZ regs1 = spZ regs - 80)
  by (unfold spZ at 1; rewrite R2; unfold w64, ps_sp0; apply unsigned_lit_small; lia).
(* the recorder's bytes lie below the stack; at the call they are the entry's *)
assert (REPLO : forall x, rep_bytes A_G_REC A_REC_SPILL Q x -> 0 <= x < alloc_ceiling).
{ intros x [Hx | [Hx | ([p n] & Hpn & Hx)]]; [unfold A_G_REC, REC_SIZE in *; lia | unfold A_REC_SPILL, SC_SIZE in *; lia |].
  cbn [fst snd] in Hx.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (lay_blocks_in _ _ _ _ _ _ HA (p, n) Hpn))
    as (_ & H4096 & Hcl & _ & _ & _ & Hn0).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. lia. }
assert (KREP : forall x, rep_bytes A_G_REC A_REC_SPILL Q x -> rdW W mem1 x = rdW W mem x).
{ intros x Hx. pose proof (REPLO x Hx) as Hxl.
  destruct (Z_lt_le_dec x (A_G_REC + OFF_NCALLS)) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec x (A_G_REC + OFF_NCALLS + 4)) as [Hhi | Hhi]].
  - apply KEPT; [lia | unfold ps_sp0; lia | lia].
  - exact (pse_aval_same (rdW W mem) (rdW W mem1) (A_G_REC + OFF_NCALLS) 4 (ps_n R) HNC0 NC1 x ltac:(lia)).
  - apply KEPT; [lia | unfold ps_sp0; lia | lia]. }
assert (HAc : arep_at (ablocks B ly S) (rdW W mem1) A_G_REC A_REC_SPILL R Q)
  by exact (arep_kept (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W mem1) R Q HA KREP
             (lay_blocks_in _ _ _ _ _ _ HA)).
pose proof HAc as (_ & _ & _ & (_ & _ & _ & _ & HSPILLc & _) & _).
pose proof HSPILLc as (_ & Hlen6 & HlenP & _ & Hnargs & HNDsp & HARGSsp).
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W mem1))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
             (ps_FP_ro B cmd_ro_prog_apart ly S W regs mem md ch R O HPRE HREPA) HROD).
assert (HEV1 : EV_REC_CALLS_FREE [l_spill Q] = rec_spill_frees R)
  by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r, HlenP, Hrsf; reflexivity).
assert (XMe : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT)
  by (unfold XM_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r, HlenP, Hrsf; reflexivity).
(* every byte rec_calls_free may write lies below the stack *)
assert (RCFLO : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> a < alloc_ceiling).
{ intros a Hfp. unfold rcf_fp in Hfp. cbn [length seq map app] in Hfp.
  apply inFP_cons in Hfp as [Ha | Hfp].
  - cbn [Z.of_nat] in Ha. unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS in Ha. lia.
  - apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr). cbn [concat] in Hin. rewrite app_nil_r in Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (lay_blocks_in _ _ _ _ _ _ HA (p, n) (ps_lay_spill_in Q (p, n) Hin)))
      as (_ & _ & Hcl & _). lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regs1 mem1 (Z_to_bv 64 (BASE + AF_rec_calls_free)) PINS_SET_STK (spZ regs) (ps_FP O)
    ly S W mem md [] ly S md1 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q])
    (EV_REC_CALLS_FREE [l_spill Q]) (-80) (getr regs1 1) [] _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - unfold REC_CALLS_FREE_STK, ASTACK. lia.
  - lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite K1. apply ret_ok_codeptr_v; [unfold PS_RET_RCF, AF_pins_set; lia | reflexivity].
  - rewrite K1, unsigned_lit_small; unfold PS_RET_RCF, AF_pins_set; lia.
  - left. split; [left | reflexivity]. unfold s0Z. rewrite R8, Hcsp. unfold w64.
    rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia). unfold A_REC_SPILL. lia.
  - intros HPRE1.
    pose proof (TRCF ly S W regs1 mem1 md1 [] A_REC_SPILL [l_spill Q] HPRE1 HROD2) as HX.
    unfold apost_base, cfg_at, w64 in HX. apply HX.
    + exact K10.
    + exact K11.
    + cbn [length]. lia.
    + right; left. cbn [length]. unfold CALL_SIZE, SC_SIZE. lia.
    + unfold A_REC_SPILL. reflexivity.
    + intros i P Hi. destruct i as [|[|i]]; cbn [nth_error] in Hi; try discriminate Hi.
      injection Hi as <-.
      split; [rewrite HlenP; exact Hlen6|].
      split.
      { replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS)
          by (cbn [Z.of_nat]; lia).
        rewrite HlenP. exact Hnargs. }
      intros a pn Ha.
      destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es.
      * destruct (HARGSsp a s pn Es Ha) as (Hv & _ & Hin & _).
        split; [|exact Hin].
        replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
          with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by (cbn [Z.of_nat]; lia).
        exact Hv.
      * exfalso. apply nth_error_None in Es.
        pose proof (proj1 (nth_error_Some (l_spill Q) a) ltac:(rewrite Ha; discriminate)). lia.
    + cbn [concat]. rewrite app_nil_r. exact HNDsp.
    + rewrite HEV1. unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP in HEV. lia.
    + rewrite XMe.
      pose proof (fun y : list byte => mo_malloc_nonneg MT MTL (Z.of_nat (length y) + 1) ltac:(lia)) as NN.
      pose proof (mo_free_nonneg MT MTL) as FNN.
      refine (mok_station MT S S (XM_PINS_SET MT R uri files layout verdict) 0 (rec_spill_frees R * mo_free MT)
        MTL HMOK (mle_start MT S MTL) _ _).
      * apply Z.mul_nonneg_nonneg; [rewrite Hrsf; lia | exact FNN].
      * unfold XM_PINS_SET, XM_ANSWER_CODE, XM_HAND_BACK, XM_XSTRDUP.
        pose proof (NN (sarg uri)). pose proof (NN (sarg files)). pose proof (NN (sarg layout)).
        pose proof (NN (darg verdict (bstr "-"%string))).
        pose proof (NN (resp (snd (pins_set_m R uri files layout verdict)))).
        lia.
  - intros a Hfp. unfold rcf_fp in Hfp. cbn [length seq map app] in Hfp.
    apply inFP_cons in Hfp as [Ha | Hfp].
    + apply (ps_awr_prog B HB cmd_prog_img). right. cbn [Z.of_nat] in Ha.
      unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS, SC_SIZE in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr). cbn [concat] in Hin. rewrite app_nil_r in Hin.
      assert (HinQ : In (p, n) (lay_blocks Q)) by exact (ps_lay_spill_in Q (p, n) Hin).
      right; left. split.
      * unfold ps_FP. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (p + (a - p)) by lia.
        apply (inFP_ablocks_fp O p n (a - p) (proj2 (HO (p, n)) HinQ)). lia.
      * exists p, n. split; [exact (lay_blocks_in _ _ _ _ _ _ HA (p, n) HinQ) | lia].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Hfp Hw _. exfalso. pose proof (RCFLO a Hfp). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (HPERM & _ & _ & _ & _ & HSPOST & _ & HBB & HMLE).
rewrite K1.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
assert (HNDp : List.NoDup (ablocks B ly2 S2 ++ concat [l_spill Q]))
  by exact (Permutation_NoDup HPERM (recb_ablocks_nodup_m B ly S W mem md HAR)).
cbn [concat] in HNDp. rewrite app_nil_r in HNDp.
assert (HIN2 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly S))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
destruct (HSPOST R Q HAc eq_refl eq_refl) as (Qb & HAb & HOb).
(* the frame is outside the callee's window and its footprint *)
assert (FRM2 : pse_frame W2 mem2).
{ intros i r Hir.
  assert (Hi : (i < 10)%nat)
    by (change 10%nat with (length ps_saved); apply nth_error_Some; rewrite Hir; discriminate).
  apply (ps_aval_mem_in (rdW W mem1)); [exact (FRM i r Hir)|].
  intros y Hy. apply J9; [unfold ps_sp0 in *; lia | unfold ps_sp0 in *; lia |].
  intros Hf. pose proof (RCFLO y Hf). unfold ps_sp0 in *. lia. }
(* the recorder after the call: record.spill emptied, ready for the new call *)
assert (HREC : ps_rec0 B ly S R O ly2 S2 W2 mem2).
{ exists (set_spill R (fst (r_spill R), [])), Qb, (rdW W2 mem2), (ablocks B ly2 S2).
  split; [exact HAb|].
  split; [reflexivity|].
  split.
  { intros A0. unfold rec_record. cbn [set_spill r_calls]. rewrite Hlen16. reflexivity. }
  split.
  { intros _. pose proof HAb as (_ & _ & _ & (_ & _ & _ & _ & HSPb & _) & _).
    pose proof HSPb as (_ & _ & HlenPb & _).
    apply length_zero_iff_nil. rewrite HlenPb. reflexivity. }
  split; [intros x _; reflexivity|].
  split.
  { intros pn Hpn.
    assert (HpO : In pn O).
    { apply (proj2 (HO pn)). apply (proj2 (HOb pn)) in Hpn. unfold lay_blocks.
      apply in_app_or in Hpn as [Hpn | Hpn]; apply in_or_app;
        [left; exact Hpn | right; apply in_or_app; right; exact Hpn]. }
    exact (conj (lay_blocks_in _ _ _ _ _ _ HAb pn Hpn) (conj HpO (proj1 (ps_O_facts B ly S _ R O HREPA pn HpO)))). }
  split.
  { intros pn Hpn.
    destruct (in_dec recb_pair_dec pn O) as [HpO | HpO]; [|left; exact (conj (HIN2 pn Hpn) HpO)].
    right. apply (proj1 (HOb pn)). apply (proj1 (HO pn)) in HpO. unfold lay_blocks in HpO.
    apply in_app_or in HpO as [Hx | HpO]; [apply in_or_app; left; exact Hx|].
    apply in_app_or in HpO as [Hx | HpO];
      [exfalso; exact (list_nodup_app_disj _ _ pn HNDp Hpn Hx) | apply in_or_app; right; exact HpO]. }
  intros Hlt. exfalso. lia. }
assert (MO2 : mo_le MT S S2 (rec_spill_frees R * mo_free MT)) by (rewrite <- XMe; exact HMLE).
assert (BB2 : blocks_bytes S2 <= blocks_bytes S) by (unfold LIVE_REC_CALLS_FREE in HBB; lia).
assert (LIVE2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn HnO. apply (Permutation_in _ HPERM) in Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exact Hpn|].
  exfalso. cbn [concat] in Hpn. rewrite app_nil_r in Hpn. exact (HnO (proj2 (HO pn) (ps_lay_spill_in Q pn Hpn))). }
exact (HCONT PS_RET_RCF ly2 S2 W2 regs2 mem2 md2 (0 + EV_REC_CALLS_FREE [l_spill Q]) (or_intror eq_refl)
  (pse_jinv_intro ly2 S2 W2 regs2 mem2 md2 (0 + EV_REC_CALLS_FREE [l_spill Q]) HJ2 ltac:(rewrite HEV1; lia)
     MO2 BB2 FRM2 LIVE2 HREC (pse_jregs_pres regs1 regs2 HP2 REGS))).
Qed.

(* --- from the entry to record()'s join, both arms ------------------------------------------------------- *)
Lemma ps_seg_entry : ps_entry_stmt B MT ly S W regs mem md pu pf pl pv uri files layout verdict R O.
Proof.
unfold ps_entry_stmt. intros HCONT.
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn16.
destruct (Z.eq_dec (ps_n R) 16) as [E16 | Hne].
- exact (pse_run_spill E16 (pse_spill_call HCONT E16)).
- exact (pse_run_table ltac:(lia) (pse_table_join HCONT ltac:(lia))).
Qed.

End entry.
End e.
End f.
End d.
