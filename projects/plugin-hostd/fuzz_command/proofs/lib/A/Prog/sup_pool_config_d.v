(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the definitions shared by the segments of sup_pool_config's ASan walk
   (plugin-hostd/fuzz_command, 0x8bcfc): the walk's hypotheses as one record, the internal statement (statement gaps
   G1 and G2), the states where the segments meet, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v. *)

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c rec_shape_of_c answer_c hand_back_c mix_call_c sup_pool_config_c PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_pool_config_s1 sup_pool_config_s2 sup_pool_config_s3 sup_pool_config_s4 sup_pool_config_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* after a symbolic run, name the model the run leaves (with_vm_backing ...) so that it does not grow over a chain of
   runs (a measured trap) *)
Ltac spc_md := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.

(* the register files of the mid-walk seeds against their environments *)
Ltac spc_reg_case E32 E34 R9 R19 R20 R21 :=
lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get ?a ?rr) =>
  let w := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with w end;
first
[ rewrite getr_zero; reflexivity
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; symmetry; apply spc_E_reg; reflexivity
| cbn [sv_denot]; rewrite E34, unsigned_lit_small by (cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia);
  rewrite ?Z.add_0_r; first [exact R9 | exact R19]
| cbn [sv_denot]; rewrite E32, unsigned_lit_small by (cbv [SB]; lia); rewrite Z.add_0_r; exact R20
| change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 4) (SLit 3)) (SOff 32 0)) with spc_shx4;
  rewrite denot_lit_U, (spc_U_shx4 _ _ E32 E34) by (cbv [A_G_REC A_REC_SPILL OFF_CALLS] in *; lia); exact R21 ].

(* the record's fields under the hypothesis names the segment proofs use *)
Ltac spc_unpack HY :=
let HY' := fresh "HY'" in pose proof HY as HY';
destruct HY' as [TRCF TXSTRDUP TARG_I TREC_SHAPE_OF TANSWER VOBJS TL HB MTL SIGP cmd_prog_img cmd_prog_writable
  cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart CMD_RO_IN cmd_heap_tail_vis].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the walk's hypotheses: the statement's (sup_pool_config_c.v:69-74), those with cgif's names, and the per-binary
   record facts the statement does not give yet (lib/A/Prog/CmdRecFacts.v is to state them), under
   the recorder walks' shared names *)
Record spc_hyps (B : asyms) (MT : ameter_ops) : Prop := mk_spc_hyps {
spch_TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT;
spch_TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT;
spch_TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT;
spch_TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT;
spch_TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT;
spch_VOBJS : cmd_val_objs;
spch_TL : PALib B;
spch_HB : CmdBSyms B;
spch_MTL : ameter_laws MT;
spch_SIGP : cmd_sig_prog;
spch_cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a;
spch_cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG ->
  writable_at SEGS (mrestrict (w_H W) mem) a;
spch_cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem);
spch_RRO : ro_below_ofl SEGS RLO RHI;
spch_RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a;
spch_cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG;
(* the statement's deleted premise, for the verb literal handed to rec_shape_of (CmdRo.v:434) *)
spch_CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI);
(* G2 (b): a heap string's tail word, for xstrdup's pre (xstrdup_c.v:75) *)
spch_cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e
}.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : spc_hyps B MT.

(* the statement's post (sup_pool_config_c.v:102-121) and its premises (:80-101), word for word *)
Definition spc_post ly S R O name max : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_pool_config_m R name max = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_POOL_CONFIG R name max /\
 mo_le MT S S' (XM_SUP_POOL_CONFIG MT R name max).

Definition spc_pre ly S W (regs : bvmap 5 word) mem md ch (pn max : Z) (name : option (list byte)) (R : rstate)
  (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SUP_POOL_CONFIG_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\ cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pn /\ 0 <= pn < 2 ^ 64 /\
getr regs 11 = w64 max /\ -2 ^ 31 <= max < 2 ^ 31 /\
(exists x, name = Some x /\
 in_blockA (ablocks B ly S) pn (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pn x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pn (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_POOL_CONFIG R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_POOL_CONFIG R name max <= LIVE_MAX /\
mo_ok MT S (XM_SUP_POOL_CONFIG MT R name max).

Definition spc_goal ly S W (regs : bvmap 5 word) mem md R O name max : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_POOL_CONFIG_STK (spc_FP O) regs ly S W mem md (EV_SUP_POOL_CONFIG R) (spc_post ly S R O name max).

(* the recorder's state record() starts from: R on the table arm, R with the spill emptied on the spill arm *)
Definition spc_RB (R : rstate) : rstate :=
if Nat.ltb (length (r_calls R)) 16 then R else set_spill R (fst (r_spill R), []).

(* the state at 0x8bdb4 (mv a0,s2; jal xstrdup): record() done (the slot holds REC_POOL_CONFIG and no argument),
   s2 = the string to copy, the saved registers in the frame *)
Definition spc_midD ly S W (regs : bvmap 5 word) mem md R O name max lyB SBs (rdB : reader)
  lyc Sc (Wc : world SEGS) memc mdc (regs1 : bvmap 5 word) (s : Z) (O0 F : list (Z * Z)) : Prop :=
let c := spc_slot R in let x := sarg name in
ajournal SEGS B SUP_POOL_CONFIG_STK (spZ regs) (spc_FP O) ly S W mem md [] lyc Sc Wc memc mdc (rec_spill_frees R) /\
(forall pn, In pn (ablocks B lyc Sc) <-> In pn (ablocks B ly S) /\ ~ In pn F) /\
(forall pn, In pn F -> In pn O) /\ (forall pn, In pn O0 <-> In pn O /\ ~ In pn F) /\
(F <> [] -> (16 <= length (r_calls R))%nat) /\
blocks_bytes Sc <= blocks_bytes S /\ mo_le MT S Sc (rec_spill_frees R * mo_free MT) /\
spc_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs /\
rec_repA B lyB SBs rdB (spc_RB R) O0 /\
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ((length (r_calls R) < 16)%nat -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) ->
   ~ (c <= a < c + CALL_SIZE) -> rdW Wc memc a = rdB a) /\
(forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc memc (fst pn + i) = rdB (fst pn + i)) /\
((length (r_calls R) < 16)%nat -> aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)) /\
aval_mem (rdW Wc memc) c 4 REC_POOL_CONFIG /\ aval_mem (rdW Wc memc) (c + 4) 4 0 /\
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] s (Some x) /\
atail_vis SEGS Wc memc (s + Z.of_nat (length x)) /\
getr regs1 2 = w64 (spZ regs - 64) /\ getr regs1 8 = w64 max /\ getr regs1 9 = w64 c /\ getr regs1 18 = w64 s /\
getr regs1 19 = w64 (c + 4) /\ getr regs1 20 = w64 SB /\ getr regs1 21 = w64 (SB + (c + 4) / 8) /\
(forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

(* the state at 0x8bd78, where record()'s two arms meet: s1 = the slot c, s0 = max, s2 = the name pointer, s4 = the
   shadow base; on the table arm g_rec.ncalls is n + 1 and nothing else moved (rdB is the entry); on the spill arm
   rec_calls_free emptied record.spill (rdB is the state it left, F the blocks it freed) *)
Definition spc_midJ ly S W (regs : bvmap 5 word) mem md R O (pn : Z) name max lyB SBs (rdB : reader)
  lyc Sc (Wc : world SEGS) memc mdc (regs1 : bvmap 5 word) (O0 F : list (Z * Z)) : Prop :=
let c := spc_slot R in
ajournal SEGS B SUP_POOL_CONFIG_STK (spZ regs) (spc_FP O) ly S W mem md [] lyc Sc Wc memc mdc (rec_spill_frees R) /\
(forall pn, In pn (ablocks B lyc Sc) <-> In pn (ablocks B ly S) /\ ~ In pn F) /\
(forall pn, In pn F -> In pn O) /\ (forall pn, In pn O0 <-> In pn O /\ ~ In pn F) /\
(F <> [] -> (16 <= length (r_calls R))%nat) /\
blocks_bytes Sc <= blocks_bytes S /\ mo_le MT S Sc (rec_spill_frees R * mo_free MT) /\
spc_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs /\
rec_repA B lyB SBs rdB (spc_RB R) O0 /\
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ((length (r_calls R) < 16)%nat -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) ->
   ~ (c <= a < c + CALL_SIZE) -> rdW Wc memc a = rdB a) /\
(forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc memc (fst pn + i) = rdB (fst pn + i)) /\
((length (r_calls R) < 16)%nat -> aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)) /\
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] pn name /\
(forall x, name = Some x -> atail_vis SEGS Wc memc (pn + Z.of_nat (length x))) /\
getr regs1 2 = w64 (spZ regs - 64) /\ getr regs1 8 = w64 max /\ getr regs1 9 = w64 c /\ getr regs1 18 = w64 pn /\
getr regs1 20 = w64 SB /\
(forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

(* the state at 0x8bdfc, the return from arg_i (the FP state may have changed there: the rest of the walk is proved
   at any FP state): the slot holds REC_POOL_CONFIG with the two arguments p1 (xstrdup's copy of the name) and p2
   (arg_i's copy of dec max); the blocks are the entry's less the F record() freed, plus the two copies *)
Definition spc_midI ly S W (regs : bvmap 5 word) mem md R O name max (O0 F : list (Z * Z)) (p1 p2 : Z)
  ly3 S3 (W3 : world SEGS) mem3 md3 (regs3 : bvmap 5 word) : Prop :=
let c := spc_slot R in let x := sarg name in
let n1 := LIVE_XSTRDUP x in let n2 := Z.of_nat (length (dec max)) + 1 in
ajournal SEGS B SUP_POOL_CONFIG_STK (spZ regs) (spc_FP O) ly S W mem md [] ly3 S3 W3 mem3 md3
  (rec_spill_frees R + EV_XSTRDUP + EV_ARG_I) /\
(forall bq, In bq (ablocks B ly3 S3) <-> (In bq (ablocks B ly S) /\ ~ In bq F) \/ bq = (p1, n1) \/ bq = (p2, n2)) /\
(forall bq, In bq F -> In bq O) /\ (forall bq, In bq O0 <-> In bq O /\ ~ In bq F) /\
~ (In (p1, n1) (ablocks B ly S) /\ ~ In (p1, n1) F) /\ ~ (In (p2, n2) (ablocks B ly S) /\ ~ In (p2, n2) F) /\
p1 <> p2 /\
blocks_bytes S3 <= blocks_bytes S + n1 + n2 /\
mo_le MT S S3 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x + XM_ARG_I MT max) /\
Z.of_nat (length (frames S3)) <= 8 /\
spc_frame_at (mrestrict (w_H W3) mem3) (spZ regs) regs /\
rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R REC_POOL_CONFIG [x; dec max]) (O0 ++ [(p1, n1); (p2, n2)]) /\
getr regs3 2 = w64 (spZ regs - 64) /\ getr regs3 8 = w64 max /\ getr regs3 9 = w64 c /\ getr regs3 20 = w64 SB /\
(forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).

(* what a segment hands to the next: the rest of the walk from the meeting state *)
Definition spc_cont_J ly S W (regs : bvmap 5 word) mem md R O pn name max : Prop :=
forall lyB SBs rdB lyc Sc Wc memc mdc regs1 O0 F,
spc_midJ ly S W regs mem md R O pn name max lyB SBs rdB lyc Sc Wc memc mdc regs1 O0 F ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SPC_JOIN)) memc (seg_rom SEGS)) mdc)
  (spc_goal ly S W regs mem md R O name max).

Definition spc_cont_D ly S W (regs : bvmap 5 word) mem md R O name max : Prop :=
forall lyB SBs rdB lyc Sc Wc memc mdc regs1 s O0 F,
spc_midD ly S W regs mem md R O name max lyB SBs rdB lyc Sc Wc memc mdc regs1 s O0 F ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SPC_DUP)) memc (seg_rom SEGS)) mdc)
  (spc_goal ly S W regs mem md R O name max).

Lemma spc_regs_okD : forall (regs regs1 : bvmap 5 word) c,
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL ->
getr regs1 9 = w64 c -> getr regs1 19 = w64 (c + 4) -> getr regs1 20 = w64 SB -> getr regs1 21 = w64 (SB + (c + 4) / 8) ->
regs_ok (Eimg (Ereg regs1 (spc_extra regs 0 c))) spc_regsD regs1.
Proof.
intros regs regs1 c Hc R9 R19 R20 R21. unfold w64 in *.
destruct (spc_E_lit regs regs1 0 c) as (E32 & _ & E34).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr]; [spc_reg_case E32 E34 R9 R19 R20 R21|]); try (destruct Hr; fail).
Qed.

Lemma spc_regs_okJ : forall (regs regs1 : bvmap 5 word) c,
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL ->
getr regs1 9 = w64 c -> getr regs1 20 = w64 SB ->
regs_ok (Eimg (Ereg regs1 (spc_extra regs 0 c))) spc_regsJ regs1.
Proof.
intros regs regs1 c Hc R9 R20. unfold w64 in *.
destruct (spc_E_lit regs regs1 0 c) as (E32 & _ & E34).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr]; [spc_reg_case E32 E34 R9 R9 R20 R20|]); try (destruct Hr; fail).
Qed.

(* s0 holds max at the program calls: a value no frame chain starts from *)
Lemma spc_achain_max : forall ly rd sp max, -2 ^ 31 <= max < 2 ^ 31 -> ly_top ly <= 2 ^ 47 ->
achain ly rd sp (bv_unsigned (w64 max)) [].
Proof.
intros ly rd sp max Hm Ht. pose proof asan_consts as (C1 & _). left. split; [|reflexivity].
unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z_lt_le_dec max 0) as [Hn | Hp].
- right; left. rewrite Z.mod_eq by lia.
  assert (Hq : max / 2 ^ 64 = -1) by (symmetry; apply Z.div_unique with (r := max + 2 ^ 64); lia). rewrite Hq. lia.
- left. rewrite Z.mod_small by lia. lia.
Qed.

(* the stack of each callee fits inside the member's *)
Lemma spc_stk : SUP_POOL_CONFIG_STK = Z.max (64 + Z.max REC_CALLS_FREE_STK (Z.max XSTRDUP_STK (Z.max ARG_I_STK REC_SHAPE_OF_STK))) ANSWER_STK.
Proof. reflexivity. Qed.

(* arodata_okP from the entry to any later state of the walk (CmdBase.arodata_ok_journalP): no read-only byte is
   in the footprint *)
Lemma spc_aro : forall STK sp0 O ly S W mem md own ly' S' W' mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (spc_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HO HJ HR.
spc_unpack HY.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B STK sp0 (spc_FP O) ly S W mem md own ly' S' W' mem' md' k HJ);
  [|exact HR].
intros a Hro (r & Hr & Ha). destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply HnPG. apply recb_grec_in. unfold REC_SIZE in *. lia.
- apply HnPG. apply recb_spill_in. unfold SC_SIZE in *. lia.
- destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & Hpn & Hpa).
  exact (proj1 (spc_blk_off B cmd_prog_img ly S W mem md p n a HAR (HO _ Hpn) Hpa) Himg).
Qed.

Lemma spc_abytes_prefix : forall (rd : reader) a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof. intros rd a l1 l2 H k Hk. rewrite (H k ltac:(rewrite length_app; lia)). rewrite app_nth1 by lia. reflexivity. Qed.

(* the verb "pool_config" (.str.12, 0x21e80) as rec_shape_of reads it *)
Definition spc_verb : list byte := bstr "pool_config"%string.
Lemma spc_verb_lit : RO_lit_21e80 = spc_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma spc_verb_len : Z.of_nat (length spc_verb) = 11.
Proof. reflexivity. Qed.

Lemma spc_verb_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21e80 spc_verb.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
assert (H : abytes_atR rd 0x21e80 RO_lit_21e80).
{ repeat match type of HRO with
  | abytes_atR _ 0x21e80 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
rewrite spc_verb_lit in H. exact (spc_abytes_prefix rd _ _ _ H).
Qed.

Lemma spc_verb_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21e80 spc_verb.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
assert (H : abytes_atR rd 0x21e80 RO_lit_21e80).
{ repeat match type of HRO with
  | abytes_atR _ 0x21e80 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
rewrite spc_verb_lit in H. split; [exact H|].
vm_compute. intros Hc. repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]). exact Hc.
Qed.

(* the verb's end is one of the record's literal ends, and its bytes pass the record's shadow checkers *)
Lemma spc_verb_end : In (0x21e80 + Z.of_nat (length spc_verb)) cmd_ro_ends.
Proof.
assert (H : existsb (Z.eqb (0x21e80 + Z.of_nat (length spc_verb))) cmd_ro_ends = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (e & He & Hq). apply Z.eqb_eq in Hq. rewrite Hq. exact He.
Qed.
Lemma spc_verb_chk : cmd_addr_b 0x21e80 (Z.of_nat (length spc_verb) + 1) = true /\
  cmd_hull_b 0x21e80 (Z.of_nat (length spc_verb) + 1) = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma spc_verb_ro : forall ro, cmd_ro_in ro -> forall i, 0 <= i < 12 -> ro (0x21e80 + i).
Proof.
intros ro HRO. unfold cmd_ro_in in HRO.
repeat match type of HRO with
| (forall i, 0 <= i < 12 -> ro (0x21e80 + i)) /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

(* the verb's bytes lie outside the runtime's owned statics and the errno cell (AF0m.v's tables) *)
Lemma spc_verb_unowned : forall a, 0x21e80 <= a < 0x21e80 + 12 ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. spc_unpack HY. rewrite (ts_owned B HB), (ts_errno B HB).
assert (Hchk : forallb (fun r => (fst r + snd r <=? 0x21e80) || (0x21e80 + 12 <=? fst r)) Tfib_owned_static = true)
  by (vm_compute; reflexivity).
split.
- intros Hown. apply Exists_exists in Hown as ([r rl] & Hr & Har). unfold in_zr in Har. cbn [fst snd] in Har.
  rewrite forallb_forall in Hchk. specialize (Hchk (r, rl) Hr). cbn [fst snd] in Hchk.
  apply orb_true_iff in Hchk as [H | H]; apply Z.leb_le in H; lia.
- unfold TFIB_ERRNO. lia.
Qed.

(* the footprint of the contract lies below the allocator's ceiling *)
Lemma spc_FP_low : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, inFP (spc_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a (r & Hr & Ha). pose proof asan_consts as (C1 & _).
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Ha))) as (p & n & Hpn & Hpa).
  destruct (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ p n HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

(* a heap string's tail word is visible at any state where its block is live (G2 (b), cmd_heap_tail_vis) *)
Lemma spc_heap_tail : forall ly S (W : world SEGS) mem md s (x : list byte), AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) s (Z.of_nat (length x) + 1) -> atail_vis SEGS W mem (s + Z.of_nat (length x)).
Proof.
intros ly S W mem md s x HAR (b & k & Hbk & Hbs & Hse). spc_unpack HY.
exact (cmd_heap_tail_vis ly S W mem md b k (s + Z.of_nat (length x)) HAR Hbk ltac:(lia)).
Qed.

End e.
End f.
End d.
