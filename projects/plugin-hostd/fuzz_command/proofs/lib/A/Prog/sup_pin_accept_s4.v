(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: block P of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command): the entry,
   the inlined record(13) with both of its arms (the call of rec_calls_free on record.spill when the table already
   holds 16 calls), the two instrumented checks on the slot and the `bnez s1` join, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed of a walk segment, the run, the step through a program call)
   over fuzz_command's listing; it finishes the function by lib/A/Prog/sup_pin_accept_s2.v's `spa_from_B0`. *)

(* sup_pin_accept (recorder.c:428-434, entry 0x8bb90): this file walks 0x8bb90 .. 0x8bc40.
   - 0x8bb90 .. 0x8bbcc: the 48-byte frame (ra, s0 .. s4), the shadow base from the GOT cell, g_rec.ncalls, and
     record()'s `bne ncalls, 16`.
   - the spill arm (ncalls = 16): rec_calls_free(&record.spill, 1) frees the spill's argument blocks and clears its
     nargs field, then `j 0x8bc04`.
   - the slot arm (ncalls < 16): g_rec.ncalls := ncalls + 1 and s0 := g_rec + 16 + 56 * ncalls.
   - MEET 0x8bc04 .. 0x8bc34: the instrumented check of the slot's shadow byte (a load of the byte at
     (a >> 3) + 0x7fff8000 and a compare; the error path it guards is not reached, because the slot lies in g_rec or
     in record.spill, which the memory-checking runtime's record marks usable), c->fn := 13, the same check on
     c->nargs, and c->nargs := 0.
   - JOIN 0x8bc34: `bnez s1`. The statement hands uri as a string in a live heap block, so s1 >= 4096 and the
     branch is taken; the NULL arm (s1 := "(null)") is shown infeasible. At B0 = 0x8bc40 `spa_from_B0`
     (lib/A/Prog/sup_pin_accept_s2.v) takes over. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c hand_back_c answer_c sup_pin_accept_c RecBLemmas
sup_pin_accept_r sup_pin_accept_s1 sup_pin_accept_s3 sup_pin_accept_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of this half's cut points in the listing *)
Definition SPA_BR : Z := AF_sup_pin_accept + 0x3c.      (* bne a2,a3 (0x8bbcc) *)
Definition SPA_RET_RCF : Z := AF_sup_pin_accept + 0x54. (* after the call of rec_calls_free (0x8bbe4) *)
Definition SPA_MEET : Z := AF_sup_pin_accept + 0x74.    (* record()'s two arms meet (0x8bc04) *)

(* --- the symbolic state of the entry segment ----------------------------------------------------------- *)
(* atoms: the 32 registers, 32 = the shadow base, 33 = g_rec.ncalls; regions: the 48-byte frame below the entry sp
   (atom 2), the GOT word of the shadow-base cell, that cell, and g_rec.ncalls *)
Definition spa_ncalls : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
  [YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition spa_rsA : smem := [stack_region SPA_FRAME; got_regionP; bcell_regionP 32%nat; spa_ncalls].
Definition spa_factsA : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 16 0);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition ss_spaA : sstate := mkSS AF_sup_pin_accept sr_atoms spa_rsA None spa_factsA.
Definition spa_BxA : sv := SOff 32 0.
Definition spa_extraA (n : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 n].

(* --- the symbolic state where record()'s two arms meet (0x8bc04) ---------------------------------------- *)
(* the registers hold: sp = the entry sp - 48, s0 = the slot c (atom 33), s1 = uri, s3 = the shadow base (atom 32);
   the frame holds the entry's ra, s0 .. s4 (atoms 34 .. 39, as spa_extra lists them) *)
Definition spa_mframe : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 SPA_FRAME 0 0
  [YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
   YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
(* the slot: the walk writes its fn and nargs fields, and reads nothing of it *)
Definition spa_mslot : YP09.region := YP09.mkRegion (Some SA_C) 0 CALL_SIZE 0 8 [].
Definition spa_mrs : smem := [spa_mframe; spa_mslot].
Definition spa_mregs : list sv := Eval vm_compute in
sr_set (sr_set sr_atoms 8 (SOff SA_C 0)) 19 spa_Bx.
Definition ss_meet : sstate := mkSS SPA_MEET spa_mregs spa_mrs None spa_facts.

(* --- the recorder's representation under record()'s stores (the forms of lib/A/Prog/sup_pin_accept_r.v) ---- *)

(* a call record with function fn and no argument yet *)
Lemma spa_acall_new : forall bl rd a fn,
  0 <= fn < REC_FN_COUNT -> aval_mem rd (a + CALL_OFF_FN) 4 fn -> aval_mem rd (a + CALL_OFF_NARGS) 4 0 ->
  acall_at bl rd a (fn, []) [].
Proof.
  intros bl rd a fn Hfn BF BA. unfold acall_at. cbn [fst snd length].
  split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
  split; [exact BF|]. split; [exact BA|]. split; [cbn [map]; constructor|].
  intros k s pn Es. destruct k; discriminate.
Qed.

Section r. Variable B : asyms.

(* record(fn) on the slot arm: ncalls := n + 1, and the slot's fn and nargs fields written *)
Lemma spa_rep_record_lt : forall ly S rd ly' S' rd' R O fn c,
  rec_repA B ly S rd R O -> (length (r_calls R) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) ->
  aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) ->
  aval_mem rd' (c + CALL_OFF_FN) 4 fn -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  (forall a, spa_in_rec a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
     ~ (c <= a < c + 8) -> rd' a = rd a) ->
  spa_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' (rec_record R fn []) O.
Proof.
  intros ly S rd ly' S' rd' R O fn c (Q & HR & HO) Hn Hfn Ec BN BF BA KG KO.
  unfold spa_keepsO in KO. subst c.
  rewrite (rec_record_calls R fn [] Hn).
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  assert (LB : lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q).
  { unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
    rewrite !app_nil_r. reflexivity. }
  exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)). split; [|rewrite LB; exact HO].
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  apply (spa_arep_rest _ _ rd rd' R _ Q _ HR); try reflexivity.
  - intros a Ha. apply KG; unfold spa_in_rec, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_calls r_calls r_spill l_calls l_spill].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ C6))))).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app, C2. reflexivity.
    + rewrite length_app, Nat2Z.inj_add. exact BN.
    + intros i cl P Ec EP.
      destruct (Nat.lt_ge_cases i (length (r_calls R))) as [Hi|Hi].
      * rewrite nth_error_app1 in Ec by exact Hi. rewrite nth_error_app1 in EP by (rewrite C2; exact Hi).
        destruct (C4 i cl P Ec EP) as [Hcl HL]. split; [|exact HL].
        apply (spa_acall_keep _ _ rd rd' _ cl P Hcl).
        -- intros x Hx. apply KG; unfold spa_in_rec, REC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
        -- intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
           exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
      * destruct (Nat.eq_dec i (length (r_calls R))) as [->|Hne].
        -- rewrite nth_error_app2, Nat.sub_diag in Ec by lia. cbn in Ec. injection Ec as <-.
           rewrite nth_error_app2 in EP by (rewrite C2; lia). rewrite C2, Nat.sub_diag in EP. cbn in EP.
           injection EP as <-.
           split; [exact (spa_acall_new _ rd' _ fn Hfn BF BA) | constructor].
        -- exfalso. assert (N : nth_error (r_calls R ++ [(fn, [])]) i = None)
             by (apply nth_error_None; rewrite length_app; cbn [length]; lia).
           rewrite N in Ec. discriminate.
    + apply (spa_acall_keep _ _ rd rd' _ _ _ C5).
      * intros x Hx. apply KG; unfold spa_in_rec, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold ag1_own. rewrite LB. exact HW.
Qed.

(* record(fn) on the spill arm, after rec_calls_free emptied the spill: its fn and nargs written *)
Lemma spa_rep_spill_fn : forall ly S rd ly' S' rd' R O fn,
  rec_repA B ly S rd R O -> snd (r_spill R) = [] -> 0 <= fn < REC_FN_COUNT ->
  aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 fn -> aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
  (forall a, spa_in_rec a -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rd a) ->
  spa_keepsO rd rd' (ablocks B ly' S') O ->
  rec_repA B ly' S' rd' (set_spill R (fn, [])) O.
Proof.
  intros ly S rd ly' S' rd' R O fn (Q & HR & HO) Hs0 Hfn BF BA KG KO.
  unfold spa_keepsO in KO.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S') /\
            forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
    by (intros pn Hpn; apply KO; apply HO; exact Hpn).
  exists Q. split; [|exact HO].
  pose proof HR as (_ & _ & H3 & HC & _ & _ & _ & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold iv_apart, REC_SIZE, SC_SIZE in H3.
  assert (Els : l_spill Q = []).
  { destruct C5 as (_ & _ & Hl & _). rewrite Hs0 in Hl. apply length_zero_iff_nil. exact Hl. }
  apply (spa_arep_rest _ _ rd rd' R _ Q Q HR); try reflexivity.
  - intros a Ha. apply KG; unfold spa_in_rec, REC_SIZE, SC_SIZE in *; lia.
  - intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn.
  - unfold ag1_calls. cbn [set_spill r_calls r_spill fst snd].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ (Forall_nil _)))))).
    + apply (spa_aval_mem_keep rd); [exact C3 | intros x Hx;
        apply KG; unfold spa_in_rec, REC_SIZE, SC_SIZE, OFF_NCALLS in *; lia].
    + intros i cl P Ec EP. destruct (C4 i cl P Ec EP) as [Hcl HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (spa_acall_keep _ _ rd rd' _ cl P Hcl).
      * intros x Hx. apply KG; unfold spa_in_rec, REC_SIZE, SC_SIZE, OFF_CALLS, CALL_SIZE in *; lia.
      * intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + rewrite Els. exact (spa_acall_new _ rd' _ fn Hfn BF BA).
  - exact HW.
Qed.

(* the call count and the spill entry, in the forms record()'s branch and rec_calls_free's pre ask them *)
Lemma spa_rep_ncalls : forall ly S rd R O, rec_repA B ly S rd R O ->
  (length (r_calls R) <= 16)%nat /\ aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))).
Proof. intros ly S rd R O (Q & (_ & _ & _ & (C1 & _ & C3 & _) & _) & _). split; assumption. Qed.

Lemma spa_rep_spill : forall ly S rd R O, rec_repA B ly S rd R O -> exists Q,
  arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)) /\
  (length (l_spill Q) <= 6)%nat /\ length (l_spill Q) = length (snd (r_spill R)) /\
  aval_mem rd (A_REC_SPILL + CALL_OFF_NARGS) 4 (Z.of_nat (length (l_spill Q))) /\
  (forall a pn, nth_error (l_spill Q) a = Some pn ->
     aval_mem rd (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\ In pn (ablocks B ly S)) /\
  NoDup (map fst (l_spill Q)) /\
  (forall pn, In pn (lay_blocks Q) <-> In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) \/ In pn (l_spill Q)).
Proof.
  intros ly S rd R O (Q & HR & HO). exists Q.
  pose proof HR as (_ & _ & _ & (_ & _ & _ & _ & C5 & _) & _).
  destruct C5 as (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk).
  split; [exact HR|]. split; [exact HO|].
  split; [rewrite Hl; exact Hn|]. split; [exact Hl|].
  split; [rewrite Hl; exact Hb1|].
  split.
  - intros a pn Ea.
    assert (Hal : (a < length (snd (r_spill R)))%nat)
      by (rewrite <- Hl; apply nth_error_Some; rewrite Ea; discriminate).
    destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (Hk a s pn Es Ea) as (V & _ & Hin & _). split; [exact V | exact Hin].
  - split; [exact Hnd|].
    intros pn. unfold lay_blocks. split.
    + intros H. apply in_app_or in H as [H|H]; [left; apply in_or_app; left; exact H|].
      apply in_app_or in H as [H|H]; [right; exact H|]. left. apply in_or_app. right. exact H.
    + intros [H|H].
      * apply in_app_or in H as [H|H]; [apply in_or_app; left; exact H|].
        apply in_or_app. right. apply in_or_app. right. exact H.
      * apply in_or_app. right. apply in_or_app. left. exact H.
Qed.
End r.

(* the slot of the recorder state R, as spa_slot_of names it *)
Lemma spa_slot_of_ok : forall R c, (length (r_calls R) <= 16)%nat -> spa_slot_of R c -> spa_slot_ok c.
Proof.
intros R c Hlen [(Hlt & ->) | (Hge & ->)]; [left | right; reflexivity].
assert (Hn : 0 <= Z.of_nat (length (r_calls R)) < 16) by lia.
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE.
split; [lia|]. split; [lia|].
replace (6174528 + 16 + 56 * Z.of_nat (length (r_calls R)))
  with ((771818 + 7 * Z.of_nat (length (r_calls R))) * 8) by lia.
apply Z_mod_mult.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition spa_EA (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (spa_extraA n)).
Definition spa_EM (regsc regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regsc (spa_extra regs c)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* --- Section e of lib/A/Prog/sup_pin_accept_s2.v, with the callee of record()'s spill arm (the statement's own,
       sup_pin_accept_c.v:67) and the per-binary pcs of the entry's GOT word and shadow cell (TL) ------------- *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S W mem md p n e, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
(* the callee of record()'s spill arm *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
(* the GOT word of the shadow-base cell and that cell, which the prologue loads (the walk hypothesis TL) *)
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* --- the two seeds ------------------------------------------------------------------------------------- *)

Lemma spa_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the seed of the entry segment: the frame the prologue will write, the GOT word of the shadow cell, that cell,
   and g_rec.ncalls *)
Lemma spa_seedA : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md n,
AR SEGS B ly S W mem md ->
astk_ok SUP_PIN_ACCEPT_STK ly (spZ regs) ->
(forall a, spZ regs - SUP_PIN_ACCEPT_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (spa_EA regs n) ss_spaA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_pin_accept)) mem (seg_rom SEGS)))
/\ sh_ok SEGS spa_BxA [] (spa_EA regs n) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md n HAR Hstk Hpres Hn HNC.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
set (E := spa_EA regs n).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold spa_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold spa_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ subst E. unfold spa_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), spa_grec_val. reflexivity. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [|unfold sh_ok; apply Forall_nil].
unfold ss_spaA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold spa_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold spa_rsA, stack_region, got_regionP, bcell_regionP, spa_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. unfold SPA_FRAME. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR).
      apply recb_grec_in. unfold A_G_REC, REC_SIZE, OFF_NCALLS in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold spa_rsA, stack_region, got_regionP, bcell_regionP, spa_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)).
  cbn [nth cmd_objs]. unfold SPA_FRAME, A_G_REC, OFF_NCALLS in *.
  rewrite WS in Hslo. repeat split; lia.
- split; [|split; exact I].
  cbn [spa_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E32, E33, EG, !unsigned_lit_small by (unfold SB, A_G_REC; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, A_G_REC.
  rewrite WS in Hslo.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the state where record()'s two arms meet (0x8bc04): the slot c is chosen, the frame holds the entry's
   ra, s0 .. s4, and nothing of the slot has been written yet *)
Lemma spa_meet_seed : forall ly S (W : world SEGS) mem md (regs regs1 : bvmap 5 word) c sp0,
AR SEGS B ly S W mem md ->
2 ^ 46 <= sp0 - SPA_FRAME -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> spa_slot_ok c ->
spZ regs1 = sp0 - SPA_FRAME ->
getr regs1 8 = w64 c -> getr regs1 19 = w64 SB ->
(forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (spa_EM regs1 regs c) ss_meet
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + SPA_MEET)) mem (seg_rom SEGS)))
/\ sh_ok SEGS spa_Bx spa_SH (spa_EM regs1 regs c) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regs1 c sp0 HAR Hsp Hsp47 Hsp16 Hc Hsp1 R8 R19 HFR.
destruct (spa_slot_bounds c Hc) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e3750 <= c <= 0x5e3be0 /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := spa_EM regs1 regs c).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r).
{ intros nn r Hnn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. unfold spa_EM.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (spa_extra regs c) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold spa_EM. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E SA_SB = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E SA_C = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (ESB' : ew E 32 = Z_to_bv 64 SB) by exact ESB.
assert (EC' : ew E 33 = Z_to_bv 64 c) by exact EC.
assert (Usp : bv_unsigned (ew E 2) = sp0 - SPA_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp1).
assert (UC : bv_unsigned (ew E SA_C) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E SA_SB) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
split; [|exact (spa_shok B HB ly S W mem md E c HAR Hc ESB' EC')].
rewrite restrict_mkst_fx. unfold ss_meet. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr.
  clear HFR.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
        let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      first [ apply getr_zero
            | symmetry; apply EE; reflexivity
            | rewrite ESB'; exact R19
            | rewrite EC'; exact R8 ]
    | ]); try (destruct Hr; fail).
- vm_compute. reflexivity.
- unfold spa_mrs, spa_mframe, spa_mslot.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold SPA_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?nn 0))) =>
      let j := eval compute in (nn - 34)%nat in let r := eval compute in (nth j spa_saved 0) in
      let m := eval compute in (nn - 32)%nat in
      apply (chunk_ok_val SEGS E _ (sp0 - 48) off 8 (SOff nn 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        change (ew E nn) with (ew E (32 + m)%nat); rewrite (EX m ltac:(cbv; lia));
        cbn [spa_extra nth map app spa_saved]; symmetry; apply Z_to_bv_bv_unsigned
      | let HR := fresh in pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR;
        change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
      | cbn; lia
      | replace (sp0 - 48 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
  + rewrite UC. split; [lia|]. split; [unfold CALL_SIZE; lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|].
    apply (spa_in_PG c); [exact Hc | unfold CALL_SIZE; lia].
- apply pairwise_disjoint_of_extents. unfold spa_mrs, spa_mframe, spa_mslot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SPA_FRAME, CALL_SIZE in *. repeat split; lia.
- split; [|split; exact I].
  cbn [spa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, UC, USB. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold SPA_FRAME in *. split; [split; [lia | split; [|lia]]|].
  { replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
  split; [unfold SB; lia | split; [|exact I]].
  split; [unfold A_G_REC, OFF_CALLS, A_REC_SPILL; lia | split; [exact Hc8 | lia]].
Qed.

(* --- the state at B0, once each arm has reached it ------------------------------------------------------- *)
Lemma spa_B0_gen : forall ly S W regs mem md ch uri R O lyc Sc Wc memc (mdc : Model) k c O1
  (regs2 : bvmap 5 word) memB mdB s,
afn_pre SEGS B SUP_PIN_ACCEPT_STK ly S W regs mem md ch ->
frm0 fx ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_PIN_ACCEPT R <= EV_MAX -> blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri <= LIVE_MAX ->
mo_ok MT S (XM_SUP_PIN_ACCEPT MT R uri) ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
ajournal SEGS B SUP_PIN_ACCEPT_STK (spZ regs) (spa_FP O) ly S W mem md [] lyc Sc Wc memB mdB k ->
k <= rec_spill_frees R -> mo_le MT S Sc (rec_spill_frees R * mo_free MT) -> blocks_bytes Sc <= blocks_bytes S ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
spZ regs2 = spZ regs - SPA_FRAME ->
getr regs2 8 = w64 c -> getr regs2 9 = w64 s -> getr regs2 18 = w64 (c + 4) ->
getr regs2 19 = w64 SB -> getr regs2 20 = w64 (SB + (c + 4) / 8) ->
getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
(forall r, 21 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
spa_slot_ok c -> spa_slot_of R c ->
(forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rd' a = rdW Wc memc a) ->
   aval_mem rd' (c + CALL_OFF_FN) 4 REC_PIN_ACCEPT -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
   rec_repA B lyc Sc rd' (rec_record R REC_PIN_ACCEPT []) O1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc memB a = rdW Wc memc a) ->
aval_mem (rdW Wc memB) (c + CALL_OFF_FN) 4 REC_PIN_ACCEPT ->
aval_mem (rdW Wc memB) (c + CALL_OFF_NARGS) 4 0 ->
astr_argA B lyc Sc (rdW Wc memB) (in_roP SEGS RLO RHI) [] s (Some (sarg uri)) ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SPA_B0)) memB (seg_rom SEGS)) mdB)
  (apost_baseF SEGS B SUP_PIN_ACCEPT_STK (spa_FP O) regs ly S W mem md (EV_SUP_PIN_ACCEPT R) (spa_post B MT R uri O ly S)).
Proof.
intros ly S W regs mem md ch uri R O lyc Sc Wc memc mdc k c O1 regs2 memB mdB s
  HPRE HFRM Hfr8 Hev Hlive HMOK HRODc HJ Hk HMLE Hbb HBK1 HBK2 HO1 HOO1 HOS Rsp R8 R9 R18 R19 R20 R3 R4 Rhi
  HFR Hc Hcm HPEND KEEP VFN VNA HSTR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
destruct (spa_slot_bounds c Hc) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e3750 <= c <= 0x5e3be0 /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
pose proof (proj1 HJ) as HARB.
(* the recorder at B0 *)
assert (HREP : rec_repA B lyc Sc (rdW Wc memB) (rec_record R REC_PIN_ACCEPT []) O1)
  by (apply HPEND; [exact KEEP | exact VFN | exact VNA]).
(* the read-only bytes at B0 *)
assert (HRO_slot : forall a, in_roP SEGS RLO RHI a -> 0 <= a < 2 ^ 64 /\ ~ (c <= a < c + 8)).
{ intros a Ha. destruct (cmd_ro_prog_apart a Ha) as [Hi Hn]. pose proof (pa_img_range a Hi).
  unfold kLowMemEnd in *. split; [lia|]. intros Hin.
  apply Hn. exact (spa_in_PG c a Hc ltac:(unfold CALL_SIZE; lia)). }
assert (HRODB : arodata_okP SEGS RLO RHI B (rdW Wc memB)).
{ apply (spa_aro_kept B RLO RHI (rdW Wc memc)); [exact HRODc|].
  intros a Ha. destruct (HRO_slot a Ha) as [H1 H2]. exact (KEEP a H1 H2). }
pose proof (cmd_ro_ok_of_aro lyc Sc Wc memB mdB HARB HRODB) as HROB.
(* the frame's six words at B0 *)
assert (HFRB : forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H Wc) memB) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj.
  assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some spa_saved j)); rewrite Hj; discriminate).
  apply (val_mem_view SEGS (w_H Wc) memB). apply (spa_aval_mem_keep (rdW Wc memc)); [apply (aval_mem_view SEGS (w_H Wc) memc); exact (HFR j r Hj)|].
  intros x Hx. cbn [Z.of_nat] in Hx. rewrite WS in Hslo. apply KEEP; lia. }
(* spa_from_B0's Section hypotheses are this Section's (the same names and forms): fill each from the context, then
   its own premises in its intro order *)
pose proof (spa_from_B0 B MT) as FB.
repeat (lazymatch type of FB with ?A -> ?C => specialize (FB ltac:(assumption)) end).
exact (FB ly S W regs mem md ch uri R O lyc Sc Wc regs2 memB mdB k c O1 s
  HPRE HFRM Hfr8 Hev Hlive HMOK HJ Hk HMLE Hbb HBK1 HBK2 HO1 HOO1 HOS Rsp R8 R9 R18 R19 R20 R3 R4 Rhi HFRB
  Hc Hcm HREP HRODB HROB HSTR).
Qed.

(* --- from the meet of record()'s two arms to B0 ---------------------------------------------------------- *)
Lemma spa_meet : forall ly S W regs mem md ch (pu : Z) uri x R O lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k c O1,
afn_pre SEGS B SUP_PIN_ACCEPT_STK ly S W regs mem md ch ->
frm0 fx ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_PIN_ACCEPT R <= EV_MAX -> blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri <= LIVE_MAX ->
mo_ok MT S (XM_SUP_PIN_ACCEPT MT R uri) ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
ajournal SEGS B SUP_PIN_ACCEPT_STK (spZ regs) (spa_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= rec_spill_frees R -> mo_le MT S Sc (rec_spill_frees R * mo_free MT) -> blocks_bytes Sc <= blocks_bytes S ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
spZ regs1 = spZ regs - SPA_FRAME ->
getr regs1 8 = w64 c -> getr regs1 9 = w64 pu -> getr regs1 19 = w64 SB ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall r, 21 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
spa_slot_ok c -> spa_slot_of R c ->
(forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rd' a = rdW Wc memc a) ->
   aval_mem rd' (c + CALL_OFF_FN) 4 REC_PIN_ACCEPT -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
   rec_repA B lyc Sc rd' (rec_record R REC_PIN_ACCEPT []) O1) ->
(* the caller's string, in a live heap block *)
uri = Some x ->
in_blockA (ablocks B lyc Sc) pu (Z.of_nat (length x) + 1) -> astr_atR (rdW Wc memc) pu x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
SRr SEGS Wc (cfg_at SEGS (BASE + SPA_MEET) regs1 memc mdc)
  (apost_baseF SEGS B SUP_PIN_ACCEPT_STK (spa_FP O) regs ly S W mem md (EV_SUP_PIN_ACCEPT R) (spa_post B MT R uri O ly S)).
Proof.
intros ly S W regs mem md ch pu uri x R O lyc Sc Wc regs1 memc mdc k c O1
  HPRE HFRM Hfr8 Hev Hlive HMOK HRODc HJ Hk HMLE Hbb HBK1 HBK2 HO1 HOO1 HOS Rsp R8 R9 R19 R3 R4 Rhi HFR
  Hok Hcm HPEND Hux HBLKx HSTRx HLx.
subst uri.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
destruct (spa_slot_bounds c Hok) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e3750 <= c <= 0x5e3be0 /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
assert (Hsp46 : 2 ^ 46 <= sp0 - SPA_FRAME) by (unfold SPA_FRAME; rewrite WS in Hslo; lia).
pose proof (proj1 HJ) as HARc.
(* the caller's block: above 4096, below the stack, no byte of the image *)
pose proof HBLKx as (qx & kx & HXqk & HXlo & HXhi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ qx kx HARc HXqk) as (_ & HX4096 & HXceil & _ & _ & _ & HXk0).
pose proof (req_size_pos kx ltac:(lia)) as [_ HXqr].
destruct (spa_meet_seed lyc Sc Wc memc mdc regs regs1 c sp0 HARc Hsp46 ltac:(lia) Hal16 Hok Rsp R8 R19 HFR)
  as [HS SHOK].
set (E := spa_EM regs1 regs c) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, spa_EM; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r).
{ intros nn r Hnn. unfold E, spa_EM. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (spa_extra regs c) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, spa_EM. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E 33 = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (UC : bv_unsigned (ew E 33) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = sp0 - SPA_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
clearbody E.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK spa_Bspan.
{ unfold ss_meet, spa_mrs, spa_mframe, spa_mslot. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := SA_C) (b := c); [reflexivity | exact UC | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (spa_awr_slot B HB cmd_prog_img c a); [exact Hok | unfold CALL_SIZE; lia]. }
(* the two stores wrote the slot's fn and nargs fields and nothing else *)
lazymatch goal with Hfr : frame_of E _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc m1 a = rdW Wc memc a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c <= a < c + 8) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?Usp, ?UC in Hrr; cbv beta; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]); clear Hfr end.
(* 0x8bc34: `bnez s1`, the two arms of the NULL test *)
psrr_branch_tok RUN BR HS SHOK spa_Bspan.
- (* uri is not NULL: s1 is the caller's pointer *)
  paj_run_to_tok RUNTO HS HJ SHOK spa_Bspan SPA_B0.
  { cbn [ss_mem add_cond].
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := SA_C) (b := c); [reflexivity | exact UC | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (spa_awr_slot B HB cmd_prog_img c a); [exact Hok | unfold CALL_SIZE; lia]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19.
  pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ _ (20%bv : bv 5) HS) as Q20.
  lazymatch type of Q20 with _ = sv_denot _ (sr_get ?aa ?rr) =>
    let v := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with v in Q20 end.
  cbn [ms_regs restrict mkst] in Q20.
  assert (Rsp2 : spZ (ms_regs ms0) = spZ regs - SPA_FRAME) by (unfold spZ at 1; rewrite Q2; exact Usp).
  assert (Q3' : getr (ms_regs ms0) 3 = getr regs 3) by (rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3).
  assert (Q4' : getr (ms_regs ms0) 4 = getr regs 4) by (rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4).
  assert (Q8' : getr (ms_regs ms0) 8 = w64 c) by (rewrite Q8; exact EC).
  assert (Q18' : getr (ms_regs ms0) 18 = w64 (c + 4)) by (rewrite Q18, UC; reflexivity).
  assert (Q19' : getr (ms_regs ms0) 19 = w64 SB) by (rewrite Q19; exact ESB).
  assert (Q20' : getr (ms_regs ms0) 20 = w64 (SB + (c + 4) / 8)).
  { rewrite Q20, (denot_shx E 33 32 4 c SB EC ESB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)).
    reflexivity. }
  assert (Qhi : forall r, 21 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (Rhi r Hr).
    assert (Hr7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr7 as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Qr end;
     rewrite Qr; apply EE; reflexivity). }
  lazymatch goal with Hfr : frame_of E _ (mrestrict _ ?mA) (mrestrict _ ?mB) |- _ =>
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc mB a = rdW Wc memc a)
    by (intros a Ha Hn; etransitivity; [|exact (KEEP1 a Ha Hn)];
        apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c <= a < c + 8) Hfr);
        [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
            rewrite ?Usp, ?UC in Hrr; cbv beta; lia|]);
          destruct Hin
        | exact Ha | exact Hn ]) end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) spa_mslot) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRs end.
  cbn [ms_mem restrict mkst] in HRs.
  assert (VFN' : aval_mem (rdW Wc (ms_mem ms0)) (c + CALL_OFF_FN) 4 REC_PIN_ACCEPT).
  { apply (aval_mem_view SEGS (w_H Wc) (ms_mem ms0)).
    exact (field_of_region (segs:=SEGS) E _ 33 c _ _ _ _ _ 0 4%N (SLit 13) 13 HRs UC
      ltac:(cbn; right; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (VNA' : aval_mem (rdW Wc (ms_mem ms0)) (c + CALL_OFF_NARGS) 4 0).
  { apply (aval_mem_view SEGS (w_H Wc) (ms_mem ms0)).
    exact (field_of_region (segs:=SEGS) E _ 33 c _ _ _ _ _ 4 4%N (SLit 0) 0 HRs UC
      ltac:(cbn; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the string at B0: the stores touched only the slot, which is image, the string's block is not *)
  assert (HSTRB : astr_argA B lyc Sc (rdW Wc (ms_mem ms0)) (in_roP SEGS RLO RHI) [] pu (Some (sarg (Some x)))).
  { cbn [sarg astr_argA]. split; [lia|]. split.
    - apply (spa_astr_keep (rdW Wc memc)); [exact HSTRx|]. intros a Ha.
      apply KEEP; [lia|]. intros Hin.
      apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc qx kx a HARc HXqk ltac:(lia)).
      apply cmd_prog_img. apply (spa_in_PG c a Hok). unfold CALL_SIZE. lia.
    - split; [exact HLx|]. left. split; [exists qx, kx; split; [exact HXqk | lia] | apply Forall_nil]. }
  assert (Q9' : getr (ms_regs ms0) 9 = w64 pu) by (rewrite Q9, (EE 9%nat 9%bv eq_refl); exact R9).
  exact (spa_B0_gen ly S W regs mem md ch (Some x) R O lyc Sc Wc memc mdc k c O1 (ms_regs ms0) (ms_mem ms0) _ pu
    HPRE HFRM Hfr8 Hev Hlive HMOK HRODc HJ Hk HMLE Hbb HBK1 HBK2 HO1 HOO1 HOS
    Rsp2 Q8' Q9' Q18' Q19' Q20' Q3' Q4' Qhi HFR Hok Hcm HPEND KEEP VFN' VNA' HSTRB).
- (* s1 = 0: the NULL arm, which no heap string takes *)
  exfalso.
  assert (HU : U E (SOff 9 0) = pu)
    by (apply (U_atom E 9 pu); [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | lia]).
  rewrite branch_ne_U, HU, U_SLit in Hc.
  replace (zcanon 0) with 0 in Hc by (vm_compute; reflexivity).
  apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia.
Qed.

(* --- the entry segment's facts ---------------------------------------------------------------------------- *)

(* a write of g_rec / record.spill is one the footprint names (the core's program-static disjunct of awr_byte) *)
Lemma spa_awr_rec : forall STK sp0 O bl0 blc fr0 ly own a,
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp0 (spa_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha.
right; right; right; right; left.
assert (HP : Exists (in_zr a) recb_PG) by (destruct Ha as [Ha | Ha]; [apply recb_grec_in | apply recb_spill_in]; exact Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma spa_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma spa_zcanon : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x.
Proof. intros x Hx. unfold zcanon, M64. apply Z.mod_small. exact Hx. Qed.

(* s0 on the slot arm: g_rec + 16 + 56 * ncalls (slli / slli / sub folded to one multiplication) *)
Lemma spa_denot_slot : forall E nn, ew E 33 = Z_to_bv 64 (Z.of_nat nn) -> ew E 285 = Z_to_bv 64 A_G_REC ->
(nn < 16)%nat ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat nn).
Proof.
intros E nn E33 E285 Hn. apply spa_denot_U.
assert (U1 : U E (SOff 33 0) = Z.of_nat nn) by (apply (U_atom E 33 (Z.of_nat nn) E33); lia).
assert (U5 : U E (SOff 285 0) = A_G_REC) by (apply (U_atom E 285 A_G_REC E285); unfold A_G_REC; lia).
rewrite U_SAlu, U_SAlu, U_SMd, U1, U5, !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (spa_zcanon 56), (spa_zcanon 16) by lia.
rewrite (spa_zcanon (Z.of_nat nn * 56)) by lia.
rewrite (spa_zcanon (Z.of_nat nn * 56 + 16)) by lia.
unfold A_G_REC, OFF_CALLS, CALL_SIZE. rewrite spa_zcanon by lia. lia.
Qed.

(* the seed of a segment that starts right after a call, with no region: the registers only *)
Lemma spa_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS spa_BxA [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split; [|apply Forall_nil].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.

(* the blocks rec_calls_free frees take their bytes out of the live count *)
Lemma spa_bb_perm : forall ly S ly2 S2 P, Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ P) ->
(forall pn, In pn P -> 0 <= snd pn) -> blocks_bytes S2 <= blocks_bytes S.
Proof.
intros ly S ly2 S2 P HP Hpos.
rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B ly2 S2).
rewrite (bsum_perm _ _ HP), bsum_app.
assert (HP0 : 0 <= bsum P).
{ clear - Hpos. induction P as [|pn P IH]; [cbn; lia|].
  rewrite bsum_cons. pose proof (Hpos pn (or_introl eq_refl)).
  assert (0 <= bsum P) by (apply IH; intros q Hq; apply Hpos; right; exact Hq). lia. }
lia.
Qed.

(* the frame's six words, read off the entry segment's stack region *)
Lemma spa_frame_words : forall (W : world SEGS) m (regs : bvmap 5 word) E0 sp0 cs,
(forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r) ->
bv_unsigned (ew E0 2) = sp0 ->
region_ok SEGS E0 (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 cs) ->
(forall j r, nth_error spa_saved j = Some r ->
   In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) m) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros W m regs E0 sp0 cs HEL Hsp HR HIn j r Hj.
assert (Hr : In r spa_saved) by (eapply nth_error_In; exact Hj).
assert (Hr32 : 0 <= r < 32) by (cbv [spa_saved In] in Hr; lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region (segs:=SEGS) E0 _ 2%nat sp0 cs _ _ _ _ (-8 - 8 * Z.of_nat j) 8%N
  (SOff (Z.to_nat r) 0) (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HEL (Z.to_nat r) (Z_to_bv 5 r)).
  + rewrite Z.add_0_r. reflexivity.
  + rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
Qed.

(* the footprint of rec_calls_free on record.spill alone: the spill's nargs word and the blocks it frees *)
Lemma spa_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
A_REC_SPILL + 4 <= a < A_REC_SPILL + 8 \/ exists p n, In (p, n) P /\ p <= a < p + req_size n.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat] in Ha. rewrite app_nil_r in Ha.
apply inFP_app in Ha as [Ha | Ha].
- left. apply inFP_cons in Ha as [Ha | Ha];
  [unfold CALL_SIZE, CALL_OFF_NARGS in Ha; cbn in Ha; lia | exact (False_ind _ (inFP_nil a Ha))].
- right. exact (inFP_ablocks_fp_inv P a Ha).
Qed.

Lemma spa_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite SIGP by (vm_compute; repeat (first [left; reflexivity | right])). reflexivity. Qed.

Lemma spa_rcf_spares : forall P a, (forall p k, In (p, k) P -> 4096 <= p) ->
~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) -> (forall p k, In (p, k) P -> ~ (p <= a < p + req_size k)) ->
fp_spares (rcf_fp A_REC_SPILL [P]) a.
Proof.
intros P a Hpos Hs Hb. apply fp_spares_closed.
- intros H0. unfold YI16.sink_open_fp in H0. apply in_fp_inFP in H0.
  destruct (spa_rcf_fp_inv P 0 H0) as [H | (p & k & Hin & Hr)]; [unfold A_REC_SPILL in H; lia|].
  pose proof (Hpos p k Hin). lia.
- intros H. destruct (spa_rcf_fp_inv P a H) as [H' | (p & k & Hin & Hr)]; [exact (Hs H') | exact (Hb p k Hin Hr)].
Qed.

Theorem spa_entry : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)),
afn_pre SEGS B SUP_PIN_ACCEPT_STK ly S W regs mem md ch ->
frm0 fx ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(exists x, uri = Some x /\
 in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_PIN_ACCEPT R <= EV_MAX -> blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri <= LIVE_MAX ->
mo_ok MT S (XM_SUP_PIN_ACCEPT MT R uri) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_pin_accept) regs mem md)
  (apost_baseF SEGS B SUP_PIN_ACCEPT_STK (spa_FP O) regs ly S W mem md (EV_SUP_PIN_ACCEPT R) (spa_post B MT R uri O ly S)).
Proof.
intros ly S W regs mem md ch pu uri R O HPRE HFRM HROD HROOK H10 Hpu HURI HREP HFR8 HEV HLIVE HMOK.
destruct HURI as (x & Hux & HBLKx & HSTRx & HLx & HAPx).
(* the caller's block, which is none of the recorder's *)
pose proof HBLKx as (qx & kx & HXqk & HXlo & HXhi).
assert (HXnO : ~ In (qx, kx) O).
{ intros HqO. rewrite Forall_forall in HAPx. pose proof (HAPx (qx, kx) HqO) as Hd.
  unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
assert (Hsp46 : 2 ^ 46 + 48 <= spZ regs <= 2 ^ 47)
  by (change (2 ^ 46) with 70368744177664; change (2 ^ 47) with 140737488355328; rewrite WS in Hslo; lia).
destruct (spa_rep_ncalls B ly S (rdW W mem) R O HREP) as [Hlen HNC].
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj1 (spa_rep_blocks B ly S (rdW W mem) R O HREP pn Hpn))).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
destruct (spa_seedA ly S W regs mem md n HAR Hstk Hpres Hn HNC) as [HS SHOK].
set (E := spa_EA regs n) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, spa_EA; apply Eimg_env).
assert (EL : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs r).
{ intros kk r Hk. unfold E, spa_EA. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (unfold E, spa_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
  by (unfold E, spa_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat)).
assert (EG : ew E 285 = Z_to_bv 64 A_G_REC).
{ change 285%nat with (A_OBJ 44).
  rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), spa_grec_val. reflexivity. }
assert (ESP : ew E 292 = Z_to_bv 64 A_REC_SPILL).
{ change 292%nat with (A_OBJ 51).
  rewrite (img_env_atomP E (A_OBJ 51) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
assert (UG : bv_unsigned (ew E 285) = A_G_REC) by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
clearbody E.
pose proof (ajournal_init SEGS B SUP_PIN_ACCEPT_STK (spa_FP O) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at, w64.
(* 0x8bb90 .. 0x8bbcc: the frame, the shadow base, g_rec.ncalls, record()'s branch *)
paj_run_tok RUN HS HJ SHOK spa_Bspan.
{ awr_ok_tac; [exact Usp|].
  eapply awr_ok_cons_gen; [reflexivity | exact UG | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply spa_awr_rec. left.
  unfold OFF_NCALLS, REC_SIZE in *. lia. }
assert (WIN : forall b wlo whi a, In (b, wlo, whi) (windows spa_rsA) ->
  base_val E b + wlo <= a < base_val E b + whi ->
  spZ regs - 48 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4).
{ intros b wlo whi a Hin Hrr. vm_compute in Hin. cbv beta.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UG in Hrr;
     first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin. }
psrr_branch_tok RUN BR HS SHOK spa_Bspan.
- (* g_rec.ncalls <> 16: the call takes the slot g_rec.calls[ncalls] *)
  assert (Hn16 : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33 n E33 ltac:(lia)), U_SLit in Hc.
    rewrite (spa_zcanon 16) in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc. unfold n in Hc. lia. }
  assert (Hsf : rec_spill_frees R = 0).
  { unfold rec_spill_frees.
    replace (Nat.ltb (length (r_calls R)) 16) with true by (symmetry; apply Nat.ltb_lt; exact Hn16). reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK spa_Bspan SPA_MEET.
  { awr_ok_tac; [exact Usp|].
    eapply awr_ok_cons_gen; [reflexivity | exact UG | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply spa_awr_rec. left.
    unfold OFF_NCALLS, REC_SIZE in *. lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ (8%bv : bv 5) HS) as P8.
  lazymatch type of P8 with _ = sv_denot _ (sr_get ?aa ?rr) =>
    let v := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with v in P8 end.
  cbn [ms_regs restrict mkst] in P8.
  (* the memory the prologue and the slot arm wrote *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha H1 H2.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
      (fun a => spZ regs - 48 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr0);
      [ | intros b wlo whi a' Hin Hrr; vm_compute in Hin; cbv beta;
          repeat (destruct Hin as [Hq | Hin];
            [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UG in Hrr;
             first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin
      | exact Ha | tauto].
    exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) _ HFr WIN a Ha ltac:(tauto)). }
  assert (HGt : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms0)))
    by exact (mem_grows_trans _ _ _ HG HG0).
  (* the frame and the bumped call count *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region SPA_FRAME)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRst;
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) spa_ncalls) in
    pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn end.
  cbn [ms_mem restrict mkst] in HRst, HRn.
  assert (HFRW : forall j r, nth_error spa_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 8 - 8 * Z.of_nat j) 8
      (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  { apply (spa_frame_words W (ms_mem ms0) regs E (spZ regs) _ EL Usp HRst).
    intros j r Hj.
    do 6 (destruct j as [|j];
      [ cbn [nth_error spa_saved] in Hj; injection Hj as <-;
        lazymatch goal with |- In ?x ?l => let y := eval vm_compute in x in change (In y l) end;
        cbn [In]; repeat (first [left; reflexivity | right]) |]).
    destruct j; cbn in Hj; discriminate. }
  assert (HNC1 : aval_mem (rdW W (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4 (n + 1)).
  { apply (aval_mem_view SEGS (w_H W) (ms_mem ms0)). change 4%nat with (N.to_nat 4).
    apply (field_of_region (segs:=SEGS) E _ 285 A_G_REC _ _ _ _ _ 8 4%N (SOff 33 1) _ HRn UG
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); [|cbn; lia|cbn; lia].
    apply spa_denot_U. rewrite U_SOff, E33, unsigned_lit_small by lia. apply spa_zcanon. lia. }
  (* the read-only image and the blocks are untouched *)
  assert (KEEPB : forall q k a, In (q, k) (ablocks B ly S) -> q <= a < q + k ->
    rdW W (ms_mem ms0) a = rdW W mem a).
  { intros q k a Hin Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hin) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
    apply KEEP; [lia | rewrite WS in Hslo; lia |].
    intros Hnc. apply (blk_img SEGS B LAWS ly S W mem md q k a HAR Hin ltac:(lia)).
    apply cmd_prog_img, recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
  assert (KEEPR : forall a, in_roP SEGS RLO RHI a -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Hro. destruct (cmd_ro_prog_apart a Hro) as [Hi Hpg].
    pose proof (pa_img_range a Hi) as Hrg. unfold kLowMemEnd in Hrg.
    apply KEEP; [lia | rewrite WS in Hslo; lia |].
    intros Hnc. apply Hpg, recb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia. }
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0)))
    by (apply (spa_aro_kept B RLO RHI (rdW W mem)); [exact HROD | exact KEEPR]).
  (* the registers at the meet *)
  assert (Rsp2 : spZ (ms_regs ms0) = spZ regs - SPA_FRAME).
  { unfold spZ at 1. rewrite P2. cbn [sv_denot]. rewrite Usp, unsigned_lit_small by lia.
    unfold SPA_FRAME. lia. }
  assert (P3' : getr (ms_regs ms0) 3 = getr regs 3) by (rewrite P3; apply EL; reflexivity).
  assert (P4' : getr (ms_regs ms0) 4 = getr regs 4) by (rewrite P4; apply EL; reflexivity).
  assert (P9' : getr (ms_regs ms0) 9 = w64 pu) by (rewrite P9, (EL 10%nat 10%bv eq_refl); exact H10).
  assert (P19' : getr (ms_regs ms0) 19 = w64 SB) by (rewrite P19; exact E32).
  assert (P8' : getr (ms_regs ms0) 8 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * n)).
  { rewrite P8, (spa_denot_slot E (length (r_calls R)) E33 EG Hn16). reflexivity. }
  assert (Phi : forall r, 21 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (Hr7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr7 as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Pr end; rewrite Pr; apply EL; reflexivity). }
  (* the caller's string at the meet *)
  assert (HSTRc : astr_atR (rdW W (ms_mem ms0)) pu x).
  { apply (spa_astr_keep (rdW W mem)); [exact HSTRx|]. intros a Ha. apply (KEEPB qx kx a HXqk). lia. }
  set (c := A_G_REC + OFF_CALLS + CALL_SIZE * n) in P8' |- *.
  assert (Hcm : spa_slot_of R c) by (left; split; [exact Hn16 | reflexivity]).
  assert (Hok : spa_slot_ok c) by (apply (spa_slot_of_ok R); [lia | exact Hcm]).
  (* the recorder after record()'s stores into the slot *)
  assert (HPEND : forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rd' a = rdW W (ms_mem ms0) a) ->
    aval_mem rd' (c + CALL_OFF_FN) 4 REC_PIN_ACCEPT -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
    rec_repA B ly S rd' (rec_record R REC_PIN_ACCEPT []) O).
  { intros rd' Hrd' HFN HNA.
    apply (spa_rep_record_lt B ly S (rdW W mem) ly S rd' R O REC_PIN_ACCEPT c HREP Hn16
      ltac:(unfold REC_PIN_ACCEPT, REC_FN_COUNT; lia) eq_refl).
    - apply (spa_aval_mem_keep (rdW W (ms_mem ms0))); [exact HNC1|].
      intros y Hy. apply Hrd'; unfold c, A_G_REC, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
    - exact HFN.
    - exact HNA.
    - intros a Ha Hnc Hslot.
      rewrite (Hrd' a); [|unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact Hslot].
      apply KEEP; [unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
        | rewrite WS in Hslo; unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact Hnc].
    - intros pn Hpn. split; [exact (HOS pn Hpn)|]. intros i Hi.
      destruct pn as [q k]. cbn [fst snd] in Hi |- *.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR (HOS _ Hpn)) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
      rewrite (Hrd' (q + i)).
      + exact (KEEPB q k (q + i) (HOS _ Hpn) ltac:(lia)).
      + lia.
      + intros Hin.
        apply (blk_img SEGS B LAWS ly S W mem md q k (q + i) HAR (HOS _ Hpn) ltac:(lia)).
        apply cmd_prog_img, recb_grec_in. unfold c, A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. nia. }
  exact (spa_meet ly S W regs mem md ch pu uri x R O ly S W (ms_regs ms0) (ms_mem ms0) _ 0 c O
    HPRE HFRM HFR8 HEV HLIVE HMOK HRODc HJ ltac:(rewrite Hsf; lia)
    ltac:(rewrite Hsf, Z.mul_0_l; exact (mle_start MT S MTL)) ltac:(lia)
    (fun pn Hpn => Hpn) (fun pn Hpn (_ : ~ In pn O) => Hpn)
    (fun pn Hpn => Hpn) (fun pn Hpn (_ : In pn (ablocks B ly S)) => Hpn) HOS
    Rsp2 P8' P9' P19' P3' P4' Phi HFRW Hok Hcm HPEND Hux HBLKx HSTRc HLx).
- (* g_rec.ncalls = 16: record() frees the spill's arguments by rec_calls_free(&record.spill, 1) *)
  assert (Hn16 : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U, (U_atom E 33 n E33 ltac:(lia)), U_SLit in Hc.
    rewrite (spa_zcanon 16) in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc. unfold n in Hc. lia. }
  destruct HREP as (QL & HA & HO).
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & HSP & _) & _).
  pose proof HSP as (_ & HSP6 & HLP & _ & HSPN & HSPND & HSPA).
  set (P := l_spill QL) in *.
  assert (Hsf : rec_spill_frees R = Z.of_nat (length P)).
  { unfold rec_spill_frees.
    replace (Nat.ltb (length (r_calls R)) 16) with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite HLP. reflexivity. }
  assert (HEVk : EV_REC_CALLS_FREE [P] = Z.of_nat (length P))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (HPin : forall pn, In pn P -> In pn (ablocks B ly S))
    by (intros pn Hpn; exact (proj1 (spa_acall_in _ _ _ _ _ pn HSP Hpn))).
  assert (HPO : forall pn, In pn P -> In pn O).
  { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  assert (HPpos : forall p k, In (p, k) P -> 4096 <= p).
  { intros p k Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & H4096 & _). exact H4096. }
  (* 0x8bbd0 .. 0x8bbe0: s0 := &record.spill, the call rec_calls_free(&record.spill, 1) *)
  paj_run_tok RUN HS HJ SHOK spa_Bspan.
  { awr_ok_tac; [exact Usp|].
    eapply awr_ok_cons_gen; [reflexivity | exact UG | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply spa_awr_rec. left.
    unfold OFF_NCALLS, REC_SIZE in *. lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (19%bv : bv 5) Q19.
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region SPA_FRAME)) in
      pose proof (st_ok_pi_region_nth E ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRst;
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) spa_ncalls) in
      pose proof (st_ok_pi_region_nth E ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn
  | st_ok _ _ ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region SPA_FRAME)) in
      pose proof (st_ok_region_nth (segs:=SEGS) E ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRst;
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) spa_ncalls) in
      pose proof (st_ok_region_nth (segs:=SEGS) E ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn
  end.
  cbn [ms_mem restrict mkst] in HRst, HRn.
  set (regsc := ms_regs ms0) in *. set (memc := ms_mem ms0) in *.
  (* the prologue wrote the frame only: g_rec.ncalls still holds ncalls *)
  assert (HNCc : aval_mem (rdW W memc) (A_G_REC + OFF_NCALLS) 4 n).
  { apply (aval_mem_view SEGS (w_H W) memc). change 4%nat with (N.to_nat 4).
    apply (field_of_region (segs:=SEGS) E _ 285 A_G_REC _ _ _ _ _ 8 4%N (SOff 33 0) _ HRn UG
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); [|cbn; lia|cbn; lia].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (KEEPw : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memc a = rdW W mem a).
  { intros a Ha H1 H2.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) memc
      (fun a => spZ regs - 48 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr0);
      [ | intros b wlo whi a' Hin Hrr; vm_compute in Hin; cbv beta;
          repeat (destruct Hin as [Hq | Hin];
            [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UG in Hrr;
             first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin
      | exact Ha | tauto].
    exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) _ HFr WIN a Ha ltac:(tauto)). }
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> rdW W memc a = rdW W mem a).
  { intros a Ha H1. destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hl | Hl];
    [|destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh | Hh]].
    - apply KEEPw; [exact Ha | exact H1 | lia].
    - replace a with ((A_G_REC + OFF_NCALLS) + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
      rewrite (HNCc (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)),
              (HNC (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)). reflexivity.
    - apply KEEPw; [exact Ha | exact H1 | lia]. }
  assert (KEEPBc : forall q k a, In (q, k) (ablocks B ly S) -> q <= a < q + k -> rdW W memc a = rdW W mem a).
  { intros q k a Hin Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hin) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
    apply KEEPc; [lia | rewrite WS in Hslo; lia]. }
  assert (KEEPRc : forall a, in_roP SEGS RLO RHI a -> rdW W memc a = rdW W mem a).
  { intros a Hro. destruct (cmd_ro_prog_apart a Hro) as [Hi Hpg].
    pose proof (pa_img_range a Hi) as Hrg. unfold kLowMemEnd in Hrg.
    apply KEEPc; [lia | rewrite WS in Hslo; lia]. }
  assert (HAc : arep_at (ablocks B ly S) (rdW W memc) A_G_REC A_REC_SPILL R QL).
  { apply (spa_arep_keep (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W memc) R QL HA).
    - intros a Ha. apply KEEPc;
      [unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
      | rewrite WS in Hslo; unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia].
    - intros pn Hpn. split; [exact (proj1 (spa_arep_in _ _ _ _ _ _ pn HA Hpn))|].
      intros i Hi. destruct pn as [q k]. cbn [fst snd] in Hi |- *.
      exact (KEEPBc q k (q + i) (proj1 (spa_arep_in _ _ _ _ _ _ (q, k) HA Hpn)) ltac:(lia)). }
  assert (HSPc : acall_at (ablocks B ly S) (rdW W memc) A_REC_SPILL (r_spill R) P)
    by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj2 (proj2 (proj2 HAc))))))))).
  pose proof HSPc as (_ & _ & _ & _ & HSPNc & HSPNDc & HSPAc).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W memc))
    by (apply (spa_aro_kept B RLO RHI (rdW W mem)); [exact HROD | exact KEEPRc]).
  (* the registers at the call *)
  assert (HRA : getr regsc 1 = Z_to_bv 64 (BASE + SPA_RET_RCF))
    by (rewrite Q1; first [reflexivity | apply codeptr_val; exact HEI]).
  assert (Q2' : getr regsc 2 = w64 (spZ regs - 48)).
  { rewrite Q2. cbn [sv_denot]. rewrite Usp. unfold w64. f_equal; try lia. }
  assert (Q3' : getr regsc 3 = getr regs 3) by (rewrite Q3; apply EL; reflexivity).
  assert (Q4' : getr regsc 4 = getr regs 4) by (rewrite Q4; apply EL; reflexivity).
  assert (Q8' : getr regsc 8 = w64 A_REC_SPILL) by (rewrite Q8; exact ESP).
  assert (Q9' : getr regsc 9 = w64 pu) by (rewrite Q9, (EL 10%nat 10%bv eq_refl); exact H10).
  assert (Q10' : getr regsc 10 = w64 A_REC_SPILL) by (rewrite Q10; exact ESP).
  assert (Q11' : getr regsc 11 = w64 (Z.of_nat (length [P]))) by (rewrite Q11; reflexivity).
  assert (Q19' : getr regsc 19 = w64 SB) by (rewrite Q19; exact E32).
  assert (Qhi : forall r, 21 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. unfold regsc.
    assert (Hr7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr7 as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Qr end; rewrite Qr; apply EL; reflexivity). }
  assert (HFRc : forall j r, nth_error spa_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  { apply (spa_frame_words W memc regs E (spZ regs) _ EL Usp HRst).
    intros j r Hj.
    do 6 (destruct j as [|j];
      [ cbn [nth_error spa_saved] in Hj; injection Hj as <-;
        lazymatch goal with |- In ?x ?l => let y := eval vm_compute in x in change (In y l) end;
        cbn [In]; repeat (first [left; reflexivity | right]) |]).
    destruct j; cbn in Hj; discriminate. }
  rewrite spa_sig_rcf.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W regsc memc _ SUP_PIN_ACCEPT_STK (spZ regs) (spa_FP O) ly S W mem md [] ly S _ 0
      REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [P]) (EV_REC_CALLS_FREE [P]) (-48) (getr regsc 1) [] _ HJ);
    [ unfold spZ at 1; rewrite Q2'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | reflexivity | lia | vm_compute; congruence | rewrite WS; vm_compute; congruence
    | rewrite Q3'; exact Hgp | rewrite Q4'; exact Htp | reflexivity
    | rewrite HRA; apply ret_ok_codeptr_v; [unfold SPA_RET_RCF, AF_sup_pin_accept; lia | reflexivity]
    | rewrite HRA, unsigned_lit_small by (unfold SPA_RET_RCF, AF_sup_pin_accept; lia);
      unfold SPA_RET_RCF, AF_sup_pin_accept; lia
    | apply achain_low; unfold s0Z; rewrite Q8'; unfold w64;
      rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia); unfold A_REC_SPILL; lia
    | | | ].
    - intros HPRE1.
      assert (HT := TRCF fx ly S W regsc memc _ [] A_REC_SPILL [P] HPRE1 HRODc Q10' Q11'
        ltac:(cbn [length]; lia)
        ltac:(right; left; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE; cbn [length Z.of_nat]; lia)
        ltac:(unfold A_REC_SPILL; reflexivity)).
      unfold apost_base, cfg_at, w64 in HT. apply HT.
      + intros i P' Hi. destruct i as [|i]; [|destruct i; discriminate Hi].
        cbn [nth_error] in Hi. injection Hi as <-.
        split; [rewrite HLP; exact HSP6|]. split.
        * cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r, HLP. exact HSPNc.
        * intros a pn Ha. destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es.
          -- destruct (HSPAc a s pn Es Ha) as (G1 & _ & G3 & _). split; [|exact G3].
             cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact G1.
          -- exfalso. apply nth_error_None in Es.
             pose proof (proj1 (nth_error_Some P a) ltac:(rewrite Ha; discriminate)). unfold P in *. lia.
      + cbn [concat]. rewrite app_nil_r. exact HSPNDc.
      + rewrite HEVk, <- Hsf. unfold EV_SUP_PIN_ACCEPT, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia.
      + apply (mo_ok_le MT MTL S _ (XM_SUP_PIN_ACCEPT MT R uri) HMOK).
        unfold XM_REC_CALLS_FREE, XM_SUP_PIN_ACCEPT, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
        cbn [concat]. rewrite app_nil_r, <- Hsf.
        pose proof (mo_free_nonneg MT MTL).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg uri)) + 1) ltac:(lia)).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_pin_accept_m R uri))) + 1) ltac:(lia)). lia.
    - intros a Ha. destruct (spa_rcf_fp_inv P a Ha) as [Hs | (p & k & Hin & Hr)].
      + apply spa_awr_rec. right. unfold A_REC_SPILL, SC_SIZE in *. lia.
      + unfold awr_byte. right; left. split; [|exists p, k; split; [exact (HPin _ Hin) | exact Hr]].
        unfold spa_FP. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp O p k (a - p)); [exact (HPO _ Hin) | lia].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
      destruct (spa_rcf_fp_inv P a Ha) as [Hs | (p & k & Hin & Hr)];
        [unfold A_REC_SPILL in Hs; rewrite WS in Hw; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & _ & Hpc & _). rewrite WS in Hw. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJr & HP2 & HK2).
  destruct HK2 as (HPERM & _ & _ & _ & _ & HRSP & _ & _ & HMLE).
  pose proof (HRSP R QL HAc eq_refl eq_refl) as HREP2.
  pose proof (proj1 HJr) as HAR2.
  pose proof HJr as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  (* 0x8bbe4: `j 0x8bc04`, record()'s arms meet *)
  rewrite HRA.
  destruct (spa_seed0 W2 regs2 mem2 SPA_RET_RCF) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 spa_Bspan SPA_MEET.
  { apply awr_ok_nil. }
  pmkst HS2.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H W2) mem2 (ms_mem ms1) (fun _ => False) HFr1);
    [|exact Ha | tauto]. intros b wlo whi a' Hin. destruct Hin. }
  assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 []))).
  { split; [intros nn Hnn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HAE2 ltac:(vm_compute; reflexivity)) as HPT3.
  cbn [ms_regs restrict] in HPT3.
  pose proof (aregs_preserved_trans _ _ _ HP2 HPT3) as HPR.
  (* the blocks across the call *)
  assert (HBK1 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly S)).
  { intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hpn. }
  assert (HBK2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
  { intros pn Hpn HnO. apply (Permutation_in _ HPERM) in Hpn. apply in_app_or in Hpn as [H | H]; [exact H|].
    exfalso. cbn [concat] in H. rewrite app_nil_r in H. exact (HnO (HPO _ H)). }
  set (O1 := concat (l_calls QL) ++ oblk (l_answer QL) ++ oblk (l_reply QL)) in *.
  assert (HO1 : forall pn, In pn O1 -> In pn O).
  { intros pn Hpn. apply HO. unfold lay_blocks, O1 in *. apply in_app_iff in Hpn as [H | H]; apply in_app_iff;
    [left; exact H | right; apply in_app_iff; right; exact H]. }
  assert (HNDl : List.NoDup (ablocks B ly S)) by exact (recb_ablocks_nodup_m B ly S W mem md HAR).
  assert (HOO1 : forall pn, In pn O -> In pn (ablocks B ly2 S2) -> In pn O1).
  { intros pn Hpn Hin2. apply HO in Hpn. unfold lay_blocks in Hpn. unfold O1.
    apply in_app_iff in Hpn as [H | H]; [apply in_app_iff; left; exact H|].
    apply in_app_iff in H as [H | H]; [|apply in_app_iff; right; exact H].
    exfalso. apply (list_nodup_app_disj (ablocks B ly2 S2) P pn); [|exact Hin2 | exact H].
    apply (Permutation_NoDup (l := ablocks B ly S)); [|exact HNDl].
    cbn [concat] in HPERM. rewrite app_nil_r in HPERM. exact HPERM. }
  (* the memory across the call *)
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) ->
    rdW W2 mem2 a = rdW W memc a).
  { intros a Hi Ho He Hs. apply (G3 a Hi Ho He). apply spa_rcf_spares; [exact HPpos | exact Hs|].
    intros p k Hin Hr. exact (blk_img SEGS B LAWS ly S W mem md p k a HAR (HPin _ Hin) Hr Hi). }
  assert (KBLK : forall q k a, In (q, k) (ablocks B ly S) -> ~ In (q, k) O -> q <= a < q + k ->
    rdW W2 mem2 a = rdW W memc a).
  { intros q k a Hin HnO Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hin) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
    replace a with (q + (a - q)) by lia.
    apply (G2 q k (a - q) Hin (HBK2 (q, k) Hin HnO)); [lia|].
    replace (q + (a - q)) with a by lia. intros Hf.
    destruct (spa_rcf_fp_inv P a Hf) as [Hs | (p & m & Hinp & Hr)].
    - apply (blk_img SEGS B LAWS ly S W mem md q k a HAR Hin ltac:(lia)).
      apply cmd_prog_img, recb_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia.
    - assert (Hne : (p, m) <> (q, k)) by (intros Eq; rewrite Eq in Hinp; exact (HnO (HPO _ Hinp))).
      pose proof (sep_blocks SEGS B LAWS ly S W mem md p m q k HAR (HPin _ Hinp) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KEEPB2 : forall q k a, In (q, k) (ablocks B ly S) -> ~ In (q, k) O -> q <= a < q + k ->
    rdW W2 (ms_mem ms1) a = rdW W mem a).
  { intros q k a Hin HnO Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hin) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
    rewrite KEEP3 by lia. rewrite (KBLK q k a Hin HnO Ha). exact (KEEPBc q k a Hin Ha). }
  assert (KEEPR2 : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 (ms_mem ms1) a = rdW W mem a).
  { intros a Hro Ho He. destruct (cmd_ro_prog_apart a Hro) as [Hi Hpg].
    pose proof (pa_img_range a Hi) as Hrg. unfold kLowMemEnd in Hrg.
    rewrite KEEP3 by lia.
    rewrite (KIMG a Hi Ho He
      ltac:(intros Hs; apply Hpg, recb_spill_in; unfold A_REC_SPILL, SC_SIZE in *; lia)).
    exact (KEEPRc a Hro). }
  (* the frame's six words across the call *)
  assert (HFRm : forall j r, nth_error spa_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (spZ regs - 8 - 8 * Z.of_nat j) 8
      (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  { intros j r Hj.
    assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some spa_saved j)); rewrite Hj; discriminate).
    apply (val_mem_view SEGS (w_H W2) (ms_mem ms1)). apply (spa_aval_mem_keep (rdW W memc)); [apply (aval_mem_view SEGS (w_H W) memc); exact (HFRc j r Hj)|].
    intros y Hy. cbn [Z.of_nat] in Hy. rewrite WS in Hslo.
    rewrite KEEP3 by lia.
    apply G1; [lia | unfold REC_CALLS_FREE_STK, ASTACK; lia |].
    intros Hf. destruct (spa_rcf_fp_inv P y Hf) as [Hs | (p & k & Hin & Hr)];
      [unfold A_REC_SPILL in Hs; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & _ & Hqc & _). lia. }
  (* the recorder after record()'s stores into the emptied spill *)
  assert (HPENDm : forall rd',
    (forall a, 0 <= a < 2 ^ 64 -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) -> rd' a = rdW W2 (ms_mem ms1) a) ->
    aval_mem rd' (A_REC_SPILL + CALL_OFF_FN) 4 REC_PIN_ACCEPT ->
    aval_mem rd' (A_REC_SPILL + CALL_OFF_NARGS) 4 0 ->
    rec_repA B ly2 S2 rd' (rec_record R REC_PIN_ACCEPT []) O1).
  { intros rd' Hrd' HFN HNA.
    rewrite (rec_record_spill R REC_PIN_ACCEPT [] Hn16).
    change (set_spill R (REC_PIN_ACCEPT, []))
      with (set_spill (set_spill R (fst (r_spill R), [])) (REC_PIN_ACCEPT, [])).
    apply (spa_rep_spill_fn B ly2 S2 (rdW W2 mem2) ly2 S2 rd' _ O1 REC_PIN_ACCEPT HREP2 eq_refl
      ltac:(unfold REC_PIN_ACCEPT, REC_FN_COUNT; lia) HFN HNA).
    - intros a Ha Hs. rewrite (Hrd' a)
        by (unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia).
      apply KEEP3. unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
    - intros pn Hpn.
      pose proof (proj1 (spa_rep_blocks B ly2 S2 (rdW W2 mem2) _ O1 HREP2 pn Hpn)) as Hin2.
      split; [exact Hin2|].
      intros i Hi. destruct pn as [q k]. cbn [fst snd] in Hi, Hin2 |- *.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR2 Hin2) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
      rewrite (Hrd' (q + i)).
      + apply KEEP3. lia.
      + lia.
      + intros Hin. apply (blk_img SEGS B LAWS ly2 S2 W2 mem2 md2 q k (q + i) HAR2 Hin2 ltac:(lia)).
        apply cmd_prog_img, recb_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia. }
  (* the read-only image at the meet *)
  assert (HRODm : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms1))).
  { intros a Hro Ho He. rewrite (KEEPR2 a Hro Ho He). exact (HROD a Hro Ho He). }
  (* the caller's string at the meet: its block is none of the recorder's, so rec_calls_free kept it *)
  assert (HBLKm : in_blockA (ablocks B ly2 S2) pu (Z.of_nat (length x) + 1)).
  { exists qx, kx. split; [exact (HBK2 (qx, kx) HXqk HXnO) | lia]. }
  assert (HSTRm : astr_atR (rdW W2 (ms_mem ms1)) pu x).
  { apply (spa_astr_keep (rdW W mem)); [exact HSTRx|]. intros a Ha. apply (KEEPB2 qx kx a HXqk HXnO). lia. }
  (* the registers at the meet *)
  assert (M2a : getr (ms_regs ms1) 2 = getr regsc 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
  assert (M8a : getr (ms_regs ms1) 8 = getr regsc 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
  assert (M9a : getr (ms_regs ms1) 9 = getr regsc 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
  assert (M19a : getr (ms_regs ms1) 19 = getr regsc 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
  assert (M3a : getr (ms_regs ms1) 3 = getr regsc 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
  assert (M4a : getr (ms_regs ms1) 4 = getr regsc 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
  assert (Rsp2 : spZ (ms_regs ms1) = spZ regs - SPA_FRAME).
  { unfold spZ at 1. rewrite M2a, Q2'.
    unfold w64. rewrite unsigned_lit_small by (rewrite WS in Hslo; lia). unfold SPA_FRAME. lia. }
  assert (M8 : getr (ms_regs ms1) 8 = w64 A_REC_SPILL) by (rewrite M8a; exact Q8').
  assert (M9 : getr (ms_regs ms1) 9 = w64 pu) by (rewrite M9a; exact Q9').
  assert (M19 : getr (ms_regs ms1) 19 = w64 SB) by (rewrite M19a; exact Q19').
  assert (M3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite M3a; exact Q3').
  assert (M4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite M4a; exact Q4').
  assert (Mhi : forall r, 21 <= r <= 27 -> getr (ms_regs ms1) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (intros r Hr; rewrite (HPR r ltac:(unfold acallee_saved; lia)); exact (Qhi r Hr)).
  assert (Hok : spa_slot_ok A_REC_SPILL) by (right; reflexivity).
  assert (Hcm : spa_slot_of R A_REC_SPILL) by (right; split; [lia | reflexivity]).
  assert (HBBm : blocks_bytes S2 <= blocks_bytes S).
  { apply (spa_bb_perm ly S ly2 S2 (concat [P])); [exact HPERM|].
    intros pn Hpn. cbn [concat] in Hpn. rewrite app_nil_r in Hpn.
    destruct pn as [q k]. cbn [snd].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR (HPin _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk0). lia. }
  exact (spa_meet ly S W regs mem md ch pu uri x R O ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _
    (0 + EV_REC_CALLS_FREE [P]) A_REC_SPILL O1
    HPRE HFRM HFR8 HEV HLIVE HMOK HRODm HJ2 ltac:(rewrite HEVk, Hsf; lia)
    ltac:(unfold XM_REC_CALLS_FREE in HMLE; cbn [concat] in HMLE; rewrite app_nil_r in HMLE;
          rewrite Hsf; exact HMLE) HBBm
    HBK1 HBK2 HO1 HOO1 HOS
    Rsp2 M8 M9 M19 M3 M4 Mhi HFRm Hok Hcm HPENDm Hux HBLKm HSTRm HLx).
Qed.

End e.
End f.
End d.
