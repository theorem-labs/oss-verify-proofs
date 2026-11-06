(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_chain (plugin-hostd/fuzz_command, 0x8c2b4), after
   lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v, AChc.v at c8557374ad2e
   (the segment walk of cgif_close). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c xstrdup_c rec_shape_of_c answer_c sup_chain_c RecBLemmas sup_chain_s1 sup_chain_s2 sup_chain_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the offsets of the walk's segment boundaries in the listing (MEASURED: the disassembly of sup_chain) *)
Definition SC_BR16 : Z := AF_sup_chain + 0x60.      (* bne a2,a3 (0x8c314) *)
Definition SC_SPILL_ARM : Z := AF_sup_chain + 0x64.  (* the spill arm (0x8c318) *)
Definition SC_SLOT_ARM : Z := AF_sup_chain + 0x7c.   (* the table arm (0x8c330) *)
Definition SC_RET_RCF : Z := AF_sup_chain + 0x78.    (* after the call of rec_calls_free (0x8c32c) *)
Definition SC_JOIN : Z := AF_sup_chain + 0x98.       (* the two arms meet (0x8c34c) *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses that this segment uses *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary record, as cgif's walks take it *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the program's writable statics (the recorder walks' shared form) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the listing's symbol for a program callee is the callee's entry (CmdObj.v's cmd_sig_prog, restricted to
   this walk's callees) *)
Hypothesis SIGP : cmd_sig_prog.
(* arodata_ok_journalP's two record facts, and the fact that a read-only byte is an image byte outside the
   program's own writable statics (the recorder walks' shared hypotheses `RRO`, `RELRO_IMG`, `cmd_ro_prog_apart`) *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a ->
in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.

Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let errno_low := pal_env B TL.

(* the saved registers of sup_chain's frame, at their offsets below the entry sp *)
Definition sc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition sc_frame_at (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error sc_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* the walk's footprint: g_rec, record.spill and the recorder's own blocks *)
Definition sc_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the slot the table arm computes: g_rec + 16 + 56 * ncalls, as the symbolic executor writes it *)
Lemma sc_den_slot : forall E m g n,
ew E m = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E g = Z_to_bv 64 A_G_REC ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 56)) (SLit 16)) (SOff g 0))
= Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E m g n Hm Hn Hg.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
assert (Hmul : U E (SMd M_MUL (SOff m 0) (SLit 56)) = 56 * n).
{ change (SMd M_MUL (SOff m 0) (SLit 56)) with (mono m 56).
  rewrite mono_sound, Hm, unsigned_lit_small by lia. unfold M64. apply Z.mod_small. lia. }
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 56)) (SLit 16)) (SOff g 0))
        = A_G_REC + OFF_CALLS + CALL_SIZE * n).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hmul, U_SLit, U_SOff, Hg, unsigned_lit_small by (unfold A_G_REC; lia).
assert (Z16 : zcanon 16 = 16) by (apply ZC; lia).
assert (ZG : zcanon (A_G_REC + 0) = A_G_REC) by (apply ZC; unfold A_G_REC; lia).
rewrite Z16, ZG.
assert (Z1 : zcanon (56 * n + 16) = 56 * n + 16) by (apply ZC; lia).
rewrite Z1.
assert (Z2 : zcanon (56 * n + 16 + A_G_REC) = 56 * n + 16 + A_G_REC) by (apply ZC; unfold A_G_REC; lia).
rewrite Z2. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
Qed.

(* a register's symbolic value without normalising the denotation (CmdPaLib's prreg normalises it) *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* the write-permission obligation of every run of this walk: the frame, the two read-only cells that carry
   the shadow base, and g_rec's own bytes, which are in the footprint and are program statics *)
Ltac sc_awr Usp HEI :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
eapply awr_ok_cons_stack; [reflexivity | exact Usp | vm_compute; discriminate | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply awr_ok_cons_gen with (n := SC_GREC) (b := A_G_REC);
[ reflexivity
| rewrite (img_env_atomP _ SC_GREC HEI ltac:(unfold SC_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (sc_grec_val VOBJS);
  apply unsigned_lit_small; unfold A_G_REC; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  right; right; right; right; left;
  (split; [| split]);
  [ exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity|];
    cbn [fst snd]; unfold OFF_NCALLS, REC_SIZE in *; lia
  | rewrite (ts_prog B HB); apply recb_grec_in; unfold OFF_NCALLS, REC_SIZE in *; lia
  | apply cmd_prog_img; apply recb_grec_in; unfold OFF_NCALLS, REC_SIZE in *; lia ]
| apply awr_ok_nil ].

(* the saved registers lie in [0, 32) *)
Lemma sc_saved_range : forall j r, nth_error sc_saved j = Some r -> 0 <= r < 32.
Proof.
intros j r Hj.
assert (H32 : Forall (fun x => 0 <= x < 32) sc_saved) by (unfold sc_saved; repeat constructor; lia).
rewrite Forall_forall in H32. apply H32. eapply nth_error_In. exact Hj.
Qed.

(* the frame the prologue wrote, read off the stack region of the symbolic state *)
Lemma sc_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
(forall j r, nth_error sc_saved j = Some r ->
   In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
sc_frame_at m sp0 regs.
Proof.
intros E m sp0 regs cs HR Hsp HE HIn j r Hj.
pose proof (sc_saved_range j r Hj) as Hr32.
assert (Hr5 : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
{ rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. symmetry. apply Z.mod_small. lia. }
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (- 8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2%nat sp0 cs (-112) 0 (-112) 0 (- 8 - 8 * Z.of_nat j) 8
  (SOff (Z.to_nat r) 0) _ HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r) Hr5), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. cbn. lia.
- cbn. lia.
Qed.

(* --- segment A: the prologue and the inlined record()'s choice of slot, 0x8c2b4 .. 0x8c34c ----------------
   It ends where the two arms meet (SC_JOIN): the slot is in s0, the shadow base in s6, the call's three
   arguments in s5 / s2 / s1, and the frame holds the callee-saved registers. *)

Lemma sc_segA_table : forall ly S W regs mem md ch (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z))
(Q : world SEGS -> config -> Prop),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
(* the table arm: record() has room for the call (the spill arm is the walk's other segment) *)
(length (r_calls R) < 16)%nat ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 id -> getr regs 11 = w64 pids -> getr regs 12 = w64 (Z.of_nat (length ids)) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + rec_spill_frees R <= EV_MAX ->
mo_ok MT S (rec_spill_frees R * mo_free MT) ->
(* the continuation at the join: the two arms of the inlined record() *)
(forall lyc Sc Wc (regsc : bvmap 5 word) memc mdc k c,
 ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
 k <= rec_spill_frees R ->
 spZ regsc = spZ regs - 112 ->
 getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
 getr regsc 8 = w64 c -> getr regsc 22 = w64 SB ->
 getr regsc 9 = w64 (Z.of_nat (length ids)) -> getr regsc 18 = w64 pids -> getr regsc 21 = w64 id ->
 sc_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
 sc_slot_ok c ->
 (* what the meter and the live bytes of the following segments need *)
 mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
 blocks_bytes Sc <= blocks_bytes S ->
 (* the table arm: the slot is the next entry, the count is one higher, nothing else changed *)
 (((length (r_calls R) < 16)%nat /\ lyc = ly /\ Sc = S /\ k = 0 /\
   c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) /\
   aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs) -> rdW Wc memc a = rdW W mem a)) \/
  (* the spill arm: the spill's arguments are freed and its call is cleared; the only blocks freed are the
     spill's, which the recorder owned *)
  ((length (r_calls R) = 16)%nat /\ c = A_REC_SPILL /\
   (exists O1, rec_repA B lyc Sc (rdW Wc memc) (set_spill R (fst (r_spill R), [])) O1 /\
      (forall pn, In pn O1 -> In pn O) /\
      (forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
      (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
      (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1)))) ->
 SRr SEGS Wc (cfg_at SEGS (BASE + SC_JOIN) regsc memc mdc) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain) regs mem md) Q.
Proof.
intros ly S W regs mem md ch id pids ids R O Q HPRE Hlt0 HROD H10 H11 H12 HREP HEV HMOK KJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshi0 & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
(* the recorder's call count *)
destruct HREP as (Qy & HQy & HOy).
pose proof HQy as (Hg8 & Hs8 & Hap & HCALLS & HANS & HRPL & HSCAL & HOWN).
pose proof HCALLS as (HL16 & HLQ & HNC & HSLOTS & HSPILL & HSPLEN).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
destruct (sc_entry B TL VOBJS cmd_prog_writable W regs mem ly S md n HAR Hstk Hpres HNC Hn) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_CHAIN_STK (sc_FP O) ly S W regs mem md ch HPRE) as HJ.
set (E := sc_E regs n) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, sc_E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, sc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E 285%nat) = A_G_REC).
{ change 285%nat with SC_GREC.
  rewrite (img_env_atomP E SC_GREC HEI ltac:(unfold SC_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (sc_grec_val VOBJS).
  apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (EGz : ew E 285%nat = Z_to_bv 64 A_G_REC)
  by (rewrite <- EGu, Z_to_bv_bv_unsigned; reflexivity).
assert (E33 : ew E 33%nat = Z_to_bv 64 n)
  by (unfold E, sc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
(* the bytes this walk may change: its own frame and g_rec.ncalls *)
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK SC_Bspan.
{ sc_awr Usp HEI. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - SUP_CHAIN_STK <= a < spZ regs \/
            A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
       unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SC_Bspan.
- (* the table arm: the call table has room *)
  paj_run_to_tok RUNTO HS HJ SHOK SC_Bspan SC_JOIN.
  { sc_awr Usp HEI. }
  pose proof Hlt0 as Hlt.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  preg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => spZ regs - SUP_CHAIN_STK <= a < spZ regs \/
              A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
         unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN2.
  clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 ->
      ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs \/
         A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); exact (UN1 a Ha Hna)) end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict mkst] in HRg end.
  pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 1) (n + 1) HRg EGu
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc.
  change (N.to_nat 4) with 4%nat in Vnc.
  unfold cfg_at, w64.
  eapply (KJ ly S W _ _ _ 0 (A_G_REC + OFF_CALLS + CALL_SIZE * n)).
  all: cycle 1.
  + unfold rec_spill_frees. destruct (Nat.ltb (length (r_calls R)) 16); lia.
  + unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. lia.
  + rewrite P3, (EEo 3%nat 3%bv eq_refl). exact Hgp.
  + rewrite P4, (EEo 4%nat 4%bv eq_refl). exact Htp.
  + rewrite P8. exact (sc_den_slot E 33%nat 285%nat n E33 Hn EGz).
  + rewrite P22. unfold E, sc_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
  + rewrite P9, (EEo 12%nat 12%bv eq_refl). exact H12.
  + rewrite P18, (EEo 11%nat 11%bv eq_refl). exact H11.
  + rewrite P21, (EEo 10%nat 10%bv eq_refl). exact H10.
  + lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
      cbn [ms_mem restrict mkst] in HR0 end.
    apply (sc_frame_of_region E _ (spZ regs) regs _ HR0 Usp EEo).
    intros j r Hj. unfold sc_saved in Hj.
    do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
      destruct j; cbn in Hj; discriminate Hj.
  + left. exists n. split; [lia | reflexivity].
  + apply (mle_weaken MT S S 0); [exact MTL | exact (mle_start MT S MTL)|].
    pose proof (mo_free_nonneg MT MTL). unfold rec_spill_frees.
    destruct (Nat.ltb (length (r_calls R)) 16); [lia|].
    apply Z.mul_nonneg_nonneg; [apply Zle_0_nat | lia].
  + lia.
  + left. split; [exact Hlt|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split.
    * apply (aval_mem_view SEGS). exact Vnc.
    * intros a Ha0 Ha1 Ha2. apply UN; [lia | intros [Hx | Hx]; [exact (Ha2 Hx) | exact (Ha1 Hx)]].
  + exact HJ.
- (* the spill arm: under this segment's premise the table has room, so the branch cannot fall through *)
  exfalso.
  assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
    by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
  rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  rewrite U_SOff, E33, unsigned_lit_small in Hc by lia.
  rewrite U_SLit, (ZC (n + 0)) in Hc by lia. rewrite (ZC 16) in Hc by lia.
  change n with (Z.of_nat (length (r_calls R))) in Hc. lia.
Qed.

(* the record's representation at a memory that agrees with it on g_rec (apart from the one word g_rec.ncalls,
   which the run reads and the caller supplies on its own), on record.spill and on the blocks the recorder owns *)
Lemma sc_arep_kept : forall bl (rd rd' : reader) R Qr,
arep_at bl rd A_G_REC A_REC_SPILL R Qr ->
rd_agree rd rd' A_G_REC OFF_NCALLS ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))) ->
rd_agree rd rd' (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS) ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_blocks Qr) -> rd_agree rd rd' (fst pn) (snd pn)) ->
arep_at bl rd' A_G_REC A_REC_SPILL R Qr.
Proof.
intros bl rd rd' R Qr (Hg8 & Hs8 & Hap & HC & HAns & HRep & HSc & HOwn) Hlo HNC' Hhi Hsp Hblk.
assert (AV : forall b (m : nat) v, aval_mem rd b m v -> A_G_REC + OFF_CALLS <= b ->
  b + Z.of_nat m <= A_G_REC + REC_SIZE -> aval_mem rd' b m v)
  by (intros b m v Hv Hb1 Hb2;
      exact (aval_mem_agree_in rd rd' (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS) b m v Hv Hhi Hb1
               ltac:(unfold OFF_CALLS, REC_SIZE in *; lia))).
assert (AVl : forall b (m : nat) v, aval_mem rd b m v -> A_G_REC <= b ->
  b + Z.of_nat m <= A_G_REC + OFF_NCALLS -> aval_mem rd' b m v)
  by (intros b m v Hv Hb1 Hb2; exact (aval_mem_agree_in rd rd' A_G_REC OFF_NCALLS b m v Hv Hlo Hb1 Hb2)).
assert (Hans : forall pn, l_answer Qr = Some pn -> rd_agree rd rd' (fst pn) (snd pn)).
{ intros pn Hq. apply Hblk. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. left. rewrite Hq. left. reflexivity. }
assert (Hrp : forall pn, l_reply Qr = Some pn -> rd_agree rd rd' (fst pn) (snd pn)).
{ intros pn Hq. apply Hblk. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right.
  apply in_or_app. right. rewrite Hq. left. reflexivity. }
unfold arep_at. split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split; [| split; [| split; [| split; [| exact HOwn]]]].
- destruct HC as (HL & HLQ & HNC & HSlots & HSpill & HSpF).
  unfold ag1_calls. split; [exact HL|]. split; [exact HLQ|].
  split; [exact HNC'|].
  split.
  + intros i c P Hc Hp. destruct (HSlots i c P Hc Hp) as [Hcall HFa]. split; [| exact HFa].
    assert (Hi : (i < 16)%nat).
    { assert (Hlt : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate). lia. }
    assert (Hi' : 0 <= Z.of_nat i <= 15) by lia.
    apply (acall_at_agree bl bl rd rd'); [exact Hcall | |].
    * apply (rd_agree_sub rd rd' (A_G_REC + OFF_CALLS) (REC_SIZE - OFF_CALLS));
      [exact Hhi | unfold OFF_CALLS, CALL_SIZE; lia | unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia].
    * intros pn Hpn. split; [exact (acall_at_in bl rd _ c P Hcall pn Hpn)|].
      apply Hblk. unfold lay_blocks. apply in_or_app. left.
      exact (In_concat_nth (l_calls Qr) i P pn Hp Hpn).
  + split; [| exact HSpF].
    apply (acall_at_agree bl bl rd rd'); [exact HSpill | exact Hsp |].
    intros pn Hpn. split; [exact (acall_at_in bl rd _ _ _ HSpill pn Hpn)|].
    apply Hblk. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
- unfold aanswer_at in HAns |- *.
  destruct (r_answer R) as [x|]; destruct (l_answer Qr) as [pn|] eqn:Eq; try (destruct HAns; fail).
  + destruct HAns as (V & Hnz & Hin & Hlen & Hstr & Hx).
    split; [apply AV; [exact V | unfold A_G_REC, OFF_CALLS, OFF_ANSWER; lia
                      | unfold A_G_REC, OFF_ANSWER, REC_SIZE; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hin|]. split; [exact Hlen|]. split; [| exact Hx].
    apply (astr_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hstr | exact (Hans pn eq_refl) | lia | lia].
  + apply AV; [exact HAns | unfold A_G_REC, OFF_CALLS, OFF_ANSWER; lia
              | unfold A_G_REC, OFF_ANSWER, REC_SIZE; cbn; lia].
- unfold areply_at in HRep |- *.
  destruct (r_reply R) as [x|]; destruct (l_reply Qr) as [pn|] eqn:Eq; try (destruct HRep; fail).
  + destruct HRep as (V1 & V2 & Hnz & Hne & Hin & Hlen & Hby & Hx).
    split; [apply AV; [exact V1 | unfold A_G_REC, OFF_CALLS, OFF_REPLY; lia
                      | unfold A_G_REC, OFF_REPLY, REC_SIZE; cbn; lia]|].
    split; [apply AV; [exact V2 | unfold A_G_REC, OFF_CALLS, OFF_REPLY_SIZE; lia
                      | unfold A_G_REC, OFF_REPLY_SIZE, REC_SIZE; cbn; lia]|].
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin|]. split; [exact Hlen|]. split; [| exact Hx].
    apply (abytes_atR_agree_in rd rd' (fst pn) (snd pn)); [exact Hby | exact (Hrp pn eq_refl) | lia | lia].
  + destruct HRep as [V1 V2].
    split; [apply AV; [exact V1 | unfold A_G_REC, OFF_CALLS, OFF_REPLY; lia
                      | unfold A_G_REC, OFF_REPLY, REC_SIZE; cbn; lia]|].
    apply AV; [exact V2 | unfold A_G_REC, OFF_CALLS, OFF_REPLY_SIZE; lia
              | unfold A_G_REC, OFF_REPLY_SIZE, REC_SIZE; cbn; lia].
- destruct HSc as (V1 & V2 & V3 & V4 & V5 & B1 & B2 & B3 & B4 & B5).
  unfold ag1_scalars.
  split; [apply AVl; [exact V1 | unfold A_G_REC, OFF_REFUSE; lia
                     | unfold A_G_REC, OFF_REFUSE, OFF_NCALLS; cbn; lia]|].
  split; [apply AVl; [exact V2 | unfold A_G_REC, OFF_CODE; lia
                     | unfold A_G_REC, OFF_CODE, OFF_NCALLS; cbn; lia]|].
  split; [apply AV; [exact V3 | unfold A_G_REC, OFF_CALLS, OFF_NREPLIES; lia
                    | unfold A_G_REC, OFF_NREPLIES, REC_SIZE; cbn; lia]|].
  split; [apply AV; [exact V4 | unfold A_G_REC, OFF_CALLS, OFF_STATE; lia
                    | unfold A_G_REC, OFF_STATE, REC_SIZE; cbn; lia]|].
  split; [apply AV; [exact V5 | unfold A_G_REC, OFF_CALLS, OFF_HOST; lia
                    | unfold A_G_REC, OFF_HOST, REC_SIZE; cbn; lia]|].
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. exact B5.
Qed.

(* the same, at a memory that agrees with the record on the whole of g_rec *)
Lemma sc_arep_kept_all : forall bl (rd rd' : reader) R Qr,
arep_at bl rd A_G_REC A_REC_SPILL R Qr ->
rd_agree rd rd' A_G_REC REC_SIZE ->
rd_agree rd rd' A_REC_SPILL SC_SIZE ->
(forall pn, In pn (lay_blocks Qr) -> rd_agree rd rd' (fst pn) (snd pn)) ->
arep_at bl rd' A_G_REC A_REC_SPILL R Qr.
Proof.
intros bl rd rd' R Qr HA Hgr Hsp Hblk.
apply (sc_arep_kept bl rd); [exact HA | | | | exact Hsp | exact Hblk].
- apply (rd_agree_sub rd rd' A_G_REC REC_SIZE);
  [exact Hgr | lia | unfold OFF_NCALLS, REC_SIZE; lia].
- pose proof HA as (_ & _ & _ & (_ & _ & HNC & _) & _).
  exact (aval_mem_agree_in rd rd' A_G_REC REC_SIZE (A_G_REC + OFF_NCALLS) 4
           (Z.of_nat (length (r_calls R))) HNC Hgr ltac:(unfold OFF_NCALLS; lia)
           ltac:(unfold OFF_NCALLS, REC_SIZE; cbn; lia)).
- apply (rd_agree_sub rd rd' A_G_REC REC_SIZE);
  [exact Hgr | unfold OFF_CALLS; lia | unfold OFF_CALLS, REC_SIZE; lia].
Qed.

(* --- segment A on the spill arm: the same prologue, then record()'s call of rec_calls_free -----------------
   0x8c2b4 .. the branch, 0x8c318 .. the call at 0x8c328, its return at 0x8c32c and the jump to the join. *)

Lemma sc_segA_spill : forall ly S W regs mem md ch (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z))
(Q : world SEGS -> config -> Prop),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
(* the spill arm: record()'s call table is full, so the call takes the spill slot *)
(length (r_calls R) = 16)%nat ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 id -> getr regs 11 = w64 pids -> getr regs 12 = w64 (Z.of_nat (length ids)) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + rec_spill_frees R <= EV_MAX ->
mo_ok MT S (rec_spill_frees R * mo_free MT) ->
(* the continuation at the join: the two arms of the inlined record() *)
(forall lyc Sc Wc (regsc : bvmap 5 word) memc mdc k c,
 ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
 k <= rec_spill_frees R ->
 spZ regsc = spZ regs - 112 ->
 getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
 getr regsc 8 = w64 c -> getr regsc 22 = w64 SB ->
 getr regsc 9 = w64 (Z.of_nat (length ids)) -> getr regsc 18 = w64 pids -> getr regsc 21 = w64 id ->
 sc_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
 sc_slot_ok c ->
 (* what the meter and the live bytes of the following segments need *)
 mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
 blocks_bytes Sc <= blocks_bytes S ->
 (* the table arm: the slot is the next entry, the count is one higher, nothing else changed *)
 (((length (r_calls R) < 16)%nat /\ lyc = ly /\ Sc = S /\ k = 0 /\
   c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) /\
   aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs) -> rdW Wc memc a = rdW W mem a)) \/
  (* the spill arm: the spill's arguments are freed and its call is cleared; the only blocks freed are the
     spill's, which the recorder owned *)
  ((length (r_calls R) = 16)%nat /\ c = A_REC_SPILL /\
   (exists O1, rec_repA B lyc Sc (rdW Wc memc) (set_spill R (fst (r_spill R), [])) O1 /\
      (forall pn, In pn O1 -> In pn O) /\
      (forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
      (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
      (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1)))) ->
 SRr SEGS Wc (cfg_at SEGS (BASE + SC_JOIN) regsc memc mdc) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain) regs mem md) Q.
Proof.
intros ly S W regs mem md ch id pids ids R O Q HPRE Heq16 HROD H10 H11 H12 HREP HEV HMOK KJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshi0 & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
destruct HREP as (Qy & HQy & HOy).
pose proof HQy as (Hg8 & Hs8 & Hap & HCALLS & HANS & HRPL & HSCAL & HOWN).
pose proof HCALLS as (HL16 & HLQ & HNC & HSLOTS & HSPILL & HSPLEN).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
destruct (sc_entry B TL VOBJS cmd_prog_writable W regs mem ly S md n HAR Hstk Hpres HNC Hn) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_CHAIN_STK (sc_FP O) ly S W regs mem md ch HPRE) as HJ.
set (E := sc_E regs n) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, sc_E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, sc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E 285%nat) = A_G_REC).
{ change 285%nat with SC_GREC.
  rewrite (img_env_atomP E SC_GREC HEI ltac:(unfold SC_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (sc_grec_val VOBJS).
  apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (E33 : ew E 33%nat = Z_to_bv 64 n)
  by (unfold E, sc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E32 : ew E 32%nat = Z_to_bv 64 SB)
  by (unfold E, sc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
(* the only bytes the prologue changes are its own frame *)
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK SC_Bspan.
{ sc_awr Usp HEI. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv1 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv1 end).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - SUP_CHAIN_STK <= a < spZ regs \/
            A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
       unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SC_Bspan.
- (* the table arm: this segment's premise says the table is full, so the branch is not taken *)
  exfalso.
  assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
    by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
  rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  rewrite U_SOff, E33, unsigned_lit_small in Hc by lia.
  rewrite U_SLit, (ZC (n + 0)) in Hc by lia. rewrite (ZC 16) in Hc by lia.
  change n with (Z.of_nat (length (r_calls R))) in Hc. lia.
- (* the spill arm: record() frees the spill's arguments *)
  paj_run_tok RUN HS HJ SHOK SC_Bspan.
  { sc_awr Usp HEI. }
  try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
    set (mdv2 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv2 end).
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
  prreg HS (4%bv : bv 5) R4. prreg HS (11%bv : bv 5) R11. preg HS (8%bv : bv 5) R8.
  preg HS (10%bv : bv 5) R10.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => spZ regs - SUP_CHAIN_STK <= a < spZ regs \/
              A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu in Hrr;
         unfold OFF_NCALLS, A_G_REC in *; first [left; lia | right; lia]|]); destruct Hin)) as UN2.
  clear HF HFr HG.
  (* the facts rec_calls_free reads, at the memory the call starts from *)
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs) ->
      ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hf Hg;
          rewrite (UN2 a Ha ltac:(intros [Hx | Hx]; [exact (Hf Hx) | exact (Hg Hx)]));
          apply UN1; [lia | intros [Hx | Hx]; [exact (Hf Hx) | exact (Hg Hx)]]) end.
  (* g_rec.ncalls, read off the region the symbolic state still carries *)
  pose proof (st_ok_region_nth E _ _ 3 _ HS eq_refl) as HRg. cbn [ms_mem restrict mkst] in HRg.
  pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 0) n HRg EGu
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; f_equal; lia)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc.
  change (N.to_nat 4) with 4%nat in Vnc.
  lazymatch type of KEEP with forall a, _ -> _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (HARC : arep_at (ablocks B ly S) (aview SEGS (w_H W) m2) A_G_REC A_REC_SPILL R Qy) end.
  { apply (sc_arep_kept (ablocks B ly S) (rdW W mem)); [exact HQy | | | | |].
    - apply rd_agree_of. intros x Hx. apply KEEP; unfold A_G_REC, OFF_NCALLS in *; lia.
    - apply (aval_mem_view SEGS). unfold OFF_NCALLS. exact Vnc.
    - apply rd_agree_of. intros x Hx. apply KEEP;
      unfold A_G_REC, OFF_NCALLS, OFF_CALLS, REC_SIZE in *; lia.
    - apply rd_agree_of. intros x Hx. apply KEEP;
      unfold A_REC_SPILL, SC_SIZE, A_G_REC, OFF_NCALLS in *; lia.
    - intros [q nq] Hpn.
      pose proof (lay_blocks_in (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Qy HQy (q, nq) Hpn) as Hin.
      apply rd_agree_of. intros x Hx. cbn [fst snd] in Hx.
      destruct (al_blocks SEGS B LAWS ly S W mem md q nq HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hnq).
      pose proof (req_size_pos nq ltac:(lia)) as [_ Hrq].
      pose proof (blk_off_imgP B ly S W mem md q nq HAR Hin) as Hoff. unfold off_img in Hoff.
      apply KEEP; unfold A_G_REC, OFF_NCALLS in *; lia. }
  (* the spill's own blocks are live, and they are what rec_calls_free frees *)
  destruct HSPILL as (HSPfn & HSPn6 & HLsp & HSPf & HSPna & HSPnd & HSParg).
  assert (HSPL : acall_at (ablocks B ly S) (rdW W mem) A_REC_SPILL (r_spill R) (l_spill Qy))
    by (split; [exact HSPfn|]; split; [exact HSPn6|]; split; [exact HLsp|]; split; [exact HSPf|];
        split; [exact HSPna|]; split; [exact HSPnd | exact HSParg]).
  assert (HSPin : forall pn, In pn (l_spill Qy) -> In pn (ablocks B ly S))
    by (exact (acall_at_in (ablocks B ly S) (rdW W mem) A_REC_SPILL (r_spill R) (l_spill Qy) HSPL)).
  assert (BS0 : forall l, (forall pn, In pn l -> In pn (ablocks B ly S)) -> 0 <= bsum l).
  { induction l as [|pn l IH]; intros Hl; [cbn; lia|].
    rewrite bsum_cons. destruct pn as [q nq].
    destruct (al_blocks SEGS B LAWS ly S W mem md q nq HAR (Hl (q, nq) ltac:(left; reflexivity)))
      as (_ & _ & _ & _ & _ & _ & Hnq).
    pose proof (IH ltac:(intros x Hx; apply Hl; right; exact Hx)). cbn [snd]. lia. }
  (* the call of rec_calls_free(&record.spill, 1) *)
  assert (HRCFAF : SIG CS_rec_calls_free = BASE + AF_rec_calls_free).
  { rewrite (SIGP CS_rec_calls_free ltac:(unfold cmd_prog_syms; cbn [In]; tauto)).
    unfold cmd_af, AF_rec_calls_free, cmd_sigma, cmd_text. cbn. reflexivity. }
  assert (HSPv : ew E 292%nat = Z_to_bv 64 A_REC_SPILL).
  { change 292%nat with SC_SPILL.
    rewrite (img_env_atomP E SC_SPILL HEI ltac:(unfold SC_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), (sc_spill_val VOBJS).
    reflexivity. }
  (* a read-only byte is no byte of this walk's footprint: not g_rec or record.spill (program statics), not a
     block (an image byte) *)
  assert (APART : forall a, in_roP SEGS RLO RHI a -> ~ inFP (sc_FP O) a).
  { intros a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
    unfold sc_FP in Hfp. destruct Hfp as (r & Hr & Hra2).
    destruct Hr as [<- | [<- | Hr]].
    - cbn [fst snd] in Hra2. apply Hpg. apply recb_grec_in. exact Hra2.
    - cbn [fst snd] in Hra2. apply Hpg. apply recb_spill_in. exact Hra2.
    - destruct (inFP_ablocks_fp_inv O a ltac:(exists r; split; [exact Hr | exact Hra2]))
        as (q & nq & Hin & Hr2).
      assert (HinB : In (q, nq) (ablocks B ly S))
        by (apply (scA_own_live B ly S (rdW W mem) R O); [exists Qy; exact (conj HQy HOy) | exact Hin]).
      exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
                      (or_introl (ex_intro _ q (ex_intro _ nq (conj HinB Hr2))))) Himg). }
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (Rsp' : spZ rg = spZ regs + -112)
      by (unfold spZ at 1; rewrite R2, Usp; rewrite unsigned_lit_small by lia; lia);
    assert (R3' : getr rg 3 = w64 (as_gp B)) by (rewrite R3, (EEo 3%nat 3%bv eq_refl); exact Hgp);
    assert (R4' : getr rg 4 = w64 (as_tp B)) by (rewrite R4, (EEo 4%nat 4%bv eq_refl); exact Htp);
    assert (R8' : getr rg 8 = w64 A_REC_SPILL)
      by (rewrite R8; cbn [sv_denot]; rewrite HSPv, unsigned_lit_small, Z.add_0_r by (unfold A_REC_SPILL; lia);
          reflexivity);
    assert (R10' : getr rg 10 = w64 A_REC_SPILL)
      by (rewrite R10; cbn [sv_denot]; rewrite HSPv, unsigned_lit_small, Z.add_0_r by (unfold A_REC_SPILL; lia);
          reflexivity);
    assert (R11' : getr rg 11 = w64 1) by (rewrite R11; reflexivity);
    assert (Rs0 : achain ly (aview SEGS (w_H W) mm) (spZ regs + -112) (s0Z rg) [])
      by (unfold achain, s0Z; rewrite R8'; unfold w64;
          rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia);
          left; split; [left; unfold A_REC_SPILL; lia | reflexivity]) end.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    eapply (cl_callS_wide B LAWS W rg mm _ SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] ly S mdq 0
        REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Qy]) (EV_REC_CALLS_FREE [l_spill Qy]) (-112)
        (Z_to_bv 64 (BASE + 24136)) []
        (fun ly2 S2 W2 regs2 mem2 md2 =>
           Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ concat [l_spill Qy]) /\
           rec_repA B ly2 S2 (aview SEGS (w_H W2) mem2) (set_spill R (fst (r_spill R), []))
             (concat (l_calls Qy) ++ oblk (l_answer Qy) ++ oblk (l_reply Qy)) /\
           mo_le MT S S2 (XM_REC_CALLS_FREE MT [l_spill Qy]))
        HJ Rsp') end.
    - reflexivity.
    - lia.
    - unfold REC_CALLS_FREE_STK, ASTACK. lia.
    - vm_compute; discriminate.
    - exact R3'.
    - exact R4'.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - exact Rs0.
    - (* the callee: rec_calls_free's contract, weakened to the three facts the join needs *)
      intros HPREc. rewrite HRCFAF.
      eapply SRr_mono.
      { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
        apply (TRCF fx ly S W rg mm mdq [] A_REC_SPILL [l_spill Qy] HPREc) end.
        - (* the read-only bytes are kept across the prologue *)
          eapply (arodata_ok_journalP (RO:=RRO) SEGS RLO RHI RELRO_IMG B SUP_CHAIN_STK (spZ regs) (sc_FP O)
                    ly S W mem md [] ly S _ _ _ 0); [exact HJ | exact APART | exact HROD].
        - exact R10'.
        - cbn [length]. exact R11'.
        - cbn [length]. lia.
        - unfold rcf_home. right. left. cbn [length].
          unfold CALL_SIZE, SC_SIZE. lia.
        - (* record.spill is 8-aligned (0x5e3be0) *)
          unfold A_REC_SPILL. reflexivity.
        - intros i P Hi. destruct i as [|i]; cbn [nth_error] in Hi; [|destruct i; cbn in Hi; discriminate Hi].
          injection Hi as <-.
          pose proof HARC as (_ & _ & _ & HCc & _).
          destruct HCc as (_ & _ & _ & _ & HSPc & _).
          destruct HSPc as (HCfn & HCn6 & HCL & HCf & HCna & HCnd & HCarg).
          split; [rewrite HCL; exact HCn6|].
          split.
          + replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS)
              with (A_REC_SPILL + CALL_OFF_NARGS) by (cbn; lia).
            rewrite HCL. exact HCna.
          + intros a pn Ha.
            assert (Hs : exists s, nth_error (snd (r_spill R)) a = Some s).
            { assert (Hlt : (a < length (snd (r_spill R)))%nat)
                by (rewrite <- HCL; apply nth_error_Some; rewrite Ha; discriminate).
              destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es;
                [exists s; reflexivity | apply nth_error_None in Es; lia]. }
            destruct Hs as [s Hs].
            destruct (HCarg a s pn Hs Ha) as (V & _ & Hin & _).
            split; [| exact Hin].
            replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
              with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by (cbn; lia).
            exact V.
        - cbn [concat]. rewrite app_nil_r. exact HSPnd.
        - unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, HLsp.
          unfold rec_spill_frees in HEV. rewrite Heq16 in HEV. cbn [Nat.ltb Nat.leb] in HEV. lia.
        - apply (mo_ok_le MT MTL S (XM_REC_CALLS_FREE MT [l_spill Qy])
                   (rec_spill_frees R * mo_free MT) HMOK).
          unfold XM_REC_CALLS_FREE, rec_spill_frees. cbn [concat]. rewrite app_nil_r, HLsp, Heq16.
          cbn [Nat.ltb Nat.leb]. lia. }
      cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJc & HPc & Hperm & _ & _ & _ & _ & Hrecs & _ & _ & Hmle).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite R1; reflexivity|]. split; [exact HJc|]. split; [exact HPc|].
      split; [exact Hperm|]. split; [| exact Hmle].
      apply (Hrecs R Qy HARC eq_refl eq_refl).
    - (* every byte the call may write is a byte this walk may write: the spill's nargs word (a program
         static of the footprint) and the spill's argument blocks (footprint blocks) *)
      intros a Hf1. unfold rcf_fp in Hf1. destruct Hf1 as (r & Hr & Hra2).
      apply in_app_or in Hr as [Hr | Hr].
      + cbn [length seq map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra2.
        right. right. right. right. left. split; [| split].
        * exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity|].
          cbn [fst snd]. unfold CALL_SIZE, CALL_OFF_NARGS, SC_SIZE in *. lia.
        * rewrite (ts_prog B HB). apply recb_spill_in.
          unfold CALL_SIZE, CALL_OFF_NARGS, SC_SIZE in *. lia.
        * apply cmd_prog_img. apply recb_spill_in.
          unfold CALL_SIZE, CALL_OFF_NARGS, SC_SIZE in *. lia.
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q nq] & Heqr & Hin).
        subst r. cbn [fst snd] in Hra2. cbn [concat] in Hin. rewrite app_nil_r in Hin.
        right. left. split.
        * exists (q, q + req_size nq). split; [| cbn [fst snd]; lia].
          right. right. unfold ablocks_fp.
          apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) O (q, nq)).
          apply (proj2 (HOy (q, nq))). unfold lay_blocks. apply in_or_app. right.
          apply in_or_app. left. exact Hin.
        * exists q, nq. split; [exact (HSPin (q, nq) Hin) | lia].
    - (* no byte of the call's footprint lies in this walk's stack window *)
      intros ly4 S4 W4 regs4 mem4 md4 _ a Hf1 Hw _. exfalso.
      unfold rcf_fp in Hf1. destruct Hf1 as (r & Hr & Hra2).
      apply in_app_or in Hr as [Hr | Hr].
      + cbn [length seq map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra2.
        unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS in *. lia.
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q nq] & Heqr & Hin).
        subst r. cbn [fst snd] in Hra2. cbn [concat] in Hin. rewrite app_nil_r in Hin.
        destruct (al_blocks SEGS B LAWS ly S W mem md q nq HAR (HSPin (q, nq) Hin))
          as (_ & _ & Hpceil & _). lia.
  }
  (* back at the return address, with the frame the callee kept *)
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2i & HP2 & Hperm2 & HrepA2 & MLE2).
  jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B).
    - exact HJ2i.
    - exact HJ2.
    - exact Usp.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros a Ha Hf1. unfold rcf_fp in Hf1. destruct Hf1 as (r & Hr & Hra2).
      apply in_app_or in Hr as [Hr | Hr].
      + cbn [length seq map] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra2.
        unfold A_REC_SPILL, CALL_SIZE, CALL_OFF_NARGS in *. lia.
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q nq] & Heqr & Hin).
        subst r. cbn [fst snd] in Hra2. cbn [concat] in Hin. rewrite app_nil_r in Hin.
        destruct (al_blocks SEGS B LAWS ly S W mem md q nq HAR (HSPin (q, nq) Hin))
          as (_ & _ & Hpceil & _). lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 34 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD2 : forall m, (m < 34)%nat -> ew E2 m = ew E m)
    by (intros m Hm; rewrite HE2; apply YN3v.ew_havoc_old; exact Hm).
  clear HE2.
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite (OLD2 2%nat ltac:(lia)); exact Usp).
  assert (EGu2 : bv_unsigned (ew E2 285%nat) = A_G_REC).
  { change 285%nat with SC_GREC.
    rewrite (img_env_atomP E2 SC_GREC HEI2 ltac:(unfold SC_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (sc_grec_val VOBJS).
    apply unsigned_lit_small. unfold A_G_REC. lia. }
  assert (HSPv2 : ew E2 292%nat = Z_to_bv 64 A_REC_SPILL).
  { change 292%nat with SC_SPILL.
    rewrite (img_env_atomP E2 SC_SPILL HEI2 ltac:(unfold SC_SPILL, A_OBJ, A_TEXT, A_LIM; lia)),
      (sc_spill_val VOBJS).
    reflexivity. }
  assert (EEo2 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs rr).
  { intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite (OLD2 m ltac:(lia)). exact (EEo m rr Hm). }
  assert (SHOK2 : sh_ok SEGS SC_Bx sc_SH0 E2 (mrestrict (w_H W2) mem2))
    by (unfold sh_ok, sc_SH0; apply Forall_nil).
  paj_run_to_tok RUNTO HS HJ2 SHOK2 SC_Bspan SC_JOIN.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | vm_compute; discriminate | cbn; lia |].
    apply awr_ok_nil. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => spZ regs - SUP_CHAIN_STK <= a < spZ regs) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]); destruct Hin)) as UN3.
  clear HF HFr HG.
  pose proof HJ2 as (HAR2 & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  preg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  unfold cfg_at, w64.
  eapply (KJ ly2 S2 W2 _ _ _ _ A_REC_SPILL).
  + exact HJ2.
  + unfold EV_REC_CALLS_FREE, rec_spill_frees. cbn [concat]. rewrite app_nil_r, HLsp, Heq16.
    cbn [Nat.ltb Nat.leb]. lia.
  + unfold spZ at 1. rewrite P2, Usp2. rewrite unsigned_lit_small by lia. lia.
  + rewrite P3, (EEo2 3%nat 3%bv eq_refl). exact Hgp.
  + rewrite P4, (EEo2 4%nat 4%bv eq_refl). exact Htp.
  + rewrite P8. cbn [sv_denot].
    rewrite HSPv2, unsigned_lit_small, Z.add_0_r by (unfold A_REC_SPILL; lia). reflexivity.
  + rewrite P22, (OLD2 32%nat ltac:(lia)), E32. reflexivity.
  + rewrite P9, (EEo2 12%nat 12%bv eq_refl). exact H12.
  + rewrite P18, (EEo2 11%nat 11%bv eq_refl). exact H11.
  + rewrite P21, (EEo2 10%nat 10%bv eq_refl). exact H10.
  + lazymatch type of HS with
    | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
        pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
    | st_ok _ _ ?ssx (restrict _ ?msx) =>
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
        pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
    end; cbn [ms_mem restrict mkst] in HR0.
    apply (sc_frame_of_region E2 _ (spZ regs) regs _ HR0 Usp2 EEo2).
    intros j r Hj. unfold sc_saved in Hj.
    do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
      destruct j; cbn in Hj; discriminate Hj.
  + right. reflexivity.
  + apply (mle_weaken MT S S2 (XM_REC_CALLS_FREE MT [l_spill Qy])); [exact MTL | exact MLE2 |].
    unfold XM_REC_CALLS_FREE, rec_spill_frees. cbn [concat]. rewrite app_nil_r, HLsp, Heq16.
    cbn [Nat.ltb Nat.leb]. lia.
  + rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S).
    rewrite (bsum_perm _ _ Hperm2), bsum_app.
    pose proof (BS0 (concat [l_spill Qy]) ltac:(cbn [concat]; rewrite app_nil_r; exact HSPin)). lia.
  + right. split; [exact Heq16|]. split; [reflexivity|].
    exists (concat (l_calls Qy) ++ oblk (l_answer Qy) ++ oblk (l_reply Qy)).
    split.
    * destruct HrepA2 as (Q2 & HQ2 & HO2). exists Q2. split; [| exact HO2].
      apply (sc_arep_kept_all (ablocks B ly2 S2) (rdW W2 mem2)); [exact HQ2 | | |].
      -- apply rd_agree_of. intros x Hx. apply UN3; unfold A_G_REC, REC_SIZE in *; lia.
      -- apply rd_agree_of. intros x Hx. apply UN3; unfold A_REC_SPILL, SC_SIZE in *; lia.
      -- intros [q nq] Hpn. apply rd_agree_of. intros x Hx. cbn [fst snd] in Hx.
         pose proof (lay_blocks_in (ablocks B ly2 S2) (rdW W2 mem2) A_G_REC A_REC_SPILL
                       (set_spill R (fst (r_spill R), [])) Q2 HQ2 (q, nq) Hpn) as Hin2.
         destruct (al_blocks SEGS B LAWS ly2 S2 _ _ _ q nq HAR2 Hin2)
           as (_ & Hp4096 & Hpceil & _ & _ & _ & Hnq).
         pose proof (req_size_pos nq ltac:(lia)) as [_ Hrq].
         apply UN3; lia.
    * split.
      -- intros pn Hpn. apply (proj2 (HOy pn)). unfold lay_blocks.
         apply in_app_or in Hpn as [Hcl | Hpn].
         ++ apply in_or_app. left. exact Hcl.
         ++ apply in_or_app. right. apply in_or_app. right. exact Hpn.
      -- split.
         { intros pn Hpn. eapply Permutation_in; [apply Permutation_sym; exact Hperm2 |].
           apply in_or_app. left. exact Hpn. }
         split.
         { (* a live block that is none of the recorder's is not one the call freed *)
           intros pn Hpn HnO. pose proof (Permutation_in pn Hperm2 Hpn) as Hpn2.
           apply in_app_or in Hpn2 as [Hl | Hs]; [exact Hl|]. exfalso. apply HnO.
           apply (proj2 (HOy pn)). unfold lay_blocks. apply in_or_app. right. apply in_or_app. left.
           cbn [concat] in Hs. rewrite app_nil_r in Hs. exact Hs. }
         { (* a recorder block still live is none of the freed spill blocks: the entry's blocks are distinct *)
           intros pn HpO Hpn2. pose proof (proj1 (HOy pn) HpO) as HpQ. unfold lay_blocks in HpQ.
           apply in_app_or in HpQ as [Hcl | HpQ]; [apply in_or_app; left; exact Hcl|].
           apply in_app_or in HpQ as [Hsp | Har]; [| apply in_or_app; right; exact Har].
           exfalso. pose proof (Permutation_NoDup Hperm2 (recb_ablocks_nodup_m B ly S W mem md HAR)) as ND2.
           apply (list_nodup_app_disj _ _ pn ND2 Hpn2). cbn [concat]. rewrite app_nil_r. exact Hsp. }
Qed.

(* the whole of segment A: record()'s two arms joined *)
Lemma sc_segA : forall ly S W regs mem md ch (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z))
(Q : world SEGS -> config -> Prop),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 id -> getr regs 11 = w64 pids -> getr regs 12 = w64 (Z.of_nat (length ids)) ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + rec_spill_frees R <= EV_MAX ->
mo_ok MT S (rec_spill_frees R * mo_free MT) ->
(* the continuation at the join: the two arms of the inlined record() *)
(forall lyc Sc Wc (regsc : bvmap 5 word) memc mdc k c,
 ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
 k <= rec_spill_frees R ->
 spZ regsc = spZ regs - 112 ->
 getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
 getr regsc 8 = w64 c -> getr regsc 22 = w64 SB ->
 getr regsc 9 = w64 (Z.of_nat (length ids)) -> getr regsc 18 = w64 pids -> getr regsc 21 = w64 id ->
 sc_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
 sc_slot_ok c ->
 (* what the meter and the live bytes of the following segments need *)
 mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
 blocks_bytes Sc <= blocks_bytes S ->
 (* the table arm: the slot is the next entry, the count is one higher, nothing else changed *)
 (((length (r_calls R) < 16)%nat /\ lyc = ly /\ Sc = S /\ k = 0 /\
   c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) /\
   aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) /\
   (forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
      ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs) -> rdW Wc memc a = rdW W mem a)) \/
  (* the spill arm: the spill's arguments are freed and its call is cleared; the only blocks freed are the
     spill's, which the recorder owned *)
  ((length (r_calls R) = 16)%nat /\ c = A_REC_SPILL /\
   (exists O1, rec_repA B lyc Sc (rdW Wc memc) (set_spill R (fst (r_spill R), [])) O1 /\
      (forall pn, In pn O1 -> In pn O) /\
      (forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
      (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
      (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1)))) ->
 SRr SEGS Wc (cfg_at SEGS (BASE + SC_JOIN) regsc memc mdc) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_chain) regs mem md) Q.
Proof.
intros ly S W regs mem md ch id pids ids R O Q HPRE HROD H10 H11 H12 HREP HEV HMOK KJ.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- exact (sc_segA_table ly S W regs mem md ch id pids ids R O Q HPRE Hlt HROD H10 H11 H12 HREP HEV HMOK KJ).
- assert (H16 : length (r_calls R) = 16%nat)
    by (pose proof (scA_slot_in B ly S (rdW W mem) R O HREP); lia).
  exact (sc_segA_spill ly S W regs mem md ch id pids ids R O Q HPRE H16 HROD H10 H11 H12 HREP HEV HMOK KJ).
Qed.



End e.
End f.
End d.
