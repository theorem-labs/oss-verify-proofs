(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: one part of sup_connect's walk on fuzz_command.asan-ubsan (image B),
   `scb_seg_e : SCB_1_stmt B MT -> SCB_E_stmt B MT` (interface lib/B/Prog/sup_connect_s0.v): the entry
   BASE + AF_sup_connect = 0x8b45c, the prologue 0x4f2c .. 0x4f58 (the 48-byte frame with ra, s0 .. s4; s3, s2, s1,
   s0 := a0, a1, a2, a3; a0 := 4) and the call record(4) at 0x4f5c through PaCallPg's cl_callS_pg, handed over at
   the return point BASE + SCB_R1 (0x8b490) in scb_mid form. The shape is the one of the entry segment of
   lib/B/Prog/sup_quarantine_clear.v at e2bb651b627 (its prologue and its call of record). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c arg_line_c answer_c sup_connect_c RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCallPg CmdRecBase xmalloc_c rec_canonical_c hand_back_c sup_connect_s0.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the slot record() returns lies in g_rec's call table or is record.spill (sqcb_slot_bounds of
   lib/B/Prog/sup_quarantine_clear_aux.v at e2bb651b627) *)
Lemma scb1_slot_bounds : forall R, (length (r_calls R) <= 16)%nat ->
((A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL) /\
A_G_REC + OFF_CALLS <= rec_slot R <= A_REC_SPILL.
Proof.
intros R H. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L|L];
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL;
[split; [left; split; lia | lia] | split; [right; reflexivity | lia]].
Qed.

Definition scb1_pdec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* record()'s footprint (record_c.v:107-108) *)
Definition scb1_FP1 (R : rstate) (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
(if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O).

(* after a symbolic run the model term grows: name it *)
Ltac scb1_md nm :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (nm := d) in *; clearbody nm end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the frame the prologue wrote, read from the stack region of the symbolic state at the call: the entry's ra,
   s0, s1, s2, s3, s4 at sp0 - 8 .. sp0 - 48 (A's scn_frame_of_region) *)
Lemma scb1_frame_of : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) lo hi wlo whi cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
In (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))) cs -> In (YP09.mkChunk (-16) (CVal 8 (SOff 8 0))) cs ->
In (YP09.mkChunk (-24) (CVal 8 (SOff 9 0))) cs -> In (YP09.mkChunk (-32) (CVal 8 (SOff 18 0))) cs ->
In (YP09.mkChunk (-40) (CVal 8 (SOff 19 0))) cs -> In (YP09.mkChunk (-48) (CVal 8 (SOff 20 0))) cs ->
scb_frame m sp0 regs.
Proof.
intros E m sp0 regs lo hi wlo whi cs HR Hsp HE C1 C2 C3 C4 C5 C6 j r Hj.
unfold scb_saved in Hj.
destruct j as [|[|[|[|[|[|j]]]]]]; cbn in Hj; try (destruct j; cbn in Hj; discriminate); injection Hj as <-.
- replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 + -8) by lia.
  apply (field_of_region E m 2 sp0 cs lo hi wlo whi (-8) 8 (SOff 1 0) _ HR Hsp C1).
  + cbn [sv_denot]. rewrite (HE 1%nat (Z_to_bv 5 1) eq_refl), Z.add_0_r. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 1))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    cbn; lia.
  + cbn; lia.
- replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 + -16) by lia.
  apply (field_of_region E m 2 sp0 cs lo hi wlo whi (-16) 8 (SOff 8 0) _ HR Hsp C2).
  + cbn [sv_denot]. rewrite (HE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 8))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    cbn; lia.
  + cbn; lia.
- replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 + -24) by lia.
  apply (field_of_region E m 2 sp0 cs lo hi wlo whi (-24) 8 (SOff 9 0) _ HR Hsp C3).
  + cbn [sv_denot]. rewrite (HE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 9))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    cbn; lia.
  + cbn; lia.
- replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 + -32) by lia.
  apply (field_of_region E m 2 sp0 cs lo hi wlo whi (-32) 8 (SOff 18 0) _ HR Hsp C4).
  + cbn [sv_denot]. rewrite (HE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 18))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    cbn; lia.
  + cbn; lia.
- replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 + -40) by lia.
  apply (field_of_region E m 2 sp0 cs lo hi wlo whi (-40) 8 (SOff 19 0) _ HR Hsp C5).
  + cbn [sv_denot]. rewrite (HE 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 19))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    cbn; lia.
  + cbn; lia.
- replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 + -48) by lia.
  apply (field_of_region E m 2 sp0 cs lo hi wlo whi (-48) 8 (SOff 20 0) _ HR Hsp C6).
  + cbn [sv_denot]. rewrite (HE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 20))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    cbn; lia.
  + cbn; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

(* every byte record() may write is a byte of the walk's footprint: g_rec.ncalls and the slot's first 8 bytes are
   program statics in the image, the spill arm's argument blocks are blocks of O *)
Lemma scb1_fp1 : forall ly S R O a,
(forall pn, In pn O -> In pn (ablocks B ly S)) -> (length (r_calls R) <= 16)%nat ->
inFP (scb1_FP1 R O) a ->
inFP (scb_FP O) a /\ ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)).
Proof.
intros ly S R O a HO Hn16 Ha.
assert (PGg : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> Exists (in_zr x) (as_prog_static B) /\ in_img SEGS x).
{ intros x Hx. split.
  - rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    unfold A_G_REC, REC_SIZE in Hx. lia.
  - apply (cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + 960).
    split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hx; lia]. }
assert (PGs : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> Exists (in_zr x) (as_prog_static B) /\ in_img SEGS x).
{ intros x Hx. split.
  - rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr.
    cbn [fst snd]. unfold A_REC_SPILL, SC_SIZE in Hx. lia.
  - apply (cif_prog_img _ _ IMG). exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hx; lia]. }
unfold scb1_FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha].
- split; [unfold scb_FP; apply inFP_cons; left; exact Ha|].
  right. apply PGg. unfold OFF_NCALLS, REC_SIZE in *. lia.
- apply inFP_cons in Ha as [Ha | Ha].
  + destruct (scb1_slot_bounds R Hn16) as ([(H1 & H2) | H1] & _).
    * split.
      -- unfold scb_FP. apply inFP_cons. right. apply inFP_cons. left.
         unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE in *. lia.
      -- right. apply PGg. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    * rewrite H1 in Ha. split.
      -- unfold scb_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right.
         apply inFP_cons. left. unfold SC_SIZE. lia.
      -- right. apply PGs. unfold SC_SIZE. lia.
  + destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    split.
    * unfold scb_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right.
      apply inFP_cons. right. exact Ha.
    * left. destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr). exists p, n.
      split; [exact (HO _ Hin) | exact Hr].
Qed.

(* record()'s post at the call state (record_c.v:110-122, fn = REC_CONNECT), the K of cl_callS_pg *)
Definition scb1_K (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly1 S1 W1 regs1 mem1 md1 => exists (F O1 : list (Z * Z)),
  getr regs1 10 = w64 (rec_slot R) /\
  Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) /\
  Z.of_nat (length F) = rec_spill_frees R /\
  (forall pn, In pn F -> In pn O) /\
  rec_repA B ly1 S1 (rdW W1 mem1) (rec_record R REC_CONNECT []) O1 /\
  (forall pn, In pn O1 <-> In pn O /\ ~ In pn F) /\
  blocks_bytes S1 <= blocks_bytes S /\
  mo_le MT S S1 (XM_RECORD MT R).

(* the entry 0x8b45c to the return point 0x8b490 after record(4) *)
Lemma scb_seg_e : SCB_1_stmt B MT -> SCB_E_stmt B MT.
Proof using TRECORD VOBJS HB LAWS MTL SIGP IMG.
intros SCB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t HPRE.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
pose proof HPRE as (HFN & Hfrm & Hfr8 & HROD & HRO & H10 & Hpv & H11 & Hpl & H12 & Hpa & H13 & Hpb &
  HSV & HSVT & HSL & HSA & HSB & HREP & Hev & Hlive & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP Hpn)).
assert (Hn16 : (length (r_calls R) <= 16)%nat).
{ destruct HREP as (Q0 & (_ & _ & _ & (Gl & _) & _) & _). exact Gl. }
(* port_b's pointer pb (s0 at the call) lies in a heap block, so below alloc_ceiling *)
assert (Hpbc : pb < alloc_ceiling).
{ destruct HSB as ((p & k & Hin & Hp1 & Hp2) & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hq]. lia. }
destruct (scb_entry B W ly S regs mem md ch HFN) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_CONNECT_STK (scb_FP O) ly S W regs mem md ch HFN) as HJ.
set (E := Eimg (Ereg regs scb_extra_e)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clearbody E.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_sup_connect)) with (Z_to_bv 64 (BASE + AF_sup_connect)).
(* 0x4f2c .. 0x4f5c: the 48-byte frame (ra, s0 .. s4), s0 .. s3 := a3 .. a0, a0 := 4, jal record *)
paj_run_tok RUN HS HJ SHOK scb_Bspan.
{ awr_ok_tac. all: exact Usp. }
pmkst HS. scb1_md mdv.
rewrite (scb_sig_record SIGP).
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRA end.
(* the run wrote the frame only *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1.
  apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) (fun a => spZ regs - 48 <= a < spZ regs) HFRA);
  [|exact Ha | exact H1].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]).
  destruct Hin. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + SCB_R1)) by (rewrite P1; reflexivity).
assert (G2 : getr (ms_regs ms) 2 = w64 (spZ regs - 48)) by (rewrite P2, Usp; unfold w64; f_equal; lia).
assert (G2s : spZ (ms_regs ms) = spZ regs + -48).
{ unfold spZ at 1. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (G3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite P3; exact (EE 3%nat 3%bv eq_refl)).
assert (G4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite P4; exact (EE 4%nat 4%bv eq_refl)).
assert (G8 : getr (ms_regs ms) 8 = getr regs 13) by (rewrite P8; exact (EE 13%nat 13%bv eq_refl)).
assert (G9 : getr (ms_regs ms) 9 = getr regs 12) by (rewrite P9; exact (EE 12%nat 12%bv eq_refl)).
assert (G10 : getr (ms_regs ms) 10 = w64 REC_CONNECT) by (rewrite P10; reflexivity).
assert (G18 : getr (ms_regs ms) 18 = getr regs 11) by (rewrite P18; exact (EE 11%nat 11%bv eq_refl)).
assert (G19 : getr (ms_regs ms) 19 = getr regs 10) by (rewrite P19; exact (EE 10%nat 10%bv eq_refl)).
assert (X21 : forall r, 21 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hr7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hr7 as [-> | Hr7]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
(* the frame the prologue wrote *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) scb_stack_m) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict mkst] in HR0 end.
assert (HFRc : scb_frame (mrestrict (w_H W) (ms_mem ms)) (spZ regs) regs)
  by (apply (scb1_frame_of E _ (spZ regs) regs _ _ _ _ _ HR0 Usp EE); cbn; tauto).
(* record's premises at the call state *)
assert (HROc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ intros a Hro Ho He. pose proof (cif_ro_end _ _ IMG a Hro) as Hlo.
  rewrite (KEEP a ltac:(lia) ltac:(lia)). exact (HROD a Hro Ho He). }
assert (HREPc : rec_repA B ly S (rdW W (ms_mem ms)) R O).
{ apply (rec_repA_kept B ly S (rdW W mem) ly S (rdW W (ms_mem ms)) R O HREP HOin).
  intros a Ha. assert (Hlow : 0 <= a < alloc_ceiling).
  { destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOin _ Hin)) as (_ & H4096 & Hc & _). lia. }
  apply KEEP; lia. }
assert (HFNc : 0 <= REC_CONNECT < REC_FN_COUNT) by (unfold REC_CONNECT, REC_FN_COUNT; lia).
assert (HEVR : st_nev S + EV_RECORD R <= EV_MAX).
{ unfold EV_SUP_CONNECT, EV_ARG_S, EV_ARG_LINE, EV_REC_CANONICAL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in Hev. lia. }
assert (HMOKR : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_CONNECT.
  assert (HX : forall n, 0 <= XM_XMALLOC MT n)
    by (intros n; unfold XM_XMALLOC, LIVE_XMALLOC; apply (mo_malloc_nonneg MT MTL); lia).
  pose proof (mo_free_nonneg MT MTL) as HF0.
  assert (HXS : forall v, 0 <= XM_ARG_S MT v) by (intros v; unfold XM_ARG_S; apply HX).
  assert (HXL : 0 <= XM_ARG_LINE MT line) by (unfold XM_ARG_LINE, XM_REC_CANONICAL; apply HX).
  assert (HXA : 0 <= XM_ANSWER MT t).
  { unfold XM_ANSWER, XM_HAND_BACK. pose proof (HX (Z.of_nat (length t) + 1)). lia. }
  pose proof (HXS verb). pose proof (HXS (Some port_a)). pose proof (HXS (Some port_b)). lia. }
assert (HFP1 : forall a, inFP (scb1_FP1 R O) a -> inFP (scb_FP O) a /\
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)))
  by (intros a Ha; exact (scb1_fp1 ly S R O a HOin Hn16 Ha)).
assert (HFP1low : forall a, inFP (scb1_FP1 R O) a -> a < alloc_ceiling)
  by (intros a Ha; exact (scb_fp_low B LAWS ly S W mem md O a HAR HOin (proj1 (HFP1 a Ha)))).
(* 0x4f5c: record(4) *)
eapply SRr_bind.
{ eapply (cl_callS_pg B LAWS W (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_record)) SUP_CONNECT_STK (spZ regs)
    (scb_FP O) ly S W mem md [] ly S mdv 0 RECORD_STK (scb1_FP1 R O) (EV_RECORD R) (-48)
    (Z_to_bv 64 (BASE + SCB_R1)) [] (scb1_K ly S R O) HJ G2s).
  - reflexivity.
  - lia.
  - exact K5.
  - lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - exact G1.
  - apply ret_ok_codeptr_v; [unfold SCB_R1; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold SCB_R1; lia). unfold SCB_R1. lia.
  - apply achain_low. unfold s0Z. rewrite G8, H13. unfold w64. rewrite unsigned_lit_small by lia. exact Hpbc.
  - intros HPRE1. eapply SRr_mono.
    + exact (TRECORD fx ly S W (ms_regs ms) (ms_mem ms) mdv [] REC_CONNECT R O HPRE1 HROc G10 HFNc HREPc
        HEVR HMOKR).
    + cbv beta. unfold apost_base. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & HQ1).
      exists ly1, S1, regs1, mem1, md1. split; [rewrite G1; reflexivity|]. split; [exact HJ1|].
      split; [exact HP1 | exact HQ1].
  - intros a Ha. left. exact (HFP1 a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
unfold scb1_K in HK2. destruct HK2 as (F & O2 & HR10 & HPERM & HFl & HFO & HREP2 & HO2 & HBB2 & MLE2).
(* the registers after record: its callee-saved ones are the call state's *)
assert (CS1 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr (ms_regs ms) rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (R2 : getr regs2 2 = w64 (spZ regs - 48))
  by (rewrite (CS1 2%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G2).
(* the frame survives record, whose footprint lies below the stack *)
assert (HFR2 : scb_frame (mrestrict (w_H W2) mem2) (spZ regs) regs).
{ intros j r Hj. apply (recb_val_mem_frame_m (w_H W) (w_H W2) (ms_mem ms) mem2 _ 8 _ (HFRc j r Hj)).
  assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some scb_saved j)); rewrite Hj; discriminate).
  intros k Hk. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply F1; [lia | lia | intros Hf; pose proof (HFP1low _ Hf); lia]. }
assert (HND : List.NoDup (ablocks B ly2 S2 ++ F))
  by (eapply Permutation_NoDup; [exact HPERM | exact (recb_ablocks_nodup_m B ly S W mem md HAR)]).
apply (SCB1 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly2 S2 W2 regs2 mem2 md2
  (0 + EV_RECORD R) O2 HPRE).
- unfold scb_mid.
  split; [exact HJ2|].
  split; [unfold SCB_EV1; lia|].
  split.
  { unfold scb_regs_at.
    split; [unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia|].
    split; [rewrite (CS1 8%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G8|].
    split; [rewrite (CS1 9%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G9|].
    split; [rewrite (CS1 18%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G18|].
    split; [rewrite (CS1 19%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G19|].
    split; [rewrite (CS1 3%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G3|].
    split; [rewrite (CS1 4%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G4|].
    intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). exact (X21 r Hr). }
  split; [exact HFR2|].
  split; [exact HREP2|].
  split; [intros pn Hpn _; exact (proj1 (proj1 (HO2 pn) Hpn))|].
  split.
  { intros pn Hpn.
    assert (Hin : In pn (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
    destruct (in_dec scb1_pdec pn O) as [HinO | HnO]; [right | left; split; assumption].
    apply (proj2 (HO2 pn)). split; [exact HinO|]. intros HinF.
    exact (list_nodup_app_disj _ _ pn HND Hpn HinF). }
  split.
  { intros pn Hin HnO. apply (Permutation_in _ HPERM) in Hin. apply in_app_or in Hin as [Hin | Hin]; [exact Hin|].
    exfalso. exact (HnO (HFO pn Hin)). }
  split; [pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr2 & _); exact Hfr2|].
  split; [unfold SCB_LV1; lia|].
  unfold SCB_XM1. exact MLE2.
- exact HR10.
Qed.
End e.
End f.
End d.
