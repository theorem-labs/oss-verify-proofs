(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan) and the two arms of the inlined record(), from 0x8d10c to the join at 0x8d180, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement) with the shared seed pieces of lib/A/Prog/RecBTemplate.v. *)

(* descriptors_panel_get (recorder.c:554-560, entry 0x8d10c): the prologue stores ra, s0 .. s4 in a 48-byte
   frame, loads the shadow base through the GOT word 0xa63f0 and g_rec.ncalls, and the inlined record() takes
   one of two arms on `bne ncalls, 16`:
   - the table arm (0x8d164): ncalls := ncalls + 1 and the slot is g_rec.calls[ncalls];
   - the spill arm (0x8d14c): rec_calls_free(&record.spill, 1) frees the spill's arguments and the slot is
     record.spill.
   Both reach 0x8d180 (DPG_JOIN) with s0 = the slot, s1 = uri, s3 = the shadow base and the frame up, which is
   where `dpg_J_stmt` (descriptors_panel_get_s3.v) takes over. The call count's atom carries each arm's bounds
   ([0, 15] on the table arm, the literal 16 on the spill arm), so the symbolic executor decides the branch and
   each arm is one straight run. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c hand_back_c rec_shape_of_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_c descriptors_panel_get_s1 descriptors_panel_get_s2 descriptors_panel_get_s3
descriptors_panel_get_s6.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain RecBTemplate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offset of the return of record()'s call of rec_calls_free (0x8d160) *)
Definition DPG_RET_RCF : Z := AF_descriptors_panel_get + 0x54.

(* the regions of this segment: the member's frame, the two read-only words that carry the shadow base, and
   g_rec.ncalls with its loaded value `nv` (the call count's atom on the table arm, the literal 16 on the
   spill arm). The slot is not a region here: this segment stops at the join, before record()'s stores. *)
Definition dpg7_rs0 (nv : sv) : YP09.smem :=
[rbt_stack (- DPG_FRAME) []; got_regionP; bcell_regionP RB_SB; rbt_ncalls nv].
(* the seed of the state the call of rec_calls_free returns to: only the jump to the join follows, which
   reads and writes nothing *)
Definition dpg7_ret_ss : sstate := mkSS DPG_RET_RCF sr_atoms [] None (mkFacts [] [] []).

(* two readers that hold the same field value agree on its bytes *)
Lemma dpg7_aval_eq : forall (rd rd' : reader) b n v, aval_mem rd b n v -> aval_mem rd' b n v ->
forall a, b <= a < b + Z.of_nat n -> rd' a = rd a.
Proof.
intros rd rd' b n v Hv Hv' a Ha.
assert (Hk : (Z.to_nat (a - b) < n)%nat) by lia.
replace a with (b + Z.of_nat (Z.to_nat (a - b))) by lia.
rewrite (Hv' _ Hk), (Hv _ Hk). reflexivity.
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

(* the slot record()'s table arm computes: g_rec + 16 + 56 * ncalls, as the symbolic executor folds the two
   shifts and the subtraction into one multiplication *)
Lemma dpg7_den_slot : forall E m g n,
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

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee of record()'s spill arm *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
(* the per-binary record, with the recorder walks' shared names *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---------- the listing's symbol of the callee ---------- *)

Lemma dpg7_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof.
rewrite (SIGP CS_rec_calls_free ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity.
Qed.

(* ---------- the program's own statics ---------- *)

Lemma dpg7_in_PG : forall a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
Exists (in_zr a) recb_PG.
Proof. intros a [Ha | Ha]; [apply recb_grec_in | apply recb_spill_in]; exact Ha. Qed.

(* a store to g_rec or record.spill is one the journal allows: the bytes are in the footprint and are the
   program's own statics (the core's program-static disjunct of awr_byte) *)
Lemma dpg7_awr_rec : forall STK sp0 O bl0 blc fr0 lyx own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (dpg_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha. right; right; right; right. left.
split; [| split].
- destruct Ha as [Ha | Ha];
  [ exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]
  | exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia] ].
- rewrite (recb_ts_prog_m B HB). exact (dpg7_in_PG a Ha).
- apply cmd_prog_img. exact (dpg7_in_PG a Ha).
Qed.

(* ---------- the walk's footprint ---------- *)

Lemma dpg7_inFP : forall O a, inFP (dpg_FP O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. left. exact Ha.
- left. right. exact Ha.
- right. apply (inFP_ablocks_fp_inv O a). exists r. split; [exact Hr | exact Ha].
Qed.

Lemma dpg7_inFP_blk : forall O b m i, In (b, m) O -> 0 <= i < req_size m -> inFP (dpg_FP O) (b + i).
Proof.
intros O b m i Hin Hi. destruct (inFP_ablocks_fp O b m i Hin Hi) as (r & Hr & Ha).
exists r. split; [right; right; exact Hr | exact Ha].
Qed.

Lemma dpg7_FP_closed : forall ly S O, (forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall (W : world SEGS) mem md, AR SEGS B ly S W mem md -> ~ YI16.sink_open_fp (dpg_FP O).
Proof.
intros ly S O HO W mem md HAR. unfold dpg_FP. apply sink_closed_cons; [cbn; unfold A_G_REC; lia|].
apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|]. apply sink_closed_ablocks_fp.
apply Forall_forall. intros [p n] Hpn. cbn [fst].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hpn)) as (_ & H4096 & _). lia.
Qed.

(* ---------- the live blocks ---------- *)

Lemma dpg7_blk_rng : forall ly1 S1 (W1 : world SEGS) mem1 md1 p m a,
AR SEGS B ly1 S1 W1 mem1 md1 -> In (p, m) (ablocks B ly1 S1) -> p <= a < p + m -> 0 <= a < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 p m a HAR Hin Ha.
destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 p m HAR Hin) as (_ & H4096 & Hc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
Qed.

(* ---------- the recorder's bytes a run of this walk keeps ---------- *)

Lemma dpg7_rdkept_of : forall ly1 S1 (W1 : world SEGS) mem1 md1 (rd' : reader) Qx R1 (Wr : Z -> Prop),
AR SEGS B ly1 S1 W1 mem1 md1 ->
arep_at (ablocks B ly1 S1) (rdW W1 mem1) A_G_REC A_REC_SPILL R1 Qx ->
(forall a, 0 <= a < alloc_ceiling -> ~ Wr a -> rd' a = rdW W1 mem1 a) ->
rec_rd_kept Qx (rdW W1 mem1) rd' Wr.
Proof.
intros ly1 S1 W1 mem1 md1 rd' Qx R1 Wr HAR HA HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
intros a Ha Hw. apply HK; [| exact Hw].
destruct Ha as [Ha | [Ha | ([q m] & Hpn & Hr)]].
- unfold A_G_REC, REC_SIZE in *. lia.
- unfold A_REC_SPILL, SC_SIZE in *. lia.
- cbn [fst snd] in Hr.
  exact (dpg7_blk_rng ly1 S1 W1 mem1 md1 q m a HAR
    (RecBLemmas.lay_blocks_in (ablocks B ly1 S1) (rdW W1 mem1) A_G_REC A_REC_SPILL R1 Qx HA (q, m) Hpn) Hr).
Qed.

(* ---------- the read-only bytes of the image along the walk ---------- *)

Lemma dpg7_rodata_kept : forall STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (dpg_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k HAR0 HO HJ HR a Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
rewrite (F3 a Himg Hown Herr); [exact (HR a Hro Hown Herr)|].
apply fp_spares_closed; [exact (dpg7_FP_closed ly S O HO W mem md HAR0)|].
intros HF. destruct (dpg7_inFP O a HF) as [Hg | (p & n & Hpn & Hr)].
- exact (Hpg (dpg7_in_PG a Hg)).
- exact (blk_img SEGS B LAWS ly S W mem md p n a HAR0 (HO _ Hpn) Hr Himg).
Qed.

(* ---------- the string argument's block along the walk ---------- *)

(* a live block the recorder does not own is still live, and its bytes are kept, at every point of the walk:
   its bytes are none of the walk's footprint (they are off the image, so not g_rec or record.spill, and the
   recorder's blocks are apart from it) *)
Lemma dpg7_blk_kept : forall STK sp0 ly S (W : world SEGS) mem md O lyc Sc (Wc : world SEGS) memc mdc k p n,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (dpg_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
0 < n -> in_blockA (ablocks B ly S) p n ->
Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O ->
in_blockA (ablocks B lyc Sc) p n /\
(forall i, 0 <= i < n -> rdW Wc memc (p + i) = rdW W mem (p + i)).
Proof.
intros STK sp0 ly S W mem md O lyc Sc Wc memc mdc k p n HAR0 HJ HOin HKeep Hn Hblk Hap.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hblk as (pb & pk & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS ly S W mem md pb pk HAR0 Hin) as (_ & Hb4096 & Hbc & _ & _ & _ & Hpk0).
pose proof (req_size_pos pk ltac:(lia)) as [_ Rk].
assert (HnO : ~ In (pb, pk) O).
{ intros HO. rewrite Forall_forall in Hap. pose proof (Hap _ HO) as Hiv. cbn [fst snd] in Hiv.
  unfold iv_apart in Hiv. lia. }
assert (Hinc : In (pb, pk) (ablocks B lyc Sc)) by exact (HKeep _ Hin HnO).
split; [exists pb, pk; split; [exact Hinc | split; [exact Hlo | exact Hhi]]|].
intros i Hi. replace (p + i) with (pb + (p - pb + i)) by lia.
apply (F2 pb pk (p - pb + i) Hin Hinc); [lia|].
intros Hf. destruct (dpg7_inFP O _ Hf) as [Hg | (q & m & Hq & Hr)].
- apply (blk_img SEGS B LAWS ly S W mem md pb pk (pb + (p - pb + i)) HAR0 Hin ltac:(lia)).
  apply cmd_prog_img. exact (dpg7_in_PG _ Hg).
- destruct (dpg_pdec (pb, pk) (q, m)) as [Heq | Hne].
  + injection Heq as <- <-. exact (HnO Hq).
  + pose proof (sep_blocks SEGS B LAWS ly S W mem md pb pk q m HAR0 Hin (HOin _ Hq) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct (al_blocks _ _ LAWS ly S W mem md q m HAR0 (HOin _ Hq)) as (_ & _ & _ & _ & _ & _ & Hm0).
    pose proof (req_size_pos m ltac:(lia)) as [_ Rm]. lia.
Qed.

(* ---------- the footprint of the call of rec_calls_free ---------- *)

Lemma dpg7_rcf_fp_in : forall (P : list (Z * Z)) a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
exists b k, In (b, k) P /\ b <= a < b + req_size k.
Proof.
intros P a (r & Hr & Ha). unfold rcf_fp in Hr. cbn [length seq map concat] in Hr.
apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. left. cbn [fst snd] in Ha. unfold CALL_SIZE in Ha. lia.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b k] & <- & Hin). rewrite app_nil_r in Hin.
  cbn [fst snd] in Ha. exists b, k. split; [exact Hin | exact Ha].
Qed.

(* ---------- the frame the prologue wrote ---------- *)

Lemma dpg7_saved_range : forall j r, nth_error dpg_saved j = Some r -> 0 <= r < 32.
Proof.
intros j r Hj.
assert (H32 : Forall (fun x => 0 <= x < 32) dpg_saved) by (unfold dpg_saved; repeat constructor; lia).
rewrite Forall_forall in H32. apply H32. eapply nth_error_In. exact Hj.
Qed.

Lemma dpg7_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (- DPG_FRAME) 0 (- DPG_FRAME) 0 cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
(forall j r, nth_error dpg_saved j = Some r ->
   In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
forall j r, nth_error dpg_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E m sp0 regs cs HR Hsp HE HIn j r Hj.
pose proof (dpg7_saved_range j r Hj) as Hr32.
assert (Hr5 : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
{ rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. symmetry. apply Z.mod_small. lia. }
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (- 8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2%nat sp0 cs (- DPG_FRAME) 0 (- DPG_FRAME) 0 (- 8 - 8 * Z.of_nat j) 8
  (SOff (Z.to_nat r) 0) _ HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r) Hr5), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. cbn. lia.
- cbn. lia.
Qed.

(* ---------- the seeds ---------- *)

Lemma dpg7_entry_seed : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) E sp n c nv lo hi,
AR SEGS B ly1 S1 W1 mem1 md1 ->
rbt_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> lo <= n <= hi ->
rbt_slot_ok c ->
(forall a, sp - DPG_FRAME <= a < sp -> apresent (w_H W1) mem1 a) ->
aval_mem (rdW W1 mem1) (A_G_REC + OFF_NCALLS) 4 n ->
sv_denot E nv = Z_to_bv 64 n ->
regs_ok E sr_atoms regs1 ->
st_ok_pi SEGS VAL E (mkSS AF_descriptors_panel_get sr_atoms (dpg7_rs0 nv) None (rbt_facts lo hi))
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + AF_descriptors_panel_get)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbt_SH E (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 E sp n c nv lo hi HAR HE Hsp Hsp16 Hn Hlh Hc Hpres HNC HV HREG.
pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (EG : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (rbt_grec_val VOBJS); reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (EV0 : VAL (A_OBJ 0) = 0xa63f0)
  by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV12 : VAL (A_OBJ 12) = 0xb10b8)
  by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [| exact (rbt_sh_ok B LAWS HB ly1 S1 W1 mem1 md1 E sp n c HAR HE Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- unfold dpg7_rs0, rbt_stack, got_regionP, bcell_regionP, rbt_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat sp E2) by lia. split; [unfold DPG_FRAME; lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbt_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxr SHADOW_OFF);
    [cbn [sv_denot Bxr]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbt_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB RB_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 nv n);
    [exact HV | rewrite rbt_pow4; lia | cbn; lia |].
    exact (RecBLemmas.val_mem_view SEGS (w_H W1) mem1 (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold dpg7_rs0, rbt_stack, got_regionP, bcell_regionP, rbt_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB RB_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB 2%nat sp E2) by lia.
  rewrite EV0, EV12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold DPG_FRAME, A_G_REC, OFF_NCALLS in *. repeat split; lia.
- exact (rbt_facts_ok VOBJS E sp n c lo hi HE Hsp Hsp16 Hlh Hn Hc).
Qed.

Lemma dpg7_ret_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) dpg7_ret_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DPG_RET_RCF)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxr [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [| apply Forall_nil].
rewrite restrict_mkst_fx. unfold dpg7_ret_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I | split; exact I].
Qed.

(* a callee-saved register a call keeps *)
Lemma dpg7_keep_reg : forall (rx r2 : bvmap 5 word) (n : Z) (rb : bv 5) (v : word),
aregs_preserved rx r2 -> acallee_saved n -> Z_to_bv 5 n = rb -> getr rx rb = v -> getr r2 rb = v.
Proof. intros rx r2 n rb v HP Hn <- Hv. rewrite (HP n Hn). exact Hv. Qed.

(* ---------- record()'s table arm: the call takes the slot g_rec.calls[ncalls] ---------- *)

Lemma dpg7_table : forall ly S W regs mem md ch pu x R O,
dpg_J_stmt B MT ->
dpg_ctx B MT ly S W regs mem md ch pu x R O ->
(length (r_calls R) < 16)%nat ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_panel_get) regs mem md)
  (dpg_post B MT ly S W regs mem md R (Some x) O).
Proof.
intros ly S W regs mem md ch pu x R O HJstmt CTX Hlt.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & HFP0 & HROD & HRO & H10 & Hpu & HBLK & HSTR & HLX & HAP & HREP & Hfr8 & Hev & Hlive & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HREP as (Q & HAREP & HOQ).
pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HG1 & HANS & HRPL & HSCAL & HOWN).
pose proof HG1 as (HL16 & HLQ & HNC & HCALLS & HSPILL & HSPMAX).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. exact (RecBLemmas.lay_blocks_in (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q HAREP pn
    (proj1 (HOQ pn) Hpn)). }
assert (HSF : rec_spill_frees R = 0).
{ unfold rec_spill_frees. rewrite (proj2 (Nat.ltb_lt (length (r_calls R)) 16) Hlt). reflexivity. }
assert (HSTKge : DPG_FRAME <= DPG_STK) by (vm_compute; discriminate).
assert (HSTK48 : 48 <= DPG_STK) by (vm_compute; discriminate).
assert (Hn : 0 <= Z.of_nat (length (r_calls R)) <= 16) by lia.
destruct (dpg_c_ok R HL16) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hcv : dpg_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))).
{ unfold dpg_c. rewrite (proj2 (Nat.ltb_lt (length (r_calls R)) 16) Hlt). reflexivity. }
assert (HcOK : rbt_slot_ok (dpg_c R)).
{ left. split; [exact Hc1|]. split; [| exact Hc8].
  rewrite Hcv. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia. }
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  clear - Hceil Hslo Hshi H47 Hstk0 C1. lia. }
set (E := Eimg (Ereg regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R)))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HENV : rbt_env_ok E (spZ regs) (Z.of_nat (length (r_calls R))) (dpg_c R)).
{ split; [exact HEI|]. unfold E.
  rewrite (Eimg_low (Ereg regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R))) 2%nat
    ltac:(unfold A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R))) RB_SB
    ltac:(unfold RB_SB, A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R))) RB_N
    ltac:(unfold RB_N, A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R))) RB_C
    ltac:(unfold RB_C, A_TEXT; lia)).
  rewrite (ew_Ereg_nat regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R)) 2%nat 2%bv eq_refl).
  change RB_SB with (32 + 0)%nat. change RB_N with (32 + 1)%nat. change RB_C with (32 + 2)%nat.
  rewrite (ew_Ereg_extra regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R)) 0%nat),
          (ew_Ereg_extra regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R)) 1%nat),
          (ew_Ereg_extra regs (rbt_extra regs (Z.of_nat (length (r_calls R))) (dpg_c R)) 2%nat).
  cbn [rbt_extra nth map app].
  split; [unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [reflexivity | split; reflexivity]. }
assert (EEo : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr).
{ intros nn rr Hnn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (proj1 (proj2 HENV)); apply unsigned_lit_small; lia).
assert (EGz : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (rbt_grec_val VOBJS); reflexivity).
assert (EGu : bv_unsigned (ew E RB_GREC) = A_G_REC)
  by (rewrite EGz; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (ERN : ew E RB_N = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
  by exact (proj1 (proj2 (proj2 (proj2 HENV)))).
assert (EGu2 : bv_unsigned (ew E 285%nat) = A_G_REC) by exact EGu.
assert (ERN2 : ew E 33%nat = Z_to_bv 64 (Z.of_nat (length (r_calls R)))) by exact ERN.
pose proof (ajournal_init SEGS B DPG_STK (dpg_FP O) ly S W regs mem md ch HPRE) as HJ.
destruct (dpg7_entry_seed ly S W mem md regs E (spZ regs) (Z.of_nat (length (r_calls R))) (dpg_c R)
  (SOff RB_N 0) 0 15 HAR HENV Hsp46 Hal16 Hn ltac:(lia) HcOK
  ltac:(intros a Ha; apply Hpres; lia)
  HNC
  ltac:(cbn [sv_denot]; rewrite ERN, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
  ltac:(unfold E; apply regs_ok_Eimg_Ereg)) as [HS SHOK].
unfold cfg_at, w64.
paj_run_to_tok RUNTO HS HJ SHOK Bspan DPG_JOIN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat).
  - reflexivity.
  - exact Usp.
  - cbn [YP09.r_wlo]. lia.
  - cbn [YP09.r_whi]. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := RB_GREC).
    + reflexivity.
    + exact EGu.
    + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply dpg7_awr_rec.
      left. cbv [REC_SIZE]. lia.
    + apply awr_ok_nil. }
rewrite ?wvb_collapse in HJ.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - 48 <= a < spZ regs \/ A_G_REC + 8 <= a < A_G_REC + 12) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu2 in Hrr; lia|]);
    exfalso; exact Hin)) as UN.
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
preg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
lazymatch type of HS with st_ok_pi _ _ _ ?SSX (restrict _ ?MSX) =>
  assert (KR : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) E SSX MSX r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EEo; lia);
  let r3 := eval vm_compute in (nth 3 (ss_mem SSX) got_regionP) in
  pose proof (st_ok_pi_region_nth E SSX (restrict (w_H W) MSX) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg;
  let r0 := eval vm_compute in (nth 0 (ss_mem SSX) got_regionP) in
  pose proof (st_ok_pi_region_nth E SSX (restrict (w_H W) MSX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
end.
cbn [ms_mem restrict mkst] in HRg, HR0.
pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33%nat 1)
  (Z.of_nat (length (r_calls R)) + 1) HRg EGu2 ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite ERN2, unsigned_lit_small by lia; reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc.
change (N.to_nat 4) with 4%nat in Vnc.
pose proof (dpg7_frame_of_region E _ (spZ regs) regs _ HR0 Usp EEo
  ltac:(intros j r Hj; unfold dpg_saved in Hj;
        do 6 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
        destruct j; cbn in Hj; discriminate Hj)) as HFRM.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsJ := rg) in *; set (memJ := mm) in * end.
assert (Rsp : spZ regsJ = spZ regs + -48).
{ unfold spZ at 1. rewrite P2, (proj1 (proj2 HENV)).
  rewrite (unsigned_lit_small (spZ regs)) by lia.
  rewrite (unsigned_lit_small (spZ regs + -48)) by lia. reflexivity. }
assert (Vnc2 : aval_mem (rdW W memJ) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1))
  by (apply (RecBLemmas.aval_mem_view SEGS); exact Vnc).
assert (Hrdk : rec_rd_kept Q (rdW W mem) (rdW W memJ)
  (fun a => A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)).
{ apply (dpg7_rdkept_of ly S W mem md (rdW W memJ) Q R _ HAR HAREP).
  intros a Ha Hw. apply UN; [lia|]. intros [Hx | Hx].
  - lia.
  - apply Hw. cbv [OFF_NCALLS]. lia. }
assert (HBK : in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\
  (forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW W memJ (pu + i) = rdW W mem (pu + i))).
{ apply (dpg7_blk_kept DPG_STK (spZ regs) ly S W mem md O ly S W memJ mdv 0 pu
    (Z.of_nat (length x) + 1) HAR HJ HOin (fun pn Hpn _ => Hpn) ltac:(lia) HBLK HAP). }
eapply (HJstmt ly S W regs mem md ch pu x R O CTX ly S _ _ _ _
  (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) O).
- unfold dpg_mid. rewrite HSF, Z.mul_0_l.
  split; [exact HJ|].
  split; [exact (mle_start MT S MTL)|].
  split; [rewrite Rsp; cbv [DPG_FRAME]; lia|].
  split; [rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp|].
  split; [rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp|].
  split; [rewrite P8, Hcv;
          exact (dpg7_den_slot E RB_N RB_GREC (Z.of_nat (length (r_calls R))) ERN Hn EGz)|].
  split; [rewrite P19; exact (proj1 (proj2 (proj2 HENV)))|].
  split.
  { intros r Hr. apply KR.
    assert (Hrr : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hrr as [-> | Hrr]; [vm_compute; reflexivity|]). subst r. vm_compute. reflexivity. }
  intros j r Hj. apply (RecBLemmas.aval_mem_view SEGS). exact (HFRM j r Hj).
- split; [intros pn Hpn; exact Hpn|].
  split; [intros pn H1 H2; exfalso; exact (H2 H1)|].
  split; [intros pn Hpn; exact Hpn|].
  split; [intros pn H1 H2; exfalso; exact (H2 H1)|].
  exists []. rewrite app_nil_r. apply Permutation_refl.
- intros rd' Vfn Vna Hkeep.
  exact (dpg_hrec_slot (ablocks B ly S) (rdW W mem) (rdW W memJ) R Q REC_DESCRIPTORS_PANEL_GET
    HAREP Hlt ltac:(cbv [REC_DESCRIPTORS_PANEL_GET REC_FN_COUNT]; lia) Vnc2 Hrdk rd' Vfn Vna Hkeep).
- intros pn. rewrite dpg_lay_nil. exact (HOQ pn).
- rewrite P9, (EEo 10%nat 10%bv eq_refl). exact H10.
- exact (proj1 HBK).
- exact (rastr_kept (rdW W mem) (rdW W memJ) pu x HSTR (proj2 HBK)).
Qed.

(* ---------- record()'s spill arm: the table is full, so the call frees the spill's arguments ---------- *)

Lemma dpg7_spill : forall ly S W regs mem md ch pu x R O,
dpg_J_stmt B MT ->
dpg_ctx B MT ly S W regs mem md ch pu x R O ->
length (r_calls R) = 16%nat ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_panel_get) regs mem md)
  (dpg_post B MT ly S W regs mem md R (Some x) O).
Proof.
intros ly S W regs mem md ch pu x R O HJstmt CTX He16.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & HFP0 & HROD & HRO & H10 & Hpu & HBLK & HSTR & HLX & HAP & HREP & Hfr8 & Hev & Hlive & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HREP as (Q & HAREP & HOQ).
pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HG1 & HANS & HRPL & HSCAL & HOWN).
pose proof HG1 as (HL16 & HLQ & HNC & HCALLS & HSPILL & HSPMAX).
pose proof HSPILL as (Sfn & Slen6 & SlenP & Sfnv & Snargs & Snodup & Sargs).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. exact (RecBLemmas.lay_blocks_in (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q HAREP pn
    (proj1 (HOQ pn) Hpn)). }
assert (HSF : rec_spill_frees R = Z.of_nat (length (l_spill Q))).
{ unfold rec_spill_frees. rewrite He16. cbn [Nat.ltb Nat.leb]. rewrite <- SlenP. reflexivity. }
assert (HSTKge : DPG_FRAME <= DPG_STK) by (vm_compute; discriminate).
assert (HSTK48 : 48 <= DPG_STK) by (vm_compute; discriminate).
assert (Hn16 : Z.of_nat (length (r_calls R)) = 16) by (rewrite He16; reflexivity).
assert (Hcv : dpg_c R = A_REC_SPILL) by (unfold dpg_c; rewrite He16; reflexivity).
assert (HcOKs : rbt_slot_ok A_REC_SPILL) by (right; reflexivity).
assert (HNC16 : aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 16) by (rewrite <- Hn16; exact HNC).
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  clear - Hceil Hslo Hshi H47 Hstk0 C1. lia. }
set (E := Eimg (Ereg regs (rbt_extra regs 16 A_REC_SPILL))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HENV : rbt_env_ok E (spZ regs) 16 A_REC_SPILL).
{ split; [exact HEI|]. unfold E.
  rewrite (Eimg_low (Ereg regs (rbt_extra regs 16 A_REC_SPILL)) 2%nat ltac:(unfold A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs 16 A_REC_SPILL)) RB_SB ltac:(unfold RB_SB, A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs 16 A_REC_SPILL)) RB_N ltac:(unfold RB_N, A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs 16 A_REC_SPILL)) RB_C ltac:(unfold RB_C, A_TEXT; lia)).
  rewrite (ew_Ereg_nat regs (rbt_extra regs 16 A_REC_SPILL) 2%nat 2%bv eq_refl).
  change RB_SB with (32 + 0)%nat. change RB_N with (32 + 1)%nat. change RB_C with (32 + 2)%nat.
  rewrite (ew_Ereg_extra regs (rbt_extra regs 16 A_REC_SPILL) 0%nat),
          (ew_Ereg_extra regs (rbt_extra regs 16 A_REC_SPILL) 1%nat),
          (ew_Ereg_extra regs (rbt_extra regs 16 A_REC_SPILL) 2%nat).
  cbn [rbt_extra nth map app].
  split; [unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [reflexivity | split; reflexivity]. }
assert (EEo : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr).
{ intros nn rr Hnn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (proj1 (proj2 HENV)); apply unsigned_lit_small; lia).
assert (EGz : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (rbt_grec_val VOBJS); reflexivity).
assert (EGu : bv_unsigned (ew E RB_GREC) = A_G_REC)
  by (rewrite EGz; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EGu2 : bv_unsigned (ew E 285%nat) = A_G_REC) by exact EGu.
assert (ESPz : ew E 292%nat = Z_to_bv 64 A_REC_SPILL).
{ change 292%nat with RB_SPILL.
  rewrite (img_env_atomP E RB_SPILL HEI ltac:(unfold RB_SPILL, A_OBJ, A_TEXT, A_LIM; lia)),
    (rbt_spill_val VOBJS). reflexivity. }
pose proof (ajournal_init SEGS B DPG_STK (dpg_FP O) ly S W regs mem md ch HPRE) as HJ.
destruct (dpg7_entry_seed ly S W mem md regs E (spZ regs) 16 A_REC_SPILL (SLit 16) 16 16
  HAR HENV Hsp46 Hal16 ltac:(lia) ltac:(lia) HcOKs
  ltac:(intros a Ha; apply Hpres; lia) HNC16 ltac:(reflexivity)
  ltac:(unfold E; apply regs_ok_Eimg_Ereg)) as [HS SHOK].
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat).
  - reflexivity.
  - exact Usp.
  - cbn [YP09.r_wlo]. lia.
  - cbn [YP09.r_whi]. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := RB_GREC).
    + reflexivity.
    + exact EGu.
    + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply dpg7_awr_rec.
      left. cbv [REC_SIZE]. lia.
    + apply awr_ok_nil. }
rewrite ?wvb_collapse in HJ.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => spZ regs - 48 <= a < spZ regs \/ A_G_REC + 8 <= a < A_G_REC + 12) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu2 in Hrr; lia|]);
    exfalso; exact Hin)) as UN1.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (19%bv : bv 5) P19.
lazymatch type of HS with st_ok _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KRc : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) Ex SSX MSX r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EEo; lia);
  let r3 := eval vm_compute in (nth 3 (ss_mem SSX) got_regionP) in
  pose proof (st_ok_region_nth E SSX (restrict (w_H W) MSX) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg;
  let r0 := eval vm_compute in (nth 0 (ss_mem SSX) got_regionP) in
  pose proof (st_ok_region_nth E SSX (restrict (w_H W) MSX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
end.
cbn [ms_mem restrict mkst] in HRg, HR0.
pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SLit 16) 16 HRg EGu2
  ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnc.
change (N.to_nat 4) with 4%nat in Vnc.
pose proof (dpg7_frame_of_region E _ (spZ regs) regs _ HR0 Usp EEo
  ltac:(intros j r Hj; unfold dpg_saved in Hj;
        do 6 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
        destruct j; cbn in Hj; discriminate Hj)) as HFRM.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsx := rg) in *; set (memx := mm) in * end.
assert (Rsp : spZ regsx = spZ regs + -48).
{ unfold spZ at 1. rewrite P2, (proj1 (proj2 HENV)).
  rewrite (unsigned_lit_small (spZ regs)) by lia.
  rewrite (unsigned_lit_small (spZ regs + -48)) by lia. reflexivity. }
assert (R1 : getr regsx 1 = Z_to_bv 64 (BASE + DPG_RET_RCF)) by (rewrite P1; reflexivity).
assert (R3 : getr regsx 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (R4 : getr regsx 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (R8 : getr regsx 8 = w64 A_REC_SPILL) by (rewrite P8; exact ESPz).
assert (R9 : getr regsx 9 = w64 pu) by (rewrite P9, (EEo 10%nat 10%bv eq_refl); exact H10).
assert (R10 : getr regsx 10 = w64 A_REC_SPILL) by (rewrite P10; exact ESPz).
assert (R11 : getr regsx 11 = w64 (Z.of_nat (length [l_spill Q]))) by (rewrite P11; reflexivity).
assert (R19 : getr regsx 19 = w64 SB) by (rewrite P19; exact (proj1 (proj2 (proj2 HENV)))).
(* the recorder at the call: the run wrote only the frame, and g_rec.ncalls still reads 16 *)
assert (Vnc2 : aval_mem (rdW W memx) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))))
  by (rewrite Hn16; apply (RecBLemmas.aval_mem_view SEGS); exact Vnc).
assert (KEEPA : forall a, 0 <= a < alloc_ceiling -> rdW W memx a = rdW W mem a).
{ intros a Ha.
  destruct (Z_lt_le_dec a (A_G_REC + 8)) as [Hlo | Hlo];
  [ apply UN1; [lia|]; intros [Hz | Hz]; cbv [A_G_REC] in *; lia |].
  destruct (Z_lt_le_dec a (A_G_REC + 12)) as [Hhi | Hhi];
  [| apply UN1; [lia|]; intros [Hz | Hz]; cbv [A_G_REC] in *; lia ].
  apply (dpg7_aval_eq (rdW W mem) (rdW W memx) (A_G_REC + OFF_NCALLS) 4
    (Z.of_nat (length (r_calls R))) HNC Vnc2 a).
  cbv [OFF_NCALLS A_G_REC] in *. lia. }
assert (Hrdk0 : rec_rd_kept Q (rdW W mem) (rdW W memx) (fun _ => False)).
{ apply (dpg7_rdkept_of ly S W mem md (rdW W memx) Q R _ HAR HAREP).
  intros a Ha _. apply KEEPA. exact Ha. }
assert (HAREPx : arep_at (ablocks B ly S) (rdW W memx) A_G_REC A_REC_SPILL R Q)
  by exact (arep_kept (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W memx) R Q HAREP
      (fun pn Hpn => RecBLemmas.lay_blocks_in (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q HAREP pn Hpn)
      Hrdk0).
pose proof HAREPx as (_ & _ & _ & HG1x & _).
pose proof HG1x as (_ & _ & _ & _ & HSPILLx & _).
pose proof HSPILLx as (Xfn & Xlen6 & XlenP & Xfnv & Xnargs & Xnodup & Xargs).
(* what the call's contract asks *)
assert (HRODx : arodata_okP SEGS RLO RHI B (rdW W memx))
  by exact (dpg7_rodata_kept DPG_STK (spZ regs) ly S W mem md O [] ly S W memx mdv 0 HAR HOin HJ HROD).
assert (HnFP1 : forall a, alloc_ceiling <= a -> ~ inFP (rcf_fp A_REC_SPILL [l_spill Q]) a).
{ intros a Ha Hf. destruct (dpg7_rcf_fp_in (l_spill Q) a Hf) as [Hnn | (b0 & m0 & Hbm & Hr)].
  - cbv [A_REC_SPILL CALL_OFF_NARGS] in Hnn. lia.
  - assert (Hin : In (b0, m0) (ablocks B ly S)).
    { apply HOin. apply (proj2 (HOQ (b0, m0))). unfold lay_blocks. apply in_or_app. right.
      apply in_or_app. left. exact Hbm. }
    destruct (al_blocks _ _ LAWS ly S W mem md b0 m0 HAR Hin) as (_ & _ & Hc & _). lia. }
assert (Hps2 : (length [l_spill Q] <= 2)%nat) by (cbn [length]; lia).
assert (Hhome : rcf_home B ly S W memx A_REC_SPILL (CALL_SIZE * Z.of_nat (length [l_spill Q]))).
{ right. left. split; [lia|]. cbn [length]. cbv [CALL_SIZE SC_SIZE]. lia. }
assert (Hentries : forall i P, nth_error [l_spill Q] i = Some P ->
  (length P <= 6)%nat /\
  aval_mem (rdW W memx) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
  forall a pn, nth_error P a = Some pn ->
    aval_mem (rdW W memx) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
    In pn (ablocks B ly S)).
{ intros i P HP. destruct i as [|i]; [|cbn in HP; destruct i; discriminate HP].
  cbn in HP. injection HP as <-.
  split; [rewrite XlenP; exact Xlen6|].
  cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
  split; [rewrite XlenP; exact Xnargs|].
  intros a0 pn Hpn.
  assert (Hs : exists s, nth_error (snd (r_spill R)) a0 = Some s).
  { destruct (nth_error (snd (r_spill R)) a0) as [s|] eqn:Es; [exists s; reflexivity|].
    exfalso. apply nth_error_None in Es.
    pose proof (proj1 (nth_error_Some (l_spill Q) a0) ltac:(rewrite Hpn; discriminate)). lia. }
  destruct Hs as (s & Hs). destruct (Xargs a0 s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
  split; [exact G1 | exact G3]. }
assert (Hnodupc : NoDup (map fst (concat [l_spill Q]))).
{ cbn [concat]. rewrite app_nil_r. exact Xnodup. }
assert (HEVc : st_nev S + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
{ unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r.
  unfold EV_DESCRIPTORS_PANEL_GET in Hev. rewrite HSF in Hev.
  cbv [EV_XSTRDUP EV_ANSWER EV_HAND_BACK] in Hev. lia. }
assert (HMOKc : mo_ok MT S (XM_REC_CALLS_FREE MT [l_spill Q])).
{ apply (mo_ok_le MT MTL S (XM_REC_CALLS_FREE MT [l_spill Q])
    (XM_DESCRIPTORS_PANEL_GET MT R (Some x)) HMOK).
  unfold XM_REC_CALLS_FREE, XM_DESCRIPTORS_PANEL_GET, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  cbn [concat]. rewrite app_nil_r, HSF.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg (Some x))) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL
    (Z.of_nat (length (snd (descriptors_panel_get_m R (Some x)))) + 1) ltac:(lia)).
  lia. }
(* the call of rec_calls_free(&record.spill, 1) *)
rewrite dpg7_sig_rcf.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsx memx _ DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] ly S mdv 0
    REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (-48)
    (Z_to_bv 64 (BASE + DPG_RET_RCF)) []
    (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat [l_spill Q]) /\
       rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), []))
         (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) /\
       mo_le MT S S' (XM_REC_CALLS_FREE MT [l_spill Q]))
    HJ Rsp);
  [ reflexivity | lia | cbv [REC_CALLS_FREE_STK ASTACK]; lia | vm_compute; discriminate
  | exact R3 | exact R4 | exact R1
  | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | rewrite unsigned_lit_small by (cbv [DPG_RET_RCF AF_descriptors_panel_get]; lia);
    cbv [DPG_RET_RCF AF_descriptors_panel_get]; lia
  | apply achain_low; unfold s0Z; rewrite R8; unfold w64;
    rewrite unsigned_lit_small by (cbv [A_REC_SPILL]; lia); cbv [A_REC_SPILL]; lia
  | intros HPREx; eapply SRr_mono;
    [ apply (TRCF fx ly S W regsx memx mdv [] A_REC_SPILL [l_spill Q] HPREx HRODx R10 R11
        Hps2 Hhome ltac:(cbv [A_REC_SPILL]; reflexivity) Hentries Hnodupc HEVc HMOKc)
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
      exists ly3, S3, regs3, mem3, md3; split; [rewrite R1; reflexivity|];
      split; [exact HJ1|]; split; [exact HP|];
      destruct HK as (HPerm & _ & _ & _ & _ & HRep & _ & _ & HMLE);
      split; [exact HPerm|];
      split; [exact (HRep R Q HAREPx eq_refl eq_refl) | exact HMLE] ]
  | intros a Ha; destruct (dpg7_rcf_fp_in (l_spill Q) a Ha) as [Hnn | (b0 & m0 & Hbm & Hr)];
    [ apply dpg7_awr_rec; right; cbv [CALL_OFF_NARGS] in Hnn; cbv [SC_SIZE]; lia
    | assert (HbmO : In (b0, m0) O)
        by (apply (proj2 (HOQ (b0, m0))); unfold lay_blocks; apply in_or_app; right;
            apply in_or_app; left; exact Hbm);
      right; left; split;
      [ replace a with (b0 + (a - b0)) by lia; apply (dpg7_inFP_blk O b0 m0 (a - b0)); [exact HbmO | lia]
      | exists b0, m0; split; [exact (HOin _ HbmO) | exact Hr] ] ]
  | intros ly3 S3 W3 regs3 mem3 md3 _ a Ha Hw _; exfalso; apply (HnFP1 a); [lia | exact Ha] ]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJi & HP2 & HK2).
destruct HK2 as (HPerm & HRepc & HMLE).
pose proof (proj1 HJi) as HAR2.
assert (KEEPR : forall n (rb : bv 5), acallee_saved n -> Z_to_bv 5 n = rb -> getr regs2 rb = getr regsx rb)
  by (intros n rb Hn Hrb; exact (dpg7_keep_reg regsx regs2 n rb (getr regsx rb) HP2 Hn Hrb eq_refl)).
assert (HKeep2 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hin Hno. apply (Permutation_in pn HPerm) in Hin. apply in_app_or in Hin as [H | H]; [exact H|].
  exfalso. apply Hno. apply (proj2 (HOQ pn)). unfold lay_blocks. apply in_or_app. right.
  apply in_or_app. left. cbn [concat] in H. rewrite app_nil_r in H. exact H. }
assert (HEVeq : 0 + EV_REC_CALLS_FREE [l_spill Q] = rec_spill_frees R).
{ unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, HSF. lia. }
rewrite HEVeq in HJ2.
assert (HXMeq : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT).
{ unfold XM_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, HSF. reflexivity. }
rewrite HXMeq in HMLE.
destruct HRepc as (Q1 & HARQ1 & HO1Q1).
(* the jump from the call's return to the join: no memory, no register changes *)
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
destruct (dpg7_ret_seed W2 regs2 mem2) as [HS2 SHOK2].
clear HS SHOK.
paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan DPG_JOIN.
{ apply awr_ok_nil. }
rewrite ?wvb_collapse in HJ2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; exfalso; exact Hin)) as UN2.
pmkst HS2.
lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KR2 : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs2 r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W2) Ex SSX MSX r HS2), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; lia)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsJ := rg) in *; set (memJ2 := mm) in * end.
assert (HFKEEP : forall a, spZ regs - 48 <= a < spZ regs -> rdW W2 memJ2 a = rdW W memx a).
{ intros a Ha. pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (UN2 a ltac:(lia) ltac:(intros F; exact F)).
  apply F1; [lia | lia | apply HnFP1; lia]. }
assert (HARQ1J : arep_at (ablocks B ly2 S2) (rdW W2 memJ2) A_G_REC A_REC_SPILL
  (set_spill R (fst (r_spill R), [])) Q1).
{ apply (arep_kept (ablocks B ly2 S2) (ablocks B ly2 S2) (rdW W2 mem2) (rdW W2 memJ2) _ Q1 HARQ1
    (fun pn Hpn => RecBLemmas.lay_blocks_in (ablocks B ly2 S2) (rdW W2 mem2) A_G_REC A_REC_SPILL _ Q1 HARQ1 pn Hpn)).
  apply (dpg7_rdkept_of ly2 S2 W2 mem2 md2 (rdW W2 memJ2) Q1
    (set_spill R (fst (r_spill R), [])) _ HAR2 HARQ1).
  intros a Ha _. apply UN2; [lia | intros F; exact F]. }
assert (HBK : in_blockA (ablocks B ly2 S2) pu (Z.of_nat (length x) + 1) /\
  (forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW W2 memJ2 (pu + i) = rdW W mem (pu + i))).
{ apply (dpg7_blk_kept DPG_STK (spZ regs) ly S W mem md O ly2 S2 W2 memJ2 mdw (rec_spill_frees R) pu
    (Z.of_nat (length x) + 1) HAR HJ2 HOin HKeep2 ltac:(lia) HBLK HAP). }
assert (Z2 : getr regsJ (2%bv : bv 5) = getr regsx (2%bv : bv 5)).
{ rewrite (KR2 (2%bv : bv 5) ltac:(vm_compute; reflexivity)).
  exact (KEEPR 2 (2%bv : bv 5) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). }
assert (Rsp2 : spZ regsJ = spZ regs + -48) by (unfold spZ; rewrite Z2; exact Rsp).
assert (Z3 : getr regsJ (3%bv : bv 5) = w64 (as_gp B)).
{ rewrite (KR2 (3%bv : bv 5) ltac:(vm_compute; reflexivity)).
  rewrite (KEEPR 3 (3%bv : bv 5) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R3. }
assert (Z4 : getr regsJ (4%bv : bv 5) = w64 (as_tp B)).
{ rewrite (KR2 (4%bv : bv 5) ltac:(vm_compute; reflexivity)).
  rewrite (KEEPR 4 (4%bv : bv 5) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R4. }
assert (Z8 : getr regsJ (8%bv : bv 5) = w64 (dpg_c R)).
{ rewrite Hcv. rewrite (KR2 (8%bv : bv 5) ltac:(vm_compute; reflexivity)).
  rewrite (KEEPR 8 (8%bv : bv 5) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R8. }
assert (Z9 : getr regsJ (9%bv : bv 5) = w64 pu).
{ rewrite (KR2 (9%bv : bv 5) ltac:(vm_compute; reflexivity)).
  rewrite (KEEPR 9 (9%bv : bv 5) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R9. }
assert (Z19 : getr regsJ (19%bv : bv 5) = w64 SB).
{ rewrite (KR2 (19%bv : bv 5) ltac:(vm_compute; reflexivity)).
  rewrite (KEEPR 19 (19%bv : bv 5) ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  exact R19. }
eapply (HJstmt ly S W regs mem md ch pu x R O CTX ly2 S2 _ _ _ _ Q1
  (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))).
- unfold dpg_mid.
  split; [exact HJ2|].
  split; [exact HMLE|].
  split; [rewrite Rsp2; cbv [DPG_FRAME]; lia|].
  split; [exact Z3|]. split; [exact Z4|]. split; [exact Z8|]. split; [exact Z19|].
  split.
  { intros r Hr.
    assert (Hrr : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    transitivity (getr regs2 (Z_to_bv 5 r)).
    - apply KR2. destruct Hrr as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; vm_compute; reflexivity.
    - rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
      apply KRc. destruct Hrr as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; vm_compute; reflexivity. }
  intros j r Hj.
  assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some dpg_saved j)); rewrite Hj; discriminate).
  apply (aval_mem_kept (rdW W memx)); [apply (RecBLemmas.aval_mem_view SEGS); exact (HFRM j r Hj)|].
  intros kk Hkk. apply HFKEEP. lia.
- split.
  { intros pn Hpn. apply (Permutation_in pn (Permutation_sym HPerm)). apply in_or_app. left. exact Hpn. }
  split.
  { intros pn Hpn Hno. split; [|lia].
    apply (Permutation_in pn HPerm) in Hpn. apply in_app_or in Hpn as [H | H]; [exfalso; exact (Hno H)|].
    apply (proj2 (HOQ pn)). unfold lay_blocks. apply in_or_app. right. apply in_or_app. left.
    cbn [concat] in H. rewrite app_nil_r in H. exact H. }
  split.
  { intros pn Hpn. apply (proj2 (HOQ pn)). unfold lay_blocks.
    apply in_app_or in Hpn as [H | H]; [apply in_or_app; left; exact H|].
    apply in_or_app. right. apply in_or_app. right. exact H. }
  split.
  { intros pn HO HnO1 Hin2.
    assert (Hsp : In pn (l_spill Q)).
    { apply (proj1 (HOQ pn)) in HO. unfold lay_blocks in HO.
      apply in_app_or in HO as [H | H]; [exfalso; apply HnO1; apply in_or_app; left; exact H|].
      apply in_app_or in H as [H | H]; [exact H|].
      exfalso. apply HnO1. apply in_or_app. right. exact H. }
    apply (RecBLemmas.list_nodup_app_disj (ablocks B ly2 S2) (concat [l_spill Q]) pn);
      [ exact (Permutation_NoDup HPerm (RecBLemmas.recb_ablocks_nodup_m B ly S W mem md HAR)) | exact Hin2 |
        cbn [concat]; rewrite app_nil_r; exact Hsp ]. }
  exists (concat [l_spill Q]). exact HPerm.
- intros rd' Vfn Vna Hkeep.
  exact (dpg_hrec_spill (ablocks B ly2 S2) (rdW W2 memJ2) R Q1 REC_DESCRIPTORS_PANEL_GET
    HARQ1J He16 ltac:(cbv [REC_DESCRIPTORS_PANEL_GET REC_FN_COUNT]; lia) rd' Vfn Vna Hkeep).
- exact HO1Q1.
- exact Z9.
- exact (proj1 HBK).
- exact (rastr_kept (rdW W mem) (rdW W2 memJ2) pu x HSTR (proj2 HBK)).
Qed.

Theorem dpg_entry : dpg_J_stmt B MT ->
forall ly S W regs mem md ch pu x R O,
dpg_ctx B MT ly S W regs mem md ch pu x R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_panel_get) regs mem md)
  (dpg_post B MT ly S W regs mem md R (Some x) O).
Proof.
intros HJstmt ly S W regs mem md ch pu x R O CTX.
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- exact (dpg7_table ly S W regs mem md ch pu x R O HJstmt CTX Hlt).
- assert (He16 : length (r_calls R) = 16%nat).
  { pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _).
    destruct HREP as (Qy & HAy & _).
    destruct HAy as (_ & _ & _ & (HL16 & _) & _). lia. }
  exact (dpg7_spill ly S W regs mem md ch pu x R O HJstmt CTX He16).
Qed.

End e.
End f.
End d.