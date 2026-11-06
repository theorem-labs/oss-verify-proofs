(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3c), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepS3c.v. *)
(* What segment 3 of the sweep phase of fuzz_grant's entry function on IMAGE B shares
   (0x815d0 .. 0x8173c: LLVMFEntrySweepS3.v, the two head comparisons, and the group-A
   segments S3d, S3a and S3b): the model facts about the sweep and the two frame arrays,
   seats with no regions, and the transfer of a cut's memory facts.

   Adapted from lib/A/Prog/GrantEntrySweepS3c.v (a working branch afd75724b5b, blob
   6bd27280c, 488 lines), which carries no licence header of its own.
   Image B's cuts keep no register in `gsw_blk` and,
   on every cut of this phase, hold the box the input asked for in `a` (0x81394 took the
   branch), so `gsw_blk_move` has no register premise and moves the two bytes of `a`
   without a case on `ok`; image B's `gsw_rows` does not carry `ok`, so `gsw_rows_move`
   takes it as a premise; and image A's reac_headamp_default call lemma is left out, as
   image B calls want_of there. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC1i YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the model facts the two bcmp rest on ---- *)
Lemma bytes_HEAD_ACK : Forall (fun z => 0 <= z < 256) HEAD_ACK34z.
Proof. unfold HEAD_ACK34z. repeat constructor; lia. Qed.
Lemma bytes_HEAD_MARK : Forall (fun z => 0 <= z < 256) HEAD_MARK34z.
Proof. unfold HEAD_MARK34z. repeat constructor; lia. Qed.
Lemma length_ga_chan : forall base vals c, length (ga_chan base vals c) = 102%nat.
Proof. intros. unfold ga_chan, ga_row. rewrite !length_app, !length_GA. reflexivity. Qed.

(* Row 0 of every sweep is HEAD_ACK and row 4 is HEAD_MARK, byte for byte
   (GrantSweepModel.v's SWEEP). *)
Lemma sweep_head_ack : forall base w vals i, (i < 34)%nat ->
  nth i (map bv_unsigned (SWEEP base w vals)) 0 = nth i HEAD_ACK34z 0.
Proof.
  intros base w vals i Hi. unfold SWEEP. rewrite map_app.
  rewrite app_nth1 by (rewrite length_map; exact Hi).
  unfold HEAD_ACK34. rewrite map_unsigned_bl by exact bytes_HEAD_ACK. reflexivity.
Qed.
Lemma sweep_head_mark : forall base w vals i, (i < 34)%nat ->
  nth (136 + i) (map bv_unsigned (SWEEP base w vals)) 0 = nth i HEAD_MARK34z 0.
Proof.
  intros base w vals i Hi. unfold SWEEP. rewrite !map_app.
  assert (L1 : length (map bv_unsigned HEAD_ACK34) = 34%nat) by (rewrite length_map; reflexivity).
  assert (L2 : length (map bv_unsigned (ga_chan base vals 0)) = 102%nat) by (rewrite length_map; apply length_ga_chan).
  rewrite app_nth2 by lia. rewrite L1.
  rewrite app_nth2 by lia. rewrite L2.
  replace (136 + i - 34 - 102)%nat with i by lia.
  rewrite app_nth1 by (rewrite length_map; exact Hi).
  unfold HEAD_MARK34. rewrite map_unsigned_bl by exact bytes_HEAD_MARK. reflexivity.
Qed.
Lemma length_sweep_ge : forall base w vals, (170 <= length (SWEEP base w vals))%nat.
Proof.
  intros base w vals. unfold SWEEP. rewrite !length_app, length_ga_chan.
  change (length HEAD_ACK34) with 34%nat. change (length HEAD_MARK34) with 34%nat. lia.
Qed.

(* ---- the lengths of the harness's two frame arrays (GrantSlotPlan.v's tables) ---- *)
Lemma length_after_sets : forall cs T ws st, length ws = 144%nat -> length st = 144%nat ->
  length (snd (fst (fold_left set_step cs (T, ws, st)))) = 144%nat /\
  length (snd (fold_left set_step cs (T, ws, st))) = 144%nat.
Proof.
  induction cs as [|[[c q] v] cs IH]; intros T ws st Hw Hs; cbn [fold_left]; [cbn; auto|].
  destruct (set_step (T, ws, st) (c, q, v)) as [[T' ws'] st'] eqn:Hst.
  unfold set_step in Hst. destruct ((c <? 48) && legalb q v) eqn:Hg.
  - injection Hst as _ <- <-. apply andb_prop in Hg as [Hc Hq]. apply Z.ltb_lt in Hc.
    assert (Hq3 : q < 3) by
      (unfold legalb in Hq; apply orb_prop in Hq as [Hq | Hq]; apply andb_prop in Hq as [Hq _];
       [apply Z.ltb_lt in Hq | apply Z.eqb_eq in Hq]; lia).
    unfold ws_put. apply IH; rewrite Mem.upd_bytes_length; first [assumption | cbn [length]; lia].
  - injection Hst as _ <- <-. apply IH; assumption.
Qed.
Lemma length_ws_end : forall pl, length (ws_end pl) = 144%nat.
Proof. intros pl. unfold ws_end, tables_end, tables_at, after_sets. apply length_after_sets; reflexivity. Qed.
Lemma length_st_end : forall pl, length (st_end pl) = 144%nat.
Proof. intros pl. unfold st_end, tables_end, tables_at, after_sets. apply length_after_sets; reflexivity. Qed.

(* The symbolic states between two calls: every register is its own atom. *)
Definition ss_plain (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition ss_pin10 (pc : Z) : sstate := mkSS pc (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
Definition SB3 : Z := 0x7fff8000.
Definition Bx3 : sv := SLit SB3.
Definition Bsp3 : Z * Z := (SB3, SB3 + 2 ^ 44 - 1).
Lemma aview_ext_mem : forall segs H (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' a Hm. unfold aview, mbyte, mrestrict. rewrite !Hm. reflexivity. Qed.
Lemma frame_of_nil_eq : forall E (m m' : word -> option byte), frame_of E [] m m' -> forall x, m' x = m x.
Proof. intros E m m' H x. apply H. intros (r & Hr & _). destruct Hr. Qed.
Lemma ap_get : forall (r0 r1 : bvmap 5 word) (r : bv 5) (z : Z), bv_unsigned r = z -> acallee_saved z ->
  aregs_preserved r0 r1 -> getr r1 r = getr r0 r.
Proof. intros r0 r1 r z Hz Hr H. subst z. specialize (H _ Hr). rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
(* rewrite a callee-saved register r (numbered z) through `aregs_preserved` *)
Ltac apg P r z := rewrite (ap_get _ _ r z eq_refl ltac:(unfold acallee_saved; lia) P).
Ltac in_tac := cbn [In]; repeat (first [left; reflexivity | right]).
(* 34 <= the sweep buffer's size *)
Lemma sw_mbytes_ge : forall pl, 34 <= sw_mbytes pl.
Proof. intros pl. unfold sw_mbytes. destruct (0 <? sw_rows pl) eqn:Hr; cbv iota; [apply Z.ltb_lt in Hr; lia | lia]. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Lemma garr8_slice : forall (m : word -> option byte) p (L L' : list Z) (off : nat),
  garr8 SEGS m p L -> (off + length L' <= length L)%nat ->
  (forall j, (j < length L')%nat -> nth (off + j) L 0 = nth j L' 0) ->
  garr8 SEGS m (p + Z.of_nat off) L'.
Proof.
  intros m p L L' off HG Hlen Hn j Hj. destruct (HG (off + j)%nat ltac:(lia)) as [Hv Hr].
  rewrite (Hn j Hj) in Hv, Hr. rewrite Nat2Z.inj_add, Z.add_assoc in Hv. split; assumption.
Qed.

Lemma ms_shape : forall (ms : machine_state) pc,
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc me ro] pc H1 H2 H3 H4 H5 H6; cbn in *. subst. reflexivity.
Qed.

Lemma plain_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ss_plain pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_plain. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I].
Qed.

Lemma pin10_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  getr regs 10 = Z_to_bv 64 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (ss_pin10 pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc H10. rewrite restrict_mkst_fx. unfold ss_pin10. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H10].
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I].
Qed.

Lemma env_agree_Eimg : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the bytes the cuts of this part name, and their transfer ---- *)
Definition gsw_out0 (cx : ecx) (fp a : Z) : Prop :=
  (c_sp1 cx <= a < spZ (c_regs cx)) \/ (gSH cx fp <= a < gSH cx fp + 104) \/
  (gF cx fp <= a < gF cx fp + 1024) \/ (c_p cx <= a < c_p cx + c_n cx).
Definition gsw_out (cx : ecx) (fp t s a : Z) : Prop :=
  gsw_out0 cx fp a \/ (t <= a < t + 460) \/ (s <= a < s + sw_mbytes (c_pl cx)).
Definition vkeep (P : Z -> Prop) (W : world SEGS) (m : word -> option byte) (W' : world SEGS)
  (m' : word -> option byte) : Prop :=
  forall a, P a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a.

Lemma vkeep_trans : forall P W m W1 m1 W2 m2, vkeep P W m W1 m1 -> vkeep P W1 m1 W2 m2 -> vkeep P W m W2 m2.
Proof. intros P W m W1 m1 W2 m2 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma vkeep_mem : forall P W (m m' : word -> option byte), (forall x, m' x = m x) -> vkeep P W m W m'.
Proof. intros P W m m' Hm a _. apply aview_ext_mem. exact Hm. Qed.
Lemma vkeep_sub : forall (P Q : Z -> Prop) W m W' m', (forall a, Q a -> P a) -> vkeep P W m W' m' -> vkeep Q W m W' m'.
Proof. intros P Q W m W' m' HPQ H a Ha. exact (H a (HPQ a Ha)). Qed.

Lemma rdword_vkeep : forall (P : Z -> Prop) W m W' m' a v,
  vkeep P W m W' m' -> (forall k, 0 <= k < 8 -> P (a + k)) ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W') m') a = Some v.
Proof.
  intros P W m W' m' a v HK HP Hr. rewrite <- Hr. apply rdword_ext. intros k Hk. apply HK, HP, Hk.
Qed.
Lemma garr8_vkeep : forall (P : Z -> Prop) W m W' m' p L,
  vkeep P W m W' m' -> (forall a, p <= a < p + Z.of_nat (length L) -> P a) ->
  garr8 SEGS (mrestrict (w_H W) m) p L -> garr8 SEGS (mrestrict (w_H W') m') p L.
Proof. intros P W m W' m' p L HK HP. apply garr8_aview_kept. intros a Ha. apply HK, HP, Ha. Qed.

(* The facts every cut of the phase carries, read off ge_base. *)
Lemma gsw_base_facts : forall cx, ge_base B MT cx ->
  afn_pre SEGS B GE_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
  c_sp1 cx = 32 * ((spZ (c_regs cx) + -288) / 32) /\
  (c_n cx = 0 \/ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))).
Proof.
  intros cx HB. unfold ge_base in HB. decompose [and] HB.
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  match goal with H : (c_n cx = 0 /\ _) \/ (_ /\ In (c_p cx, c_n cx) _) |- _ =>
    destruct H as [[H _] | [_ H]]; [left | right]; exact H end.
Qed.

Lemma gsw_bounds : forall cx fp k ly3 S3 W3 mem3 md3 t s,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  In (t, 460) (ablocks B ly3 S3) -> In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3) ->
  AR_laws SEGS B ->
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + GE_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\ c_sp1 cx mod 32 = 0 /\
  4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\ gF cx fp mod 32 = 0 /\
  4096 <= t /\ t + 460 <= alloc_ceiling /\ 4096 <= s /\ s + sw_mbytes (c_pl cx) <= alloc_ceiling /\
  (c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 t s HB HJ Hfr Ht Hs LAWS.
  destruct (gsw_base_facts cx HB) as (HPRE & _ & Hsp1 & HINP).
  pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  assert (HPB : c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
  { destruct HINP as [H0 | Hin]; [left; exact H0 | right].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HPRE) Hin) as (_ & Hp0 & Hpc & _).
    pose proof (req_size_pos' (c_n cx) ltac:(unfold c_n; lia)) as [_ Hrq]. lia. }
  pose proof (proj1 HJ) as HAR.
  pose proof HJ as (_ & Hly & _).
  assert (Hin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 GE_CID fp HAR Hin) as (Hf0 & Hfc & _).
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 GE_CID fp HAR Hin) as (Hf32 & _).
  assert (EF : gF cx fp = frame_addr ly3 GE_CID fp).
  { unfold gF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  change (fs_frame_bytes GE_CID) with 1024 in Hfc.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ t 460 HAR Ht) as (_ & Ht0 & Htc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ s _ HAR Hs) as (_ & Hs0 & Hsc & _).
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  change (req_size 460) with 460 in Htc.
  pose proof (req_size_pos' (sw_mbytes (c_pl cx)) ltac:(lia)) as [_ Hrq].
  pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hm.
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in *.
  repeat split; try lia; try exact HPB.
  all: first [rewrite Hsp1; rewrite Z.mul_comm; apply Z_mod_mult | rewrite EF; exact Hf32].
Qed.

(* Every byte the cuts name is either in the machine frame, above the stack pointer, or
   below the allocator's ceiling. *)
Lemma gsw_out_cases : forall cx fp t s a,
  4096 <= gF cx fp -> gF cx fp + 1024 <= alloc_ceiling ->
  4096 <= t -> t + 460 <= alloc_ceiling -> 4096 <= s -> s + sw_mbytes (c_pl cx) <= alloc_ceiling ->
  (c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)) ->
  gsw_out cx fp t s a -> (c_sp1 cx <= a < spZ (c_regs cx)) \/ (0 <= a < alloc_ceiling).
Proof.
  intros cx fp t s a HF0 HFc Ht0 Htc Hs0 Hsc HPB Ha.
  pose proof (@alloc_ceiling_value rc) as HAC.
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (gF cx fp) 8 ltac:(lia)) as M8.
  destruct Ha as [[H|[H|[H|H]]]|[H|H]];
    [left; exact H | right; unfold gSH, shadow_of_addr, SHADOW_OFF in H; lia | right; lia | | right; lia | right; lia].
  destruct HPB as [H0|H0]; [lia | right; lia].
Qed.

(* ---- the transfer of every cut's memory facts ---- *)
Lemma ge_body_move : forall cx fp pc pc' (W W' : world SEGS) (ms : machine_state) (regs' : bvmap 5 word) mem' sh,
  ge_body cx fp pc W ms sh ->
  vkeep (gsw_out0 cx fp) W (ms_mem ms) W' mem' ->
  c_sp1 cx + 288 <= spZ (c_regs cx) ->
  getr regs' 2 = getr (ms_regs ms) 2 -> getr regs' 3 = getr (ms_regs ms) 3 -> getr regs' 4 = getr (ms_regs ms) 4 ->
  getr regs' 8 = getr (ms_regs ms) 8 -> getr regs' 9 = getr (ms_regs ms) 9 ->
  ge_body cx fp pc' W' (mkst regs' (Z_to_bv 64 (BASE + pc')) mem' (seg_rom SEGS)) sh.
Proof.
  intros cx fp pc pc' W W' ms regs' mem' sh HBD HK Hsp R2 R3 R4 R8 R9.
  destruct HBD as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & (S1 & S2) & HSH & HFL & HLEN & HIN).
  unfold ge_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
  split; [reflexivity|]. do 5 (split; [reflexivity|]).
  split; [unfold gregs; cbn [ms_regs mkst]; rewrite R2, R3, R4, R8, R9; repeat split; assumption|].
  split.
  { split.
    - eapply rdword_vkeep; [exact HK | | exact S1]. intros kk Hk. left. lia.
    - intros j Hj. eapply rdword_vkeep; [exact HK | | exact (S2 j Hj)]. intros kk Hk. left. lia. }
  split.
  { intros i Hi. cbn [ms_mem mkst]. rewrite (HK (gSH cx fp + Z.of_nat i)); [exact (HSH i Hi)|].
    right; left. rewrite HLEN in Hi. unfold GE_NSH in Hi. lia. }
  split.
  { eapply rdword_vkeep; [exact HK | | exact HFL]. intros kk Hk. right; right; left. lia. }
  split; [exact HLEN|].
  eapply garr8_vkeep; [exact HK | | exact HIN]. intros a Ha. right; right; right.
  rewrite length_map in Ha. unfold c_n. lia.
Qed.

(* Image B's `gsw_blk` names no register, and its two bytes of `a` are the box the input
   asked for on every cut of this phase (image A's are under a case on `ok`). *)
Lemma gsw_blk_move : forall cx fp ly3 S3 W ms ly4 S4 W' ms' t s,
  gsw_blk B cx fp ly3 S3 W ms t s ->
  ablocks B ly4 S4 = ablocks B ly3 S3 ->
  vkeep (gsw_out cx fp t s) W (ms_mem ms) W' (ms_mem ms') ->
  c_sp1 cx + 288 <= spZ (c_regs cx) ->
  gsw_blk B cx fp ly4 S4 W' ms' t s.
Proof.
  intros cx fp ly3 S3 W ms ly4 S4 W' ms' t s HBK Hab HK Hsp.
  destruct HBK as (Hab3 & Hins & (Hint & Ht0 & HTl & HTb) & HWS & HST & HREL & HI1 & HSL
    & Hcn & Ht & Hs & Hok & A0 & A1).
  assert (KS : forall off v, 8 <= off <= 176 -> gslot cx W ms off v -> gslot cx W' ms' off v).
  { intros off v Hoff Hg. unfold gslot in *.
    eapply rdword_vkeep; [exact HK | | exact Hg]. intros kk Hk. left; left. lia. }
  assert (KF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 -> gfarr cx fp W ms off l ->
            gfarr cx fp W' ms' off l).
  { intros off l H0 Hl Hg. unfold gfarr in *.
    eapply garr8_vkeep; [exact HK | | exact Hg]. intros a Ha. rewrite length_map in Ha. left; right; right; left. lia. }
  assert (KB : forall off v, 0 <= off < 1024 -> gfb cx fp W ms off v -> gfb cx fp W' ms' off v).
  { intros off v Hoff Hg. unfold gfb in *. rewrite (HK (gF cx fp + off)); [exact Hg|].
    left; right; right; left. lia. }
  unfold gsw_blk. rewrite Hab. split; [exact Hab3|]. split; [exact Hins|].
  split.
  { split; [rewrite Hab; exact Hint|]. split; [exact Ht0|]. split; [exact HTl|].
    intros i Hi H1 H2 H3. rewrite (HK (t + i)); [exact (HTb i Hi H1 H2 H3)|]. right; left. lia. }
  split; [apply KF; [unfold GO_WAS; lia | rewrite length_ws_end; unfold GO_WAS; lia | exact HWS]|].
  split; [apply KF; [unfold GO_SET; lia | rewrite length_st_end; unfold GO_SET; lia | exact HST]|].
  split; [exact HREL|]. split; [exact HI1|].
  split.
  { destruct HSL as (L8 & L16 & L40 & L48 & L56 & L64 & L72 & L80 & L96 & L104 & L112 & L120
      & L128 & L136 & L144 & L152).
    unfold gsw_slots. repeat split; apply KS; first [lia | assumption]. }
  split; [exact Hcn|]. split; [exact Ht|]. split; [exact Hs|]. split; [exact Hok|].
  split; (apply KB; [unfold GO_A; lia | assumption]).
Qed.

Lemma sw_bytes_len : forall cx t, ok (c_pl cx) = true -> sw_want (c_pl cx) <= sw_rows (c_pl cx) ->
  Z.of_nat (length (sw_bytes (c_pl cx) t)) <= sw_mbytes (c_pl cx).
Proof.
  intros cx t Hok Hw.
  unfold ok, fits in Hok. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok _].
  apply andb_prop in Hok as [Hw1 _]. apply Z.leb_le in Hw1. fold (sw_in (c_pl cx)) in Hw1.
  assert (Hpos : 0 < sw_rows (c_pl cx)) by (unfold sw_want in Hw; lia).
  assert (Hm : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
    by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt _ _) Hpos); reflexivity).
  rewrite Hm. unfold sw_bytes. rewrite SWEEP_rows.
  assert (HL : forall L : list (list byte), Forall (fun r => length r = 34%nat) L -> length (concat L) = (34 * length L)%nat).
  { induction L as [|r L IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [concat].
    rewrite length_app, IH by assumption. cbn [length]. lia. }
  rewrite HL by (apply Forall_rowok_len, sweep_rows_ok).
  rewrite Nat2Z.inj_mul, length_sweep_rows by lia. rewrite Z2Nat.id by lia.
  unfold sw_want in Hw. lia.
Qed.

(* Image B's `gsw_rows` does not carry `ok`; every cut that names it names `gsw_blk` too,
   which does. *)
Lemma gsw_rows_move : forall cx fp W ms W' ms' t s,
  ok (c_pl cx) = true ->
  gsw_rows cx W ms t s -> vkeep (gsw_out cx fp t s) W (ms_mem ms) W' (ms_mem ms') ->
  gsw_rows cx W' ms' t s.
Proof.
  intros cx fp W ms W' ms' t s Hok (Hw & Hg) HK. split; [exact Hw|].
  eapply garr8_vkeep; [exact HK | | exact Hg].
  intros a Ha. rewrite length_map in Ha. pose proof (sw_bytes_len cx t Hok Hw). right; right. lia.
Qed.

(* ---- the calls a cut of this part makes ---- *)
(* The call chain a callee gets: the entry function's own frame on top of its caller's. *)
Lemma gsw_achain : forall cx fp k ly3 S3 W3 memT mdT (regsT : bvmap 5 word),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  getr regsT 8 = w64 (spZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  c_sp1 cx + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) memT) (c_sp1 cx) (s0Z regsT) (gch cx).
Proof.
  intros cx fp k ly3 S3 W3 memT mdT regsT HB HJ R8 H8 H16 Hsp.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  destruct (gsw_base_facts cx HB) as (HPRE & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  assert (S0 : s0Z regsT = spZ (c_regs cx)).
  { unfold s0Z. rewrite R8. apply unsigned_lit_small. unfold GE_STK, STK_LLVMFuzzerTestOneInput in *.
    pose proof (@alloc_ceiling_value rc). lia. }
  rewrite S0.
  assert (Etop : ly_top ly3 = ly_top (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); exact Etop).
  assert (GA : achain (c_ly cx) (aview SEGS (w_H W3) memT) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
  { apply (ge_achain B MT cx HB); [| exact H8 | exact H16 | exact Hsp].
    intros a Ha. apply F1; [pose proof (@alloc_ceiling_value rc); unfold GE_STK, STK_LLVMFuzzerTestOneInput in *; lia | lia]. }
  unfold achain in *. rewrite Etop. exact GA.
Qed.

(* The bytes the cuts name, across a call made from the realigned stack pointer whose
   journal keeps the caller's blocks and frames. *)
Lemma vkeep_callee : forall cx fp k ly3 S3 W memc mdc t s STK1 ly2 S2 W2 mem2 md2 k1,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W memc mdc k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (s, sw_mbytes (c_pl cx))] ->
  ablocks B ly2 S2 = ablocks B ly3 S3 ->
  STK1 <= c_sp1 cx - alloc_ceiling ->
  AR_laws SEGS B ->
  ajournal SEGS B STK1 (c_sp1 cx) [] ly3 S3 W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  vkeep (gsw_out cx fp t s) W memc W2 mem2.
Proof.
  intros cx fp k ly3 S3 W memc mdc t s STK1 ly2 S2 W2 mem2 md2 k1 HB HJ HFR Hab Hab2 Hstk LAWS HJ1 a Ha.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  assert (Ht : In (t, 460) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  assert (Hs : In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; right; left; reflexivity).
  destruct (gsw_bounds cx fp k ly3 S3 W memc mdc t s HB HJ HFR Ht Hs LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0 & Htc & Hs0 & Hsc & HPB).
  destruct (gsw_base_facts cx HB) as (_ & _ & _ & HINP).
  pose proof HJ as (_ & Hly & _).
  assert (EF : frame_addr ly3 GE_CID fp = gF cx fp).
  { unfold gF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  pose proof (@alloc_ceiling_value rc) as HAC.
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  assert (KB : forall q n, In (q, n) (ablocks B ly3 S3) -> 0 <= n -> q <= a < q + n ->
            aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
  { intros q n Hq Hn Hqa. pose proof (req_size_pos' n Hn) as [_ Hrq].
    replace a with (q + (a - q)) by lia.
    apply (F2 q n (a - q) Hq ltac:(rewrite Hab2; exact Hq)); [lia | apply inFP_nil]. }
  destruct Ha as [[H|[H|[H|H]]]|[H|H]].
  - apply F1; lia.
  - apply (F4 GE_CID fp a Hfin); [|apply inFP_nil]. right. unfold in_zr. cbn [fst snd].
    rewrite EF, Hfb. change (1024 / 8) with 128. unfold gSH, shadow_of_addr in H. unfold shadow_addr. lia.
  - apply (F4 GE_CID fp a Hfin); [|apply inFP_nil]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite EF, Hfb. lia.
  - destruct HINP as [H0 | Hin]; [lia|].
    apply (KB (c_p cx) (c_n cx)); [rewrite Hab; apply in_or_app; left; exact Hin | unfold c_n; lia | exact H].
  - apply (KB t 460); [exact Ht | lia | exact H].
  - apply (KB s (sw_mbytes (c_pl cx))); [exact Hs | pose proof (sw_mbytes_ge (c_pl cx)); lia | exact H].
Qed.

End c.
End b.
End a.
