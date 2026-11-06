(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnCr), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AF0s.v. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput, segment Cr: 0x8162c, the return of reac_headamp_tx_effective, ..
   0x816a4 (the cell was not set: the call of reac_headamp_default follows) or 0x816ac (the cell was set: the value
   was checked against set_to) (GrantEntrySchedTurnDefs.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntrySeat HeadampTxEffective HeadampDefault HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySchedTurnDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- the symbolic state at 0x8162c ----
   Atoms past the registers: 32 = ch, 33 = param, 34 = the address of was_set[ch][param]
   (F + 32 + 3 ch + param; set_to[ch][param] is 208 bytes above it), 35 = that was_set
   byte, 36 = that set_to byte. The run computes the address of the was_set cell as
   s1[144] + param + 3 ch; the alias names it atom 34, and the shadow entries (34, 0, 1)
   and (34, 208, 209) say that the shadow marks both cells usable. *)
Definition cellc (n : nat) (o : Z) (a : nat) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 1) 0 0 [YP09.mkChunk o (CVal 1 (SOff a 0))].
(* The spill slots the run reads: the addresses of ch, value, set_to and was_set, and the shadow offset. *)
Definition stkCr : YP09.region := YP09.mkRegion (Some 9%nat) 104 160 0 0
  [YP09.mkChunk 104 (CVal 8 (SOff 21 (-16))); YP09.mkChunk 128 (CVal 8 (SOff 21 16));
   YP09.mkChunk 136 (CVal 8 (SOff 21 (-560))); YP09.mkChunk 144 (CVal 8 (SOff 21 (-768)));
   YP09.mkChunk 152 (CVal 8 (SLit SHADOW_OFF))].
Definition rsCr : YP09.smem :=
  [stkCr; cellc 21 0 33; cellc 21 (-16) 32; cellc 21 16 19; cellc 34 0 35; cellc 34 208 36].
Definition alCr : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 21 (-768)) (SOff 33 0)) (SMd M_MUL (SOff 32 0) (SLit 3)).
Definition GCr : facts := mkFacts [(19%nat, mkAF 0 255 0); (32%nat, mkAF 0 47 0); (33%nat, mkAF 0 2 0);
  (34%nat, mkAF 4096 (2 ^ 47) 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)] [] [(alCr, SOff 34 0)].
Definition SHCr : list shent := [mkSHE 34 0 1; mkSHE 34 208 209].
Definition BspCr : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 45).

Lemma cr_agree_ewset : forall E0 E k w, env_agree 32 E0 E -> (32 <= k)%nat -> env_agree 32 E0 (ewset E k w).
Proof. intros E0 E k w H Hk. exact (gagree_ext E0 E k [w] H Hk). Qed.

(* The shadow bytes of was_set and set_to while a turn runs. *)
Lemma GSH_turn_tables : forallb (fun j => Z.eqb (nth j GSH_turn 0) 0) (seq 4 18 ++ seq 30 18) = true.
Proof. vm_compute. reflexivity. Qed.

Ltac cr_pow := repeat match goal with |- context [2 ^ (8 * Z.of_N ?n)] =>
  let r := eval vm_compute in (2 ^ (8 * Z.of_N n)) in change (2 ^ (8 * Z.of_N n)) with r end.

(* A branch condition at a state whose atoms 512.. the run added, as an arithmetic fact. *)
Ltac cr_hc Hc :=
  rewrite ?branch_ne_U, ?branch_eq_U in Hc; unfold U in Hc; rewrite ?ge_sv_SOff0 in Hc;
  repeat (rewrite ew_ewset_other in Hc by lia);
  repeat match goal with H : ew ?Ex ?n = w64 _ |- _ => match type of Hc with context [ew Ex n] => rewrite H in Hc end end;
  cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite ?unsigned_lit_small in Hc by lia;
  first [ apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc
        | apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc ].

Ltac cr_awr_ro := lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* A run whose regions are read-only keeps every byte. *)
Lemma cr_kept_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF Hro a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
  apply (aview_kept_out E rs H m m' HF); [apply Z.mod_pos_bound; lia|].
  intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma cellc_ok : forall E m n o a b x, bv_unsigned (ew E n) = b -> bv_unsigned (ew E a) = x -> 0 <= x < 256 ->
  0 <= b + o -> b + o + 1 <= 2 ^ 64 -> val_mem SEGS m (b + o) 1 x -> region_ok SEGS E m (cellc n o a).
Proof.
  intros E m n o a b x Hb Ha Hx H0 H1 Hv. unfold region_ok, cellc.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E m b o 1 (SOff a 0) x).
  - rewrite ge_sv_SOff0, <- Ha. symmetry. apply Z_to_bv_bv_unsigned.
  - cbn. lia.
  - cbn. lia.
  - exact Hv.
Qed.

(* One byte of an array of the frame. *)
Lemma cr_farr_cell : forall cx fp W3 ms3 off (l : list byte) kk,
  gfarr cx fp W3 ms3 off l -> 0 <= kk < Z.of_nat (length l) ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (gF cx fp + off + kk) 1 (HeadampModel.tb l kk) /\
  0 <= HeadampModel.tb l kk < 256.
Proof.
  intros cx fp W3 ms3 off l kk Ha Hk. unfold gfarr in Ha.
  destruct (garr8_nthZ SEGS _ _ _ kk Ha ltac:(lia) ltac:(rewrite length_map; lia)) as [Hv Hr].
  assert (Hn : nth (Z.to_nat kk) (map (fun b : byte => bv_unsigned b) l) 0 = HeadampModel.tb l kk).
  { pose proof (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) (Z.to_nat kk)) as Hm. cbv beta in Hm.
    unfold HeadampModel.tb. rewrite <- Hm. apply nth_indep. rewrite length_map. lia. }
  rewrite Hn in Hv, Hr. split; [exact Hv | exact Hr].
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of GrantEntrySchedTurnDefs.v at this section's asyms, meter and laws. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation TD := (TD B MT).
#[local] Notation TE := (TE B MT).
#[local] Notation TF := (TF B MT).
#[local] Notation gtracked := (gtracked B).
#[local] Notation gctx := (gctx B MT LAWS).
#[local] Notation gaddr_ok := (gaddr_ok B).
#[local] Notation ginput_ok := (ginput_ok B MT LAWS).
#[local] Notation tbody_keep := (tbody_keep B MT).
#[local] Notation tcom_keep := (tcom_keep B MT).
#[local] Notation gpres := (gpres B MT LAWS).
#[local] Notation gtracked_rng := (gtracked_rng B MT LAWS).
#[local] Notation table_out := (table_out B MT LAWS).
#[local] Notation gtab_keep := (gtab_keep B).
#[local] Notation GI_sched_of := (GI_sched_of B MT).
#[local] Notation tcom_of_GI_sched := (tcom_of_GI_sched B MT).
#[local] Notation GI_freeT_of := (GI_freeT_of B MT).
#[local] Notation table_sep := (table_sep B LAWS).
#[local] Notation table_new := (table_new B LAWS).
#[local] Notation garo := (garo B MT).
#[local] Notation gtab_obj := (gtab_obj B).
#[local] Notation obj_gtab := (obj_gtab B).

(* 0x8162c .. 0x816a4 (the cell was not set) or 0x816ac (the cell was set). *)
Lemma segCr : seg_Cr_ok B MT POST.
Proof.
  intros m HTD HTE cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T & us & c & p & v & T' & (HT & Hm & Hsch & Hnx & Htab & Hlus & Hus & Cc & Cp & Cv) & R10 & R19).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  pose proof HT as (HTB0 & Hi & R18).
  pose proof HTB0 as (HBD & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HWS & HST & HH).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof HSL as ((M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176) & L8 & L32 & L40 & L72 & L80 & L104 & L112 & L128).
  pose proof Htab as (Hint & Ht0 & HTl & HTb).
  pose proof asan_consts as (C1 & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  (* the five checks of the frame (HeadampSched.v:162-209) at this turn *)
  pose proof (HeadampSched.frame_ok (c_pl cx) t i Ht0) as FO.
  revert FO. destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe]. intros FO.
  rewrite Hsch in FO. cbv beta iota zeta in FO. rewrite Hnx in FO. cbv beta iota zeta in FO.
  destruct FO as (_ & _ & _ & _ & _ & _ & _ & FR1).
  destruct (FR1 eq_refl) as (Hc48 & Hp3 & Hleg & Hveff & Hset & _). clear FR1.
  pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
  destruct (val_mem1_of_aview SEGS _ _ _ _ Cc) as (VCc & Rc).
  destruct (val_mem1_of_aview SEGS _ _ _ _ Cp) as (VCp & Rp).
  destruct (val_mem1_of_aview SEGS _ _ _ _ Cv) as (VCv & Rv).
  destruct (cr_farr_cell cx fp W3 ms3 GO_WAS _ (3 * c + p) HWS ltac:(rewrite Lws; lia)) as (VW & RW).
  destruct (cr_farr_cell cx fp W3 ms3 GO_SET _ (3 * c + p) HST ltac:(rewrite Lst; lia)) as (VS & RS).
  remember (HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p)) as wv eqn:Hwv.
  remember (HeadampModel.tb (GrantSlotPlan.st_end (c_pl cx)) (3 * c + p)) as sv eqn:Hsv.
  remember (gF cx fp + 32 + (3 * c + p)) as X eqn:HX.
  (* the trace and the cut the run reaches carry over from TCr: no byte changes *)
  assert (KEEP : forall pc' (msF : machine_state),
     (forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     ms_pc_val msF = w64 (BASE + pc') -> ms_resv msF = None -> ms_svc_pending msF = None ->
     ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
     gtregs (ms_regs ms3) (ms_regs msF) -> getr (ms_regs msF) 18 = getr (ms_regs ms3) 18 ->
     trec cx fp pc' m k acc ly3 S3 W3 msF i t T us c p v T').
  { intros pc' msF FK Fpc Frv Fsvc From Ffr Ffc FR F18.
    split.
    { eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
        | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc | exact FR | exact Hi
        | rewrite F18; exact R18 | intros a _ _; apply FK | | exact GSH_turn_len].
      intros j Hj. rewrite FK. apply HSHW. exact Hj. }
    split; [exact Hm|]. split; [exact Hsch|]. split; [exact Hnx|].
    split; [eapply gtab_keep; [exact Htab | intros j _; apply FK]|].
    split; [exact Hlus|]. split; [eapply gfarr_keep; [exact Hus | intros a _; apply FK]|].
    unfold gfb in Cc, Cp, Cv |- *. rewrite !FK. split; [exact Cc|]. split; [exact Cp | exact Cv]. }
  (* the environment: the registers at 0x8162c and the five atoms *)
  remember (Eimg (Ereg (ms_regs ms3) [w64 c; w64 p; w64 X; w64 wv; w64 sv])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [w64 c; w64 p; w64 X; w64 wv; w64 sv]) E) by (subst E; apply gagree0).
  assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
    by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E32 : ew E 32 = w64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = w64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E34 : ew E 34 = w64 X) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (E35 : ew E 35 = w64 wv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
  assert (E36 : ew E 36 = w64 sv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
  assert (E19 : ew E 19 = w64 v) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (HXr : 4096 <= X /\ X + 209 <= gF cx fp + 1024) by (subst X; lia).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = gF cx fp + 800)
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold GO_PAR; lia).
  assert (U19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = X) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = wv) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = sv) by (rewrite E36; apply unsigned_lit_small; lia).
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS GP_effr sr_atoms rsCr None GCr) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_effr ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold rsCr. apply Forall_cons.
      { unfold region_ok, stkCr.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 104 8 (SOff 21 (-16)) (gF cx fp + 784)).
          + cbn [sv_denot]. rewrite U21. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact L104.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 128 8 (SOff 21 16) (gF cx fp + 816)).
          + cbn [sv_denot]. rewrite U21. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact L128.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 21 (-560)) (gF cx fp + 240)).
          + cbn [sv_denot]. rewrite U21. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact M136.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SOff 21 (-768)) (gF cx fp + 32)).
          + cbn [sv_denot]. rewrite U21. f_equal. lia.
          + cr_pow. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact M144.
        - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SLit SHADOW_OFF) SHADOW_OFF).
          + reflexivity.
          + cr_pow. unfold SHADOW_OFF. lia.
          + cbn. lia.
          + apply val_mem_of_rdword. exact M152. }
      apply Forall_cons; [eapply cellc_ok; [exact U21 | exact U33 | lia | lia | lia |
        replace (gF cx fp + 800 + 0) with (gF cx fp + GO_PAR) by (unfold GO_PAR; lia); exact VCp]|].
      apply Forall_cons; [eapply cellc_ok; [exact U21 | exact U32 | lia | lia | lia |
        replace (gF cx fp + 800 + -16) with (gF cx fp + GO_CH) by (unfold GO_CH; lia); exact VCc]|].
      apply Forall_cons; [eapply cellc_ok; [exact U21 | exact U19 | lia | lia | lia |
        replace (gF cx fp + 800 + 16) with (gF cx fp + GO_VAL) by (unfold GO_VAL; lia); exact VCv]|].
      apply Forall_cons; [eapply cellc_ok; [exact U34 | exact U35 | lia | lia | lia |
        replace (X + 0) with (gF cx fp + GO_WAS + (3 * c + p)) by (unfold GO_WAS; lia); exact VW]|].
      apply Forall_cons; [eapply cellc_ok; [exact U34 | exact U36 | lia | lia | lia |
        replace (X + 208) with (gF cx fp + GO_SET + (3 * c + p)) by (unfold GO_SET; lia); exact VS]|].
      apply Forall_nil.
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, rsCr, stkCr, cellc.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21, U34.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok GCr]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U19, U32, U33, U34, U35, U36. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
      + cbn [f_alias alias_ok GCr]. split; [|exact I]. unfold alCr.
        apply U_inj. rewrite !U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw].
        rewrite U21, U32, U33, U34.
        repeat match goal with |- context [zcanon ?z] => rewrite (zcanon_id z) by (unfold M64; lia) end.
        lia. }
  clear HE.
  (* a0 := s3 (both hold the value, `v = eff T' t c p`, HeadampSched.v:169); s11 := 2 *)
  pose proof (ast_ok_pi_set_reg_fp E _ _ 10%bv (SOff 19 0) HS0 eq_refl
    ltac:(rewrite ge_sv_SOff0, E19; cbn [ms_regs restrict]; rewrite R10, <- Hveff; reflexivity)) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ 27%bv (SLit 2) HS1 eq_refl
    ltac:(cbn [sv_denot ms_regs restrict]; rewrite R27; reflexivity)) as HS.
  clear HS0 HS1.
  (* the shadow marks the was_set and set_to cells of (ch, param) usable *)
  assert (HZ : forall j, 4 <= j < 22 \/ 30 <= j < 48 -> aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + j) = Some 0).
  { intros j Hj. pose proof GSH_turn_len as Lt. unfold GE_NSH in Lt.
    pose proof (HSHW (Z.to_nat j) ltac:(rewrite Lt; lia)) as Hj'. rewrite Z2Nat.id in Hj' by lia. rewrite Hj'.
    pose proof GSH_turn_tables as Hb. rewrite forallb_forall in Hb.
    specialize (Hb (Z.to_nat j) ltac:(apply in_app_iff; destruct Hj; [left | right]; apply in_seq; lia)).
    cbv beta in Hb. apply Z.eqb_eq in Hb. rewrite Hb. reflexivity. }
  assert (UBx : U E BxL = SHADOW_OFF) by (unfold BxL; rewrite U_SLit; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  assert (UX : U E (SOff 34 0) = X) by (rewrite U_SOff, U34, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (SHOK : sh_ok SEGS BxL SHCr E (mrestrict (w_H W3) (ms_mem ms3))).
  { unfold sh_ok, SHCr. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite UBx, UX;
      (split; [|intros a Ha; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia]);
      intros x Hx; exists 0; (split; [|left; reflexivity]);
      unfold shadow_of_addr; dm x 8; dm (gF cx fp) 8; dm (gF cx fp) 64; dm (x - gF cx fp) 8.
    - replace (SHADOW_OFF + x / 8) with (gSH cx fp + (x - gF cx fp) / 8) by (rewrite HSH; lia).
      exact (HZ ((x - gF cx fp) / 8) ltac:(left; lia)).
    - replace (SHADOW_OFF + x / 8) with (gSH cx fp + (x - gF cx fp) / 8) by (rewrite HSH; lia).
      exact (HZ ((x - gF cx fp) / 8) ltac:(right; lia)). }
  (* 0x8162c .. 0x81674: the param, the shadow of the was_set cell, the value, the was_set byte *)
  paj_run_tok RUN HS HJ SHOK BspCr.
  { cr_awr_ro. }
  psrr_branch_tok RUN BR HS SHOK BspCr.
  - (* 0x81674 taken: the cell was not set; on to the call of reac_headamp_default *)
    cr_hc Hc. rename Hc into Hw0.
    paj_run_to_tok RUNTO HS HJ SHOK BspCr GP_dfl.
    { cr_awr_ro. }
    lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
      assert (HAEx : env_agree 32 (Ereg (ms_regs ms3) [w64 c; w64 p; w64 X; w64 wv; w64 sv]) Ex)
        by (repeat (apply cr_agree_ewset; [|lia]); exact HAE);
      pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W3) msF) (ms_regs ms3) [w64 c; w64 p; w64 X; w64 wv; w64 sv]
        [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv HSx HAEx ltac:(vm_compute; reflexivity)) as FR;
      cbn [ms_regs restrict] in FR;
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HSx) as F27;
      let e := eval vm_compute in (sr_get (ss_regs ssx) 27%bv) in change (sr_get (ss_regs ssx) 27%bv) with e in F27;
      cbn [ms_regs restrict sv_denot] in F27;
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSx) as F10;
      let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in F10;
      cbn [ms_regs restrict] in F10; rewrite ge_sv_SOff0 in F10; repeat (rewrite ew_ewset_other in F10 by lia);
      rewrite E33 in F10;
      assert (FK : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a; repeat match goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |-
              aview _ _ (ms_mem ?m1) a = _ => rewrite (cr_kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end;
            reflexivity);
      assert (FG : gtregs (ms_regs ms3) (ms_regs msF))
        by (repeat split; first [apply FR; cbv; tauto | rewrite F27, R27; reflexivity]);
      pose proof (KEEP GP_dfl msF FK Fpc Frv Fsvc From Ffr Ffc FG ltac:(apply FR; cbv; tauto)) as KT;
      apply (HTD cx fp k acc ly3 S3 W3 msF mdF HB HJ Hfr HMLE)
    end.
    exists i, t, T, us, c, p, v, T'. split; [exact KT|]. split; [exact F10|].
    split; [rewrite FR by (cbv; tauto); exact R19|]. rewrite <- Hwv. exact Hw0.
  - (* 0x81674 not taken: the cell was set; the shadow of the set_to cell and its byte *)
    cr_hc Hc. rename Hc into Hw0.
    paj_run_tok RUN HS HJ SHOK BspCr.
    { cr_awr_ro. }
    psrr_branch_tok RUN BR HS SHOK BspCr.
    + (* 0x8169c to the error path: the value is not set_to[ch][param]; `v = tb (st_end pl) (3c+p)`, HeadampSched.v:170 *)
      exfalso. cr_hc Hc. apply Hc. apply Hset. exact Hw0.
    + (* 0x8169c not taken: on to the scene check at 0x816ac *)
      cr_hc Hc.
      paj_run_to_tok RUNTO HS HJ SHOK BspCr GP_scn.
      { cr_awr_ro. }
      lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
        destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
        assert (HAEx : env_agree 32 (Ereg (ms_regs ms3) [w64 c; w64 p; w64 X; w64 wv; w64 sv]) Ex)
          by (repeat (apply cr_agree_ewset; [|lia]); exact HAE);
        pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W3) msF) (ms_regs ms3) [w64 c; w64 p; w64 X; w64 wv; w64 sv]
          [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25]%bv HSx HAEx ltac:(vm_compute; reflexivity)) as FR;
        cbn [ms_regs restrict] in FR;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HSx) as F27;
        let e := eval vm_compute in (sr_get (ss_regs ssx) 27%bv) in change (sr_get (ss_regs ssx) 27%bv) with e in F27;
        cbn [ms_regs restrict sv_denot] in F27;
        assert (FK : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
          by (intros a; repeat match goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |-
                aview _ _ (ms_mem ?m1) a = _ => rewrite (cr_kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end;
              reflexivity);
        assert (FG : gtregs (ms_regs ms3) (ms_regs msF))
          by (repeat split; first [apply FR; cbv; tauto | rewrite F27, R27; reflexivity]);
        pose proof (KEEP GP_scn msF FK Fpc Frv Fsvc From Ffr Ffc FG ltac:(apply FR; cbv; tauto)) as KT;
        apply (HTE cx fp k acc ly3 S3 W3 msF mdF HB HJ Hfr HMLE)
      end.
      exists i, t, T, us, c, p, v, T'. exact KT.
Qed.

End c.
End b.
End a.
