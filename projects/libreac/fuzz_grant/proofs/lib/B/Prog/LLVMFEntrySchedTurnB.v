(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnB), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedTurnB.v. *)
(* The image-B (UBSan) walk of the frame-loop turn's segment B,
   over image B's own addresses, registers, spill slots and UBSan guards; the shape is image A's.
   Ported from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnB.v at e6bd82f51c9. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput (0x80a3c) on the ASan+UBSan build, segment B:
   0x81bdc (GP_nx), the return of reac_headamp_tx_next, .. 0x81d5c (GP_end, no record: the cut
   TF) or 0x81c18 (GP_eff, a record: the answer, the channel, the parameter and the value
   checked: the cut TC) (LLVMFEntrySchedTurnDefs.v).

   The fifteen slots 0x81bdc .. 0x81c14 hold five checks that end in abort() (0x81d98):
     0x81bdc bgeu a0,s11   the answer r >= 2
     0x81be8 bltu s2,a1    the channel c > 47
     0x81c04 bgeu s4,a0    the parameter is 2 and the value v >= 56
     0x81c0c bltu s11,a2   the parameter p > 2
     0x81c10 bltu s9,s4    the parameter is 0 or 1 and the value v > 1
   Each is refuted from HeadampSched.frame_ok, never assumed: `r = 0 \/ r = 1` makes the answer
   a literal; `r = 1 -> 0 <= c < 48 /\ 0 <= p < 3` and the cut's bytes at &ch and &param become
   the interval facts of the atoms the two loads give, which decide 0x81be8 and 0x81c0c; and
   `HeadampModel.legal p v` refutes 0x81c04 and 0x81c10 by hand after the split on p = 2.

   Image B against image A's 0x815f0 .. 0x81624: 47 is in s2 (A: s7) and 1 in s9 (A: s8);
   &param and &value are read from the spill slots 112 and 96 (A: the register s5 and the slot
   128); the value byte lands in s4, the table register (A: s3, the &ch register); and the last
   slot of the range, `ld a0,0x98(s1)`, reads the table back from slot 152 for the call that
   follows, where image A's cut is its `mv a0,s4`. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySchedTurnDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* As image A's segment B does for its whole file: no lia below reasons about / or mod, and the
   cut's context carries several (gF mod 64, gF / 8, c_sp1 mod 32), which the euclidean-division
   translation would expand into every lia call; with the flag off they stay atoms. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of LLVMFEntrySchedTurnDefs.v at this section's asyms, meter and laws. Image B has
   no segment D, so image A's TD has no twin. The lane's own names this file uses (`stk96`,
   `gslots_turn`, `gtregs`, `gwr`, `BxL`, `Bsp0`) take none of B, MT and LAWS, so they need no
   abbreviation. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
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

(* A byte the runtime's view shows, as a one-byte value in memory. *)
Lemma val1_of_aview : forall H mem a v, aview SEGS H mem a = Some v ->
  val_mem SEGS (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros H mem a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. split; [|exact Hr].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  rewrite (le_byte_small (bv_unsigned b) 1 0) by first [change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
  cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
  symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* A run whose regions are read-only keeps every byte. *)
Lemma kept_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => Z.leb (YP09.r_whi r) (YP09.r_wlo r)) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF Hro a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
  apply (aview_kept_out E rs H m m' HF); [apply Z.mod_pos_bound; lia|].
  intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

(* A register after a run: what the symbolic state says, by the atoms' values. *)
Ltac greg HS EE :=
  lazymatch goal with |- getr (ms_regs ?m) ?r = ?rhs =>
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ m) =>
      let R := fresh "R" in
      pose proof (st_ok_pi_restrict_reg _ Ex ssx m r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in R;
      cbn [ms_regs restrict] in R; rewrite R; clear R;
      first [ rewrite ge_sv_SOff0; first [apply EE; reflexivity | eassumption]
            | cbn [sv_denot]; lazymatch rhs with getr (ms_regs ?m0) r =>
                match goal with H : getr (ms_regs m0) r = w64 _ |- _ => rewrite H; reflexivity end end ]
    end
  end.

(* A branch condition as an arithmetic fact. *)
Ltac hcz Hc :=
  rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U, ?branch_geu_U in Hc; unfold U in Hc;
  rewrite ?ge_sv_SOff0 in Hc;
  repeat match goal with H : ew ?Ex ?n = w64 _ |- _ => match type of Hc with context [ew Ex n] => rewrite H in Hc end end;
  cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite ?unsigned_lit_small in Hc by lia;
  first [ apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc
        | apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc
        | apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc | idtac ].

(* One byte of the frame, read back as the atom `a`: a read-only region at offset `o` from the
   base atom `n`. *)
Definition cellv (n : nat) (o : Z) (a : nat) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 1) 0 0 [YP09.mkChunk o (CVal 1 (SOff a 0))].
(* The spill slot 152, which 0x81c14 reads: the table, which is atom 20, the s4 of 0x81bdc,
   since 0x81bf8 overwrites s4 with the value. *)
Definition stkB152 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 20 0))].
(* Image B reaches the three cells off s6 = &ch (atom 22), at 0, 16 and 32 (ch, param, value),
   through the slots 112 and 96 for the last two (stk96, LLVMFEntrySchedTurnDefs.v). The
   channel, the parameter and the value are the atoms 32, 33 and 34. *)
Definition rs_B1 : YP09.smem := [stk96; stkB152; cellv 22 0 32; cellv 22 16 33; cellv 22 32 34].
Definition G_B1 : facts := mkFacts [(32%nat, mkAF 0 47 0); (33%nat, mkAF 0 2 0); (34%nat, mkAF 0 255 0)] [] [].

Lemma cellv_ok : forall E m n o a b x, bv_unsigned (ew E n) = b -> ew E a = w64 x -> 0 <= x < 256 ->
  0 <= b + o -> b + o + 1 <= 2 ^ 64 -> val_mem SEGS m (b + o) 1 x -> region_ok SEGS E m (cellv n o a).
Proof.
  intros E m n o a b x Hb Ha Hx H0 H1 Hv. unfold region_ok, cellv.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E m b o 1 (SOff a 0) x).
  - rewrite ge_sv_SOff0, Ha. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact Hv.
Qed.

(* The write windows of a run over read-only regions only. *)
Ltac awr_ro := lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]).

(* Land on the cut at 0x81c18 through FINB: the bytes kept, the machine fields, the registers. *)
Ltac finB FINB HJ EE :=
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
    destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
    apply (FINB msF mdF HJ);
    [ intros a; repeat match goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |-
          aview _ _ (ms_mem ?m1) a = _ => rewrite (kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end;
      reflexivity
    | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc
    | repeat split; greg HSx EE | greg HSx EE | greg HSx EE | greg HSx EE | greg HSx EE | greg HSx EE ]
  end.

Lemma segB : seg_B_ok B MT POST.
Proof.
  intros m HTF HTC cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T & us & r & c & p & v & T' & HT & Hm & R20 & Hsch & Hnx & R10 & Htab & Hlus & Hus & Hcell).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  destruct (gpres cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr) as (HFP & HSP).
  pose proof HT as (HTB0 & Hi & R21).
  pose proof HTB0 as (HBD & Hk & Hacc & Hbl & Hn & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27 &
    HSC & HSL & HWS & HST & HH).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof HSL as (L8 & L40 & L64 & L72 & L80 & L88 & L96 & L112 & L128 & L136 & L144 & L152).
  pose proof Htab as (Hint & Ht0 & HTl & HTb).
  pose proof (HeadampSched.frame_ok (c_pl cx) t i Ht0) as FO.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe] eqn:Hsrd.
  rewrite Hsch, Hnx in FO.
  destruct FO as (FL1 & FL2 & FL3 & FLT' & FI1 & FSch & FR01 & FR1).
  pose proof asan_consts as (C1 & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  (* a run that writes nothing keeps the cut; image B's turn counter is s5, register 21 *)
  assert (KEEP : forall pc' (msF : machine_state),
     (forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     ms_pc_val msF = w64 (BASE + pc') -> ms_resv msF = None -> ms_svc_pending msF = None ->
     ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
     gtregs (ms_regs ms3) (ms_regs msF) -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 21 ->
     tcom cx fp pc' GSH_turn i t k acc ly3 S3 W3 msF /\ gtab B cx ly3 S3 W3 msF t T' /\
     gfarr cx fp W3 msF GO_UNSET us /\ (forall o x, gfb cx fp W3 ms3 o x -> gfb cx fp W3 msF o x)).
  { intros pc' msF FK Fpc Frv Fsvc From Ffr Ffc FR F21.
    split.
    { eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
        | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc | exact FR | exact Hi
        | rewrite F21; exact R21 | intros a _ _; apply FK | | exact GSH_turn_len].
      intros j Hj. rewrite FK. apply HSHW. exact Hj. }
    split; [eapply gtab_keep; [exact Htab | intros j _; apply FK]|].
    split; [eapply gfarr_keep; [exact Hus | intros a _; apply FK]|].
    intros o x Hx. unfold gfb in *. rewrite FK. exact Hx. }
  destruct FR01 as [Er | Er]; subst r.
  - (* no record: 0x81bdc and 0x81be0 decide on the literal answer 0, on to the end of the turn *)
    remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
      by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
    assert (HS0 : st_ok_pi SEGS VAL E (mkSS GP_nx sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
    { rewrite (gms_eq (w_H W3) GP_nx ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
      - rewrite HE. apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor.
      - exact I.
      - split; [exact I | split; exact I]. }
    clear HE.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 10%bv (SLit 0) HS0 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R10; reflexivity)) as HS1.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 25%bv (SLit 1) HS1 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R25; reflexivity)) as HS2.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 27%bv (SLit 2) HS2 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R27; reflexivity)) as HS.
    clear HS0 HS1 HS2.
    assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK Bsp0 GP_end.
    { lazymatch goal with |- awr_ok ?E0 ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a1 a2 a3 a4 a5 a6 a7) end. apply awr_ok_nil. }
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
      assert (FK : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a; repeat match goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |-
              aview _ _ (ms_mem ?m1) a = _ => rewrite (kept_ro _ _ _ _ _ HFx ltac:(vm_compute; reflexivity) a); clear HFx end;
            reflexivity);
      assert (FR : gtregs (ms_regs ms3) (ms_regs msF)) by (repeat split; greg HSx EE);
      assert (F21 : getr (ms_regs msF) 21 = getr (ms_regs ms3) 21) by greg HSx EE;
      assert (F20 : getr (ms_regs msF) 20 = getr (ms_regs ms3) 20) by greg HSx EE;
      destruct (KEEP GP_end msF FK Fpc Frv Fsvc From Ffr Ffc FR F21) as (KT & KG & KU & _);
      apply (HTF cx fp k acc ly3 S3 W3 msF mdF HB HJ Hfr HMLE)
    end.
    exists i, t, T', us. split; [exact KT|]. split; [exact Hm|]. split; [rewrite F20; exact R20|].
    split; [rewrite FSch, HeadampSched.us_step_0; reflexivity|].
    split; [exact KG|]. split; [exact FI1|]. split; [exact Hlus | exact KU].
  - (* a record: the answer, the channel, the parameter and the value *)
    destruct (FR1 eq_refl) as (Hc48 & Hp3 & Hleg & _).
    destruct (Hcell eq_refl) as (Cc & Cp & Cv).
    destruct (val1_of_aview _ _ _ _ Cc) as (VCc & Rc).
    destruct (val1_of_aview _ _ _ _ Cp) as (VCp & Rp).
    destruct (val1_of_aview _ _ _ _ Cv) as (VCv & Rv).
    unfold HeadampModel.legal in Hleg.
    remember (Eimg (Ereg (ms_regs ms3) [w64 c; w64 p; w64 v])) as E eqn:HE.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
      by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
    assert (E32 : ew E 32 = w64 c)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
    assert (E33 : ew E 33 = w64 p)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
    assert (E34 : ew E 34 = w64 v)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
    assert (E20 : ew E 20 = w64 t) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
    assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
    assert (U22 : bv_unsigned (ew E 22) = gF cx fp + 784)
      by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold GO_CH; lia).
    destruct (table_out cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl 0 ltac:(lia)) as (_ & Ht64).
    assert (HS0 : st_ok_pi SEGS VAL E (mkSS GP_nx sr_atoms rs_B1 None G_B1) (restrict (w_H W3) ms3)).
    { rewrite (gms_eq (w_H W3) GP_nx ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
      - rewrite HE. apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - unfold rs_B1. apply Forall_cons.
        { unfold region_ok, stk96.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
          - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 22 32) (gF cx fp + 816)).
            + cbn [sv_denot]. rewrite U22. f_equal. lia.
            + cbn -[gF]. lia.
            + cbn. lia.
            + apply val_mem_of_rdword. exact L96.
          - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 22 16) (gF cx fp + 800)).
            + cbn [sv_denot]. rewrite U22. f_equal. lia.
            + cbn -[gF]. lia.
            + cbn. lia.
            + apply val_mem_of_rdword. exact L112. }
        apply Forall_cons.
        { unfold region_ok, stkB152.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
          apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SOff 20 0) t).
          - rewrite ge_sv_SOff0, E20. reflexivity.
          - cbn. lia.
          - cbn. lia.
          - apply val_mem_of_rdword. exact L152. }
        apply Forall_cons; [eapply cellv_ok; [exact U22 | exact E32 | lia | lia | lia |
          replace (gF cx fp + 784 + 0) with (gF cx fp + GO_CH) by (unfold GO_CH; lia); exact VCc]|].
        apply Forall_cons; [eapply cellv_ok; [exact U22 | exact E33 | lia | lia | lia |
          replace (gF cx fp + 784 + 16) with (gF cx fp + GO_PAR) by (unfold GO_PAR; lia); exact VCp]|].
        apply Forall_cons; [eapply cellv_ok; [exact U22 | exact E34 | lia | lia | lia |
          replace (gF cx fp + 784 + 32) with (gF cx fp + GO_VAL) by (unfold GO_VAL; lia); exact VCv]|].
        apply Forall_nil.
      - apply pairwise_disjoint_of_extents. unfold extent_of_region, rs_B1, stk96, stkB152, cellv.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok G_B1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat split; lia. }
    clear HE.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 10%bv (SLit 1) HS0 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R10; reflexivity)) as HS1.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 18%bv (SLit 47) HS1 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R18; reflexivity)) as HS2.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 25%bv (SLit 1) HS2 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R25; reflexivity)) as HS3.
    pose proof (ast_ok_pi_set_reg_fp E _ _ 27%bv (SLit 2) HS3 eq_refl
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite R27; reflexivity)) as HS.
    clear HS0 HS1 HS2 HS3.
    assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
    (* the cut at 0x81c18: a0 holds the table again, a1 the channel, a2 the parameter, s4 the value *)
    assert (FINB : forall msF mdF,
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly3 S3 W3 (ms_mem msF) mdF k ->
       (forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
       ms_pc_val msF = w64 (BASE + GP_eff) -> ms_resv msF = None -> ms_svc_pending msF = None ->
       ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
       gtregs (ms_regs ms3) (ms_regs msF) -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 21 ->
       getr (ms_regs msF) 10 = w64 t -> getr (ms_regs msF) 11 = w64 c -> getr (ms_regs msF) 12 = w64 p ->
       getr (ms_regs msF) 20 = w64 v ->
       SRr SEGS W3 (mkCfg msF mdF) (POST cx)).
    { intros msF mdF HJF FK Fpc Frv Fsvc From Ffr Ffc FR F21 F10 F11 F12 F20.
      destruct (KEEP GP_eff msF FK Fpc Frv Fsvc From Ffr Ffc FR F21) as (KT & KG & KU & KC).
      apply (HTC cx fp k acc ly3 S3 W3 msF mdF HB HJF Hfr HMLE).
      exists i, t, T, us, c, p, v, T'.
      split; [|split; [exact F10 | split; [exact F11 | split; [exact F12 | exact F20]]]].
      split; [exact KT|]. split; [exact Hm|]. split; [exact Hsch|]. split; [exact Hnx|].
      split; [exact KG|]. split; [exact Hlus|]. split; [exact KU|].
      split; [exact (KC _ _ Cc)|]. split; [exact (KC _ _ Cp) | exact (KC _ _ Cv)]. }
    (* 0x81bdc and 0x81be0 decide on the literal answer 1; 0x81be8 (c > 47) is decided by atom 32's
       fact; the run stops at 0x81bfc, the split on p = 2 *)
    paj_run_tok RUN HS HJ SHOK Bsp0.
    { awr_ro. }
    psrr_branch_tok RUN BR HS SHOK Bsp0.
    + (* param <> 2: 0x81c0c (p > 2) is decided by atom 33's fact; the run stops at 0x81c10 *)
      hcz Hc. rename Hc into Hpar.
      paj_run_tok RUN HS HJ SHOK Bsp0.
      { awr_ro. }
      psrr_branch_tok RUN BR HS SHOK Bsp0.
      * (* 0x81c10 to the error path: value > 1 for a 0/1 parameter *)
        exfalso. hcz Hc. lia.
      * paj_run_to_tok RUNTO HS HJ SHOK Bsp0 GP_eff.
        { awr_ro. }
        finB FINB HJ EE.
    + (* param = 2 *)
      hcz Hc. rename Hc into Hpar.
      paj_run_tok RUN HS HJ SHOK Bsp0.
      { awr_ro. }
      psrr_branch_tok RUN BR HS SHOK Bsp0.
      * (* 0x81c04 to the error path: value >= 56 for parameter 2 *)
        exfalso. hcz Hc. lia.
      * paj_run_to_tok RUNTO HS HJ SHOK Bsp0 GP_eff.
        { awr_ro. }
        finB FINB HJ EE.
Qed.

End c.
End b.
End a.
