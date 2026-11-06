(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS1s), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Segment 1s of the sweep phase: 0x80e58 -> 0x80e98, fuzz_grant.c:285-300. The walk
   reads the two bytes of the allocation `a` that reac_grant_allocate left in the
   frame on the side stack and tests them against the answer it gave: a refused box
   has both bytes 0 and goes straight to the hand-built block at 0x812ac, an admitted
   one has them equal to the base and the width the input named. The admitted box
   then gets its sweep buffer from the malloc wrapper at 0x80e8c, of
   (rows > 0 ? rows : 1) * 34 bytes, and the walk stores it in spill slot 64.

   The five branches to the error path (a call of __asan_handle_no_return and then
   abort, at 0x81a0c) are 0x80e60 and 0x80e6c (the refused box's two bytes are 0),
   0x80e70 and 0x80e78 (the admitted box's two bytes are what the input named) and
   0x80e90 (the sweep buffer is not null). None is taken. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo
GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySweepS1c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The two bytes of `a`, as a read-only region over the register that holds its
   address (x18 = s2), and the spill slots the walk reads and writes. *)
Definition gss_a_region (b0 b1 : Z) : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 2 0 0
    [YP09.mkChunk 0 (CVal 1 (SLit b0)); YP09.mkChunk 1 (CVal 1 (SLit b1))].
Definition gss_slot_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 192 64 72 [YP09.mkChunk 16 (CVal 8 (SOff 32 0))].

(* After a run over read-only regions: the memory is the one the walk started from. *)
Ltac gs_rw_mem mem0 :=
  lazymatch goal with HF : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    let H := fresh "HM" in
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HF) as H;
    tryif constr_eq m mem0 then idtac else
      (lazymatch m with ms_mem ?o =>
         lazymatch goal with HMo : ms_mem o = mem0 |- _ => rewrite HMo in H; clear HMo; rename H into HM end end)
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* An address the walk keeps across the malloc and the store into slot 64. *)
Ltac gs_pk :=
  split; [unfold gs_keep_at; try change (Z.of_nat GE_NSH) with 104;
          try change (fs_frame_bytes GE_CID) with 1024;
          first [ left; lia | right; left; lia | right; right; left; lia
                                   | right; right; right; left; lia | right; right; right; right; lia ]
         | split; lia ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

Lemma gs_sweep :
  ge_from B MT (ge_post B MT) (GIS_mal B MT) ->
  ge_from B MT (ge_post B MT) (GI_raw B MT) ->
  ge_from B MT (ge_post B MT) (GI_sweep B MT).
Proof.
intros HMAL HRAW cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & Hblk & Hn26 & R18 & R20 & R21 & R22 & R23 & R24 & R25 & R26
  & R19 & R10 & HAB & SL88 & SL120 & SL64 & SL96 & SLATE & HTAB & HWAS & HSET & HREL & HI1).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HREGS & HSAVED & HSH & HFL & HLEN & HINP).
pose proof HREGS as (G2 & G8 & G9 & G3 & G4).
pose proof HB as (HPRE & H10 & H11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Hsp1d & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk0 & JK1 & _).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
assert (HEV : EV_MAX = 11776) by reflexivity.
assert (HGEV : GE_EV = 2000) by reflexivity.
assert (HLIVE : GE_LIVE = 2 ^ 33) by reflexivity.
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Hsp288 : 0 <= spZ (c_regs cx) + -288) by lia.
assert (Hmod288 : (spZ (c_regs cx) + -288) mod 16 = 0)
  by (rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity).
destruct (sp1_facts (spZ (c_regs cx) + -288) Hsp288 Hmod288) as (Hsp1r & Hsp1al32 & Hsp1al16).
rewrite <- Hsp1d in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1lo : alloc_ceiling <= c_sp1 cx) by lia.
assert (Hsp1hi : c_sp1 cx + 192 <= 2 ^ 64) by lia.
destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly3 HAR0 Hly3) as (Eabl & Efa & Eown).
assert (EFA : frame_addr ly3 GE_CID fp = gF cx fp) by (unfold gF; rewrite Efa; reflexivity).
assert (HfrIn : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 HfrIn) as (HF0 & HF1 & _).
rewrite EFA in HF0, HF1. rewrite Hfb in HF1.
assert (HtIn : In (t, 460) (ablocks B ly3 S3)) by (destruct HTAB as (H & _); exact H).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 t 460 HAR3 HtIn) as (_ & Ht4096 & Htceil & _).
change (req_size 460) with 460 in Htceil.
assert (HpIn : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ intros Hn. rewrite Hblk. apply in_or_app. left.
  destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
assert (Hpceil : 0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling).
{ destruct Hpn as [(Hz & Hemp) | (Hn & Hin)].
  - rewrite Hz, Hemp. unfold GE_EMPTY. lia.
  - destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hin)
      as (_ & Hp4096 & Hce & _). pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia. }
destruct Hpceil as (Hp0 & Hpceil).
assert (Hshlo : 0 <= gSH cx fp /\ gSH cx fp + 128 <= alloc_ceiling).
{ unfold gSH, shadow_of_addr, SHADOW_OFF.
  assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia). lia. }
destruct Hshlo as (Hsh0 & Hshc).
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_sweep)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms3; cbn in *; subst; reflexivity. }
destruct (ok (c_pl cx)) eqn:Hok.
- (* the box was admitted *)
  destruct HAB as (HA0 & HA1).
  destruct (gs_ok_range (c_pl cx) Hok) as (Hb0 & Hw0 & Hbw).
  set (bse := sw_base (c_pl cx)) in *. set (wdt := sw_in (c_pl cx)) in *.
  set (rws := sw_rows (c_pl cx)) in *.
  pose proof (gs_rows_range (c_pl cx)) as Hrws. fold rws in Hrws.
  assert (U18 : bv_unsigned (ew (Eimg (edset (Ereg (ms_regs ms3) [w64 rws]) 0
                  [Z_to_bv 8 bse; Z_to_bv 8 wdt])) 18%nat) = gF cx fp + GO_A).
  { cbn [edset ew]. rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) [w64 rws] 18%nat 18%bv eq_refl), R18.
    apply unsigned_lit_small. unfold GO_A. lia. }
  assert (U9 : bv_unsigned (ew (Eimg (edset (Ereg (ms_regs ms3) [w64 rws]) 0
                  [Z_to_bv 8 bse; Z_to_bv 8 wdt])) 9%nat) = c_sp1 cx).
  { cbn [edset ew]. rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) [w64 rws] 9%nat 9%bv eq_refl), G9.
    apply unsigned_lit_small. lia. }
  assert (E32 : ew (Eimg (edset (Ereg (ms_regs ms3) [w64 rws]) 0
                  [Z_to_bv 8 bse; Z_to_bv 8 wdt])) 32%nat = w64 rws).
  { cbn [edset ew]. rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ms_regs ms3) [w64 rws] 0). }
  assert (ED : ed (Eimg (edset (Ereg (ms_regs ms3) [w64 rws]) 0
                  [Z_to_bv 8 bse; Z_to_bv 8 wdt])) 0 = [Z_to_bv 8 bse; Z_to_bv 8 wdt])
    by reflexivity.
  assert (Hrs : Forall (YP09.region_ok SEGS (Eimg (edset (Ereg (ms_regs ms3) [w64 rws]) 0
                  [Z_to_bv 8 bse; Z_to_bv 8 wdt])) (mrestrict (w_H W3) (ms_mem ms3)))
                  [YP09.mkRegion (Some 9%nat) 0 192 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 32 0))];
                   YP09.mkRegion (Some 18%nat) 0 2 0 0 [YP09.mkChunk 0 (CData 0 0 2)]]).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (gs_slotreg_ok W3 _ (ms_mem ms3) _ (c_sp1 cx) 0 0 U9 ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)).
      apply Forall_cons; [|apply Forall_nil].
      apply (gs_slot_chunk W3 _ (ms_mem ms3) 16 32%nat rws (c_sp1 cx) E32 U9).
      exact (proj1 (proj1 SLATE)).
    - unfold YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U18. split; [unfold GO_A; lia|]. split; [unfold GO_A; lia|].
      split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      intros i Hi. cbn [YP09.c_len YP09.c_val YP09.c_off YP09.cv_len] in Hi |- *.
      exists (nth (Z.to_nat i) [Z_to_bv 8 bse; Z_to_bv 8 wdt] (Z_to_bv 8 0)).
      cbn [YP09.cbyte]. rewrite ED. split.
      + rewrite Z.add_0_l. apply nth_error_nth'. cbn [length]. lia.
      + rewrite Z.add_0_r.
        assert (Hc : i = 0 \/ i = 1) by lia. destruct Hc as [-> | ->]; cbn [Z.to_nat nth].
        * rewrite Z.add_0_r. apply (gs_mbyte_byte (w_H W3) (ms_mem ms3)); [exact HA0 | lia].
        * replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia.
          apply (gs_mbyte_byte (w_H W3) (ms_mem ms3)); [exact HA1 | lia]. }
  pose proof (gs_seatD W3 (ms_regs ms3) (ms_mem ms3) [w64 rws] 0 [Z_to_bv 8 bse; Z_to_bv 8 wdt] GP_sweep
     [YP09.mkRegion (Some 9%nat) 0 192 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 32 0))];
      YP09.mkRegion (Some 18%nat) 0 2 0 0 [YP09.mkChunk 0 (CData 0 0 2)]] []
     ltac:(vm_compute; reflexivity) Hrs ltac:(cbn; repeat split; unfold YP09.extent_disjoint;
       cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]; rewrite U9, U18; unfold GO_A; lia) I) as HS.
  rewrite <- Ems3 in HS.
  remember (Eimg (edset (Ereg (ms_regs ms3) [w64 rws]) 0 [Z_to_bv 8 bse; Z_to_bv 8 wdt])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn. rewrite HE. cbn [edset ew]. apply (ew_Eimg_Ereg_nat (ms_regs ms3) [w64 rws]). exact Hn. }
  clear HE.
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS R10 ltac:(vm_compute; reflexivity)) as HS1.
  clear HS. rename HS1 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
  assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly3 c p) by reflexivity.
  assert (E23 : ew E 23 = w64 bse) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = w64 wdt) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
  paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
  gs_rw_mem (ms_mem ms3).
  assert (UD : forall i (v : Z), 0 <= i -> nth_error (ed E 0) (Z.to_nat i) = Some (Z_to_bv 8 v) ->
    0 <= v < 256 -> U E (SData 0 i 1) = v).
  { intros i v Hi Hn Hv. rewrite (gs_U_data1 E i (Z_to_bv 8 v) Hi Hn).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    apply Z.mod_small. exact Hv. }
  (* 0x80e70: the base byte of `a` is the base the input named *)
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ne_U in Hc.
    rewrite (U_atom E 23 bse) in Hc by (first [exact E23 | lia]).
    rewrite (UD 0 bse ltac:(lia) ltac:(rewrite ED; reflexivity) ltac:(lia)) in Hc.
    rewrite Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc. paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
  gs_rw_mem (ms_mem ms3).
  (* 0x80e78: the width byte of `a` is the width the input named *)
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ne_U in Hc.
    rewrite (U_atom E 26 wdt) in Hc by (first [exact E26 | lia]).
    rewrite (UD 1 wdt ltac:(lia) ltac:(rewrite ED; reflexivity) ltac:(lia)) in Hc.
    rewrite Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc. paj_run_shc RUNP RUNC HS HJ.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
  gs_rw_mem (ms_mem ms3).
  (* 0x80e84: the rows the input named, or one row *)
  (* the malloc of the sweep buffer and the store into slot 64, from either path *)
  assert (CONT : forall (msc : machine_state) (mdc : Model),
    ms_mem msc = ms_mem ms3 ->
    ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 W3 (ms_mem msc) mdc k ->
    msc = mkst (ms_regs msc) (Z_to_bv 64 (pc_wrap_malloc (as_code B))) (ms_mem msc) (seg_rom SEGS) ->
    getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + 2016) ->
    getr (ms_regs msc) 2 = w64 (c_sp1 cx) -> getr (ms_regs msc) 3 = w64 (as_gp B) ->
    getr (ms_regs msc) 4 = w64 (as_tp B) -> getr (ms_regs msc) 8 = w64 (spZ (c_regs cx)) ->
    getr (ms_regs msc) 9 = w64 (c_sp1 cx) -> getr (ms_regs msc) 10 = w64 (sw_mbytes (c_pl cx)) ->
    getr (ms_regs msc) 18 = w64 (gF cx fp + GO_A) -> getr (ms_regs msc) 19 = w64 rws ->
    getr (ms_regs msc) 20 = w64 t -> getr (ms_regs msc) 22 = w64 (gSH cx fp) ->
    SRr SEGS W3 (mkCfg msc mdc) (ge_post B MT cx)).
  { intros msc mdc HMc HJc Emsc QRA QSP QGP QTP QS0 QS1 QA0 Q18 Q19 Q20 Q22.
    pose proof (gs_mbytes_range (c_pl cx)) as Hswr.
    assert (HBB : blocks_bytes S3 = blocks_bytes (c_S cx) + 460).
    { rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)), Hblk,
        bsum_app. cbn [bsum fold_right snd]. lia. }
    rewrite Emsc. eapply SRr_bind.
    { eapply (AMALLOC4 W3 (ms_regs msc) (ms_mem msc) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
        (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 mdc k (sw_mbytes (c_pl cx))
        (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2016)) (gch cx) HJc).
      - exact QA0.
      - unfold MALLOC_MAX. lia.
      - rewrite HBB. unfold GE_LIVE in Hlive. lia.
      - unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. lia.
      - pose proof (proj1 (Z.mod_divide (c_sp1 cx) 16 ltac:(lia)) Hsp1al16) as [q1 Hq1].
        pose proof (proj1 (Z.mod_divide (spZ (c_regs cx)) 16 ltac:(lia)) Hal16) as [q2 Hq2].
        rewrite Hq1, Hq2. replace (q1 * 16 - q2 * 16) with ((q1 - q2) * 16) by lia. apply Z_mod_mult.
      - lia.
      - lia.
      - exact QGP.
      - exact QTP.
      - exact QRA.
      - apply (ret_ok_codeptr_v 2016 ltac:(lia) ltac:(reflexivity)).
      - lia.
      - assert (Hrd : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
          aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
        { intros a Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; lia. }
        assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
          by (rewrite HMc; exact (proj1 HSAVED)).
        assert (H16 : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
        { rewrite HMc. pose proof (proj2 HSAVED 0 ltac:(lia)) as Hj0.
          replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
          cbn [Z.ltb Z.compare] in Hj0. exact Hj0. }
        pose proof (ge_achain B MT cx HB (aview SEGS (w_H W3) (ms_mem msc)) (c_sp1 cx) Hrd H8 H16 ltac:(lia)) as HCH.
        apply (achain_chain_pre ly3 (aview SEGS (w_H W3) (ms_mem msc)) (c_sp1 cx) (spZ (c_regs cx))
                 (gch cx) (ms_regs msc)).
        + exact (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop HCH).
        + unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. lia.
        + unfold s0Z. rewrite QS0. unfold w64. apply unsigned_lit_small. lia.
        + unfold raZ. rewrite QRA. rewrite unsigned_lit_small by lia. lia.
      - apply HTR. left. split; [reflexivity|].
        unfold raZ. rewrite QRA, unsigned_lit_small by lia.
        replace (BASE + 2016 - BASE) with 2016 by lia. unfold GE_MSITES. cbn [In]. auto.
      - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT (sw_mbytes (c_pl cx))) MTL HMOK HMO
          (mo_malloc_nonneg MT MTL (sw_mbytes (c_pl cx)) ltac:(lia))).
        pose proof (mo_malloc_mono MT MTL (sw_mbytes (c_pl cx)) 8670 ltac:(lia)) as Mm.
        pose proof (mo_malloc_nonneg MT MTL 460 ltac:(lia)) as M1.
        pose proof (mo_malloc_nonneg MT MTL 4352 ltac:(lia)) as M3.
        pose proof (mo_free_nonneg MT MTL) as M4.
        unfold GE_NEED, GE_A3, GE_A2, GE_A1 in *. lia. }
    cbv beta.
    intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfrs2 & Hres4096 & Eab2 & HK & HMLE).
    replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK by lia.
    (* the blocks after the malloc: the sweep buffer is the last one *)
    assert (Eab3 : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (res, sw_mbytes (c_pl cx))])
      by (rewrite Eab2, Hblk, <- app_assoc; reflexivity).
    pose proof HJ2 as (HAR2 & Hly2 & _).
    assert (Hnotin : ~ In (res, sw_mbytes (c_pl cx)) (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)]))
      by exact (gs_blocks_tail B ly2 S2 W2 mem2 md2 (ablocks B (c_ly cx) (c_S cx)) (t, 460)
                  (res, sw_mbytes (c_pl cx)) LAWS HAR2 ltac:(cbn [snd]; lia) Eab3).
    assert (HtIn2 : In (t, 460) (ablocks B ly2 S2))
      by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
    assert (HrIn2 : In (res, sw_mbytes (c_pl cx)) (ablocks B ly2 S2))
      by (rewrite Eab3; apply in_or_app; right; right; left; reflexivity).
    destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly2 HAR0 Hly2)
      as (_ & Efa2 & _).
    assert (EFA2 : frame_addr ly2 GE_CID fp = gF cx fp) by (unfold gF; rewrite Efa2; reflexivity).
    assert (GEO : gs_geo cx fp t res (sw_mbytes (c_pl cx))).
    { apply (gs_geo_of B cx fp t res (sw_mbytes (c_pl cx)) ly2 S2 W2 mem2 md2 LAWS HAR2 HtIn2
        ltac:(intros Heq; apply Hnotin; apply in_or_app; right; left; exact Heq)).
      - intros Hn. assert (Hin : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))
          by (destruct Hpn as [(Hz & _) | (_ & H)]; [lia | exact H]).
        split; [rewrite Eab3; apply in_or_app; left; exact Hin|].
        intros Heq. apply Hnotin. apply in_or_app. left. rewrite <- Heq. exact Hin.
      - exact HrIn2.
      - rewrite Hfrs2, HFR. left. reflexivity.
      - exact EFA2.
      - exact Hsp1lo.
      - exact Hsp1hi. }
    assert (KEEP : gs_keepW cx fp t W3 W2 (ms_mem ms3) mem2).
    { rewrite <- HMc.
      apply (gs_keep_of_call B cx fp t res (sw_mbytes (c_pl cx)) ly3 S3 W3 (ms_mem msc) W2 mem2
        (fun a => res <= a < res + req_size (sw_mbytes (c_pl cx))) HK ltac:(intros a Ha; exact Ha)
        HtIn HpIn HFR EFA GEO). }
    (* 0x80e90: the sweep buffer is not null; 0x80e94 stores it in slot 64 *)
    assert (Q9b : getr regs2 9 = w64 (c_sp1 cx)).
    { rewrite (gs_kept_reg (ms_regs msc) regs2 (9%bv : bv 5) HP2
        ltac:(assert (HX : bv_unsigned (9%bv : bv 5) = 9) by (vm_compute; reflexivity);
              unfold acallee_saved; rewrite HX; lia)). exact QS1. }
    assert (U9b : bv_unsigned (ew (Eimg (Ereg regs2 [])) 9%nat) = c_sp1 cx).
    { rewrite (ew_Eimg_Ereg_nat regs2 [] 9%nat 9%bv eq_refl), Q9b. apply unsigned_lit_small. lia. }
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    assert (Hrs2 : Forall (YP09.region_ok SEGS (Eimg (Ereg regs2 [])) (mrestrict (w_H W2) mem2))
                     [YP09.mkRegion (Some 9%nat) 0 192 64 72 []]).
    { apply Forall_cons; [|apply Forall_nil].
      apply (gs_slotreg_ok W2 _ mem2 [] (c_sp1 cx) 64 72 U9b ltac:(lia) ltac:(lia)); [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres2. lia. }
    pose proof (gs_seat W2 regs2 mem2 [] 2016 [YP09.mkRegion (Some 9%nat) 0 192 64 72 []] []
       ltac:(vm_compute; reflexivity) Hrs2 ltac:(cbn; tauto) I) as HS2.
    remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
    assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
    assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
      by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
    clear HE2.
    clear HEI. rename HEI2 into HEI.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (sw_mbytes (c_pl cx)) HAR2 HrIn2)
      as (_ & _ & Hresc & _).
    pose proof (req_size_pos (sw_mbytes (c_pl cx)) ltac:(lia)) as [Hrq1 Hrq2].
    psrr_branch_pi RUNP BR HS2.
    { exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
      rewrite (U_atom E2 10 res) in Hc by (first [rewrite (EE2 10%nat 10%bv eq_refl); exact Hres | lia]).
      rewrite U_lit in Hc by lia. lia. }
    clear Hc.
    paj_run_to_sh RUNTOP HS2 HJ2 GPS_mal.
    { intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha. rewrite U9b in Ha.
      left. lia. }
    (* every byte outside the window the store wrote is the one the call left *)
    lazymatch type of HJ2 with context [ms_mem ?m] => rename m into msF end.
    assert (HOUT : forall x, 0 <= x < 2 ^ 64 -> ~ (c_sp1 cx + 64 <= x < c_sp1 cx + 72) ->
      aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W2) mem2 x).
    { intros x Hx Hnx. apply (aview_eq_of SEGS (w_H W2)). apply HFr.
      intros (r & Hin & Hr). cbn in Hin. destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr. rewrite U9b in Hr.
      rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      rewrite Z.mod_small in Hr by lia. lia. }
    clear HF HFr HG.
    assert (HKC : forall x, (gs_keep_at cx fp t x /\ 0 <= x < 2 ^ 64 /\ ~ (c_sp1 cx + 64 <= x < c_sp1 cx + 72)) ->
      aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W3) (ms_mem ms3) x).
    { intros x (Hk1 & Hk2 & Hk3). rewrite (HOUT x Hk2 Hk3). exact (KEEP x Hk1). }
    assert (SLK : forall off v, 0 <= off -> off + 8 <= 64 \/ 72 <= off -> off + 8 <= 192 ->
      gslot cx W3 ms3 off v -> gslot cx W2 msF off v).
    { intros off v H0 H1 H2 Hv. unfold gslot in *.
      apply (gs_word_out W3 W2 (ms_mem ms3) (ms_mem msF) _ (c_sp1 cx + off) v HKC); [|exact Hv].
      intros i Hi. gs_pk. }
    (* the slot the store wrote *)
    assert (SL64n : gslot cx W2 msF 64 res).
    { unfold gslot. apply (rdword_of_val_mem SEGS (w_H W2) (ms_mem msF)); [|lia].
      apply (field_of_region E2 (mrestrict (w_H W2) (ms_mem msF)) 9%nat (c_sp1 cx) _ 0 192 64 72 64 8%N
        (SOff 10 0) res (st_ok_pi_region_nth E2 _ _ 0%nat _ HS2 eq_refl) U9b).
      - cbn [In]. left. reflexivity.
      - rewrite ge_sv_SOff0, (EE2 10%nat 10%bv eq_refl). exact Hres.
      - cbn [Z.of_N]. change (8 * 8) with 64. lia.
      - cbn [Z.of_N]. lia. }
    (* the registers of the cut *)
    assert (F2 : getr (ms_regs msF) 2 = w64 (c_sp1 cx)).
    { prreg HS2 (2%bv : bv 5) RR. rewrite RR, (EE2 2%nat 2%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (2%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (2%bv : bv 5) = 2) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact QSP. }
    assert (F3 : getr (ms_regs msF) 3 = w64 (as_gp B)).
    { prreg HS2 (3%bv : bv 5) RR. rewrite RR, (EE2 3%nat 3%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (3%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (3%bv : bv 5) = 3) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact QGP. }
    assert (F4 : getr (ms_regs msF) 4 = w64 (as_tp B)).
    { prreg HS2 (4%bv : bv 5) RR. rewrite RR, (EE2 4%nat 4%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (4%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (4%bv : bv 5) = 4) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact QTP. }
    assert (F8 : getr (ms_regs msF) 8 = w64 (spZ (c_regs cx))).
    { prreg HS2 (8%bv : bv 5) RR. rewrite RR, (EE2 8%nat 8%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (8%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (8%bv : bv 5) = 8) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact QS0. }
    assert (F9 : getr (ms_regs msF) 9 = w64 (c_sp1 cx)).
    { prreg HS2 (9%bv : bv 5) RR. rewrite RR, (EE2 9%nat 9%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (9%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (9%bv : bv 5) = 9) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact QS1. }
    assert (F18 : getr (ms_regs msF) 18 = w64 (gF cx fp + GO_A)).
    { prreg HS2 (18%bv : bv 5) RR. rewrite RR, (EE2 18%nat 18%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (18%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (18%bv : bv 5) = 18) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact Q18. }
    assert (F19 : getr (ms_regs msF) 19 = w64 rws).
    { prreg HS2 (19%bv : bv 5) RR. rewrite RR, (EE2 19%nat 19%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (19%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (19%bv : bv 5) = 19) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact Q19. }
    assert (F20 : getr (ms_regs msF) 20 = w64 t).
    { prreg HS2 (20%bv : bv 5) RR. rewrite RR, (EE2 20%nat 20%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (20%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (20%bv : bv 5) = 20) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact Q20. }
    assert (F22 : getr (ms_regs msF) 22 = w64 (gSH cx fp)).
    { prreg HS2 (22%bv : bv 5) RR. rewrite RR, (EE2 22%nat 22%bv eq_refl),
        (gs_kept_reg (ms_regs msc) regs2 (22%bv : bv 5) HP2
          ltac:(assert (HX : bv_unsigned (22%bv : bv 5) = 22) by (vm_compute; reflexivity);
                unfold acallee_saved; rewrite HX; lia)).
      exact Q22. }
    assert (F10 : getr (ms_regs msF) 10 = w64 res)
      by (prreg HS2 (10%bv : bv 5) RR; rewrite RR, (EE2 10%nat 10%bv eq_refl); exact Hres).
    pose proof HS2 as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
    cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
      in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
    destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & HwsL & HstL & _).
    pose proof (mo_malloc_mono MT MTL (sw_mbytes (c_pl cx)) 8670 ltac:(lia)) as Mm.
    apply (HMAL cx fp (k + 1) (acc + mo_malloc MT (sw_mbytes (c_pl cx))) ly2 S2 W2 msF).
    - exact HB.
    - exact HJ2.
    - rewrite Hfrs2. exact HFR.
    - exact (mle_station MT (c_S cx) S3 S2 acc _ MTL HMO HMLE).
    - exists t, res.
      split.
      { apply (gs_body_out cx fp GP_sweep GPS_mal _ W3 W2 ms3 msF GSH_a HKC).
        - intros a Ha. gs_pk.
        - intros i Hi. unfold GE_NSH in Hi. cbn [Z.of_nat] in Hi. gs_pk.
        - intros i Hi. rewrite Hfb in Hi. gs_pk.
        - intros i Hi. gs_pk.
        - exact Hpcv0.
        - exact Hresv0.
        - exact Hpend0.
        - exact Hrom0.
        - exact Hfrg0.
        - exact Hfcsr0.
        - unfold gregs. split; [exact F2|]. split; [exact F8|]. split; [exact F9|].
          rewrite F3, F4. split; [symmetry; exact Hgp | symmetry; exact Htp].
        - exact HBODY. }
      split; [lia|].
      split; [unfold GE_A2, GE_A1 in *; lia|].
      split.
      { split; [exact Eab3|]. split; [exact HrIn2|].
        split.
        { destruct HTAB as (_ & Ht0 & Hlen & Hbytes).
          split; [exact HtIn2|]. split; [exact Ht0|]. split; [exact Hlen|].
          intros i Hi H1 H2 H3. rewrite (HKC (t + i) ltac:(gs_pk)). exact (Hbytes i Hi H1 H2 H3). }
        split.
        { unfold gfarr in *. apply (gs_garr_out W3 W2 (ms_mem ms3) (ms_mem msF) _ _ _ HKC); [|exact HWAS].
          intros j Hj. rewrite HwsL in Hj. unfold GO_WAS. gs_pk. }
        split.
        { unfold gfarr in *. apply (gs_garr_out W3 W2 (ms_mem ms3) (ms_mem msF) _ _ _ HKC); [|exact HSET].
          intros j Hj. rewrite HstL in Hj. unfold GO_SET. gs_pk. }
        split; [exact HREL|]. split; [exact HI1|].
        split.
        { destruct SLATE as (SMID & S8 & S32 & S40 & S72 & S80 & S104 & S112 & S128).
          destruct SMID as (S16 & S24 & S48 & S56 & S136 & S144 & S152 & S176).
          split; [split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]|];
            [ apply (SLK 16) | apply (SLK 24) | apply (SLK 48) | apply (SLK 56) | apply (SLK 136)
            | apply (SLK 144) | apply (SLK 152) | apply (SLK 176) | ];
            try (first [lia | assumption]).
          split; [apply (SLK 8); first [lia | assumption]|].
          split; [apply (SLK 32); first [lia | assumption]|].
          split; [apply (SLK 40); first [lia | assumption]|].
          split; [apply (SLK 72); first [lia | assumption]|].
          split; [apply (SLK 80); first [lia | assumption]|].
          split; [apply (SLK 104); first [lia | assumption]|].
          split; [apply (SLK 112); first [lia | assumption]|].
          apply (SLK 128); first [lia | assumption]. }
        split; [apply (SLK 88); first [lia | assumption]|].
        split; [apply (SLK 120); first [lia | assumption]|].
        split; [apply (SLK 96); first [lia | assumption]|].
        split; [exact SL64n|].
        split; [exact F20|]. split; [exact Hn26|]. split; [lia|]. split; [lia|].
        rewrite Hok. split.
        - unfold gfb in *. rewrite (HKC (gF cx fp + GO_A) ltac:(unfold GO_A; gs_pk)). exact HA0.
        - unfold gfb in *. rewrite (HKC (gF cx fp + (GO_A + 1)) ltac:(unfold GO_A; gs_pk)). exact HA1. }
      split; [exact Hok|].
      split; [exact F10|]. split; [exact F19|]. split; [exact F18 | exact F22]. }
  psrr_branch_pi RUNP BR HS.
  + assert (Hr0 : rws = 0).
    { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
      rewrite (U_atom E 32 rws) in Hc by (first [exact E32 | lia]).
      rewrite U_lit in Hc by lia. lia. }
    clear Hc. paj_run_shc RUNP RUNC HS HJ.
    { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
    gs_rw_mem (ms_mem ms3).
    pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Emsc. cbn [ss_pc setpc] in Emsc.
    rewrite (pal_malloc B TL) in Emsc.
    lazymatch type of HM with ms_mem ?mc = _ =>
      apply (CONT mc _ HM HJ Emsc) end.
    * prreg HS (1%bv : bv 5) RR. exact RR.
    * prreg HS (2%bv : bv 5) RR. rewrite RR, (EE 2%nat 2%bv eq_refl). exact G2.
    * prreg HS (3%bv : bv 5) RR. rewrite RR, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
    * prreg HS (4%bv : bv 5) RR. rewrite RR, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
    * prreg HS (8%bv : bv 5) RR. rewrite RR, (EE 8%nat 8%bv eq_refl). exact G8.
    * prreg HS (9%bv : bv 5) RR. rewrite RR, (EE 9%nat 9%bv eq_refl). exact G9.
    * prreg HS (10%bv : bv 5) RR. rewrite RR. unfold sw_mbytes. fold rws. rewrite Hr0. reflexivity.
    * prreg HS (18%bv : bv 5) RR. rewrite RR, (EE 18%nat 18%bv eq_refl). exact R18.
    * prreg HS (19%bv : bv 5) RR. rewrite RR. exact E32.
    * prreg HS (20%bv : bv 5) RR. rewrite RR, (EE 20%nat 20%bv eq_refl). exact R20.
    * prreg HS (22%bv : bv 5) RR. rewrite RR, (EE 22%nat 22%bv eq_refl). exact R22.
  + assert (Hrne : rws <> 0).
    { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
      rewrite (U_atom E 32 rws) in Hc by (first [exact E32 | lia]).
      rewrite U_lit in Hc by lia. lia. }
    clear Hc. paj_run_shc RUNP RUNC HS HJ.
    { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
    gs_rw_mem (ms_mem ms3).
    pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Emsc. cbn [ss_pc setpc] in Emsc.
    rewrite (pal_malloc B TL) in Emsc.
    lazymatch type of HM with ms_mem ?mc = _ =>
      apply (CONT mc _ HM HJ Emsc) end.
    * prreg HS (1%bv : bv 5) RR. exact RR.
    * prreg HS (2%bv : bv 5) RR. rewrite RR, (EE 2%nat 2%bv eq_refl). exact G2.
    * prreg HS (3%bv : bv 5) RR. rewrite RR, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
    * prreg HS (4%bv : bv 5) RR. rewrite RR, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
    * prreg HS (8%bv : bv 5) RR. rewrite RR, (EE 8%nat 8%bv eq_refl). exact G8.
    * prreg HS (9%bv : bv 5) RR. rewrite RR, (EE 9%nat 9%bv eq_refl). exact G9.
    * prreg HS (10%bv : bv 5) RR. rewrite RR, E32. apply bv_eq.
      cbn [mul_div]. rewrite bv_mul_unsigned. unfold w64.
      unfold sw_mbytes. fold rws. rewrite (proj2 (Z.ltb_lt 0 rws)) by lia.
      rewrite !unsigned_lit_small by lia.
      rewrite (Z.mul_comm rws 34). apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
    * prreg HS (18%bv : bv 5) RR. rewrite RR, (EE 18%nat 18%bv eq_refl). exact R18.
    * prreg HS (19%bv : bv 5) RR. rewrite RR. exact E32.
    * prreg HS (20%bv : bv 5) RR. rewrite RR, (EE 20%nat 20%bv eq_refl). exact R20.
    * prreg HS (22%bv : bv 5) RR. rewrite RR, (EE 22%nat 22%bv eq_refl). exact R22.
- (* the box was refused: both bytes of `a` are 0 and the walk reaches 0x812ac *)
  destruct HAB as (HA0 & HA1).
  assert (U18 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) [])) 18%nat) = gF cx fp + GO_A).
  { rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 18%nat 18%bv eq_refl), R18.
    apply unsigned_lit_small. unfold GO_A. lia. }
  assert (Hrs : Forall (YP09.region_ok SEGS (Eimg (Ereg (ms_regs ms3) []))
                  (mrestrict (w_H W3) (ms_mem ms3))) [gss_a_region 0 0]).
  { apply Forall_cons; [|apply Forall_nil]. unfold gss_a_region, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U18. split; [unfold GO_A; lia|]. split; [unfold GO_A; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (gs_fb_chunk W3 _ (ms_mem ms3) 0 0 (gF cx fp + GO_A)).
      rewrite Z.add_0_r. exact HA0.
    - apply (gs_fb_chunk W3 _ (ms_mem ms3) 1 0 (gF cx fp + GO_A)).
      replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia. exact HA1. }
  pose proof (gs_seat W3 (ms_regs ms3) (ms_mem ms3) [] GP_sweep [gss_a_region 0 0] []
     ltac:(vm_compute; reflexivity) Hrs ltac:(cbn; tauto) I) as HS.
  rewrite <- Ems3 in HS.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
  clear HE.
  (* the answer is -1, so the test at 0x80e5c falls through to the refused path *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) (-1) HS R10 ltac:(vm_compute; reflexivity)) as HS1.
  clear HS. rename HS1 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
  assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly3 c p) by reflexivity.
  paj_run_to_sh RUNTOP HS HJ GP_raw.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end.
  clear HF HFr HG.
  assert (KEEP : gs_keepW cx fp t W3 W3 (ms_mem ms3) (ms_mem ms))
    by (rewrite HM; apply gs_keepW_refl).
  pose proof HS as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
  cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
    in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
  assert (Q2 : getr (ms_regs ms) 2 = w64 (c_sp1 cx))
    by (prreg HS (2%bv : bv 5) RR; rewrite RR, (EE 2%nat 2%bv eq_refl); exact G2).
  assert (Q8 : getr (ms_regs ms) 8 = w64 (spZ (c_regs cx)))
    by (prreg HS (8%bv : bv 5) RR; rewrite RR, (EE 8%nat 8%bv eq_refl); exact G8).
  assert (Q9 : getr (ms_regs ms) 9 = w64 (c_sp1 cx))
    by (prreg HS (9%bv : bv 5) RR; rewrite RR, (EE 9%nat 9%bv eq_refl); exact G9).
  assert (Q3 : getr (ms_regs ms) 3 = getr (c_regs cx) 3)
    by (prreg HS (3%bv : bv 5) RR; rewrite RR, (EE 3%nat 3%bv eq_refl); exact G3).
  assert (Q4 : getr (ms_regs ms) 4 = getr (c_regs cx) 4)
    by (prreg HS (4%bv : bv 5) RR; rewrite RR, (EE 4%nat 4%bv eq_refl); exact G4).
  assert (Q20 : getr (ms_regs ms) 20 = w64 t)
    by (prreg HS (20%bv : bv 5) RR; rewrite RR, (EE 20%nat 20%bv eq_refl); exact R20).
  assert (Q21 : getr (ms_regs ms) 21 = w64 SHADOW_OFF)
    by (prreg HS (21%bv : bv 5) RR; rewrite RR, (EE 21%nat 21%bv eq_refl); exact R21).
  assert (Q22 : getr (ms_regs ms) 22 = w64 (gSH cx fp))
    by (prreg HS (22%bv : bv 5) RR; rewrite RR, (EE 22%nat 22%bv eq_refl); exact R22).
  assert (Q24 : getr (ms_regs ms) 24 = w64 (c_n cx - Z.of_nat (pos_end (c_pl cx))))
    by (prreg HS (24%bv : bv 5) RR; rewrite RR, (EE 24%nat 24%bv eq_refl); exact R24).
  assert (Q25 : getr (ms_regs ms) 25 = w64 (gF cx fp + GO_RAW))
    by (prreg HS (25%bv : bv 5) RR; rewrite RR, (EE 25%nat 25%bv eq_refl); exact R25).
  destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & HwsL & HstL & _).
  pose proof (mo_malloc_nonneg MT MTL 8670 ltac:(lia)) as M2.
  pose proof (mo_free_nonneg MT MTL) as M4.
  apply (HRAW cx fp k acc ly3 S3 W3 ms).
  + exact HB.
  + exact HJ.
  + exact HFR.
  + exact HMO.
  + exists t.
    split.
    { apply (gs_keep_body cx fp t GP_sweep GP_raw W3 W3 ms3 ms GSH_a KEEP ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(lia) Hpcv0 Hresv0 Hpend0 Hrom0 Hfrg0 Hfcsr0
        ltac:(unfold gregs; split; [exact Q2|]; split; [exact Q8|]; split; [exact Q9|];
              split; [exact Q3 | exact Q4]) HBODY). }
    split; [lia|]. split; [unfold GE_A2, GE_A1 in *; lia|].
    split; [exact Hblk|]. split; [exact Hn26|].
    split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|]. split; [exact Q24|]. split; [exact Q25|].
    split.
    { apply (gs_keep_gslot cx fp t W3 W3 ms3 ms 88 (c_p cx + Z.of_nat (pos_end (c_pl cx))) KEEP
        ltac:(lia) ltac:(lia) SL88). }
    split.
    { apply (gs_keep_gslot cx fp t W3 W3 ms3 ms 96 (gF cx fp + GO_LIT) KEEP ltac:(lia) ltac:(lia) SL96). }
    split.
    { apply (gs_keep_gslots_late cx fp t W3 W3 ms3 ms KEEP ltac:(lia) SLATE). }
    split.
    { apply (gs_keep_gtab B cx fp ly3 S3 W3 W3 ms3 ms t (T_end (c_pl cx)) KEEP HTAB). }
    split.
    { apply (gs_keep_gfarr cx fp t W3 W3 ms3 ms GO_WAS (ws_end (c_pl cx)) KEEP ltac:(unfold GO_WAS; lia)
        ltac:(rewrite HwsL; unfold GO_WAS; lia) HWAS). }
    split.
    { apply (gs_keep_gfarr cx fp t W3 W3 ms3 ms GO_SET (st_end (c_pl cx)) KEEP ltac:(unfold GO_SET; lia)
        ltac:(rewrite HstL; unfold GO_SET; lia) HSET). }
    split; [exact HREL | exact HI1].
Qed.

End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

Lemma gsw_seg_sweep : forall (B : asyms) (MT : ameter_ops), @SEG_sweep fx rc SK PI B MT.
Proof.
intros B MT RT NMAL NRAW.
destruct RT as (LAWS & TL & MTL & MTF & AMALLOC4 & AFREE4 & AFREEN4 & ABCMP & HIMG & ML & TLF).
exact (gs_sweep B MT LAWS TL MTL AMALLOC4 NMAL NRAW).
Qed.

End zb.
End z.
