(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel DeflFastModel DeflSlowModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6 FillWin6D Lmatch6_run
  DeflSlow6_1 DeflSlow6_2 DeflSlow6_3 DeflSlow6_4 DeflSlow6_5 DeflSlow6_6 DeflSlow6_7 DeflSlow6_8 DeflSlow6_M.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Section Walk.

Lemma keeps_wrap6 : keeps ds_wrap true true.
Proof using. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma tfb_wrap6 : forall s buf len last, ds_wrap (tr_flush_block s buf len last) = ds_wrap s.
Proof using. intros. rewrite (k_tr_flush_block ds_wrap keeps_wrap6). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.
Lemma tfbits_wrap6 : forall s, ds_wrap (tr_flush_bits s) = ds_wrap s.
Proof using. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; [reflexivity| |]; destruct s; reflexivity. Qed.
Lemma tfbits_strm6 : forall s, ds_strm (tr_flush_bits s) = ds_strm s.
Proof using. intros s. pose proof (tr_flush_bits_nobits s) as E0. unfold ds_nobits in E0. congruence. Qed.
Lemma fptail_wrap6 : forall s n, ds_wrap (fp_tail s n) = ds_wrap s.
Proof using. intros. unfold fp_tail. destruct (_ =? 0); destruct s; reflexivity. Qed.
Lemma fptail_pending6 : forall s n, ds_pending (fp_tail s n) = ds_pending s - n.
Proof using. intros. unfold fp_tail. destruct (_ =? 0); destruct s; reflexivity. Qed.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp : Z).
Variable FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop.
Hypothesis MEMCPY : memcpy_run6.
Hypothesis MEMSET : memset_run6.
Hypothesis ADLER : adler32_run6 ROM.
Hypothesis TFBITS : tr_flush_bits_run6.
Hypothesis TFB : tr_flush_block_run6 FBSAFE.
Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation OUTB := (zp_out zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation lbs := (ds_lit_bufsize ds).
Local Abbreviation PBL := (ds_lit_bufsize ds * 4).
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DSH ROM mem S p zp ds flush ra sp.
Local Abbreviation DI := (DeflSlow6_1.DI ROM mem S p zp ds sp).
Local Abbreviation HREGS := (DeflSlow6_1.HREGS S sp).
Local Abbreviation TREGS := (DeflSlow6_7.TREGS S sp).
Local Abbreviation LOC := (DeflSlow6_2.LOC4 sp).
Local Abbreviation FPR := (DeflSlow6_6.FPR S p).
Local Abbreviation flush_ok := (flush_ok6 FBSAFE).

Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ HH.

Definition KEEP (regs0 R : bvmap 5 word) : Prop := getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\ getr R 9 = getr regs0 9.

Lemma KEEP_via : forall regs0 R R' L,
  KEEP regs0 R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  reg_in 3%bv L = false -> reg_in 4%bv L = false -> reg_in 9%bv L = false -> KEEP regs0 R'.
Proof using.
  intros regs0 R R' L (A3 & A4 & A9) Hfr E3 E4 E9. unfold KEEP. rewrite (Hfr _ E3), (Hfr _ E4), (Hfr _ E9). repeat split; assumption.
Qed.

Local Ltac keep_via HK Hfr := apply (KEEP_via _ _ _ _ HK Hfr); reflexivity.
Definition KEEP3 (regs0 R : bvmap 5 word) : Prop := getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4.
Lemma KEEP_3 : forall regs0 R, KEEP regs0 R -> KEEP3 regs0 R. Proof using. intros regs0 R (A & B & _); split; assumption. Qed.
Lemma KEEP3_via : forall regs0 R R' L,
  KEEP3 regs0 R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  reg_in 3%bv L = false -> reg_in 4%bv L = false -> KEEP3 regs0 R'.
Proof using. intros regs0 R R' L (A3 & A4) Hfr E3 E4. unfold KEEP3. rewrite (Hfr _ E3), (Hfr _ E4). split; assumption. Qed.
Local Ltac keep3_via HK Hfr := apply (KEEP3_via _ _ _ _ HK Hfr); reflexivity.
Lemma KEEP_fb : forall regs0 R R', KEEP regs0 R -> (forall r : reg, reg_in r FB_CLOB = false -> getr R' r = getr R r) -> KEEP regs0 R'. Proof using. intros regs0 R R' HK Hfr; keep_via HK Hfr. Qed.
Lemma KEEP_mc : forall regs0 R R', KEEP regs0 R -> (forall r : reg, reg_in r memcpy_clob = false -> getr R' r = getr R r) -> KEEP regs0 R'. Proof using. intros regs0 R R' HK Hfr; keep_via HK Hfr. Qed.
Lemma KEEP3_fb : forall regs0 R R', KEEP3 regs0 R -> (forall r : reg, reg_in r FB_CLOB = false -> getr R' r = getr R r) -> KEEP3 regs0 R'. Proof using. intros regs0 R R' HK Hfr; keep3_via HK Hfr. Qed.
Lemma KEEP3_mc : forall regs0 R R', KEEP3 regs0 R -> (forall r : reg, reg_in r memcpy_clob = false -> getr R' r = getr R r) -> KEEP3 regs0 R'. Proof using. intros regs0 R R' HK Hfr; keep3_via HK Hfr. Qed.
Local Ltac hregs_via HRG Hfr := apply (DeflSlow6_1.HREGS_via S sp _ _ _ HRG Hfr); reflexivity.
Local Ltac tregs_via HRG Hfr := apply (DeflSlow6_7.TREGS_via S sp _ _ _ HRG Hfr); reflexivity.
Local Ltac retok := apply ret_ok_even; reflexivity.
Local Ltac via1 Hfr := lazymatch goal with |- getr _ ?r = _ => rewrite (Hfr r eq_refl) end.

Lemma avail_bound : forall m1 m X, DI m1 m X -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32.
Proof using HWF HH ra flush.
  intros m1 m X (_ & (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Eout & Hao & Hol)) & _).
  pose proof (wf_ao _ HWF). lia.
Qed.

Lemma di_sizes : forall m1 m X, DI m1 m X -> ds_w_size X = ws /\ ds_hash_size X = hs /\ ds_lit_bufsize X = lbs.
Proof using. intros m1 m X (_ & _ & HS3). exact HS3. Qed.

Lemma LOC_keep : forall m1 m X, LOC m1 -> DI m1 m X -> LOC m.
Proof using HH ra. intros m1 m X HL HDI. exact (LOC4_DI _ _ _ _ _ _ _ _ _ HH m1 m X HL HDI). Qed.



Section FPSeq.
  Variables (KP : bvmap 5 word -> bvmap 5 word -> Prop) (RP : bvmap 5 word -> Prop) (rs rS rl1 rl2 : reg) (PCB PCC PCD PCE : word) (regs0 : bvmap 5 word).
  Hypothesis KP_fb : forall regs0 R R', KP regs0 R -> (forall r : reg, reg_in r FB_CLOB = false -> getr R' r = getr R r) -> KP regs0 R'.
  Hypothesis KP_mc : forall regs0 R R', KP regs0 R -> (forall r : reg, reg_in r memcpy_clob = false -> getr R' r = getr R r) -> KP regs0 R'.
  Hypothesis RP_fb : forall R R', RP R -> (forall r : reg, reg_in r FB_CLOB = false -> getr R' r = getr R r) -> RP R'.
  Hypothesis RP_mc : forall R R', RP R -> (forall r : reg, reg_in r memcpy_clob = false -> getr R' r = getr R r) -> RP R'.
  Hypothesis Hrs1 : reg_in rs FB_CLOB = false.
  Hypothesis Hrs2 : reg_in rs memcpy_clob = false.
  Hypothesis HrS1 : reg_in rS FB_CLOB = false.
  Hypothesis HrS2 : reg_in rS memcpy_clob = false.
  Hypothesis Hrl1 : reg_in rl1 memcpy_clob = false.
  Hypothesis Hrl2 : reg_in rl2 memcpy_clob = false.
  Hypothesis B_blk : forall regs m1 m X,
    DI m1 m X -> RP regs -> KP regs0 regs -> 0 <= ds_strstart X <= 2 * ws ->
    exists R M,
      msteps s6_segs (mkst regs PCB m s6_rom) (mkst R (0x1ad94 : word) M s6_rom)
      /\ DI m1 M (set_block_start X (ds_strstart X))
      /\ RP R /\ KP regs0 R /\ FPR rs rS R /\ getr R 10 = zw S /\ getr R 1 = PCC.
  Hypothesis C_blk : forall regs m1 m X,
    DI m1 m X -> RP regs -> KP regs0 regs -> FPR rs rS regs ->
    0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 -> 0 <= ds_pending_out X <= PBL ->
    exists R,
      msteps s6_segs (mkst regs PCC m s6_rom) (mkst R (DeflSlow6_6.fpa_pc X PCE (0x27800 : word)) m s6_rom)
      /\ RP R /\ KP regs0 R /\ FPR rs rS R
      /\ (fp_len X <> 0 ->
          getr R 10 = zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X)))) /\ getr R 11 = zw (PB + ds_pending_out X)
          /\ getr R 12 = zw (fp_len X) /\ getr R rl1 = zw (fp_len X) /\ getr R rl2 = zw (fp_len X) /\ getr R 1 = PCD).
  Hypothesis D_blk : forall regs m1 M0 X len,
    DI m1 M0 X -> RP regs -> KP regs0 regs -> FPR rs rS regs -> getr regs rl1 = zw len -> getr regs rl2 = zw len ->
    0 < len <= ds_pending X -> ds_pending X < 2 ^ 31 -> len <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
    0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> 0 <= cs_total_out (ds_strm X) < 2 ^ 64 ->
    exists R,
      msteps s6_segs (mkst regs PCD M0 s6_rom) (mkst R PCE (DeflSlow6_6.fp_tower S p zp M0 X len) s6_rom)
      /\ RP R /\ KP regs0 R.
  Hypothesis PCC_ok : ret_ok PCC.
  Hypothesis PCD_ok : ret_ok PCD.

  Lemma fp_seq : forall regs m1 m X8,
    DI m1 m X8 -> RP regs -> KP regs0 regs ->
    0 <= ds_strstart X8 <= 2 * ws ->
    (let X9 := set_block_start X8 (ds_strstart X8) in
     BINV PBL X9 /\ ds_pending (tr_flush_bits X9) <= PBL
     /\ let X10 := tr_flush_bits X9 in
        0 <= ds_pending X10 < 2 ^ 31 /\ 0 <= ds_pending_out X10 /\ ds_pending_out X10 + fp_len X10 <= PBL
        /\ 0 <= cs_total_out (ds_strm X10) < 2 ^ 64) ->
    exists R M,
      msteps s6_segs (mkst regs PCB m s6_rom) (mkst R PCE M s6_rom)
      /\ DI m1 M (let X10 := tr_flush_bits (set_block_start X8 (ds_strstart X8)) in
                  if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10))
      /\ RP R /\ KP regs0 R.
  Proof using KP_mc KP_fb PCD_ok PCC_ok D_blk C_blk B_blk Hrl2 Hrl1 HrS2 HrS1 Hrs2 Hrs1 RP_mc RP_fb PCD PCC rl2 rl1 rS rs HWF HH TFBITS MEMCPY ra flush.
    intros regs m1 m X8 HDI8 HRG2 HK2 Hstr8 (HBI9 & Hroom & Hp10 & Hpo10 & Hpl10 & Htot10).
    pose proof (wf_lbs _ HWF) as Wlbs.
    destruct (B_blk regs m1 m X8 HDI8 HRG2 HK2 Hstr8) as (R3 & m3 & Hms3 & HDI3 & HRG3 & HK3 & F3 & B10 & B1).
    destruct (call_bits _ _ _ _ _ _ _ _ _ TFBITS HH R3 m1 m3 (set_block_start X8 (ds_strstart X8)) PCC HDI3 PCC_ok HBI9 Hroom B10 B1)
      as (R4 & m4 & Hms4 & HDI4 & Hfr4).
    assert (HK4 : KP regs0 R4) by (exact (KP_fb _ _ _ HK3 Hfr4)).
    revert Hroom Hp10 Hpo10 Hpl10 Htot10 HDI4. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))).
    intros X10 Hroom Hp10 Hpo10 Hpl10 Htot10 HDI4.
    assert (HRG4 : RP R4) by (exact (RP_fb _ _ HRG3 Hfr4)).
    assert (F4 : FPR rs rS R4).
    { destruct F3 as [F3a F3b]. split; [rewrite (Hfr4 rs Hrs1); exact F3a | rewrite (Hfr4 rS HrS1); exact F3b]. }
    pose proof (avail_bound _ _ _ HDI4) as Hav10.
    destruct (DeflSlow6_6.fp_len_eq X10 ltac:(lia) ltac:(lia)) as (_ & Hfl1 & Hfl2).
    destruct (C_blk R4 m1 m4 X10 HDI4 HRG4 HK4 F4 Hp10 Hav10 ltac:(lia)) as (R5 & Hms5 & HRG5 & HK5 & F5 & Hcopy).
    assert (MID : exists R6 m6,
              msteps s6_segs (mkst R5 (DeflSlow6_6.fpa_pc X10 PCE (0x27800 : word)) m4 s6_rom) (mkst R6 PCE m6 s6_rom)
              /\ DI m1 m6 (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10))
              /\ RP R6 /\ KP regs0 R6).
    { unfold DeflSlow6_6.fpa_pc. destruct (Z.eqb_spec (fp_len X10) 0) as [Hz|Hnz].
      - exists R5, m4. split; [apply mst_refl|]. split; [exact HDI4|]. split; [exact HRG5 | exact HK5].
      - destruct (Hcopy Hnz) as (C10 & C11 & C12 & C20 & C9 & C1).
        set (n := Z.to_nat (fp_len X10)).
        assert (En : Z.of_nat n = fp_len X10) by (subst n; lia).
        rewrite <- En in C12.
        destruct (call_mc _ _ _ _ _ _ _ _ _ MEMCPY HH R5 m1 m4 X10 n PCD HDI4 PCD_ok Hpo10 ltac:(rewrite En; lia) ltac:(rewrite En; lia)
                    C1 C10 C11 C12)
          as (R6 & Hms6 & D10 & Hfr6).
        assert (HK6 : KP regs0 R6) by (exact (KP_mc _ _ _ HK5 Hfr6)).
        set (M0 := wbytes m4 (zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X10))))) (fbytes (arr_get (ds_pending_buf X10)) (ds_pending_out X10) n)) in *.
        assert (HDI6 : DI M0 M0 X10).
        { subst M0. apply (DI_out_self _ _ _ _ _ _ _ _ _ HH m1); [exact HDI4|]. rewrite fbytes_length, En. lia. }
        assert (HRG6 : RP R6) by (exact (RP_mc _ _ HRG5 Hfr6)).
        assert (F6 : FPR rs rS R6).
        { destruct F5 as [Fa Fb]. split; [rewrite (Hfr6 rs Hrs2); exact Fa | rewrite (Hfr6 rS HrS2); exact Fb]. }
        assert (C20' : getr R6 rl1 = zw (fp_len X10)) by (rewrite (Hfr6 rl1 Hrl1); exact C20).
        assert (C9' : getr R6 rl2 = zw (fp_len X10)) by (rewrite (Hfr6 rl2 Hrl2); exact C9).
        destruct (D_blk R6 M0 M0 X10 (fp_len X10) HDI6 HRG6 HK6 F6 C20' C9' ltac:(lia) ltac:(lia) ltac:(lia) Hpo10 ltac:(lia) Htot10)
          as (R7 & Hms7 & HRG7 & HK7).
        exists R7, (DeflSlow6_6.fp_tower S p zp M0 X10 (fp_len X10)).
        split; [eapply msteps_trans; [exact Hms6 | exact Hms7]|].
        split.
        { pose proof (fp_finish _ _ _ _ _ _ _ _ _ HH m1 m4 X10 n (cs_total_out (ds_strm X10) + fp_len X10) HDI4) as FF.
          cbv zeta in FF. rewrite En in FF. unfold DeflSlow6_6.fp_tower. subst M0.
          apply FF; lia. }
        split; [exact HRG7 | exact HK7]. }
    destruct MID as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
    exists R6, m6. split; [| split; [exact HDI6 | split; [exact HRG6 | exact HK6]]].
    eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5 | exact Hms6].
  Qed.
End FPSeq.


Lemma HREGS_fb : forall R R', HREGS R -> (forall r : reg, reg_in r FB_CLOB = false -> getr R' r = getr R r) -> HREGS R'.
Proof using. intros R R' H Hfr. hregs_via H Hfr. Qed.
Lemma HREGS_mc : forall R R', HREGS R -> (forall r : reg, reg_in r memcpy_clob = false -> getr R' r = getr R r) -> HREGS R'.
Proof using. intros R R' H Hfr. hregs_via H Hfr. Qed.
Lemma TREGS_fb : forall R R', TREGS R -> (forall r : reg, reg_in r FB_CLOB = false -> getr R' r = getr R r) -> TREGS R'.
Proof using. intros R R' H Hfr. tregs_via H Hfr. Qed.
Lemma TREGS_mc : forall R R', TREGS R -> (forall r : reg, reg_in r memcpy_clob = false -> getr R' r = getr R r) -> TREGS R'.
Proof using. intros R R' H Hfr. tregs_via H Hfr. Qed.

Lemma call_fb_at : forall regs0 regs m1 m X (ra' : word) last,
  DI m1 m X -> KEEP regs0 regs -> ret_ok ra' -> flush_ok X last -> 0 <= last <= 1 ->
  getr regs 10 = zw S -> getr regs 11 = zw (DeflSlow6_6.fb_bufp p X) -> getr regs 12 = zw (DeflSlow6_6.fb_len X) ->
  getr regs 13 = zw last -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  let buf := if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None in
  let len := wrap64 (ds_strstart X - ds_block_start X) in
  exists R m',
    msteps s6_segs (mkst regs (0x1af98 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (tr_flush_block X buf len last)
    /\ KEEP regs0 R
    /\ (forall r : reg, reg_in r TFB_CLOB = false -> getr R r = getr regs r).
Proof using HWF HH TFB MEMSET MEMCPY ra flush.
  intros regs0 regs m1 m X ra' last HDI HK Hret HFO Hlast A10 A11 A12 A13 A2 A1 buf len.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  unfold flush_ok6 in HFO. rewrite Elbs, Ews in HFO. fold buf len in HFO.
  destruct HFO as (Hsafe & HBI & Hsb & Hbs & Hstr & Hs31 & Hwb & _).
  assert (Elen : len = ds_strstart X - ds_block_start X) by (subst len; rewrite wrap64_mod; apply Z.mod_small; lia).
  assert (Hbuf : match buf with
                 | None => DeflSlow6_6.fb_bufp p X = 0
                 | Some off => DeflSlow6_6.fb_bufp p X = W + off /\ 0 <= off < 2 ^ 32 /\ (len <> 0 -> off + len <= 2 * ws)
                 end).
  { subst buf. unfold DeflSlow6_6.fb_bufp. destruct (Z.leb_spec 0 (ds_block_start X)).
    - replace (ds_block_start X <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite wrap32_mod, Z.mod_small by lia. split; [reflexivity|]. split; [lia|]. intros _. lia.
    - replace (ds_block_start X <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold DeflSlow6_6.fb_len in A12. fold len in A12.
  destruct (call_fb _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET TFB HH regs m1 m X ra' buf (DeflSlow6_6.fb_bufp p X) len last
              HDI Hret Hsafe HBI Hlast ltac:(lia) Hwb Hbuf A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & CE2 & Hfr2).
  exists R2, m2. split; [exact Hms2|]. split; [exact HDI2|]. split; [keep_via HK Hfr2 | exact Hfr2].
Qed.

Lemma call_fb_at3 : forall regs0 regs m1 m X (ra' : word) last,
  DI m1 m X -> KEEP3 regs0 regs -> ret_ok ra' -> flush_ok X last -> 0 <= last <= 1 ->
  getr regs 10 = zw S -> getr regs 11 = zw (DeflSlow6_6.fb_bufp p X) -> getr regs 12 = zw (DeflSlow6_6.fb_len X) ->
  getr regs 13 = zw last -> getr regs 2 = zw SP -> getr regs 1 = ra' ->
  let buf := if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None in
  let len := wrap64 (ds_strstart X - ds_block_start X) in
  exists R m',
    msteps s6_segs (mkst regs (0x1af98 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (tr_flush_block X buf len last)
    /\ KEEP3 regs0 R
    /\ (forall r : reg, reg_in r TFB_CLOB = false -> getr R r = getr regs r).
Proof using HWF HH TFB MEMSET MEMCPY ra flush.
  intros regs0 regs m1 m X ra' last HDI HK Hret HFO Hlast A10 A11 A12 A13 A2 A1 buf len.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  unfold flush_ok6 in HFO. rewrite Elbs, Ews in HFO. fold buf len in HFO.
  destruct HFO as (Hsafe & HBI & Hsb & Hbs & Hstr & Hs31 & Hwb & _).
  assert (Elen : len = ds_strstart X - ds_block_start X) by (subst len; rewrite wrap64_mod; apply Z.mod_small; lia).
  assert (Hbuf : match buf with
                 | None => DeflSlow6_6.fb_bufp p X = 0
                 | Some off => DeflSlow6_6.fb_bufp p X = W + off /\ 0 <= off < 2 ^ 32 /\ (len <> 0 -> off + len <= 2 * ws)
                 end).
  { subst buf. unfold DeflSlow6_6.fb_bufp. destruct (Z.leb_spec 0 (ds_block_start X)).
    - replace (ds_block_start X <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite wrap32_mod, Z.mod_small by lia. split; [reflexivity|]. split; [lia|]. intros _. lia.
    - replace (ds_block_start X <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold DeflSlow6_6.fb_len in A12. fold len in A12.
  destruct (call_fb _ _ _ _ _ _ _ _ _ FBSAFE MEMCPY MEMSET TFB HH regs m1 m X ra' buf (DeflSlow6_6.fb_bufp p X) len last
              HDI Hret Hsafe HBI Hlast ltac:(lia) Hwb Hbuf A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & CE2 & Hfr2).
  exists R2, m2. split; [exact Hms2|]. split; [exact HDI2|]. split; [keep3_via HK Hfr2 | exact Hfr2].
Qed.

Lemma fp_seq1 : forall regs0 regs m1 m X8,
  DI m1 m X8 -> HREGS regs -> KEEP regs0 regs ->
  0 <= ds_strstart X8 <= 2 * ws ->
  (let X9 := set_block_start X8 (ds_strstart X8) in
   BINV PBL X9 /\ ds_pending (tr_flush_bits X9) <= PBL
   /\ let X10 := tr_flush_bits X9 in
      0 <= ds_pending X10 < 2 ^ 31 /\ 0 <= ds_pending_out X10 /\ ds_pending_out X10 + fp_len X10 <= PBL
      /\ 0 <= cs_total_out (ds_strm X10) < 2 ^ 64) ->
  exists R M,
    msteps s6_segs (mkst regs (0x199d8 : word) m s6_rom) (mkst R (0x19a5c : word) M s6_rom)
    /\ DI m1 M (let X10 := tr_flush_bits (set_block_start X8 (ds_strstart X8)) in
                if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10))
    /\ HREGS R /\ KEEP regs0 R.
Proof using HWF HH TFBITS MEMCPY ra flush.
  intros regs0.
  apply (fp_seq KEEP (DeflSlow6_1.HREGS S sp) 25%bv 18%bv 19%bv 19%bv (0x199d8 : word) (0x199f0 : word) (0x19a14 : word) (0x19a5c : word) regs0
           KEEP_fb KEEP_mc HREGS_fb HREGS_mc eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  - intros regs m1 m X HDI HRG HK Hstr.
    destruct (fb1b_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG Hstr) as (R & M & Hms & HDI' & HRG' & F & A10 & A1 & A2 & Hfr).
    exists R, M. split; [exact Hms|]. split; [exact HDI'|]. split; [exact HRG'|]. split; [keep_via HK Hfr|].
    split; [exact F|]. split; [exact A10 | exact A1].
  - intros regs m1 m X HDI HRG HK F Hp Hav Hpo.
    destruct (fb1c_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG F Hp Hav Hpo) as (R & Hms & HRG' & F' & Hc & Hfr).
    exists R. split; [exact Hms|]. split; [exact HRG'|]. split; [keep_via HK Hfr|]. split; [exact F'|].
    intros Hnz. destruct (Hc Hnz) as (C10 & C11 & C12 & C19 & C9 & C1 & C2). repeat split; assumption.
  - intros regs m1 M0 X len HDI HRG HK F Q19 Q9 Hlen Hpd Hav Hpo0 Hpo1 Htot.
    destruct (fb1d_blk _ _ _ _ _ _ _ _ _ HH regs m1 M0 X len HDI HRG F Q19 Q9 Hlen Hpd Hav Hpo0 Hpo1 Htot) as (R & Hms & HRG' & F' & Hfr).
    exists R. split; [exact Hms|]. split; [exact HRG' | keep_via HK Hfr].
  - retok.
  - retok.
Qed.

Lemma fp_seq2 : forall regs0 regs m1 m X8,
  DI m1 m X8 -> HREGS regs -> KEEP regs0 regs ->
  0 <= ds_strstart X8 <= 2 * ws ->
  (let X9 := set_block_start X8 (ds_strstart X8) in
   BINV PBL X9 /\ ds_pending (tr_flush_bits X9) <= PBL
   /\ let X10 := tr_flush_bits X9 in
      0 <= ds_pending X10 < 2 ^ 31 /\ 0 <= ds_pending_out X10 /\ ds_pending_out X10 + fp_len X10 <= PBL
      /\ 0 <= cs_total_out (ds_strm X10) < 2 ^ 64) ->
  exists R M,
    msteps s6_segs (mkst regs (0x19a84 : word) m s6_rom) (mkst R (0x195dc : word) M s6_rom)
    /\ DI m1 M (let X10 := tr_flush_bits (set_block_start X8 (ds_strstart X8)) in
                if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10))
    /\ HREGS R /\ KEEP regs0 R.
Proof using HWF HH TFBITS MEMCPY ra flush.
  intros regs0.
  apply (fp_seq KEEP (DeflSlow6_1.HREGS S sp) 25%bv 18%bv 19%bv 19%bv (0x19a84 : word) (0x19a9c : word) (0x19ac0 : word) (0x195dc : word) regs0
           KEEP_fb KEEP_mc HREGS_fb HREGS_mc eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  - intros regs m1 m X HDI HRG HK Hstr.
    destruct (fb2b_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG Hstr) as (R & M & Hms & HDI' & HRG' & F & A10 & A1 & A2 & Hfr).
    exists R, M. split; [exact Hms|]. split; [exact HDI'|]. split; [exact HRG'|]. split; [keep_via HK Hfr|].
    split; [exact F|]. split; [exact A10 | exact A1].
  - intros regs m1 m X HDI HRG HK F Hp Hav Hpo.
    destruct (fb2c_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG F Hp Hav Hpo) as (R & Hms & HRG' & F' & Hc & Hfr).
    exists R. split; [exact Hms|]. split; [exact HRG'|]. split; [keep_via HK Hfr|]. split; [exact F'|].
    intros Hnz. destruct (Hc Hnz) as (C10 & C11 & C12 & C19 & C9 & C1 & C2). repeat split; assumption.
  - intros regs m1 M0 X len HDI HRG HK F Q19 Q9 Hlen Hpd Hav Hpo0 Hpo1 Htot.
    destruct (fb2d_blk _ _ _ _ _ _ _ _ _ HH regs m1 M0 X len HDI HRG F Q19 Q9 Hlen Hpd Hav Hpo0 Hpo1 Htot) as (R & Hms & HRG' & F' & Hfr).
    exists R. split; [exact Hms|]. split; [exact HRG' | keep_via HK Hfr].
  - retok.
  - retok.
Qed.

Lemma fp_seqT : forall (PCB PCC PCD PCE : Z),
  (PCB = 0x19c0c /\ PCC = 0x19c24 /\ PCD = 0x19c48 /\ PCE = 0x19c90)
  \/ (PCB = 0x19cd0 /\ PCC = 0x19ce8 /\ PCD = 0x19d0c /\ PCE = 0x19d54) ->
  forall regs0 regs m1 m X8,
  DI m1 m X8 -> TREGS regs -> KEEP3 regs0 regs ->
  0 <= ds_strstart X8 <= 2 * ws ->
  (let X9 := set_block_start X8 (ds_strstart X8) in
   BINV PBL X9 /\ ds_pending (tr_flush_bits X9) <= PBL
   /\ let X10 := tr_flush_bits X9 in
      0 <= ds_pending X10 < 2 ^ 31 /\ 0 <= ds_pending_out X10 /\ ds_pending_out X10 + fp_len X10 <= PBL
      /\ 0 <= cs_total_out (ds_strm X10) < 2 ^ 64) ->
  exists R M,
    msteps s6_segs (mkst regs (zw PCB) m s6_rom) (mkst R (zw PCE) M s6_rom)
    /\ DI m1 M (let X10 := tr_flush_bits (set_block_start X8 (ds_strstart X8)) in
                if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10))
    /\ TREGS R /\ KEEP3 regs0 R.
Proof using HWF HH TFBITS MEMCPY ra flush.
  intros PCB PCC PCD PCE HP regs0.
  assert (HCok : ret_ok (zw PCC)) by (destruct HP as [(_ & -> & _)|(_ & -> & _)]; retok).
  assert (HDok : ret_ok (zw PCD)) by (destruct HP as [(_ & _ & -> & _)|(_ & _ & -> & _)]; retok).
  apply (fp_seq KEEP3 (DeflSlow6_7.TREGS S sp) 19%bv 9%bv 18%bv 18%bv (zw PCB) (zw PCC) (zw PCD) (zw PCE) regs0
           KEEP3_fb KEEP3_mc TREGS_fb TREGS_mc eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  - intros regs m1 m X HDI HRG HK Hstr.
    destruct (tb_blk _ _ _ _ _ _ _ _ _ HH PCB PCC PCD PCE HP regs m1 m X HDI HRG Hstr) as (R & M & Hms & HDI' & HRG' & F & A10 & A1 & A2 & Hfr).
    exists R, M. split; [exact Hms|]. split; [exact HDI'|]. split; [exact HRG'|]. split; [keep3_via HK Hfr|].
    split; [exact F|]. split; [exact A10 | exact A1].
  - intros regs m1 m X HDI HRG HK F Hp Hav Hpo.
    destruct (tc_blk _ _ _ _ _ _ _ _ _ HH PCB PCC PCD PCE HP regs m1 m X HDI HRG F Hp Hav Hpo) as (R & Hms & HRG' & F' & Hc & Hfr).
    exists R. split; [exact Hms|]. split; [exact HRG'|]. split; [keep3_via HK Hfr|]. split; [exact F'|].
    intros Hnz. destruct (Hc Hnz) as (C10 & C11 & C12 & C18 & C20 & C1 & C2). repeat split; assumption.
  - intros regs m1 M0 X len HDI HRG HK F Q18 Q20 Hlen Hpd Hav Hpo0 Hpo1 Htot.
    destruct (td_blk _ _ _ _ _ _ _ _ _ HH PCB PCC PCD PCE HP regs m1 M0 X len HDI HRG F Q18 Q20 Hlen Hpd Hav Hpo0 Hpo1 Htot) as (R & Hms & HRG' & F' & Hfr).
    exists R. split; [exact Hms|]. split; [exact HRG' | keep3_via HK Hfr].
  - exact HCok.
  - exact HDok.
Qed.


Lemma from_fb1 : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 -> getr regs 10 = zw (ds_strstart X) ->
  flush_ok X 0 ->
  exists R M,
    DI m1 M (fst (flush_block X 0)) /\ KEEP regs0 R
    /\ match snd (flush_block X 0) with
       | Some bs => msteps s6_segs (mkst regs (0x1997c : word) m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
                    /\ getr R 10 = zw (bs_code bs) /\ getr R 2 = zw SP
       | None => msteps s6_segs (mkst regs (0x1997c : word) m s6_rom) (mkst R (0x19600 : word) M s6_rom)
                 /\ HREGS R
       end.
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HK HL1 Q10 HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  pose proof (LOC_keep _ _ _ HL1 HDI) as HLm.
  destruct (fb1a_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG HLm Q10 ltac:(lia) ltac:(lia)) as (R1 & Hms1 & HRG1 & A10 & A11 & A12 & A13 & A1 & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (call_fb_at regs0 R1 m1 m X (0x199d8%bv : word) 0 HDI HK1 ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : HREGS R2) by hregs_via HRG1 Hfr2.
  rewrite flush_block_fst, flush_block_snd, flush_block_fst, flush_block_only_eq. cbv zeta.
  replace (negb (0 =? 0)) with false by reflexivity.
  revert Hstr8 HREST HDI2.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 0).
  intros X8 Hstr8 HREST HDI2.
  destruct (fp_seq1 regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST) as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  cbv zeta in HDI6. revert HDI6. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))); intros X10.
  generalize (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)); intros X11 HDI6.
  pose proof (avail_bound _ _ _ HDI6) as Hav11.
  destruct (fb1e_blk _ _ _ _ _ _ _ _ _ HH R6 m1 m6 X11 HDI6 HRG6 Hav11) as (R8 & Hms8 & HRG8 & Z10 & Hfr8).
  assert (HK8 : KEEP regs0 R8) by (keep_via HK6 Hfr8).
  exists R8, m6. split; [exact HDI6|]. split; [exact HK8|].
  unfold DeflSlow6_6.avail_pc in Hms8.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm X11)) 0) as [Hz|Hnz].
  - cbn [bs_code]. split; [| split; [exact (Z10 Hz) | destruct HRG8 as (_ & W2 & _); exact W2]].
    eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms6 | exact Hms8].
  - split; [| exact HRG8].
    eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms6 | exact Hms8].
Qed.


Lemma from_fb2 : forall regs0 regs m1 m X,
  DI m1 m X -> HREGS regs -> KEEP regs0 regs -> LOC m1 ->
  flush_ok X 0 ->
  exists R M,
    DI m1 M (flush_block_only X 0) /\ KEEP regs0 R /\ HREGS R
    /\ msteps s6_segs (mkst regs (0x1994c : word) m s6_rom) (mkst R (0x195dc : word) M s6_rom).
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra.
  intros regs0 regs m1 m X HDI HRG HK HL1 HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  pose proof (LOC_keep _ _ _ HL1 HDI) as HLm.
  destruct (fb2a_blk _ _ _ _ _ _ _ _ _ HH regs m1 m X HDI HRG HLm ltac:(lia) ltac:(lia)) as (R1 & Hms1 & HRG1 & A10 & A11 & A12 & A13 & A1 & A2 & Hfr1).
  assert (HK1 : KEEP regs0 R1) by (keep_via HK Hfr1).
  destruct (call_fb_at regs0 R1 m1 m X (0x19a84%bv : word) 0 HDI HK1 ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 A2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : HREGS R2) by hregs_via HRG1 Hfr2.
  rewrite flush_block_only_eq. cbv zeta.
  revert Hstr8 HREST HDI2.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 0).
  intros X8 Hstr8 HREST HDI2.
  destruct (fp_seq2 regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST) as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  exists R6, m6. split; [exact HDI6|]. split; [exact HK6|]. split; [exact HRG6|].
  eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms6].
Qed.


Lemma from_fbt : forall regs0 regs m1 m X,
  DI m1 m X -> TREGS regs -> KEEP3 regs0 regs ->
  getr regs 10 = zw S -> getr regs 11 = zw (DeflSlow6_6.fb_bufp p X) -> getr regs 12 = zw (DeflSlow6_6.fb_len X) ->
  getr regs 13 = zw 1 -> getr regs 1 = (0x19c0c%bv : word) ->
  0 < ds_wrap X < 2 ^ 31 ->
  flush_ok X 1 ->
  exists R M,
    DI m1 M (fst (flush_block X 1)) /\ KEEP3 regs0 R
    /\ msteps s6_segs (mkst regs (0x1af98 : word) m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
    /\ getr R 10 = zw (match snd (flush_block X 1) with Some bs => bs_code bs | None => 3 end)
    /\ getr R 2 = zw SP.
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra flush.
  intros regs0 regs m1 m X HDI HRG HK A10 A11 A12 A13 A1 Hwr HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  destruct HRG as (P8 & P2 & P21).
  destruct (call_fb_at3 regs0 regs m1 m X (0x19c0c%bv : word) 1 HDI HK ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 P2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : TREGS R2) by (unfold DeflSlow6_7.TREGS; rewrite (Hfr2 8%bv eq_refl), (Hfr2 2%bv eq_refl), (Hfr2 21%bv eq_refl); repeat split; assumption).
  rewrite flush_block_fst, flush_block_snd, flush_block_fst, flush_block_only_eq. cbv zeta.
  replace (negb (1 =? 0)) with true by reflexivity.
  pose proof (tfb_wrap6 X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 1) as W8.
  revert Hstr8 HREST HDI2 W8.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 1).
  intros X8 Hstr8 HREST HDI2 W8.
  pose proof (avail_bound _ _ _ HDI2) as Hav8.
  assert (W10 : ds_wrap (tr_flush_bits (set_block_start X8 (ds_strstart X8))) = ds_wrap X) by (rewrite tfbits_wrap6; destruct X8; exact W8).
  assert (A10' : 0 <= cs_avail_out (ds_strm (tr_flush_bits (set_block_start X8 (ds_strstart X8))))) by (rewrite tfbits_strm6; destruct X8; cbn in Hav8 |- *; lia).
  pose proof HREST as HR'. cbv zeta in HR'. destruct HR' as (_ & _ & Hp10 & _).
  destruct (fp_seqT 0x19c0c 0x19c24 0x19c48 0x19c90 ltac:(left; repeat split; reflexivity) regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST)
    as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  cbv zeta in HDI6. revert HDI6 W10 A10' Hp10. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))); intros X10 HDI6 W10 A10' Hp10.
  assert (P11 : 0 <= ds_pending (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)) < 2 ^ 31).
  { destruct (Z.eqb_spec (fp_len X10) 0); [lia|]. rewrite fptail_pending6.
    destruct (DeflSlow6_6.fp_len_eq X10 ltac:(lia) ltac:(lia)) as (_ & Hl1 & Hl2). lia. }
  assert (W11 : ds_wrap (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)) = ds_wrap X).
  { destruct (_ =? 0); [exact W10 | rewrite fptail_wrap6; exact W10]. }
  revert HDI6 P11 W11.
  generalize (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)); intros X11 HDI6 P11 W11.
  pose proof (avail_bound _ _ _ HDI6) as Hav11.
  destruct (fbte_blk _ _ _ _ _ _ _ _ _ HH R6 m1 m6 X11 HDI6 HRG6 Hav11 P11 ltac:(intros _; right; lia)) as (R8 & Hms8 & HRG8 & Z10 & Hfr8).
  assert (HK8 : KEEP3 regs0 R8) by (keep3_via HK6 Hfr8).
  exists R8, m6. split; [exact HDI6|]. split; [exact HK8|].
  symex_pc_lit_in Hms6.
  split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms6 | exact Hms8]|].
  split; [| destruct HRG8 as (_ & W2 & _); exact W2].
  rewrite Z10. destruct (cs_avail_out (ds_strm X11) =? 0); reflexivity.
Qed.


Lemma from_fin : forall regs0 regs m1 m X,
  DI m1 m X -> TREGS regs -> KEEP3 regs0 regs ->
  getr regs 10 = zw S -> getr regs 11 = zw (DeflSlow6_6.fb_bufp p X) -> getr regs 12 = zw (DeflSlow6_6.fb_len X) ->
  getr regs 13 = zw 0 -> getr regs 1 = (0x19cd0%bv : word) ->
  flush_ok X 0 ->
  exists R M,
    DI m1 M (fst (flush_block X 0)) /\ KEEP3 regs0 R
    /\ msteps s6_segs (mkst regs (0x1af98 : word) m s6_rom) (mkst R (0x19d64 : word) M s6_rom)
    /\ getr R 10 = zw (match snd (flush_block X 0) with Some bs => bs_code bs | None => 1 end)
    /\ getr R 2 = zw SP.
Proof using HWF HH TFB TFBITS MEMSET MEMCPY ra flush.
  intros regs0 regs m1 m X HDI HRG HK A10 A11 A12 A13 A1 HFO.
  pose proof (di_sizes _ _ _ HDI) as (Ews & Ehs & Elbs). pose proof (wf_wsz _ HWF) as Wws.
  pose proof HFO as HFO'. unfold flush_ok6 in HFO'. rewrite Elbs, Ews in HFO'.
  destruct HFO' as (_ & _ & Hsb & Hbs & Hstr & Hs31 & _ & Hstr8 & HREST).
  destruct HRG as (P8 & P2 & P21).
  destruct (call_fb_at3 regs0 regs m1 m X (0x19cd0%bv : word) 0 HDI HK ltac:(retok) HFO ltac:(lia) A10 A11 A12 A13 P2 A1)
    as (R2 & m2 & Hms2 & HDI2 & HK2 & Hfr2).
  assert (HRG2 : TREGS R2) by (unfold DeflSlow6_7.TREGS; rewrite (Hfr2 8%bv eq_refl), (Hfr2 2%bv eq_refl), (Hfr2 21%bv eq_refl); repeat split; assumption).
  rewrite flush_block_fst, flush_block_snd, flush_block_fst, flush_block_only_eq. cbv zeta.
  replace (negb (0 =? 0)) with false by reflexivity.
  revert Hstr8 HREST HDI2.
  generalize (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None) (wrap64 (ds_strstart X - ds_block_start X)) 0).
  intros X8 Hstr8 HREST HDI2.
  destruct (fp_seqT 0x19cd0 0x19ce8 0x19d0c 0x19d54 ltac:(right; repeat split; reflexivity) regs0 R2 m1 m2 X8 HDI2 HRG2 HK2 Hstr8 HREST)
    as (R6 & m6 & Hms6 & HDI6 & HRG6 & HK6).
  cbv zeta in HDI6. revert HDI6. generalize (tr_flush_bits (set_block_start X8 (ds_strstart X8))); intros X10.
  generalize (if fp_len X10 =? 0 then X10 else fp_tail X10 (fp_len X10)); intros X11 HDI6.
  pose proof (avail_bound _ _ _ HDI6) as Hav11.
  destruct (fine_blk _ _ _ _ _ _ _ _ _ HH R6 m1 m6 X11 HDI6 HRG6 Hav11) as (R8 & Hms8 & HRG8 & Z10 & Hfr8).
  assert (HK8 : KEEP3 regs0 R8) by (keep3_via HK6 Hfr8).
  symex_pc_lit_in Hms6. unfold DeflSlow6_6.avail_pc in Hms8.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm X11)) 0) as [Hz|Hnz].
  - exists R8, m6. split; [exact HDI6|]. split; [exact HK8|].
    split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms6 | exact Hms8]|].
    split; [cbn [bs_code]; exact (Z10 Hz) | destruct HRG8 as (_ & W2 & _); exact W2].
  - destruct (b84_blk _ _ _ _ _ _ _ _ _ HH R8 m6 HRG8) as (R9 & Hms9 & HRG9 & Z1 & Hfr9).
    exists R9, m6. split; [exact HDI6|]. split; [keep3_via HK8 Hfr9|].
    split; [eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms8 | exact Hms9]|].
    split; [exact Z1 | destruct HRG9 as (_ & W2 & _); exact W2].
Qed.

End Walk.
End FXG.
