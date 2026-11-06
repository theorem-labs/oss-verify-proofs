(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 205 of its 304 lines of code are new or changed and 1392 lines of the source are left out. *)
(* The walk of check_segments on fuzz_segconf.asan (image A, 0x8704c, 79 instructions), part 2: the loop
   0x870f8 .. 0x87114 (a0 := c + 356 i, a1 := m + 256 i, the strcmp wrapper, `bnez a0`, the three cursors,
   `bnez s3`), proved by induction on the segments left, and the theorem check_segments_walk. The entry stretch, the
   exit and the cut points are part 1 (check_segments_s1.v). The call is stepped as fuzz_command's released walk of
   rec_calls_equal steps its strcmp call (origin/ossv/recipes 501c0d516c69, lib/A/Prog/rec_calls_equal.v:854-882:
   PaArt.aj_art_at over the wrapper's contract). The premise SegModel.check_segments rcs mcs returned = true makes
   the i-th names one byte string (check_segments_s1.cs_names), so the wrapper returns 0 and the arm to the
   no-return hook and abort (0x87138 / 0x8713c) at 0x87104 is not taken. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob SegInstA check_segments_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import check_segments_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* every byte of a struct the reader fixes is mapped *)
Lemma cs_rconf_some : forall (rd : reader) c rcs a, sa_rconf rd c rcs -> c <= a < c + seg_spec.SEG_C_SIZE -> rd a <> None.
Proof.
intros rd c rcs a (bs & H & L & _) Ha. unfold seg_spec.SEG_C_SIZE in *.
replace a with (c + Z.of_nat (Z.to_nat (a - c))) by lia. rewrite H by lia. discriminate.
Qed.
Lemma cs_mconf_some : forall (rd : reader) m mcs a, sa_mconf rd m mcs -> m <= a < m + seg_spec.SEG_M_SIZE -> rd a <> None.
Proof.
intros rd m mcs a (bs & H & L & _) Ha. unfold seg_spec.SEG_M_SIZE in *.
replace a with (m + Z.of_nat (Z.to_nat (a - m))) by lia. rewrite H by lia. discriminate.
Qed.

Lemma cs_kept_widen : forall rd rd' lo hi lo' hi', kept_out rd rd' lo hi -> lo' <= lo -> hi <= hi' -> kept_out rd rd' lo' hi'.
Proof. intros rd rd' lo hi lo' hi' H H1 H2 a Ha Hn. apply H; [exact Ha | lia]. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
(* the walk's engine facts: the shadow GOT word and cell, errno, the allocator's trampolines (SegPaLib.v) *)
Hypothesis TL : PALib B.
(* the strcmp wrapper (the interceptor layer's interface row 17, fuzz_command's lib/A/Rt/RtString.v:108-119), at the listing's
   call target, at every FP state *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac cs_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac cs_kept_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.

Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (c mm : Z) (rcs : rconf) (mcs : mconf) (returned : bool).
Hypothesis HPRE : afn_pre SEGS B STK_check_segments ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO_A RHI_A B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis H11 : getr regs 11 = w64 mm.
Hypothesis H12 : getr regs 12 = w64 (seg_spec.b2z returned).
Hypothesis HC16 : c mod 16 = 0.
Hypothesis HRC : sa_rconf (rdW W mem) c rcs.
Hypothesis HHC : sa_heap B ly S c seg_spec.SEG_C_SIZE.
Hypothesis HAC : sa_addr (rdW W mem) c seg_spec.SEG_C_SIZE.
Hypothesis HM16 : mm mod 16 = 0.
Hypothesis HRM : sa_mconf (rdW W mem) mm mcs.
Hypothesis HHM : sa_heap B ly S mm seg_spec.SEG_M_SIZE.
Hypothesis HAM : sa_addr (rdW W mem) mm seg_spec.SEG_M_SIZE.
Hypothesis HCS : check_segments rcs mcs returned = true.

#[local] Notation Q := (cs_Q B ly S W regs mem md).
#[local] Notation CUT := (cs_cut B ly S W regs mem md).
#[local] Notation LP := (cs_loop B ly S W regs mem md c mm mcs).
#[local] Notation N := (length (mc_seg mcs)).

(* the loop's head: registers only, sp's fact *)
Lemma cs_loop_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 48) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [w64 SB])) cs_ss_loop
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + CS_LOOP)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS cs_Bx [] (Eimg (Ereg regs1 [w64 SB])) (mrestrict (w_H W) mem1).
Proof using HPRE c mm.
intros regs1 mem1 R2. pose proof (cs_sp B ly S W regs mem md ch c mm HPRE) as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : STK_check_segments = 8240) by reflexivity.
set (E := Eimg (Ereg regs1 [w64 SB])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold cs_ss_loop. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, cs_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* one entry of the loop: 0x870f8 .. 0x87114 *)
Lemma cs_loop_step : forall i regs1 mem1 md1,
  ((Datatypes.S i < N)%nat -> forall r m d, LP (Datatypes.S i) r m d ->
    SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + CS_LOOP)) m (seg_rom SEGS)) d) Q) ->
  LP i regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CS_LOOP)) mem1 (seg_rom SEGS)) md1) Q.
Proof using TL ASTRCMP HPRE HROD HC16 HRC HHC HAC HM16 HRM HHM HAM HCS.
intros i regs1 mem1 md1 NXT ((HJ & HK & HFR & R2 & RU & R8) & Hi & R9 & R18 & R19).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (cs_sp B ly S W regs mem md ch c mm HPRE) as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : STK_check_segments = 8240) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (cs_n W mem mm rcs mcs returned HRM HCS) as (Ln & Ov & Hret & L32).
assert (HCS' : check_segments rcs mcs true = true) by (pose proof HCS as Hx0; rewrite Hret in Hx0; exact Hx0).
destruct (cs_blk B ly S W regs mem md ch c mm HPRE c _ HHC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (Hc4 & Hcc & _ & _ & (pc & kc & Hinc & Hpc & Hkc)).
destruct (cs_blk B ly S W regs mem md ch c mm HPRE mm _ HHM ltac:(unfold seg_spec.SEG_M_SIZE; lia))
  as (Hm4 & Hmc & _ & _ & (pm & km & Hinm & Hpm & Hkm)).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
destruct (cs_names (rdW W mem) c mm rcs mcs i HRC HRM HCS' Hi) as (sx & Bc & Bm & Nx & Lx).
set (x := c + 356 * Z.of_nat i) in *. set (y := mm + 256 * Z.of_nat i) in *.
assert (Hx : 0 < x /\ x + 356 <= c + 16616) by (subst x; lia).
assert (Hy : 0 < y /\ y + 256 <= mm + 9236) by (subst y; lia).
destruct (cs_loop_seed regs1 mem1 R2) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 [w64 SB]))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 [w64 SB])) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
remember (Eimg (Ereg regs1 [w64 SB])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
(* 0x870f8 .. 0x87100: a0 := s1, a1 := s2, the call of the strcmp wrapper *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cs_md.
cs_kept_empty HFr KEEP1 (spZ regs - STK_check_segments) (spZ regs - STK_check_segments). clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KEEPc : kept_out (rdW W mem) (rdW W mT0) (spZ regs - STK_check_segments) (spZ regs))
  by (apply (kept_out_trans _ _ _ _ _ _ _ HK KEEP1); lia).
assert (HspT : spZ rT0 = spZ regs + -48) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (P3' : getr rT0 3 = w64 (as_gp B)).
{ rewrite P3, (EE 3%nat 3%bv eq_refl). exact (eq_trans (RU 3 ltac:(cbv; tauto)) Hgp). }
assert (P4' : getr rT0 4 = w64 (as_tp B)).
{ rewrite P4, (EE 4%nat 4%bv eq_refl). exact (eq_trans (RU 4 ltac:(cbv; tauto)) Htp). }
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 x) by (rewrite P10, (EE 9%nat 9%bv eq_refl), R9; reflexivity).
assert (P11' : getr rT0 11 = w64 y) by (rewrite P11, (EE 18%nat 18%bv eq_refl), R18; reflexivity).
(* the wrapper's premises on the two names *)
assert (KV : forall a, 0 <= a < alloc_ceiling -> rdW W mT0 a = rdW W mem a) by (intros a Ha; apply KEEPc; lia).
assert (STRc : astr_at SEGS W mT0 x sx).
{ split; [|exact Nx]. intros j Hj. rewrite KV by (rewrite length_app in Hj; cbn [length] in Hj; lia). exact (Bc j Hj). }
assert (STRm : astr_at SEGS W mT0 y sx).
{ split; [|exact Nx]. intros j Hj. rewrite KV by (rewrite length_app in Hj; cbn [length] in Hj; lia). exact (Bm j Hj). }
assert (RDc : aread_ok SEGS (2 * ESTACK) W rT0 mT0 x (astr_len sx + 1)).
{ unfold astr_len.
  apply (aread_ok_kept SEGS 0 (2 * ESTACK) W regs rT0 mem mT0 (spZ regs - STK_check_segments) (spZ regs) x _ KEEPc);
    [| lia | lia | lia | rewrite HspT, Hes; lia | lia].
  apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md pc kc x _ HAR Hinc); lia. }
assert (RDm : aread_ok SEGS (2 * ESTACK) W rT0 mT0 y (astr_len sx + 1)).
{ unfold astr_len.
  apply (aread_ok_kept SEGS 0 (2 * ESTACK) W regs rT0 mem mT0 (spZ regs - STK_check_segments) (spZ regs) y _ KEEPc);
    [| lia | lia | lia | rewrite HspT, Hes; lia | lia].
  apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md pm km y _ HAR Hinm); lia. }
assert (TLc : atail_vis SEGS W mT0 (x + astr_len sx)).
{ unfold astr_len. intros a Ha. pose proof (Z.mod_pos_bound (x + Z.of_nat (length sx)) 8 ltac:(lia)).
  rewrite KV by lia. apply (cs_rconf_some _ c rcs a HRC). unfold seg_spec.SEG_C_SIZE. lia. }
assert (TLm : atail_vis SEGS W mT0 (y + astr_len sx)).
{ unfold astr_len. intros a Ha. pose proof (Z.mod_pos_bound (y + Z.of_nat (length sx)) 8 ltac:(lia)).
  rewrite KV by lia. apply (cs_mconf_some _ mm mcs a HRM). unfold seg_spec.SEG_M_SIZE. lia. }
assert (ROM : rt_rom_view SEGS B W mT0).
{ intros a Hro Ho He. destruct Hro as (sg & Hsg & Hw & Hr).
  assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range _ Himg) as HR. unfold kImgEnd in HR. rewrite KV by lia.
  apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He]. }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strcmp)
    W rT0 mT0 STK_check_segments (spZ regs) [] ly S W mem md [] ly S _ 0 (-48) (Z_to_bv 64 (BASE + CS_RA)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx ly S W rT0 mT0 _ x y sx sx).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_check_segments (spZ regs) [] ly S W mem md [] ly S W mT0 _ 0 rT0 (-48)
      HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'. - exact P11'. - lia. - lia.
  - exact STRc. - exact STRm. - exact RDc. - exact RDm. - exact TLc. - exact TLm.
  - exact ROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x87104 *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs - 48) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS cs_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (KEEPk : kept_out (rdW W mT0) (rdW W mem2) (spZ regs - STK_check_segments) (spZ regs - 48))
  by (intros x0 Hx0 Hn0; apply HK2; [exact Hx0 | rewrite Hes; lia | tauto]).
clear HK2. clear HJ. rename HJ2 into HJ.
assert (KEEPm : kept_out (rdW W mem1) (rdW W mem2) (spZ regs - STK_check_segments) (spZ regs - 48))
  by (apply (kept_out_trans _ _ _ _ _ _ _ (cs_kept_widen _ _ _ _ (spZ regs - STK_check_segments) (spZ regs - 48) KEEP1 ltac:(lia) ltac:(lia)) KEEPk); lia).
clear KEEP1 KEEPk KEEPc.
(* the cut at a later state *)
assert (CUTL : forall regsF memF mdF,
  ajournal SEGS B STK_check_segments (spZ regs) [] ly S W mem md [] ly S W memF mdF 0 ->
  kept_out (rdW W mem2) (rdW W memF) (spZ regs - STK_check_segments) (spZ regs - STK_check_segments) ->
  getr regsF 2 = ew Ec 2 -> getr regsF 8 = ew Ec 8 ->
  (forall k, In k cs_untouched -> getr regsF (Z_to_bv 5 k) = ew Ec (Z.to_nat k)) ->
  CUT regsF memF mdF).
{ intros regsF memF mdF HJF HKF Q2 Q8 QU.
  assert (HKm : kept_out (rdW W mem1) (rdW W memF) (spZ regs - STK_check_segments) (spZ regs - 48))
    by (apply (kept_out_trans _ _ _ _ _ _ _ KEEPm HKF); lia).
  split; [exact HJF|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ HK HKm); lia|].
  split.
  { intros j r Hr. assert (Hj : (j < 5)%nat) by (change 5%nat with (length cs_saved); apply (proj1 (nth_error_Some cs_saved j)); rewrite Hr; discriminate).
    apply (cs_val_keep _ _ _ _ _ _ _ HKm (HFR j r Hr)); lia. }
  split; [rewrite Q2, OLD3, (EE 2%nat 2%bv eq_refl) by lia; exact R2|].
  split; [|rewrite Q8, OLD3, (EE 8%nat 8%bv eq_refl) by lia; exact R8].
  intros k Hk. rewrite QU by exact Hk.
  assert (0 <= k < 32) by (cbv [cs_untouched In] in Hk; lia).
  rewrite OLD3 by lia. rewrite <- (RU k Hk). apply EE.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
(* 0x87104: bnez a0, the wrapper's answer *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* the names differ: the abort arm 0x87138; refuted, both names are sx *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc. unfold U. f_equal. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52, (proj2 HQ2 eq_refl). reflexivity.
- clear Hc.
  (* 0x87108 .. 0x87114: s3 -= 1, s2 += 256, s1 += 356, bnez s3 *)
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { awr_ok_tac; exact Usp3. }
  cs_md.
  cs_kept_empty HFr KEEP3 (spZ regs - STK_check_segments) (spZ regs - STK_check_segments). clear HF HFr HG.
  assert (E19 : bv_unsigned (ew Ec 19) = Z.of_nat (N - i)).
  { rewrite OLD3, (EE 19%nat 19%bv eq_refl), R19 by lia. apply unsigned_lit_small. lia. }
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* segments left: back to 0x870f8 *)
    assert (HiS : (Datatypes.S i < N)%nat).
    { rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite E19 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      rewrite zcanon_small in Hc by lia. change (zcanon 0) with 0 in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan CS_LOOP.
    { awr_ok_tac; exact Usp3. }
    cs_md.
    cs_kept_empty HFr KEEP4 (spZ regs - STK_check_segments) (spZ regs - STK_check_segments). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    apply NXT; [exact HiS|].
    split; [|split; [exact HiS|]].
    { apply CUTL; [exact HJ | apply (kept_out_trans _ _ _ _ _ _ _ KEEP3 KEEP4); lia | exact Q2 | exact Q8 |].
      intros k Hk. cbv [cs_untouched In] in Hk.
      repeat (destruct Hk as [<- | Hk];
        [lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ => prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX; reflexivity end |]);
      destruct Hk. }
    split; [rewrite Q9, OLD3, (EE 9%nat 9%bv eq_refl), R9 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite Q18, OLD3, (EE 18%nat 18%bv eq_refl), R18 by lia; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    rewrite Q19, E19. unfold w64. f_equal. lia.
  + (* the last segment: to the exit 0x87118 *)
    assert (HiS : Datatypes.S i = N).
    { rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite E19 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      rewrite zcanon_small in Hc by lia. change (zcanon 0) with 0 in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan CS_EXIT.
    { awr_ok_tac; exact Usp3. }
    cs_md.
    cs_kept_empty HFr KEEP4 (spZ regs - STK_check_segments) (spZ regs - STK_check_segments). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
    apply (cs_exit B TL ly S W regs mem md ch c mm HPRE HHC HHM).
    apply CUTL; [exact HJ | apply (kept_out_trans _ _ _ _ _ _ _ KEEP3 KEEP4); lia | exact Q2 | exact Q8 |].
    intros k Hk. cbv [cs_untouched In] in Hk.
    repeat (destruct Hk as [<- | Hk];
      [lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ => prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX; reflexivity end |]);
    destruct Hk.
Qed.

(* the loop *)
Lemma cs_loop_all : forall dd i, (i + dd = N)%nat -> (i < N)%nat -> forall r m d, LP i r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + CS_LOOP)) m (seg_rom SEGS)) d) Q.
Proof using TL ASTRCMP HPRE HROD HC16 HRC HHC HAC HM16 HRM HHM HAM HCS.
induction dd as [|dd IH]; intros i Hd Hi r m d HL; [lia|].
apply (cs_loop_step i); [|exact HL].
intros Hsi r' m' d' HL'. apply (IH (Datatypes.S i)); [lia | exact Hsi | exact HL'].
Qed.

Lemma cs_main : SRr SEGS W (cfg_at SEGS (BASE + AF_check_segments) regs mem md) Q.
Proof using TL ASTRCMP HPRE HROD H10 H11 H12 HC16 HRC HHC HAC HM16 HRM HHM HAM HCS.
apply (cs_entry B TL ly S W regs mem md ch c mm rcs mcs returned HPRE H10 H11 H12 HC16 HRC HHC HAC HM16 HRM HHM HAM HCS).
intros r m d HL. apply (cs_loop_all N 0); [lia | exact (proj1 (proj2 HL)) | exact HL].
Qed.
End w.

(* the image-A walk of check_segments against its contract (lib/A/Prog/check_segments_c.v), at image A's
   numbers: the entry BASE + AF_check_segments (0x8704c, a listing term), the stack SegInstA.STK_check_segments
   (48 + 2 * ESTACK), the read-only window SegInstA.RLO_A .. RHI_A (0xa14a0 .. 0xa3748) *)
Theorem check_segments_walk :
  check_segments_contract SEGS B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.
Proof using TL ASTRCMP.
unfold check_segments_contract.
intros ly S W regs mem md ch c mm retv rcs mcs returned HPRE HROD H10 Rc H11 Rm H12 Rr
  (C0 & C16 & HRC & HHC & HAC & M0 & M16 & HRM & HHM & HAM & Hretv & HCS) HEV.
subst retv.
exact (cs_main ly S W regs mem md ch c mm rcs mcs returned HPRE HROD H10 H11 H12 C16 HRC HHC HAC M16 HRM HHM HAM HCS).
Qed.
End e.
End d.
End b.
