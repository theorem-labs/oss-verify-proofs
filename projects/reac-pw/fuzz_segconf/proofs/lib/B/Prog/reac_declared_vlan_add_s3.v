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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths and module names changed; 239 of its 313 lines of code are new or changed and 1417 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan-ubsan (image B): segment 3 of the walk of
   lib/B/Prog/reac_declared_vlan_add_c.v, after the search (0x8a614 .. 0x8a654). It adapts the checked memset step of
   lib/A/Prog/reac_segconf_init.v (commit 64746c036e80: aj_intrin_atS with OSet) and the seeds and
   branches of lib/A/Prog/reac_declared_vlan_add_s0.v (commit fcd2fa03dd27, vad_lt_seed and
   vad_latch; image A has no lemma for this stretch). A seed at 0x8a614 from the AFT cut; `bge s9,s5` taken
   (count >= max) -> the epilogue with s4 = -1 and the table kept (vad_keep); not taken: the two UBSan tests of
   tab + 18 count (0x8a624 beqz, 0x8a638 the overflow test, both refuted), memset(tab + 18 count, 0, 18) by
   aj_intrin_atS, and the MSc cut at its return 0x8a654. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase reac_declared_vlan_add_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_add_lem reac_declared_vlan_add_s0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the seed at 0x8a614: every register its own atom; no memory region, since the stretch up to the memset call reads
   and writes no memory *)
Definition vad_ss_aft : sstate := mkSS VAD_AFT sr_atoms [] None (mkFacts [(2%nat, vad_spF)] [] []).
(* `bge rs1, rs2` on two atoms that hold values below 2 ^ 63 *)
Lemma vad_bge_ab : forall E j k x y, ew E j = w64 x -> ew E k = w64 y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SOff j 0)) (sv_denot E (SOff k 0)) = (y <=? x).
Proof.
intros E j k x y Hj Hk Hx Hy. cbn [branch_taken sv_denot]. rewrite Hj, Hk, !Z.add_0_r. unfold w64.
rewrite !unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !vad_swrap_small by lia.
destruct (Z.ltb_spec x y); destruct (Z.leb_spec y x); try reflexivity; lia.
Qed.
(* the executor's expression of tab + 18 count (`li a0,18; mul a0,s9,a0; add a0,a0,s7` at 0x8a618 and
   `li s2,18; mul a0,s9,s2; add a0,s7,a0` at 0x8a63c), atom 23 = tab, atom 25 = count *)
Lemma vad_d_U : forall E tb k, U E (SOff 23 0) = tb -> U E (SOff 25 0) = k -> 0 <= k -> 0 <= tb -> tb + 18 * k < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 25 0) (SLit 18))) = tb + 18 * k.
Proof.
intros E tb k Ht Hk H0 H1 H2. rewrite U_SAlu, U_SMd, U_SLit, Ht, Hk. cbn [zalu_raw zmd_raw].
change (zcanon 18) with 18. rewrite (zcanon_small (k * 18)) by lia. rewrite zcanon_small by lia. lia.
Qed.
(* the pointer-overflow test of 0x8a628 .. 0x8a634: (a0 <u tab) xor (count <s 0) xor 1, which is 1 (vad_ovf_ok) *)
Lemma vad_ovf_U : forall E tb k, U E (SOff 23 0) = tb -> U E (SOff 25 0) = k -> 0 <= k < 2 ^ 63 -> 0 < tb ->
tb + 18 * k < 2 ^ 64 ->
U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 25 0) (SLit 18))) (SOff 23 0))
  (SAlu ALU_SLT (SOff 25 0) (SLit 0))) (SLit 1)) = 1.
Proof.
intros E tb k Ht Hk H0 H1 H2.
pose proof (vad_d_U E tb k Ht Hk ltac:(lia) ltac:(lia) H2) as UX.
repeat first [ rewrite UX | rewrite U_SAlu | rewrite U_SLit ]. rewrite Ht, Hk. cbn [zalu_raw].
destruct (vad_ovf_ok tb k H1 ltac:(lia) H2) as [_ HL].
rewrite Z.mod_small in HL by lia. rewrite HL.
replace (bv_swrap 64 k <? bv_swrap 64 (zcanon 0)) with false.
- vm_compute. reflexivity.
- symmetry. apply Z.ltb_ge. rewrite (vad_swrap_small k) by lia. change (bv_swrap 64 (zcanon 0)) with 0. lia.
Qed.

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
Hypothesis TL : PALib B.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac vad_regs_ok EE eqs :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      cbn [sv_denot];
      first [ reflexivity
            | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | rewrite ?Z.add_0_r; eqs; assumption
            | rewrite ?Z.add_0_r; eqs; unfold w64 in *; assumption ]
    | ]); try (destruct Hrr).
Ltac vad_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac vad_keep_empty HFr K :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : forall x, 0 <= x < 2 ^ 64 -> aview SEGS H m2 x = aview SEGS H m1 x)
  by (intros x0 Hx0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
Ltac vad_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : vad_kept (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.

(* ---------- one call of reac_declared_vlan_add (the same Section variables as segment 0) ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (rlo rhi tab max n par vid : Z) (t : list (list Z * Z)) (p : list Z).
Hypothesis HPRE : afn_pre SEGS B VAD_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS rlo rhi B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 tab.
Hypothesis H11 : getr regs 11 = w64 max.
Hypothesis H12 : getr regs 12 = w64 n.
Hypothesis H13 : getr regs 13 = w64 par.
Hypothesis H14 : getr regs 14 = w64 vid.
Hypothesis HADD : add_pre SEGS B ly S W mem regs tab max n par vid t p.

#[local] Notation L := (Z.of_nat (length t)).
#[local] Notation VA := (vlan_add t max p vid).
#[local] Notation sp0 := (spZ regs).
#[local] Notation VD := (tab + 18 * Z.of_nat (length t)).
(* segment 0's constants at this call (argument lists read from `About`) *)
#[local] Notation FP := (vad_FP tab max n vid t p).
#[local] Notation VE := (vad_E tab max n vid t p).
#[local] Notation Q := (@vad_Q fx rc SK PI B ly S W regs mem md tab max n vid t p).
#[local] Notation frameP := (vad_frame regs).
#[local] Notation spill := (vad_spill regs n).
#[local] Notation cutE := (@vad_cutE rc SK PI B ly S W regs mem md tab max n vid t p).
#[local] Notation cut := (@vad_cut rc SK PI B ly S W regs mem md tab max n vid t p).
#[local] Notation regsP := (vad_regs tab max n par vid t).
#[local] Notation LHc := (@vad_LHc rc SK PI B ly S W regs mem md tab max n par vid t p).
#[local] Notation LTc := (@vad_LTc rc SK PI B ly S W regs mem md tab max n par vid t p).
#[local] Notation AFTc := (@vad_AFTc rc SK PI B ly S W regs mem md tab max n par vid t p).
#[local] Notation MSc := (@vad_MSc rc SK PI B ly S W regs mem md tab max n par vid t p).
#[local] Notation SNc := (@vad_SNc rc SK PI B ly S W regs mem md tab max n par vid t p).
#[local] Notation SP0 := (@vad_sp rc PI B ly S W regs mem md ch HPRE).
#[local] Notation TABF := (@vad_tab_facts rc PI B ly S W regs mem md ch tab max n par vid t p HPRE HADD).
#[local] Notation NF := (@vad_n_facts rc PI B ly S W regs mem md ch tab max n par vid t p HPRE HADD).
#[local] Notation IMGOUT := (@vad_img_out rc PI B ly S W regs mem md ch tab max n par vid t p HPRE HADD).
#[local] Notation ROMAT := (@vad_rom_at rc PI B W mem rlo rhi HROD).
#[local] Notation PARCALL := (@vad_par_call rc PI B ly S W regs mem md ch tab max n par vid t p HPRE HADD).
#[local] Notation EPI := (@vad_epi fx rc SK PI B TL ly S W regs mem md ch tab max n par vid t p HPRE HADD).
#[local] Notation KEEP := (@vad_keep fx rc SK PI B TL ly S W regs mem md ch tab max n par vid t p HPRE HADD).
#[local] Notation CUTKEPT := (@vad_cut_kept rc SK PI B ly S W regs mem md ch tab max n vid t p HPRE).
#[local] Notation SPILLKEPT := (@vad_spill_kept rc PI B ly S W regs mem md ch n HPRE).
#[local] Notation FRM := (@vad_frm rc PI regs).
#[local] Notation FPAPP := (vad_FP_app tab max n vid t p).
#[local] Notation EAPP := (vad_E_app tab max n vid t p).
#[local] Notation AWRTAB := (@vad_awr_tab rc PI B ly S W regs mem tab max n par vid t p HADD).
#[local] Notation AWRN := (@vad_awr_n rc PI B ly S W regs mem tab max n par vid t p HADD).

(* ---------- the seed at 0x8a614 ---------- *)
Lemma vad_aft_seed : forall regs1 mem1, getr regs1 2 = w64 (sp0 - 112) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) vad_ss_aft
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_AFT)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx [] (Eimg (Ereg regs1 [])) (mrestrict (w_H W) mem1).
Proof using HPRE.
intros regs1 mem1 R2. pose proof SP0 as (Hal16 & Hslo & Hshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
set (E := Eimg (Ereg regs1 [])).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold vad_ss_aft. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, vad_spF. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* ---------- 0x8a614 .. 0x8a654: the full exit, or the pointer tests and the checked memset ---------- *)
Lemma vad_aft : forall regs1 mem1 md1,
(forall r m d, MSc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_RMS)) m (seg_rom SEGS)) d) Q) ->
AFTc regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_AFT)) mem1 (seg_rom SEGS)) md1) Q.
Proof using HPRE HADD TL AMEMSET.
intros regs1 mem1 md1 KMS (HCUT & (R8 & R9 & R19 & R20 & R21 & R23 & R24 & R25) & HSP & HEX).
pose proof HCUT as ((HJ & HFR & R2 & R3 & R4) & HK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof SP0 as (Hal16 & Hslo & Hshi & HAC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
destruct (vad_aft_seed regs1 mem1 R2) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 [])) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
remember (Eimg (Ereg regs1 [])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E25 : ew E 25 = w64 L) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E21 : ew E 21 = w64 max) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E23 : ew E 23 = w64 tab) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (U25 : U E (SOff 25 0) = L) by (apply U_atom; [exact E25 | lia]).
assert (U23 : U E (SOff 23 0) = tab) by (apply U_atom; [exact E23 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* taken: count >= max, the table is full; 0x8a720 with s4 = -1 *)
  rewrite (vad_bge_ab E 25 21 L max E25 E21) in Hc by lia. apply Z.leb_le in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_EPI.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP1. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (20%bv : bv 5) P20.
  apply (KEEP (-1)).
  + apply vad_vlan_add_full; [exact HEX | lia].
  + apply (CUTKEPT regs1 mem1 md1 _ _ _ (sp0 - VAD_STK) (sp0 - VAD_STK) HCUT HJ); [| lia | lia | rewrite P2; apply EE; reflexivity
      | rewrite P3; apply EE; reflexivity | rewrite P4; apply EE; reflexivity].
    intros x Hx _. exact (KEEP1 x Hx).
  + rewrite P20, (EE 20%nat 20%bv eq_refl). exact R20.
- (* not taken: count < max *)
  rewrite (vad_bge_ab E 25 21 L max E25 E21) in Hc by lia. apply Z.leb_gt in Hc. rename Hc into LT.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP1. clear HF HFr HG.
  (* 0x8a624 beqz a0: tab + 18 count is not 0 *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_eq_U, (vad_d_U E tab L U23 U25 ltac:(lia) ltac:(lia) ltac:(lia)), U_SLit in Hc.
    apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  (* 0x8a638 beqz a0: the overflow test gives 1 *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_eq_U, (vad_ovf_U E tab L U23 U25 ltac:(lia) ltac:(lia) ltac:(lia)), U_SLit in Hc.
    vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP3. clear HF HFr HG.
  (* 0x8a63c .. 0x8a650: s2 = 18, a0 = tab + 18 count, a2 = 18, a1 = 0, the call of the checked memset *)
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?H ?msx) =>
    pose proof (st_ok_restrict_reg sg H Ex ssx msx (10%bv : bv 5) HS) as Q10;
    let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (10%bv : bv 5)) with e in Q10;
    cbn [ms_regs restrict mkst] in Q10 end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?mdT) _ =>
    assert (KEEPm : forall x, 0 <= x < 2 ^ 64 -> rdW W mT x = rdW W mem1 x)
      by (intros x Hx; rewrite (KEEP3 x Hx), (KEEP2 x Hx); exact (KEEP1 x Hx));
    set (rT0 := rT) in *; set (mT0 := mT) in *; set (md0 := mdT) in * end.
  clear KEEP1 KEEP2 KEEP3.
  pose proof HADD as ((_ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _) & _).
  unfold seg_spec.RVLAN_SIZE in Hb2.
  pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
  pose proof (proj1 HJ) as HARm.
  assert (P10 : getr rT0 10 = w64 VD).
  { rewrite Q10. unfold w64. rewrite <- (vad_d_U E tab L U23 U25 ltac:(lia) ltac:(lia) ltac:(lia)). unfold U.
    symmetry. apply Z_to_bv_bv_unsigned. }
  assert (HspT : spZ rT0 = sp0 + -112) by (unfold spZ at 1; rewrite P2, Usp; lia).
  assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
  assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
  eapply SRr_bind;
  [ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG SS___asan_memset) (AMEMSET fx)
      W rT0 mT0 VAD_STK sp0 FP ly S W mem md [] ly S md0 0
      VD 0 18 (-112) (Z_to_bv 64 (BASE + VAD_RMS)) HJ P10 P11 P12);
    [ lia | lia | lia | exact HspT | reflexivity | lia
    | lia | exact P3' | exact P4' | exact P1
    | apply ret_ok_codeptr_v; [unfold VAD_RMS; lia | reflexivity]
    | intros a Ha; split; [apply AWRTAB; [exact HEX | exact LT | lia] | lia]
    | intros a Ha _ [[_ Himg] | Hsp]; exfalso; [exact (T7 a ltac:(lia) Himg) | lia]
    | exact (amem_range_of_block SEGS B LAWS ly S W mT0 md0 b m VD 18 HARm Hbm ltac:(lia) ltac:(lia))
    | exact (range_addressable_of_block SEGS B LAWS ly S W mT0 md0 b m VD 18 HARm Hbm ltac:(lia) ltac:(lia))
    | intros _; exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mT0 md0 b m VD 18 HARm Hbm ltac:(lia) ltac:(lia) ltac:(lia))
    | exact I ]
  | ].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hd2 & HSET2 & HKEEP2 & HPRES2 & HMAT2).
  (* back at 0x8a654: the MSc cut *)
  assert (KM : forall x, 0 <= x < 2 ^ 64 -> ~ (VD <= x < VD + 18) -> ~ (sp0 - 112 - ESTACK <= x < sp0 - 112) ->
    rdW W mem2 x = rdW W mem1 x).
  { intros x Hx Hd Hw. rewrite (HKEEP2 x Hx Hd ltac:(lia)). exact (KEEPm x Hx). }
  assert (G2 : getr regs2 2 = getr rT0 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (G3 : getr regs2 3 = getr rT0 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (G4 : getr regs2 4 = getr rT0 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (G8 : getr regs2 8 = getr rT0 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  assert (G9 : getr regs2 9 = getr rT0 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (G18 : getr regs2 18 = getr rT0 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  assert (G19 : getr regs2 19 = getr rT0 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  assert (G20 : getr regs2 20 = getr rT0 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
  assert (G21 : getr regs2 21 = getr rT0 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (G23 : getr regs2 23 = getr rT0 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
  assert (G24 : getr regs2 24 = getr rT0 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
  assert (G25 : getr regs2 25 = getr rT0 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
  apply KMS.
  split; [split; [exact HJ2|]; split|].
  { intros j r Hr.
    assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
    apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ sp0 - 112 <= x < sp0));
      [intros x [Hx1 Hx2]; apply KM; lia | exact (HFR j r Hr) |].
    intros k Hk. cbv beta. lia. }
  { split; [rewrite G2, P2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite G3, P3, (EE 3%nat 3%bv eq_refl); exact R3 | rewrite G4, P4, (EE 4%nat 4%bv eq_refl); exact R4]. }
  split.
  { split; [rewrite G8, P8, (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite G9, P9, (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite G19, P19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite G20, P20, (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite G21, P21, (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite G23, P23, (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [rewrite G24, P24, (EE 24%nat 24%bv eq_refl); exact R24|].
    rewrite G25, P25, (EE 25%nat 25%bv eq_refl); exact R25. }
  split; [rewrite G18, P18; reflexivity|].
  split.
  { unfold vad_spill in *. intros k Hk. rewrite (KM (sp0 - 112 + Z.of_nat k)) by lia. exact (HSP k Hk). }
  split; [exact LT|]. split; [exact HEX|]. split.
  { intros x Hx Hw Hd. rewrite (KM x Hx Hd) by lia. exact (HK x Hx Hw). }
  intros k Hk. rewrite (HSET2 k Hk). reflexivity.
Qed.


End w.
End e.
End d.
End b.
