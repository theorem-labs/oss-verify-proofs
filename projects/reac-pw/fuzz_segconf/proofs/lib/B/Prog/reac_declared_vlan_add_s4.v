(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command
   (0x89ef8, 164 instructions, frame 144 bytes), ported from the ASan walk lib/A/Prog/rec_calls_equal.v (0x89968). The
   shape is the A walk's: the symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the strcmp wrapper's call stepped through by its Theorem Labs lane contract (PaArt.v
   aj_art_at), the two loops cut at their heads (0x89f98, 0x8a064) and at the outer latch (0x8a0b4), each piece re-seeded
   from the concrete state there, the loops proved by induction. What B changes:
   - the frame (144 bytes) keeps n at 0(sp), the UBSan predicates `b mod 8 = 0 && b <> 0`, `b <> 0`,
     `a mod 8 = 0 && a <> 0` at 8(sp), 16(sp), 24(sp), and b at 32(sp); a stays in a5/s11 and `a <> 0` in a4/s8;
   - the inner loop counts s5 = 8k up to s2 = 8 * nargs and forms both argument addresses from s3/s10 (a[i].args) and
     s1/s9 (b[i].args) plus s5 (the seed's alias facts name the two sums);
   - eight UBSan trap branches, all to the `unimp` at 0x8a168, are refuted from the run's facts: 0x89fac, 0x89fbc,
     0x89fe4, 0x89ff4 are decided by the executor (a4 = 1 and the three predicate slots = 1 at the outer seed, which the
     entry derives from rce_calls' `a mod 8 = 0` and rce_home's 4096 <= a; a + 56i >= 4096 by the seed's atom fact);
     0x89fb4 and 0x89fec (a + 56i < a, b + 56i < b unsigned) and 0x8a064, 0x8a068 (~(a[i].args) < 8k, ~(b[i].args) < 8k)
     are refuted at the branch from the values of their operands. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths and module names changed; 327 of its 409 lines of code are new or changed and 1510 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan-ubsan (image B), segment 4 of the walk of
   lib/B/Prog/reac_declared_vlan_add_c.v: the checked memset's return RMS 0x8a654 (BASE + VAD_RMS) .. the strncpy
   call's return RSN 0x8a698 (BASE + VAD_RSN), on the append path. Adapts the image-A seeds of
   lib/A/Prog/reac_declared_vlan_add_s0.v (commit fcd2fa03dd27; vad_st_seed / vad_store: a seed with
   the count cell's region and its shadow entry) and the wrapper call of check_declared.v (commit
   68125773e710; cd_loop_step: ecall_pre_stk_at, the parent's string facts, rt_rom_view), with the call stepped by
   PaArtOwn.aj_art_own_at (the wrapper writes footprint bytes) in place of aj_art_at. Image A has no stretch of its
   own for this: its strncpy call follows the memset call in one segment.
   The code: 0x8a654 `ld a0,0(sp)` reloads the spill (the shadow address of the count cell), `lb a0,0(a0); bnez`
   (check 3, removed by the shadow entry of [n, n + 4)), `lw a1,0(s0)` (the count L), `mul a0,a1,s2; add a0,s7,a0`
   (D = tab + 18 L), UBSan's three tests (0x8a66c beqz a0; 0x8a680 the pointer-overflow test; 0x8a688 the
   alignment test of D, each refuted at its branch: D is nonzero, tab + 18 L does not wrap and L >= 0, D is even),
   then strncpy(D, parent, 15) (0x8a694, RtSeg.astrncpy_realizes; the destination [D, D + 15) is footprint of the
   append path, inside the table block). At RSN the new entry's first 16 bytes are strncpy's 15 and the 0 memset left
   at D + 15 (reac_declared_vlan_add_lem.vad_new_entry_enc). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtString RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArtOwn.
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

(* ---------- the seed at RMS 0x8a654 ---------- *)
(* atoms 0 .. 31: the registers at RMS (s0 = n, s3 = parent, s7 = tab, s9 = L); atom 32: the shadow base SB; s2 holds
   the literal 18. Regions: the frame's lowest slot [sp0 - 112, sp0 - 104) holding the spill, the executor's shadow
   address of atom 8 (vad_shx 8), and the count cell [n, n + 4) holding atom 25; both read-only. The shadow entry of
   [n, n + 4) removes check 3; atom 8's fact (n mod 4 = 0) and atom 25's (0 <= L < 2 ^ 31) give the 4-byte load. *)
Definition vad_ms_regs : list sv := sr_set sr_atoms 18 (SLit 18).
Definition vad_msS : YP09.region := YP09.mkRegion (Some 2%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (vad_shx 8))].
Definition vad_msN : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 25 0))].
Definition vad_ss_ms : sstate := mkSS VAD_RMS vad_ms_regs [vad_msS; vad_msN] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (8%nat, mkAF 4096 (2 ^ 47 - 4) 2); (23%nat, mkAF 4096 (2 ^ 47 - 64) 4);
            (25%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] []).
Definition vad_ms_SH : list shent := [mkSHE 8 0 4].

(* the end of the word that holds the last byte strncpy reads grows with the bytes it reads *)
Lemma vad_aword_mono : forall x n n', 0 < n' <= n -> RtString.aword_end x n' <= RtString.aword_end x n.
Proof.
intros x n n' Hn. unfold RtString.aword_end.
pose proof (vad_word_end (x + n' - 1)) as A1. pose proof (vad_word_end (x + n - 1)) as A2.
replace (x + n' - 1 + 1) with (x + n') in A1 by lia. replace (x + n - 1 + 1) with (x + n) in A2 by lia.
pose proof (Z.div_mod (x + n' - 1) 8 ltac:(lia)) as D1. pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2.
pose proof (Z.div_le_mono (x + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D3.
lia.
Qed.
(* strncpy's 15 bytes in the form of vad_new_entry_enc *)
Lemma vad_pad15 : forall s : list byte,
  firstn (Z.to_nat 15) s ++ repeat (Z_to_bv 8 0) (Z.to_nat 15 - length s) =
  firstn (Nat.min (length s) 15) s ++ repeat (Z_to_bv 8 0) (15 - Nat.min (length s) 15).
Proof.
intros s. change (Z.to_nat 15) with 15%nat. rewrite vad_firstn_min_len. f_equal. f_equal. lia.
Qed.
(* the words of the UBSan tests at 0x8a664 .. 0x8a688, as the executor states them: atom 23 = tab, atom 25 = the
   count the `lw` read; a0 = tab + count * 18 (0x8a664 mul, 0x8a668 add) *)
Lemma vad_D_U : forall E tb c, U E (SOff 23 0) = tb -> U E (SOff 25 0) = c -> 0 <= tb -> 0 <= c -> tb + 18 * c < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 25 0) (SLit 18))) = tb + 18 * c.
Proof.
intros E tb c H23 H25 H0 H1 H2. rewrite U_SAlu, U_SMd, H23, H25, U_SLit. cbn [zalu_raw zmd_raw].
rewrite (zcanon_small 18) by lia. rewrite (zcanon_small (c * 18)) by lia. rewrite zcanon_small by lia. lia.
Qed.
(* 0x8a670 .. 0x8a67c: (a0 <u tab) xor (count <s 0) xor 1, the executor's slti of a count below 2 ^ 31 folded to 0:
   1 when a0 = tab + 18 count does not wrap *)
Lemma vad_ovf_U : forall E d x tb, U E d = x -> U E (SOff 23 0) = tb -> tb <= x ->
  U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU d (SOff 23 0)) (SLit 0)) (SLit 1)) = 1.
Proof.
intros E d x tb Hd H23 Hx. rewrite !U_SAlu, Hd, H23, !U_SLit. cbn [zalu_raw].
replace (x <? tb) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* 0x8a684: a0 & 1, 0 when a0 = tab + 18 count with tab mod 16 = 0 *)
Lemma vad_odd_U : forall E d x, U E d = x -> x mod 2 = 0 -> U E (SAlu ALU_AND d (SLit 1)) = 0.
Proof.
intros E d x Hd Hx. rewrite U_and_lit by lia. rewrite Hd. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. exact Hx.
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
(* the read premise of a runtime entry over a prefix of a range it may read *)
Lemma vad_aread_sub : forall stk (W : world SEGS) regs mem x k k', aread_ok SEGS stk W regs mem x k -> 0 <= k' <= k ->
  aread_ok SEGS stk W regs mem x k'.
Proof using.
intros stk W regs mem x k k' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hk. unfold aread_ok.
split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|]. split; [apply (range_addressable_sub _ _ x k); [exact H5 | lia | lia]|].
intros Hp s Hs. apply (H6 ltac:(lia)). split; [lia|].
unfold shadow_addr in *.
assert (Hm : (SHADOW_OFF + (x + k' - 1) / 8) / 8 <= (SHADOW_OFF + (x + k - 1) / 8) / 8).
{ apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
(* the strncpy wrapper at its trampoline (the image-A wrapper interface, row 12; image B's copy lib/B/Rt/RtSeg.v) *)
Hypothesis ASTRNCPY : forall fx0 : YK11.FPState, @astrncpy_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncpy).
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

(* ---------- the seed at RMS (0x8a654) ---------- *)
Lemma vad_ms_seed : forall regs1 mem1,
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 8 = w64 n -> getr regs1 18 = w64 18 -> getr regs1 23 = w64 tab ->
getr regs1 25 = w64 L ->
spill (rdW W mem1) -> sa_val (rdW W mem1) n 4 L -> range_addressable (rdW W mem1) SHADOW_OFF n 4 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB]))) vad_ss_ms
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_RMS)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_ms_SH (Eimg (Ereg regs1 (map w64 [SB]))) (mrestrict (w_H W) mem1).
Proof using HPRE HADD.
intros regs1 mem1 R2 R8 R18 R23 R25 SPL VN RAN.
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & _). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof vad_STK_val as HST.
set (E := Eimg (Ereg regs1 (map w64 [SB]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32. cbn [nth Nat.add] in E32. fold E in E32.
assert (E8 : ew E 8 = w64 n) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E8u : bv_unsigned (ew E 8) = n) by (rewrite E8; apply unsigned_lit_small; lia).
assert (E23u : bv_unsigned (ew E 23) = tab) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (E25u : bv_unsigned (ew E 25) = L) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold vad_ss_ms. apply pa_entry_st_ok_full.
  + vad_regs_ok EE idtac.
  + vm_compute. reflexivity.
  + unfold vad_msS, vad_msN. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (sp0 - 112) 0 8 (vad_shx 8) (SB + n / 8)).
      -- rewrite (vad_shx_U E 8 n E32 E8) by lia. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold SB. lia.
      -- cbn. lia.
      -- rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact SPL.
    * rewrite E8u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ n 0 4 (SOff 25 0) L); [cbn [sv_denot]; rewrite E25u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact VN.
  + apply pairwise_disjoint_of_extents. unfold vad_msS, vad_msN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E8u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E8u, E23u, E25u. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | assumption].
- unfold sh_ok, vad_ms_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 8 n 0 4 E32 E8u); try lia.
  + rewrite Z.add_0_r. exact RAN.
  + intros y Hy. apply N5. lia.
Qed.

(* ---------- RMS (0x8a654) .. RSN (0x8a698) ---------- *)
Lemma vad_ms : forall regs1 mem1 md1,
(forall r m d, SNc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_RSN)) m (seg_rom SEGS)) d) Q) ->
MSc regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_RMS)) mem1 (seg_rom SEGS)) md1) Q.
Proof using HPRE HROD HADD ASTRNCPY.
intros regs1 mem1 md1 KSN (HCE & HRG & R18 & SPL & LT & HEX & HK1 & HZ).
pose proof HCE as (HJ & HFR & R2 & R3 & R4).
pose proof HRG as (R8 & R9 & R19 & R20 & R21 & R23 & R24 & R25).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof SP0 as (Hal16 & Hslo & Hshi & HAC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof HADD as ((_ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _ & _ & _ & _ & HNV & _ & HNA & _) & _ & HSTR & _ & _ & _ & _ & _ & Hvid).
unfold seg_spec.RVLAN_SIZE in Hb2.
pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
assert (HKP : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0) /\ ~ (VD <= x < VD + 18)) -> rdW W mem1 x = rdW W mem x)
  by (intros x (Hx1 & Hx2 & Hx3); exact (HK1 x Hx1 Hx2 Hx3)).
assert (VN1 : sa_val (rdW W mem1) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKP HNV); intros i Hi; cbv beta; lia).
assert (RAN1 : range_addressable (rdW W mem1) SHADOW_OFF n 4).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKP).
  - destruct HNA as (_ & _ & _ & HRAn & _). exact HRAn.
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | unfold SB; lia]. }
destruct (vad_ms_seed regs1 mem1 R2 R8 R18 R23 R25 SPL VN1 RAN1) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32. cbn [nth Nat.add] in E32.
remember (Eimg (Ereg regs1 (map w64 [SB]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
(* 0x8a654 .. 0x8a680: the spill reloaded, check 3 (removed by the shadow entry of [n, n + 4)), lw count (atom 25),
   a0 := tab + count * 18; 0x8a66c beqz a0 (UBSan: a0 = 0) is decided not taken by the executor from the facts of
   atoms 23 and 25 (tab >= 4096, 0 <= count < 2 ^ 31); the run stops at 0x8a680 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
vad_md.
vad_keep_empty HFr KEEP1. clear HF HFr HG.
(* 0x8a680 beqz a1 (UBSan's pointer-overflow test) to the trap 0x8a760: a1 = 1, tab + 18 L does not wrap *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U in Hc.
  lazymatch type of Hc with context [U ?Ex (SAlu _ _ _)] =>
    assert (U23 : U Ex (SOff 23 0) = tab) by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]);
    assert (U25 : U Ex (SOff 25 0) = L) by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia]) end.
  pose proof (vad_D_U _ _ _ U23 U25 ltac:(lia) ltac:(lia) ltac:(lia)) as UD.
  rewrite (vad_ovf_U _ _ _ _ UD U23 ltac:(lia)), U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
vad_md.
vad_keep_empty HFr KEEP2. clear HF HFr HG.
(* 0x8a688 bnez a1 (UBSan's alignment test of D) to the trap 0x8a760: D is even *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ne_U in Hc.
  lazymatch type of Hc with context [U ?Ex (SAlu _ _ _)] =>
    assert (U23 : U Ex (SOff 23 0) = tab) by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]);
    assert (U25 : U Ex (SOff 25 0) = L) by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia]) end.
  pose proof (vad_D_U _ _ _ U23 U25 ltac:(lia) ltac:(lia) ltac:(lia)) as UD.
  assert (Hev : (tab + 18 * L) mod 2 = 0) by lia.
  rewrite (vad_odd_U _ _ _ UD Hev), U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
vad_md.
vad_keep_empty HFr KEEP3. clear HF HFr HG.
(* 0x8a68c .. 0x8a694: a2 := 15, a1 := parent, the call of the strncpy wrapper *)
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KEEPc : forall x, 0 <= x < 2 ^ 64 -> rdW W mT0 x = rdW W mem1 x)
  by (intros x Hx; rewrite (KEEP3 x Hx), (KEEP2 x Hx), (KEEP1 x Hx); reflexivity).
clear KEEP1 KEEP2 KEEP3.
assert (HKc : forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - VAD_STK <= y < sp0) -> ~ (tab <= y < tab + 18 * (max + 1)) ->
  rdW W mT0 y = rdW W mem y).
{ intros y Hy1 Hy2 Hy3. rewrite (KEEPc y Hy1). apply HK1; [exact Hy1 | exact Hy2 | lia]. }
assert (HspT : spZ rT0 = sp0 + -112) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (U23 : U E (SOff 23 0) = tab) by (apply U_atom; [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]).
assert (U25 : U E (SOff 25 0) = L) by (apply U_atom; [rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia]).
pose proof (vad_D_U _ _ _ U23 U25 ltac:(lia) ltac:(lia) ltac:(lia)) as UD.
assert (P10' : getr rT0 10 = w64 VD).
{ rewrite P10. transitivity (sv_denot E (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 25 0) (SLit 18)))).
  - cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
  - rewrite denot_lit_U, UD. reflexivity. }
assert (P11' : getr rT0 11 = w64 par) by (rewrite P11, (EE 19%nat 19%bv eq_refl); exact R19).
assert (P12' : getr rT0 12 = w64 15) by (rewrite P12; reflexivity).
(* the premises of RtSeg.astrncpy_realizes at the call state *)
destruct (PARCALL mT0 rT0 HKc ltac:(lia)) as (Hp0 & STRp & LENp & RDp & TLp & AMp & Hp32 & HpAC & HDJp).
pose proof (proj1 HJ) as HARc.
assert (WRc : awrite_ok SEGS B (2 * ESTACK) ly S W rT0 mT0 VD 15)
  by (apply (awrite_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W mT0 _ rT0 b m VD 15 HARc Hbm); lia).
assert (AMD : amem_range VD (15 + 8))
  by (apply (amem_range_of_block SEGS B LAWS ly S W mT0 _ b m VD (15 + 8) HARc Hbm); lia).
assert (NROM : forall a, VD <= a < VD + 15 -> a < kLowMemEnd -> ~ in_rom SEGS a).
{ intros a Ha _ (sg & Hsg & Hw & Hr). apply (T7 a); [lia|]. exists sg. split; [exact Hsg | exact Hr]. }
assert (DJ : VD + 15 <= par \/ RtString.aword_end par (Z.min 15 (astr_len (seg_spec.zb p) + 1)) <= VD).
{ rewrite LENp. destruct HDJp as [Hl | Hr]; [right | left; lia].
  pose proof (vad_aword_mono par (Z.of_nat (length p) + 1) (Z.min 15 (Z.of_nat (length p) + 1)) ltac:(lia)) as HM.
  unfold seg_spec.cstr_span in Hl. unfold RtString.aword_end in HM |- *. lia. }
assert (ROMc : rt_rom_view SEGS B W mT0).
{ apply ROMAT. intros x Hx. destruct (IMGOUT x Hx) as (I1 & I2 & I3 & _). exact (HKc x I1 I2 I3). }
eapply SRr_bind.
{ eapply (aj_art_own_at SEGS B LAWS pa_segs_low (2 * ESTACK) (fun a => VD <= a < VD + 15)
    (SIG SS___interceptor_trampoline_strncpy) W rT0 mT0 VAD_STK sp0 FP ly S W mem md [] ly S _ 0 (-112)
    (Z_to_bv 64 (BASE + VAD_RSN)) _ HJ HspT eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1
    (fun a Ha => AWRTAB a HEX LT ltac:(cbv beta in Ha; lia))).
  apply (ASTRNCPY fx ly S W rT0 mT0 _ VD par 15 (seg_spec.zb p)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) VAD_STK sp0 FP ly S W mem md [] ly S W mT0 _ 0 rT0 (-112)
      HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'.
  - exact P11'.
  - exact P12'.
  - lia.
  - lia.
  - exact Hp0.
  - exact STRp.
  - apply (vad_aread_sub (2 * ESTACK) W rT0 mT0 par (Z.of_nat (length p) + 1)); [exact RDp | rewrite LENp; lia].
  - rewrite LENp. exact AMp.
  - exact WRc.
  - exact AMD.
  - exact NROM.
  - rewrite LENp. exact TLp.
  - exact DJ.
  - exact ROMc. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at RSN 0x8a698: the SNc cut *)
assert (KM2 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - 112 - 2 * ESTACK <= x < sp0 - 112) -> ~ (VD <= x < VD + 15) ->
  rdW W mem2 x = rdW W mem1 x).
{ intros x Hx Hw He. rewrite (HK2 x Hx ltac:(lia) He). exact (KEEPc x Hx). }
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
destruct (sa_strz_bytes SEGS (w_H W) mem par p (proj1 HSTR)) as (_ & _ & ZB).
assert (NZ : ~ In 0 p) by exact (proj2 (proj1 HSTR)).
assert (KF : forall x, (0 <= x < 2 ^ 64 /\ sp0 - 112 <= x /\ ~ (VD <= x < VD + 15)) -> rdW W mem2 x = rdW W mem1 x).
{ intros x (Hx1 & Hx2 & Hx3). apply KM2; [exact Hx1 | rewrite Hes; lia | exact Hx3]. }
apply KSN.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [exact HJ2|]. split.
  + intros j r Hr.
    assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
    apply (vad_sa_val_keep (rdW W mem1) _ _ _ _ _ KF (HFR j r Hr)).
    intros k Hk. cbv beta. lia.
  + split; [rewrite G2, P2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite G3, P3, (EE 3%nat 3%bv eq_refl); exact R3 | rewrite G4, P4, (EE 4%nat 4%bv eq_refl); exact R4].
- split; [rewrite G8, P8, (EE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite G9, P9, (EE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite G19, P19, (EE 19%nat 19%bv eq_refl); exact R19|].
  split; [rewrite G20, P20, (EE 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite G21, P21, (EE 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite G23, P23, (EE 23%nat 23%bv eq_refl); exact R23|].
  split; [rewrite G24, P24, (EE 24%nat 24%bv eq_refl); exact R24|].
  rewrite G25, P25, (EE 25%nat 25%bv eq_refl); exact R25.
- rewrite G18, P18. reflexivity.
- apply (vad_sa_val_keep (rdW W mem1) _ _ _ _ _ KF SPL).
  intros k Hk. cbv beta. lia.
- exact LT.
- exact HEX.
- intros x Hx Hw Hd. rewrite (KM2 x Hx ltac:(lia) ltac:(lia)). exact (HK1 x Hx Hw Hd).
- assert (L15 : length (firstn (Nat.min (length (seg_spec.zb p)) 15) (seg_spec.zb p) ++
    repeat (Z_to_bv 8 0) (15 - Nat.min (length (seg_spec.zb p)) 15)) = 15%nat)
    by (rewrite length_app, length_firstn, repeat_length; lia).
  exists ((firstn (Nat.min (length (seg_spec.zb p)) 15) (seg_spec.zb p) ++
    repeat (Z_to_bv 8 0) (15 - Nat.min (length (seg_spec.zb p)) 15)) ++ [Z_to_bv 8 0]).
  split; [rewrite length_app, L15; reflexivity|].
  split.
  + apply vad_sa_bytes_app. split.
    * rewrite <- vad_pad15. intros i Hi. exact (proj2 HQ2 i Hi).
    * rewrite L15. intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
      cbn [nth]. replace (VD + Z.of_nat 15 + Z.of_nat 0) with (VD + 15) by lia.
      rewrite (KM2 (VD + 15) ltac:(lia) ltac:(lia) ltac:(lia)), (HZ 15 ltac:(lia)). reflexivity.
  + pose proof (vad_new_entry_enc (seg_spec.zb p) p vid ZB NZ Hvid) as ENC. rewrite app_assoc in ENC. exact ENC.
Qed.


End w.
End e.
End d.
End b.
