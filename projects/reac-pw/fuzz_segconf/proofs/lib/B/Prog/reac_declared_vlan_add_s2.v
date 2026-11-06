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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths and module names changed; 459 of its 542 lines of code are new or changed and 1509 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan-ubsan (image B), segment 2 of the walk of
   lib/B/Prog/reac_declared_vlan_add_c.v: the search loop. It ports the loop-head seed, the latch seed and the latch
   of image A's lib/A/Prog/reac_declared_vlan_add_s0.v (commit fcd2fa03dd27: vad_lh_seed,
   vad_lt_seed, vad_latch) and the loop body with the strcmp wrapper call of image A's lib/A/Prog/check_declared.v
   (commit 68125773e710: cd_loop_step, cd_loop_seed, cd_str_call, cd_rom_at), with image B's
   UBSan tests refuted as image B's check_segments walk refutes its own (commit 165b110a4242).
   - vad_loop_step, the loop head 0x8a5b8 at entry i (cut vad_LHc i of segment 0): `beqz s2` (decided by the
     executor: s2 = tab + 18 i >= 4096), `bltu s2,s7` to the UBSan trap 0x8a760 (refuted: tab + 18 i does not wrap
     below tab), `bnez s10` (decided: s10 = tab & 1 = 0), check 2 (removed by the token of [tab + 18 i, + 18)),
     lhu tab[i].vid, `bne a0,s1`: taken -> the latch 0x8a5f0 (entry i's vid differs, so it does not match); not
     taken -> the strcmp wrapper on entry i's parent string and the parent (RtString.astrcmp_realizes), then
     `beqz a0`: taken -> the two parents are one string, entry i matches, SegModel.vlan_add returns (0, t), and
     0x8a71c `li s4,0` reaches the epilogue (segment 0's vad_keep); not taken -> the latch (vad_LTc i).
   - vad_latch, the latch 0x8a5f0 (cut vad_LTc i): s11 -= 1, s2 += 18, s6 += 18, `bnez s11` -> the loop head at
     entry i + 1 (vad_LHc (i + 1)), else `j 0x8a614` -> after the search (vad_AFTc). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtString.
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

(* the loop head at entry i: atom 32 = SB, 33 = tab + 18 i (s2 and s6), 34 = tab (s7), 35 = tab[i].vid, 36 = the
   entries left, length t - i (s11); s10 = tab & 1 = 0. The region of entry i holds its vid at offset 16; the shadow
   token covers the entry's 18 bytes. *)
Definition vad_lh_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 18 (SOff 33 0)) 22 (SOff 33 0)) 23 (SOff 34 0))
    26 (SLit 0)) 27 (SOff 36 0).
Definition vad_entryR : YP09.region := YP09.mkRegion (Some 33%nat) 0 18 0 0 [YP09.mkChunk 16 (CVal 2 (SOff 35 0))].
Definition vad_ss_lh : sstate := mkSS VAD_LH vad_lh_regs [vad_entryR] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, vad_PTRF); (34%nat, vad_PTRF); (35%nat, mkAF 0 65535 0);
            (36%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] []).
Definition vad_lh_SH : list shent := [mkSHE 33 0 18].
(* the latch at entry i: atom 32 = SB, 33 = tab + 18 i (s2 and s6), 34 = length t - i (s11) *)
Definition vad_lt_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 18 (SOff 33 0)) 22 (SOff 33 0)) 27 (SOff 34 0).
Definition vad_ss_lt : sstate := mkSS VAD_LT vad_lt_regs [] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, vad_PTRF); (34%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] []).

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
(* the strcmp wrapper (lib/B/Rt/RtString.v astrcmp_realizes), at the listing's call target, at every FP state *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
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

(* ---------- the seed at the loop head (0x8a5b8), entry i ---------- *)
Lemma vad_lh_seed : forall (i : nat) vi regs1 mem1,
(i < length t)%nat -> 0 <= vi < 65536 ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 24 = w64 SB ->
getr regs1 18 = w64 (tab + 18 * Z.of_nat i) -> getr regs1 22 = w64 (tab + 18 * Z.of_nat i) ->
getr regs1 23 = w64 tab -> getr regs1 26 = w64 0 -> getr regs1 27 = w64 (L - Z.of_nat i) ->
sa_val (rdW W mem1) (tab + 18 * Z.of_nat i + 16) 2 vi ->
range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * Z.of_nat i) 18 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; tab; vi; L - Z.of_nat i]))) vad_ss_lh
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_LH)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_lh_SH (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; tab; vi; L - Z.of_nat i])))
  (mrestrict (w_H W) mem1).
Proof using HPRE HADD LAWS.
intros i vi regs1 mem1 Hi Hvi R2 R24 R18 R22 R23 R26 R27 VV RA.
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & _).
pose proof vad_STK_val as HST.
set (X := tab + 18 * Z.of_nat i) in *.
assert (HX : tab <= X /\ X + 18 <= tab + 18 * max) by (subst X; lia).
set (E := Eimg (Ereg regs1 (map w64 [SB; X; tab; vi; L - Z.of_nat i]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 3 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E35.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 4 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E36.
cbn [nth Nat.add] in E32, E33, E34, E35, E36. fold E in E32, E33, E34, E35, E36.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = X) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = tab) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = vi) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = L - Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold vad_ss_lh. apply pa_entry_st_ok_full.
  + vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u, ?E36u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vad_entryR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E33u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ X 16 2 (SOff 35 0) vi); [cbn [sv_denot]; rewrite E35u, Z.add_0_r; try reflexivity | cbn; lia | cbn; lia |].
    apply vad_val_mem_of_sa. exact VV.
  + cbn. tauto.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_PTRF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u, E35u, E36u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
- unfold sh_ok, vad_lh_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 33 X 0 18 E32 E33u); try lia.
  + rewrite Z.add_0_r. exact RA.
  + intros y Hy. apply T5. lia.
Qed.

(* ---------- the seed at the latch (0x8a5f0), entry i ---------- *)
Lemma vad_lt_seed : forall (i : nat) regs1 mem1,
(i < length t)%nat ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 24 = w64 SB ->
getr regs1 18 = w64 (tab + 18 * Z.of_nat i) -> getr regs1 22 = w64 (tab + 18 * Z.of_nat i) ->
getr regs1 27 = w64 (L - Z.of_nat i) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; L - Z.of_nat i]))) vad_ss_lt
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_LT)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx [] (Eimg (Ereg regs1 (map w64 [SB; tab + 18 * Z.of_nat i; L - Z.of_nat i]))) (mrestrict (w_H W) mem1).
Proof using HPRE HADD LAWS.
intros i regs1 mem1 Hi R2 R24 R18 R22 R27.
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & _).
pose proof vad_STK_val as HST.
set (X := tab + 18 * Z.of_nat i) in *.
assert (HX : tab <= X /\ X + 18 <= tab + 18 * max) by (subst X; lia).
set (E := Eimg (Ereg regs1 (map w64 [SB; X; L - Z.of_nat i]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; X; L - Z.of_nat i] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; X; L - Z.of_nat i] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; X; L - Z.of_nat i] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34. fold E in E32, E33, E34.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = X) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L - Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold vad_ss_lt. apply pa_entry_st_ok_full.
- vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u).
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_PTRF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
Qed.

(* ---------- the latch: 0x8a5f0 .. 0x8a5fc, then the loop head or 0x8a614 ---------- *)
Lemma vad_latch : forall i regs1 mem1 md1,
((Datatypes.S i < length t)%nat -> forall r m d, LHc (Datatypes.S i) r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LH)) m (seg_rom SEGS)) d) Q) ->
(forall r m d, AFTc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_AFT)) m (seg_rom SEGS)) d) Q) ->
LTc i regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_LT)) mem1 (seg_rom SEGS)) md1) Q.
Proof using HPRE HADD LAWS.
intros i regs1 mem1 md1 KLH KAFT (HCUT & (R8 & R9 & R19 & R20 & R21 & R23 & R24 & R25) & HSP & Hi & HEX & R18 & R22 & R26 & R27).
pose proof HCUT as ((HJ & HFR & R2 & R3 & R4) & HK).
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & _).
pose proof vad_STK_val as HST.
destruct (vad_lt_seed i regs1 mem1 Hi R2 R24 R18 R22 R27) as [HS SHOK].
set (X := tab + 18 * Z.of_nat i) in *.
assert (HX : tab <= X /\ X + 18 <= tab + 18 * max) by (subst X; lia).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; X; L - Z.of_nat i])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; X; L - Z.of_nat i]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; X; L - Z.of_nat i] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; X; L - Z.of_nat i] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; X; L - Z.of_nat i] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34.
remember (Eimg (Ereg regs1 (map w64 [SB; X; L - Z.of_nat i]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = X) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L - Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KEEP1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s11 - 1 <> 0: the loop head at entry i + 1 *)
  assert (HiN : (Datatypes.S i < length t)%nat).
  { rewrite branch_ne_U, U_SOff, U_SLit, E34u in Hc. change (zcanon 0) with 0 in Hc.
    rewrite zcanon_small in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_LH.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KF : vad_kept (rdW W mem1) (rdW W mF) (sp0 - VAD_STK) (sp0 - VAD_STK))
      by (intros x0 Hx0 _; rewrite (KEEP2 x0 Hx0); exact (KEEP1 x0 Hx0)) end.
  apply (KLH HiN). split; [|split; [|split; [|split; [exact HiN|]]]].
  + apply (CUTKEPT regs1 mem1 md1 _ _ _ (sp0 - VAD_STK) (sp0 - VAD_STK) HCUT HJ KF); [lia | lia | rewrite P2; apply EE; reflexivity
      | rewrite P3; apply EE; reflexivity | rewrite P4; apply EE; reflexivity].
  + split; [rewrite P8; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite P9; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite P19; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite P20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite P21; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite P23; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [rewrite P24; exact E32|].
    rewrite P25; rewrite (EE 25%nat 25%bv eq_refl); exact R25.
  + exact (SPILLKEPT mem1 _ _ _ HSP KF ltac:(lia)).
  + split; [exact HEX|].
    split; [rewrite P18, E33u; unfold w64; f_equal; subst X; lia|].
    split; [rewrite P22, E33u; unfold w64; f_equal; subst X; lia|].
    split; [rewrite P26; rewrite (EE 26%nat 26%bv eq_refl); exact R26|].
    rewrite P27, E34u. unfold w64. f_equal. lia.
- (* s11 - 1 = 0: the search is done, no entry matched; 0x8a614 *)
  assert (HiN : Datatypes.S i = length t).
  { rewrite branch_ne_U, U_SOff, U_SLit, E34u in Hc. change (zcanon 0) with 0 in Hc.
    rewrite zcanon_small in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_AFT.
  { awr_ok_tac; exact Usp. }
  vad_md.
  vad_keep_empty HFr KEEP2. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KF : vad_kept (rdW W mem1) (rdW W mF) (sp0 - VAD_STK) (sp0 - VAD_STK))
      by (intros x0 Hx0 _; rewrite (KEEP2 x0 Hx0); exact (KEEP1 x0 Hx0)) end.
  apply KAFT. split; [|split; [|split]].
  + apply (CUTKEPT regs1 mem1 md1 _ _ _ (sp0 - VAD_STK) (sp0 - VAD_STK) HCUT HJ KF); [lia | lia | rewrite P2; apply EE; reflexivity
      | rewrite P3; apply EE; reflexivity | rewrite P4; apply EE; reflexivity].
  + split; [rewrite P8; rewrite (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite P9; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite P19; rewrite (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite P20; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite P21; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
    split; [rewrite P23; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [rewrite P24; exact E32|].
    rewrite P25; rewrite (EE 25%nat 25%bv eq_refl); exact R25.
  + exact (SPILLKEPT mem1 _ _ _ HSP KF ltac:(lia)).
  + rewrite HEX. apply vad_existsb_skipn_all. lia.
Qed.

(* ---------- the search loop's body: 0x8a5b8 .. 0x8a5ec, then the latch or the duplicate's exit ---------- *)
Lemma vad_loop_step : forall i regs1 mem1 md1,
(forall r m d, LTc i r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LT)) m (seg_rom SEGS)) d) Q) ->
LHc i regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_LH)) mem1 (seg_rom SEGS)) md1) Q.
Proof using HPRE HROD HADD TL ASTRCMP LAWS.
intros i regs1 mem1 md1 KLT (HCUT & (R8 & R9 & R19 & R20 & R21 & R23 & R24 & R25) & HSP & Hi & HEX & R18 & R22 & R26 & R27).
pose proof HCUT as ((HJ & HFR & R2 & R3 & R4) & HK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof SP0 as (Hal16 & Hslo & Hshi & HACm). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_STK_val as HST. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
pose proof HADD as ((_ & _ & HRT & _ & (bk & mk & Hbm & Hb1 & Hb2) & (_ & _ & _ & ARA & _) & _) & _ & HSTR & _ & _ & _ & _ & _ & Hvid).
unfold seg_spec.RVLAN_SIZE in Hb2, ARA.
pose proof (req_size_pos mk ltac:(lia)) as [_ Hreq].
destruct (sa_strz_bytes SEGS (w_H W) mem par p (proj1 HSTR)) as (_ & HN0 & HZ).
destruct HRT as (bt & HBT & HET).
destruct (vad_rtab_entry _ tab t bt i HBT HET Hi) as (VT & RV & sx & BX & ZX & NX & LX).
set (vi := snd (nth i t ([], 0))) in *.
assert (HX0 : tab <= tab + 18 * Z.of_nat i /\ tab + 18 * Z.of_nat i + 18 <= tab + 18 * max) by lia.
(* entry i's vid and the shadow of its 18 bytes at the loop head *)
assert (VT1 : sa_val (rdW W mem1) (tab + 18 * Z.of_nat i + 16) 2 vi).
{ apply (vad_sa_val_keep (rdW W mem) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0)) _ _ _
    (fun x Hx => HK x (proj1 Hx) (proj2 Hx)) VT).
  intros k Hk. cbv beta. lia. }
assert (RA1 : range_addressable (rdW W mem1) SHADOW_OFF (tab + 18 * Z.of_nat i) 18).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (sp0 - VAD_STK) sp0); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ tab (18 * max)); [exact ARA | lia | lia]. }
destruct (vad_lh_seed i vi regs1 mem1 Hi RV R2 R24 R18 R22 R23 R26 R27 VT1 RA1) as [HS SHOK].
set (X := tab + 18 * Z.of_nat i) in *.
assert (HX : 4096 <= X /\ tab <= X /\ X + 18 <= tab + 18 * max) by lia.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; X; tab; vi; L - Z.of_nat i])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (Eimg (Ereg regs1 (map w64 [SB; X; tab; vi; L - Z.of_nat i]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 3 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E35.
pose proof (vad_ex_w64 regs1 [SB; X; tab; vi; L - Z.of_nat i] 4 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E36.
cbn [nth Nat.add] in E32, E33, E34, E35, E36.
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. pose proof (EE 9%nat 9%bv eq_refl) as E9. pose proof (EE 19%nat 19%bv eq_refl) as E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. pose proof (EE 21%nat 21%bv eq_refl) as E21.
pose proof (EE 25%nat 25%bv eq_refl) as E25.
remember (Eimg (Ereg regs1 (map w64 [SB; X; tab; vi; L - Z.of_nat i]))) as E eqn:HE0. clear HE0.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = X) by (apply U_atom; [exact E33 | lia]).
assert (U34 : U E (SOff 34 0) = tab) by (apply U_atom; [exact E34 | lia]).
assert (U35 : U E (SOff 35 0) = vi) by (apply U_atom; [exact E35 | lia]).
assert (U9 : U E (SOff 9 0) = vid) by (apply U_atom; [rewrite E9, R9; reflexivity | lia]).
(* 0x8a5b8 `beqz s2` is decided by the executor (atom 33 >= 4096); the run stops at 0x8a5bc *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KEEPa. clear HF HFr HG.
(* 0x8a5bc `bltu s2,s7` -> the UBSan trap 0x8a760: refuted, tab + 18 i >= tab *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, U33, U34 in Hc. apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x8a5c0 `bnez s10` (s10 = 0), check 2 (the token of [tab + 18 i, + 18)), lhu tab[i].vid; the run stops at
   0x8a5dc `bne a0,s1` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KEEPb. clear HF HFr HG.
(* check 2's token atoms extend the environment above the seed's atoms *)
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (OLDt : forall k, (k < 1024)%nat -> ew E2 k = ew E k) by (intros k Hk; rewrite ?ew_ewset_other by lia; reflexivity);
  remember E2 as Et eqn:HEt end.
clear HEt.
assert (Uspt : bv_unsigned (ew Et 2) = sp0 - 112) by (rewrite OLDt by lia; exact Usp).
assert (U35t : U Et (SOff 35 0) = vi) by (apply U_atom; [rewrite OLDt by lia; exact E35 | lia]).
assert (U9t : U Et (SOff 9 0) = vid) by (apply U_atom; [rewrite OLDt, E9, R9 by lia; reflexivity | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* entry i's vid differs: entry i does not match; the latch *)
  assert (Hne : vi <> vid) by (rewrite branch_ne_U, U35t, U9t in Hc; apply negb_true_iff, Z.eqb_neq in Hc; exact Hc).
  assert (HM : vad_match vid p (nth i t ([], 0)) = false).
  { unfold vad_match. change (snd (nth i t ([], 0))) with vi. rewrite (proj2 (Z.eqb_neq vi vid) Hne). reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_LT.
  { awr_ok_tac; exact Uspt. }
  vad_md.
  vad_keep_empty HFr KEEPd. clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite ?OLDt in P2, P3, P4, P8, P9, P18, P19, P20, P21, P22, P23, P24, P25, P27 by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KF : vad_kept (rdW W mem1) (rdW W mF) (sp0 - VAD_STK) (sp0 - VAD_STK))
      by (intros x0 Hx0 _; rewrite (KEEPd x0 Hx0), (KEEPb x0 Hx0); exact (KEEPa x0 Hx0)) end.
  apply KLT. split; [|split; [|split; [|split; [exact Hi|]]]].
  + apply (CUTKEPT regs1 mem1 md1 _ _ _ (sp0 - VAD_STK) (sp0 - VAD_STK) HCUT HJ KF);
      [lia | lia | rewrite P2; exact E2 | rewrite P3; exact E3 | rewrite P4; exact E4].
  + split; [rewrite P8, E8; exact R8|]. split; [rewrite P9, E9; exact R9|].
    split; [rewrite P19, E19; exact R19|]. split; [rewrite P20, E20; exact R20|].
    split; [rewrite P21, E21; exact R21|]. split; [rewrite P23; exact E34|].
    split; [rewrite P24; exact E32|]. rewrite P25, E25; exact R25.
  + exact (SPILLKEPT mem1 _ _ _ HSP KF ltac:(lia)).
  + split; [rewrite HEX, (vad_existsb_skipn_S (vad_match vid p) t i ([], 0) Hi), HM; reflexivity|].
    split; [rewrite P18; exact E33|]. split; [rewrite P22; exact E33|].
    split; [rewrite P26; reflexivity|]. rewrite P27; exact E36.
- (* entry i's vid is vid: the call of the strcmp wrapper on entry i's parent string and the parent *)
  assert (Heq : vi = vid) by (rewrite branch_ne_U, U35t, U9t in Hc; apply negb_false_iff, Z.eqb_eq in Hc; exact Hc).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Uspt. }
  vad_md.
  vad_keep_empty HFr KEEPc0. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  rewrite ?OLDt in P2, P3, P4, P10, P11 by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
    set (rT0 := rT) in *; set (mT0 := mT) in * end.
  assert (KEEPc : vad_kept (rdW W mem) (rdW W mT0) (sp0 - VAD_STK) sp0).
  { intros x0 Hx0 Hn0. rewrite (KEEPc0 x0 Hx0), (KEEPb x0 Hx0), (KEEPa x0 Hx0). exact (HK x0 Hx0 Hn0). }
  assert (HspT : spZ rT0 = sp0 + -112) by (unfold spZ at 1; rewrite P2, Usp; lia).
  assert (HspT' : spZ rT0 = sp0 - 112) by lia.
  assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
  assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
  assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (P10' : getr rT0 10 = w64 X) by (rewrite P10; exact E33).
  assert (P11' : getr rT0 11 = w64 par) by (rewrite P11, E19; exact R19).
  (* entry i's parent string at the call: in the table block, below the stack window *)
  assert (STRa : astr_at SEGS W mT0 X sx).
  { split; [|exact NX]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    rewrite (KEEPc (X + Z.of_nat j)) by lia. apply BX. rewrite length_app. cbn [length]. lia. }
  assert (RDa : aread_ok SEGS (2 * ESTACK) W rT0 mT0 X (astr_len sx + 1)).
  { unfold astr_len.
    apply (aread_ok_kept SEGS 0 (2 * ESTACK) W regs rT0 mem mT0 (sp0 - VAD_STK) sp0 X _ KEEPc);
      [| lia | lia | lia | rewrite HspT, Hes; lia | lia].
    apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md bk mk X _ HAR Hbm); lia. }
  assert (TLa : atail_vis SEGS W mT0 (X + astr_len sx)).
  { unfold astr_len.
    assert (Hxe : 0 <= X + Z.of_nat (length sx) < alloc_ceiling) by lia.
    pose proof (tail_below _ _ Hxe HACm) as HTB0.
    apply (atail_vis_kept SEGS W mem mT0 (sp0 - VAD_STK) sp0 _ KEEPc); [| lia | lia | lia].
    intros a Ha. apply (AR_block_word_vis SEGS B ly S W mem md bk mk (X + Z.of_nat (length sx)) a HAR Hbm); lia. }
  (* the parent at the call (segment 0's vad_par_call) and the image bytes the wrapper reads *)
  destruct (PARCALL mT0 rT0 (fun y Hy Hw _ => KEEPc y Hy Hw) HspT')
    as (Hpar0 & STRb & LENb & RDb & TLb & _ & _ & _ & _).
  assert (ROM : rt_rom_view SEGS B W mT0).
  { apply ROMAT. intros a Ha. destruct (IMGOUT a Ha) as (Ha0 & Haw & _). exact (KEEPc a Ha0 Haw). }
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) (SIG SS___interceptor_trampoline_strcmp)
      W rT0 mT0 VAD_STK sp0 FP ly S W mem md [] ly S _ 0 (-112) (Z_to_bv 64 (BASE + VAD_RCMP)) _ HJ HspT eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
    apply (ASTRCMP fx ly S W rT0 mT0 _ X par sx (seg_spec.zb p)).
    - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) VAD_STK sp0 FP ly S W mem md [] ly S W mT0 _ 0 rT0 (-112)
        HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
    - exact P10'. - exact P11'. - lia. - exact Hpar0.
    - exact STRa. - exact STRb. - exact RDa. - rewrite LENb. exact RDb. - exact TLa. - rewrite LENb. exact TLb.
    - exact ROM. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
  (* back at 0x8a5ec *)
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { apply Forall_nil. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (A52 : ew (havoc Et 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
  remember (havoc Et 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
  assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [assumption | cbv; lia]).
  assert (OLD3 : forall k, (k < 48)%nat -> ew Ec k = ew E k)
    by (intros k Hk; rewrite HEc, YN3v.ew_havoc_old by exact Hk; apply OLDt; lia).
  clear HEc.
  assert (Usp3 : bv_unsigned (ew Ec 2) = sp0 - 112) by (rewrite OLD3 by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS vad_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
  assert (KEEPk : vad_kept (rdW W mT0) (rdW W mem2) (sp0 - VAD_STK) (sp0 - 112))
    by (intros x0 Hx0 Hn0; apply HK2; [exact Hx0 | rewrite Hes; lia | tauto]).
  clear HK2. clear HJ. rename HJ2 into HJ.
  assert (KEEPm : vad_kept (rdW W mem1) (rdW W mem2) (sp0 - VAD_STK) (sp0 - 112)).
  { intros x0 Hx0 Hn0. rewrite (KEEPk x0 Hx0 Hn0), (KEEPc0 x0 Hx0), (KEEPb x0 Hx0). exact (KEEPa x0 Hx0). }
  clear KEEPk KEEPc.
  (* 0x8a5ec `beqz a0`: the wrapper's answer *)
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* a0 = 0: the parents are one string, entry i matches: the duplicate's exit 0x8a71c `li s4,0`, the epilogue *)
    assert (A0 : getr regs2 10 = w64 0).
    { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52 in Hc. apply bv_eq. exact Hc. }
    assert (SC : strcmp (seg_spec.zs sx) (seg_spec.zs (seg_spec.zb p)) = 0)
      by (apply (vad_bridge_strcmp sx (seg_spec.zb p) NX HN0); exact (proj1 HQ2 A0)).
    rewrite HZ, ZX in SC.
    assert (HT : existsb (vad_match vid p) t = true).
    { rewrite HEX, (vad_existsb_skipn_S (vad_match vid p) t i ([], 0) Hi). unfold vad_match at 1.
      change (snd (nth i t ([], 0))) with vi. rewrite Heq, Z.eqb_refl, SC. reflexivity. }
    pose proof (vad_vlan_add_dup t max p vid HT) as EVA.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan VAD_EPI.
    { awr_ok_tac; exact Usp3. }
    vad_md.
    vad_keep_empty HFr KEEPe. clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (20%bv : bv 5) F20.
    rewrite ?OLD3 in F2, F3, F4 by lia.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KF : vad_kept (rdW W mem1) (rdW W mF) (sp0 - VAD_STK) (sp0 - 112))
        by (intros x0 Hx0 Hn0; rewrite (KEEPe x0 Hx0); exact (KEEPm x0 Hx0 Hn0)) end.
    apply (KEEP 0 _ _ _ EVA).
    * apply (CUTKEPT regs1 mem1 md1 _ _ _ (sp0 - VAD_STK) (sp0 - 112) HCUT HJ KF);
        [lia | lia | rewrite F2; exact E2 | rewrite F3; exact E3 | rewrite F4; exact E4].
    * rewrite F20. reflexivity.
  + (* a0 <> 0: the parents differ, entry i does not match; the latch *)
    assert (HSXn : sx <> seg_spec.zb p).
    { intros HSX. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. unfold U. f_equal. cbn [sv_denot].
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52, (proj2 HQ2 HSX). reflexivity. }
    assert (HM : vad_match vid p (nth i t ([], 0)) = false).
    { unfold vad_match. replace (strcmp (fst (nth i t ([], 0))) p =? 0) with false; [apply andb_false_r|].
      symmetry. apply Z.eqb_neq. intros H0. apply HSXn. apply (vad_bridge_strcmp sx (seg_spec.zb p) NX HN0).
      rewrite HZ, ZX. exact H0. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan VAD_LT.
    { awr_ok_tac; exact Usp3. }
    vad_md.
    vad_keep_empty HFr KEEPf. clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
    prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
    prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
    prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    rewrite ?OLD3 in F2, F3, F4, F8, F9, F18, F19, F20, F21, F22, F23, F24, F25, F27 by lia.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KF : vad_kept (rdW W mem1) (rdW W mF) (sp0 - VAD_STK) (sp0 - 112))
        by (intros x0 Hx0 Hn0; rewrite (KEEPf x0 Hx0); exact (KEEPm x0 Hx0 Hn0)) end.
    apply KLT. split; [|split; [|split; [|split; [exact Hi|]]]].
    * apply (CUTKEPT regs1 mem1 md1 _ _ _ (sp0 - VAD_STK) (sp0 - 112) HCUT HJ KF);
        [lia | lia | rewrite F2; exact E2 | rewrite F3; exact E3 | rewrite F4; exact E4].
    * split; [rewrite F8, E8; exact R8|]. split; [rewrite F9, E9; exact R9|].
      split; [rewrite F19, E19; exact R19|]. split; [rewrite F20, E20; exact R20|].
      split; [rewrite F21, E21; exact R21|]. split; [rewrite F23; exact E34|].
      split; [rewrite F24; exact E32|]. rewrite F25, E25; exact R25.
    * exact (SPILLKEPT mem1 _ _ _ HSP KF ltac:(lia)).
    * split; [rewrite HEX, (vad_existsb_skipn_S (vad_match vid p) t i ([], 0) Hi), HM; reflexivity|].
      split; [rewrite F18; exact E33|]. split; [rewrite F22; exact E33|].
      split; [rewrite F26; reflexivity|]. rewrite F27; exact E36.
Qed.

End w.
End e.
End d.
End b.
