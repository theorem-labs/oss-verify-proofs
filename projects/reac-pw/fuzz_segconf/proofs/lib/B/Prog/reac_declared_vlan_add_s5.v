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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths and module names changed; 407 of its 479 lines of code are new or changed and 1520 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan-ubsan (image B): segment 5 of the walk, the image-B port of the store
   stretch of lib/A/Prog/reac_declared_vlan_add_s0.v (commit fcd2fa03dd27: vad_STc, vad_st_seed,
   vad_store). Written for the image-B G4 + G5 walks.
   It walks the append exit from the strncpy call's return RSN 0x8a698 to the epilogue EPI 0x8a720:
   - RSN 0x8a698 .. ST 0x8a6d4 (seed vad_ss_sn): the spill reload, inline check 4 on the count cell, lw count,
     a0 = tab + 18 count and its three UBSan tests: beqz 0x8a6b4 is decided by the executor from the facts of tab
     (atom 23) and the count (atom 34); the overflow test 0x8a6c8 (vad_ovf_U) and the alignment test 0x8a6d0
     (vad_even_U) are refuted at the branch;
   - the cut at ST 0x8a6d4 (vad_STc, a0 = tab + 18 count), re-seeded (vad_ss_st, A's vad_st_seed with the spill
     slot): inline check 5, sh vid, the spill reload and inline check 6, lw count, addiw, the overflow test
     `blt a0,a1` 0x8a700 (decided by the executor: the count's fact is count <= 2 ^ 31 - 2, from count < max < 2 ^ 31),
     the spill reload and inline check 7, sw count, s4 = 1, j EPI;
   - EPI (segment 0's vad_epi) with the table t ++ [(firstn 15 (cut_nul p), vid)], the count L + 1, the guard and
     sa_kept over vad_E (the new entry and the count cell). *)
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

(* ---------- the symbolic states of this segment; atoms 32 .. are the seed's extra words ---------- *)
(* the spill slot 0(sp) (sp = sp0 - 112): the count cell's shadow address, what srli/add computed at 0x8a584 from the
   atom of n (atom 33) and the shadow base (atom 32); read-only *)
Definition vad_spR : YP09.region := YP09.mkRegion (Some 2%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (vad_shx 33))].
Definition vad_nF : afact := mkAF 4096 (2 ^ 47 - 4) 2.
Definition vad_cntF : afact := mkAF 0 (2 ^ 31 - 2) 0.
Definition vad_tabF : afact := mkAF 4096 (2 ^ 47 - 64) 4.
(* RSN 0x8a698: atom 32 = SB (s8), 33 = n (s0), 34 = the count; the count cell's region, read-only *)
Definition vad_sn_regs : list sv := sr_set (sr_set sr_atoms 24 (SOff 32 0)) 8 (SOff 33 0).
Definition vad_nR : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition vad_ss_sn : sstate := mkSS VAD_RSN vad_sn_regs [vad_spR; vad_nR] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, vad_nF); (34%nat, vad_cntF); (23%nat, vad_tabF)] [] []).
Definition vad_sn_SH : list shent := [mkSHE 33 0 4].
(* ST 0x8a6d4: also atom 35 = tab + 18 count (a0); the vid's two bytes of the new entry and the count cell writable *)
Definition vad_st_regs : list sv := sr_set (sr_set (sr_set sr_atoms 24 (SOff 32 0)) 8 (SOff 33 0)) 10 (SOff 35 0).
Definition vad_vidR : YP09.region := YP09.mkRegion (Some 35%nat) 0 18 16 18 [].
Definition vad_nRw : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition vad_ss_st : sstate := mkSS VAD_ST vad_st_regs [vad_vidR; vad_nRw; vad_spR] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (33%nat, vad_nF); (34%nat, vad_cntF); (35%nat, vad_PTRF)] [] []).
Definition vad_st_SH : list shent := [mkSHE 35 16 18; mkSHE 33 0 4].

(* ---------- the executor's words of the UBSan tests after the strncpy call (atom 23 = tab, 34 = the count) ---------- *)
(* a0 := tab + 18 count (0x8a6a8 .. 0x8a6b0) *)
Lemma vad_ptr_U : forall E tb c, U E (SOff 23 0) = tb -> U E (SOff 34 0) = c -> 0 <= tb -> 0 <= c -> tb + 18 * c < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 34 0) (SLit 18))) = tb + 18 * c.
Proof.
intros E tb c Ht Hc H1 H2 H3. rewrite U_SAlu, U_SMd, U_SLit, Ht, Hc. cbn [zalu_raw zmd_raw].
change (zcanon 18) with 18. rewrite (zcanon_small (c * 18)) by lia. rewrite zcanon_small by lia. lia.
Qed.
(* the overflow test of 0x8a6b8 .. 0x8a6c4 (slti a1,a1,0 is 0 by the count's fact): (a0 <u tab) xor 0 xor 1 = 1 *)
Lemma vad_ovf_U : forall E tb c, U E (SOff 23 0) = tb -> U E (SOff 34 0) = c -> 0 <= tb -> 0 <= c -> tb + 18 * c < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 34 0) (SLit 18))) (SOff 23 0))
    (SLit 0)) (SLit 1)) = 1.
Proof.
intros E tb c Ht Hc H1 H2 H3.
rewrite U_SAlu, U_SLit. rewrite U_SAlu, U_SLit. rewrite U_SAlu, (vad_ptr_U E tb c Ht Hc H1 H2 H3), Ht.
cbn [zalu_raw]. destruct (Z.ltb_spec (tb + 18 * c) tb); [lia|]. reflexivity.
Qed.
Lemma vad_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.
(* the alignment test of 0x8a6cc: (tab + 18 count) & 1 = 0 *)
Lemma vad_even_U : forall E tb c, U E (SOff 23 0) = tb -> U E (SOff 34 0) = c -> 0 <= tb -> 0 <= c -> tb + 18 * c < 2 ^ 64 ->
  tb mod 2 = 0 -> U E (SAlu ALU_AND (SAlu ALU_ADD (SOff 23 0) (SMd M_MUL (SOff 34 0) (SLit 18))) (SLit 1)) = 0.
Proof.
intros E tb c Ht Hc H1 H2 H3 H4. rewrite U_and_lit by lia. rewrite (vad_ptr_U E tb c Ht Hc H1 H2 H3), vad_land1.
rewrite Z.add_mod, H4 by lia. replace (18 * c) with ((9 * c) * 2) by lia. rewrite Z.mod_mul by lia. reflexivity.
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

(* ---------- the seed at RSN (0x8a698) ---------- *)
Lemma vad_sn_seed : forall regs1 mem1,
L < max ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 8 = w64 n -> getr regs1 23 = w64 tab -> getr regs1 24 = w64 SB ->
spill (rdW W mem1) -> sa_val (rdW W mem1) n 4 L -> range_addressable (rdW W mem1) SHADOW_OFF n 4 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; n; L]))) vad_ss_sn
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_RSN)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_sn_SH (Eimg (Ereg regs1 (map w64 [SB; n; L]))) (mrestrict (w_H W) mem1).
Proof using HPRE HADD.
intros regs1 mem1 LT R2 R8 R23 R24 SPL VN RAN.
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof vad_STK_val as HST.
assert (Hn8 : 0 <= n / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (E := Eimg (Ereg regs1 (map w64 [SB; n; L]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E23u : bv_unsigned (ew E 23) = tab) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; n; L] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34. fold E in E32, E33, E34.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold vad_ss_sn. apply pa_entry_st_ok_full.
  + vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u).
  + vm_compute. reflexivity.
  + unfold vad_spR, vad_nR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (sp0 - 112) 0 8 (vad_shx 33) (SB + n / 8));
        [exact (vad_shx_U E 33 n E32 E33 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact SPL.
    * rewrite E33u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ n 0 4 (SOff 34 0) L); [cbn [sv_denot]; rewrite E34u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact VN.
  + apply pairwise_disjoint_of_extents. unfold vad_spR, vad_nR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E33u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_nF, vad_cntF, vad_tabF.
    cbn [af_lo af_hi af_al2]. rewrite Usp, E32u, E33u, E34u, E23u.
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | assumption].
- unfold sh_ok, vad_sn_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 33 n 0 4 E32 E33u); try lia.
  + rewrite Z.add_0_r. exact RAN.
  + intros y Hy. apply N5. lia.
Qed.

(* ---------- the cut at ST (0x8a6d4) on the append path: a0 = tab + 18 count; the new entry's first 16 bytes ---------- *)
Definition vad_STc (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
cutE regs1 mem1 md1 /\ L < max /\ existsb (vad_match vid p) t = false /\
getr regs1 8 = w64 n /\ getr regs1 9 = w64 vid /\ getr regs1 24 = w64 SB /\ getr regs1 10 = w64 VD /\
spill (rdW W mem1) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - VAD_STK <= x < sp0) -> ~ (VD <= x < VD + 18) -> rdW W mem1 x = rdW W mem x) /\
(exists f16, length f16 = 16%nat /\ sa_bytes (rdW W mem1) VD f16 /\
  seg_spec.rvlan_enc (firstn 15 (cut_nul p), vid) (f16 ++ Mem.le2 (Z_to_bv 64 vid))).
Lemma vad_st_seed : forall regs1 mem1,
L < max ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 8 = w64 n -> getr regs1 24 = w64 SB -> getr regs1 10 = w64 VD ->
spill (rdW W mem1) -> sa_val (rdW W mem1) n 4 L ->
range_addressable (rdW W mem1) SHADOW_OFF (VD + 16) 2 ->
range_addressable (rdW W mem1) SHADOW_OFF n 4 ->
(forall a, VD + 16 <= a < VD + 18 -> apresent (w_H W) mem1 a) ->
(forall a, n <= a < n + 4 -> apresent (w_H W) mem1 a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; n; L; VD]))) vad_ss_st
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_ST)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_st_SH (Eimg (Ereg regs1 (map w64 [SB; n; L; VD]))) (mrestrict (w_H W) mem1).
Proof using HPRE HADD.
intros regs1 mem1 LT R2 R8 R24 R10 SPL VN RA RAN PD PN.
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof vad_STK_val as HST.
assert (Hn8 : 0 <= n / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (D := VD) in *.
set (E := Eimg (Ereg regs1 (map w64 [SB; n; L; D]))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 3 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E35.
cbn [nth Nat.add] in E32, E33, E34, E35. fold E in E32, E33, E34, E35.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = D) by (rewrite E35; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold vad_ss_st. apply pa_entry_st_ok_full.
  + vad_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E35u).
  + vm_compute. reflexivity.
  + unfold vad_vidR, vad_nRw, vad_spR.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E35u. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply PD. lia.
    * rewrite E33u. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply PN. lia. }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ n 0 4 (SOff 34 0) L); [cbn [sv_denot]; rewrite E34u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact VN.
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (sp0 - 112) 0 8 (vad_shx 33) (SB + n / 8));
        [exact (vad_shx_U E 33 n E32 E33 ltac:(lia)) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vad_val_mem_of_sa. exact SPL.
  + apply pairwise_disjoint_of_extents. unfold vad_vidR, vad_nRw, vad_spR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E33u, E35u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF, vad_nF, vad_cntF, vad_PTRF.
    cbn [af_lo af_hi af_al2]. rewrite Usp, E32u, E33u, E34u, E35u.
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | assumption].
- unfold sh_ok, vad_st_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (vad_shent_ok E _ _ 35 D 16 18 E32 E35u); try lia.
    * exact RA.
    * intros y Hy. apply T5. lia.
  + apply (vad_shent_ok E _ _ 33 n 0 4 E32 E33u); try lia.
    * rewrite Z.add_0_r. exact RAN.
    * intros y Hy. apply N5. lia.
Qed.

(* ---------- the store stretch: ST 0x8a6d4 .. EPI 0x8a720 ---------- *)
Lemma vad_store : forall regs1 mem1 md1, vad_STc regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_ST)) mem1 (seg_rom SEGS)) md1) Q.
Proof using HPRE HADD TL.
intros regs1 mem1 md1 (HCE & LT & HEX & R8 & R9 & R24 & R10 & SPL & HK2 & (f16 & L16 & HF16 & HENC)).
pose proof HCE as (HJ & HFR & R2 & R3 & R4).
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof vad_STK_val as HST.
pose proof HADD as ((_ & _ & HRT & _ & (b & m & Hbm & Hb1 & Hb2) & HTA & _ & _ & _ & HNV & _ & HNA & HDJ) & _ & _ & _ & _ & _ & _ & _ & Hvid).
destruct HRT as (bt & HBT & HET).
unfold sa_disj, seg_spec.RVLAN_SIZE in HDJ, Hb2.
set (D := VD) in *.
assert (HKP : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0) /\ ~ (D <= x < D + 18)) -> rdW W mem1 x = rdW W mem x)
  by (intros x (Hx1 & Hx2 & Hx3); exact (HK2 x Hx1 Hx2 Hx3)).
assert (VN1 : sa_val (rdW W mem1) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKP HNV); intros i Hi; cbv beta; lia).
assert (RA1 : range_addressable (rdW W mem1) SHADOW_OFF (D + 16) 2).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKP).
  - destruct HTA as (_ & _ & _ & HRA & _). apply (range_addressable_sub _ _ tab (seg_spec.RVLAN_SIZE * max)); [exact HRA | lia | unfold seg_spec.RVLAN_SIZE; lia].
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
destruct (al_blocks _ _ LAWS ly S W mem1 md1 b m (proj1 HJ) Hbm) as (_ & _ & _ & _ & Hppres & _).
pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
assert (PD1 : forall a, D + 16 <= a < D + 18 -> apresent (w_H W) mem1 a) by (intros a Ha; exact (proj1 (Hppres a ltac:(lia)))).
assert (RAN1 : range_addressable (rdW W mem1) SHADOW_OFF n 4).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKP).
  - destruct HNA as (_ & _ & _ & HRAn & _). exact HRAn.
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
assert (PN1 : forall a, n <= a < n + 4 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply (apresent_of_aview SEGS); [lia | intros Hi; destruct (IMGOUT a Hi) as (_ & _ & _ & Hn); lia |].
  pose proof (VN1 (Z.to_nat (a - n)) ltac:(lia)) as Hb. replace (n + Z.of_nat (Z.to_nat (a - n))) with a in Hb by lia.
  rewrite Hb. discriminate. }
destruct (vad_st_seed regs1 mem1 LT R2 R8 R24 R10 SPL VN1 RA1 RAN1 PD1 PN1) as [HS SHOK]. fold D in HS, SHOK.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; n; L; D])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; n; L; D]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
pose proof (vad_ex_w64 regs1 [SB; n; L; D] 3 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E35.
cbn [nth Nat.add] in E32, E33, E34, E35.
remember (Eimg (Ereg regs1 (map w64 [SB; n; L; D]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = L) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = D) by (rewrite E35; apply unsigned_lit_small; lia).
(* 0x8a6d4 .. 0x8a71c: inline check 5, sh vid, the spill reload, inline check 6, lw count, addiw, blt (the executor
   decides it from the count's fact: count + 1 <= 2 ^ 31 - 1), the spill reload, inline check 7, sw count, s4 = 1, j *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_EPI.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 35%nat) (b := D); [reflexivity | exact E35u | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply AWRTAB; [exact HEX | exact LT | lia] |].
  eapply awr_ok_cons_gen with (n := 33%nat) (b := n); [reflexivity | exact E33u | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply AWRN; [exact HEX | exact LT | lia] |].
  awr_ok_tac. }
vad_md.
(* what the run wrote: the vid at D + 16 and the new count at n; nothing else *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (stack_region 0)) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  cbn [ms_mem restrict] in HR0, HR1;
  assert (Ux35 : bv_unsigned (ew Ex 35) = D) by (cbn [ew ewset Nat.eqb]; exact E35u);
  assert (Ux33 : bv_unsigned (ew Ex 33) = n) by (cbn [ew ewset Nat.eqb]; exact E33u);
  assert (Dv : sv_denot Ex (SOff 9 0) = Z_to_bv 64 vid)
    by (cbn [sv_denot ew ewset Nat.eqb]; rewrite (EE 9%nat 9%bv eq_refl), R9, Z.add_0_r; unfold w64; apply Z_to_bv_bv_unsigned);
  assert (Dn : sv_denot Ex (SOff 34 1) = Z_to_bv 64 (L + 1))
    by (cbn [sv_denot ew ewset Nat.eqb]; rewrite E34u; reflexivity) end.
pose proof (field_of_region _ _ 35 D _ 0 18 16 18 16 2 (SOff 9 0) vid HR0 Ux35 ltac:(cbn; tauto) Dv ltac:(cbn; lia) ltac:(cbn; lia)) as VVID.
pose proof (field_of_region _ _ 33 n _ 0 4 0 4 0 4 (SOff 34 1) (L + 1) HR1 Ux33 ltac:(cbn; tauto) Dn ltac:(cbn; lia) ltac:(cbn; lia)) as VCNT.
change (N.to_nat 2) with 2%nat in VVID. change (N.to_nat 4) with 4%nat in VCNT. rewrite Z.add_0_r in VCNT.
pose proof (vad_sa_of_val_mem _ _ _ _ _ _ VVID) as SVID. pose proof (vad_sa_of_val_mem _ _ _ _ _ _ VCNT) as SCNT.
lazymatch type of HFr with frame_of ?Ex _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (KF : forall x, (0 <= x < 2 ^ 64 /\ ~ (D + 16 <= x < D + 18) /\ ~ (n <= x < n + 4)) -> aview SEGS H m2 x = aview SEGS H m1 x)
  by (intros x0 (Hx0 & Hn1 & Hn2); apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => (D + 16 <= x < D + 18) \/ (n <= x < n + 4)) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr; rewrite ?E35u, ?E33u in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
clear HF HFr HG.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (20%bv : bv 5) F20.
pose proof (vad_vlan_add_app t max p vid HEX LT) as EVA.
assert (HKF : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0) /\ ~ (D <= x < D + 18) /\ ~ (n <= x < n + 4)) ->
  rdW W (ms_mem ms) x = rdW W mem x).
{ intros x (H1 & H2 & H3 & H4). rewrite (KF x ltac:(split; [exact H1|]; split; [lia | exact H4])). exact (HKP x (conj H1 (conj H2 H3))). }
apply (EPI 1); rewrite ?EVA; cbn [fst snd].
- split; [exact HJ|]. split.
  + intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
    apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (D + 16 <= x < D + 18) /\ ~ (n <= x < n + 4)) _ _ _ KF (HFR j r Hr)).
    intros k Hk. cbv beta. lia.
  + split; [rewrite F2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite F3, (EE 3%nat 3%bv eq_refl); exact R3 | rewrite F4, (EE 4%nat 4%bv eq_refl); exact R4].
- rewrite F20. reflexivity.
- reflexivity.
- exists (bt ++ (f16 ++ Mem.le2 (Z_to_bv 64 vid))). split.
  + apply vad_sa_bytes_app. split.
    * apply (vad_sa_bytes_keep _ _ _ _ _ HKF HBT). intros i Hi. destruct HET as [HL _]. cbv beta. lia.
    * destruct HET as [HL _]. rewrite HL. replace (tab + Z.of_nat (18 * length t)) with D by lia.
      apply vad_sa_bytes_app. split.
      -- apply (vad_sa_bytes_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (D + 16 <= x < D + 18) /\ ~ (n <= x < n + 4)) _ _ KF HF16).
         intros i Hi. cbv beta. lia.
      -- rewrite L16. replace (D + Z.of_nat 16) with (D + 16) by lia.
         intros i Hi. rewrite Mem.length_le2 in Hi. rewrite (SVID i Hi). f_equal. unfold le_byte. symmetry. apply vad_le2_byte; [lia | exact Hi].
  + apply vad_rtab_enc_snoc; [exact HET | exact HENC].
- rewrite length_app. cbn [length]. replace (Z.of_nat (length t + 1)) with (L + 1) by lia. exact SCNT.
- intros HG. apply (vad_sa_bytes_keep _ _ _ _ _ HKF HG). intros i Hi. cbv beta.
  unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi. unfold seg_spec.RVLAN_SIZE. lia.
- intros a Ha Hw He. rewrite (EAPP HEX LT a) in He. apply HKF. split; [exact Ha|]. split; [exact Hw|].
  split; intros Hx; apply He; [left | right]; exact Hx.
Qed.

(* ---------- RSN (0x8a698) .. ST (0x8a6d4) ---------- *)
Lemma vad_sn : forall regs1 mem1 md1, SNc regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_RSN)) mem1 (seg_rom SEGS)) md1) Q.
Proof using HPRE HADD TL.
intros regs1 mem1 md1 (HCE & (R8 & R9 & R19 & R20 & R21 & R23 & R24 & R25) & R18 & SPL & LT & HEX & HK & HNEW).
pose proof HCE as (HJ & HFR & R2 & R3 & R4).
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof vad_STK_val as HST.
pose proof HADD as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HNV & _ & HNA & _) & _).
assert (HKP : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0) /\ ~ (VD <= x < VD + 18)) -> rdW W mem1 x = rdW W mem x)
  by (intros x (Hx1 & Hx2 & Hx3); exact (HK x Hx1 Hx2 Hx3)).
assert (VN1 : sa_val (rdW W mem1) n 4 L) by (apply (vad_sa_val_keep _ _ _ _ _ _ HKP HNV); intros i Hi; cbv beta; lia).
assert (RAN1 : range_addressable (rdW W mem1) SHADOW_OFF n 4).
{ apply (vad_ra_keep (rdW W mem) _ _ _ _ HKP).
  - destruct HNA as (_ & _ & _ & HRAn & _). exact HRAn.
  - intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | lia]. }
destruct (vad_sn_seed regs1 mem1 LT R2 R8 R23 R24 SPL VN1 RAN1) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; n; L])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 (map w64 [SB; n; L]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (vad_ex_w64 regs1 [SB; n; L] 0 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E32.
pose proof (vad_ex_w64 regs1 [SB; n; L] 1 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E33.
pose proof (vad_ex_w64 regs1 [SB; n; L] 2 ltac:(unfold A_TEXT; lia) ltac:(cbn; lia)) as E34.
cbn [nth Nat.add] in E32, E33, E34.
remember (Eimg (Ereg regs1 (map w64 [SB; n; L]))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
(* 0x8a698 .. 0x8a6c4: the spill reload, inline check 4, lw count, a0 = tab + 18 count; beqz a0 (0x8a6b4) is decided by
   the facts of atoms 23 and 34 (nonzero, no wrap); slti a1,a1,0 is 0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
vad_md.
vad_keep_empty HFr KM. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (U23 : U Ex (SOff 23 0) = tab) by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]);
  assert (U34 : U Ex (SOff 34 0) = L) by (apply U_atom; [cbn [ew ewset Nat.eqb]; exact E34 | lia]) end.
(* 0x8a6c8 beqz a1: the overflow test; a1 = 1, so the trap arm is refuted *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, (vad_ovf_U _ tab L U23 U34 ltac:(lia) ltac:(lia) ltac:(lia)), U_SLit in Hc.
  apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. lia. }
clear Hc.
(* 0x8a6cc .. 0x8a6d0: andi a1,a0,1; bnez a1: tab + 18 count is even, so the trap arm is refuted *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
vad_md.
vad_keep_empty HFr KM2. clear HF HFr HG.
pose proof (fun x Hx => eq_trans (KM2 x Hx) (KM x Hx)) as KM3. clear KM KM2. rename KM3 into KM.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (U23' : U Ex (SOff 23 0) = tab) by (rewrite <- U23; reflexivity);
  assert (U34' : U Ex (SOff 34 0) = L) by (rewrite <- U34; reflexivity) end.
clear U23 U34. rename U23' into U23. rename U34' into U34.
assert (Htab2 : tab mod 2 = 0) by lia.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ne_U, (vad_even_U _ tab L U23 U34 ltac:(lia) ltac:(lia) ltac:(lia) Htab2), U_SLit in Hc.
  change (zcanon 0) with 0 in Hc. cbn in Hc. discriminate Hc. }
clear Hc.
(* to ST 0x8a6d4 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_ST.
{ awr_ok_tac. }
vad_md.
vad_keep_empty HFr KM2. clear HF HFr HG.
pose proof (fun x Hx => eq_trans (KM2 x Hx) (KM x Hx)) as KM3. clear KM KM2. rename KM3 into KM.
pmkst HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?msx) =>
  assert (U23' : U Ex (SOff 23 0) = tab) by (rewrite <- U23; reflexivity);
  assert (U34' : U Ex (SOff 34 0) = L) by (rewrite <- U34; reflexivity);
  pose proof (st_ok_pi_restrict_reg H Ex ssx msx 10%bv HS) as F10;
  let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in F10;
  cbn [ms_regs restrict mkst] in F10 end.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (24%bv : bv 5) F24.
apply vad_store. unfold vad_STc.
split.
{ split; [exact HJ|]. split.
  - intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
    apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64) _ _ _ KM (HFR j r Hr)).
    intros k Hk. cbv beta. lia.
  - split; [rewrite F2, (EE 2%nat 2%bv eq_refl); exact R2|].
    split; [rewrite F3, (EE 3%nat 3%bv eq_refl); exact R3 | rewrite F4, (EE 4%nat 4%bv eq_refl); exact R4]. }
split; [exact LT|]. split; [exact HEX|].
split; [rewrite F8; exact E33|].
split; [rewrite F9, (EE 9%nat 9%bv eq_refl); exact R9|].
split; [rewrite F24; exact E32|].
split; [rewrite F10, denot_lit_U, (vad_ptr_U _ tab L U23' U34' ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity|].
split; [apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64) _ _ _ KM SPL); intros k Hk; cbv beta; lia|].
split; [intros x Hx Hs Hd; rewrite (KM x Hx); exact (HK x Hx Hs Hd)|].
destruct HNEW as (f16 & L16 & HF16 & HENC). exists f16. split; [exact L16|]. split; [|exact HENC].
apply (vad_sa_bytes_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ KM HF16). intros i Hi. cbv beta. lia.
Qed.


End w.
End e.
End d.
End b.
