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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths and module names changed; 277 of its 351 lines of code are new or changed and 1518 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan-ubsan (image B, entry BASE + AF_reac_declared_vlan_add = 0x8a514):
   segment 1 of the walk of lib/B/Prog/reac_declared_vlan_add_c.v, the entry stretch 0x8a514 .. 0x8a5b8 (the search
   loop's head at entry 0, when the count is > 0) or .. 0x8a614 (after the search, when the count is 0).
   The image-B port of lib/A/Prog/reac_declared_vlan_add_s0.v (commit fcd2fa03dd27): its entry
   seed vad_entry_seed, the tactics vad_entry_cut and vad_entry_regs, and vad_entry. Written for the image-B G4 + G5
   walks. Image B adds to A's stretch: the UBSan alignment test of n (andi a0,s0,3; bnez to the trap at
   0x8a568, decided by the executor from atom 12's alignment fact), the spill of the count cell's shadow address to
   the frame's lowest slot (sd a0,0(sp) at 0x8a58c: vad_spill, read back from the stack region), and the loop set-up
   0x8a5a0 .. 0x8a5b4: s10 = tab & 1 (= 0, tab mod 16 = 0), s11 = and(neg(sgtz count), count) (= count, which is
   > 0 there), s6 = s2 = tab. The registers differ from A's: s7 holds tab, s9 the count. *)
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
(* segment 2 adds:  From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtString.
   segment 4 adds:  From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtString RtSeg.
   and              From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArtOwn. *)
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

(* the entry's symbolic state: the frame window [sp0 - 112, sp0) (the saved registers and the spill slot), the GOT
   word and the shadow-base cell (atom 32 = SB), the count cell at a2 (atom 33 = its value) *)
Definition vad_entry_nregion : YP09.region := YP09.mkRegion (Some 12%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition vad_ss_entry : sstate := mkSS AF_reac_declared_vlan_add sr_atoms
  [stack_region 112; got_regionP; bcell_regionP 32; vad_entry_nregion] None
  (mkFacts [(2%nat, vad_spF); (32%nat, vad_SBF); (12%nat, mkAF 4096 (2 ^ 47 - 4) 2); (33%nat, mkAF 0 (2 ^ 31 - 1) 0)] [] []).
Definition vad_entry_SH : list shent := [mkSHE 12 0 4].

(* andi s10,s7,1 at 0x8a5a0: tab & 1 = 0 for a 16-aligned tab *)
Lemma vad_and1_al16 : forall x, 0 <= x < 2 ^ 64 -> x mod 16 = 0 ->
  alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 1) = Z_to_bv 64 0.
Proof.
intros x Hx H16. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
assert (H2 : x mod 2 = 0).
{ rewrite (Z.div_mod x 16) by lia. rewrite H16, Z.add_0_r. replace (16 * (x / 16)) with (8 * (x / 16) * 2) by ring.
  apply Z.mod_mul. lia. }
assert (HL : Z.land x 1 = x mod 2) by exact (Z.land_ones x 1 ltac:(lia)).
rewrite HL, H2. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* sgtz a0,s9; neg a0,a0; and s11,a0,s9 at 0x8a5a4 .. 0x8a5ac: the count itself when it is > 0 *)
Lemma vad_s11_pos : forall c, 0 < c < 2 ^ 63 ->
  alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 c))) (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
intros c Hc.
assert (H1 : alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 c) = Z_to_bv 64 1).
{ apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
  rewrite !vad_swrap_small by lia. destruct (Z.ltb_spec 0 c); [|lia].
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (H2 : alu64 ALU_SUB (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 (Z.ones 64)).
{ apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by (cbv; split; congruence).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
rewrite H1, H2. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (first [lia | cbv; split; congruence]).
rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
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
(* segment 2: Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
   segment 3: Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
   segment 4: Hypothesis ASTRNCPY : forall fx0 : YK11.FPState, @astrncpy_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncpy). *)
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

(* ---------- the entry: 0x8a514 .. 0x8a5b8 (or 0x8a614) ---------- *)
Lemma vad_entry_seed :
st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB; w64 L])) vad_ss_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_declared_vlan_add)) mem (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx vad_entry_SH (Eimg (Ereg regs [w64 SB; w64 L])) (mrestrict (w_H W) mem).
Proof using HPRE HADD TL LAWS H12.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & _). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof HADD as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HNV & _ & HNA & _) & _).
assert (HST : VAD_STK = 8304) by reflexivity.
set (E := Eimg (Ereg regs [w64 SB; w64 L])).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 L) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U12 : bv_unsigned (ew E 12) = n)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 12 12%bv eq_refl), H12; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = L) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
unfold kImgEnd in *.
split.
- rewrite restrict_mkst_fx. unfold vad_ss_entry. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, vad_entry_nregion.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
        | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ n 0 4 (SOff 33 0) L);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (vad_val_mem_of_sa SEGS _ _ _ _ _ HNV).
  + apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, vad_entry_nregion, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, vad_spF, vad_SBF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, U12, U33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; try lia; assumption.
- unfold sh_ok, vad_entry_SH. apply Forall_cons; [|apply Forall_nil].
  apply (vad_shent_ok E _ _ 12 n 0 4 E32 U12); try lia.
  + rewrite Z.add_0_r. destruct HNA as (_ & _ & _ & HRA & _). exact HRA.
  + intros y Hy. apply N5. lia.
Qed.
(* the spill slot sp0 - 112, read back from the stack region of a symbolic state: sd a0,0(sp) at 0x8a58c stored there
   the shadow address of atom 12 = n *)
Lemma vad_spill_of : forall E H mem' lo hi wlo whi cs,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp0 ->
In (YP09.mkChunk (-112) (CVal 8 (vad_shx 12))) cs -> ew E 32 = w64 SB -> ew E 12 = w64 n -> 0 <= n < 2 ^ 47 ->
spill (aview SEGS H mem').
Proof using.
intros E H mem' lo hi wlo whi cs HR Hsp Hin H32 Hn12 Hn. unfold vad_spill.
replace (sp0 - 112) with (sp0 + -112) by lia.
apply (vad_stack_word E H mem' sp0 lo hi wlo whi cs (-112) (vad_shx 12) (SB + n / 8) HR Hsp Hin).
- exact (vad_shx_U E 12 n H32 Hn12 Hn).
- assert (0 <= n / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia.
Qed.
(* at the end of the entry stretch: the cut (journal, frame, sp gp tp, the memory outside the window) and the spill *)
Ltac vad_entry_cut K0 K2 K3 K4 HRg HKP HSPL EE E32 HJ :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg;
    let EEx := fresh "EEx" in
    assert (EEx : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew Ex k = getr regs rr)
      by (let k := fresh "k" in let rr := fresh "rr" in let Hk := fresh "Hk" in let Hrr := fresh "Hrr" in
          intros k rr Hk; pose proof (bv_unsigned_in_range 5 rr) as Hrr; change (bv_modulus 5) with 32 in Hrr;
          cbn [ew ewset]; repeat (rewrite (proj2 (Nat.eqb_neq _ _)) by lia); apply EE; exact Hk);
    let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in
    prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
    let mdx := lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?d _ => d end in
    assert (HKP : cut (ms_regs msx) (ms_mem msx) mdx);
    [ split; [split; [exact HJ|]; split;
        [ apply (FRM Ex _ _ _ _ _ _ _ EEx HRg);
          let j := fresh "j" in let rr := fresh "rr" in let Hr := fresh "Hr" in intros j rr Hr;
          do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]);
          cbn in Hr; destruct j; discriminate Hr
        | split; [rewrite Q2, (EE 2%nat 2%bv eq_refl); unfold w64, spZ; f_equal; lia|];
          split; [rewrite Q3; apply EE; reflexivity | rewrite Q4; apply EE; reflexivity] ]
      | apply (vad_kept_trans _ _ _ _ _ _ _ (vad_kept_trans _ _ _ _ _ _ _
          (vad_kept_trans _ _ _ _ _ _ _ K0 K2 ltac:(lia) ltac:(lia)) K3 ltac:(lia) ltac:(lia)) K4);
        lia ]
    | ];
    assert (HSPL : spill (rdW W (ms_mem msx)));
    [ apply (vad_spill_of Ex _ _ _ _ _ _ _ HRg);
      [ rewrite (EEx 2%nat 2%bv eq_refl); reflexivity
      | vm_compute; repeat first [left; reflexivity | right]
      | cbn [ew ewset Nat.eqb]; exact E32
      | rewrite (EEx 12%nat 12%bv eq_refl); exact H12
      | lia ]
    | ] end.
(* the registers every cut carries (vad_regs), at the end of the entry stretch *)
Ltac vad_entry_regs EE E32 E33 :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
    let R8 := fresh "R8" in let R9 := fresh "R9" in let R19 := fresh "R19" in let R20 := fresh "R20" in
    let R21 := fresh "R21" in let R23 := fresh "R23" in let R24 := fresh "R24" in let R25 := fresh "R25" in
    prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20;
    prreg HS (21%bv : bv 5) R21; prreg HS (23%bv : bv 5) R23; prreg HS (24%bv : bv 5) R24; prreg HS (25%bv : bv 5) R25;
    split; [rewrite R8; apply (eq_trans (EE 12%nat 12%bv eq_refl)); exact H12|];
    split; [rewrite R9; apply (eq_trans (EE 14%nat 14%bv eq_refl)); exact H14|];
    split; [rewrite R19; apply (eq_trans (EE 13%nat 13%bv eq_refl)); exact H13|];
    split; [rewrite R20; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]|];
    split; [rewrite R21; apply (eq_trans (EE 11%nat 11%bv eq_refl)); exact H11|];
    split; [rewrite R23; apply (eq_trans (EE 10%nat 10%bv eq_refl)); exact H10|];
    split; [rewrite R24; exact E32|];
    rewrite R25; exact E33 end.
Lemma vad_entry :
(forall r m d, LHc 0 r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_LH)) m (seg_rom SEGS)) d) Q) ->
(forall r m d, AFTc r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + VAD_AFT)) m (seg_rom SEGS)) d) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_declared_vlan_add) regs mem md) Q.
Proof using HPRE HADD TL LAWS H10 H11 H12 H13 H14.
intros KLH KAFT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HADD as (_ & Hpz & _).
pose proof SP0 as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof TABF as (T1 & T2 & T3 & T4 & _). pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
assert (HST : VAD_STK = 8304) by reflexivity.
destruct vad_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B VAD_STK FP ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 SB; w64 L]))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs [w64 SB; w64 L])) k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (Eimg (Ereg regs [w64 SB; w64 L])) 32 = w64 SB) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Eimg (Ereg regs [w64 SB; w64 L])) 33 = w64 L) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
remember (Eimg (Ereg regs [w64 SB; w64 L])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U10 : U E (SOff 10 0) = tab) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact H10 | lia]).
assert (U13 : U E (SOff 13 0) = par).
{ apply U_atom; [rewrite (EE 13%nat 13%bv eq_refl); exact H13|]. pose proof HADD as (_ & _ & _ & HPA & _). destruct HPA as (P0 & P1 & _). lia. }
unfold cfg_at. change (w64 (BASE + AF_reac_declared_vlan_add)) with (Z_to_bv 64 (BASE + AF_reac_declared_vlan_add)).
(* 0x8a514 .. 0x8a550: the frame, s4 = -1, beqz a0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_win HFr KEEP0 (spZ regs - VAD_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x8a554 .. 0x8a560: s0 = n, beqz a2 (decided by atom 12's fact), s3 = parent, beqz a3 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_win HFr KEEP2 (spZ regs - VAD_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, U13, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x8a564 .. 0x8a59c: s7 = tab, the alignment test of n (andi a0,s0,3; bnez: decided by atom 12's fact), s1, s5,
   the shadow base, the shadow address of n spilled to 0(sp), inline check 1, s9 = the count, blez *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_win HFr KEEP3 (spZ regs - VAD_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* blez taken: the table is empty; 0x8a614 *)
  lazymatch type of Hc with context [sv_denot ?Ex (SOff 33 0)] =>
    assert (E33x : ew Ex 33 = w64 L) by (cbn [ew ewset Nat.eqb]; exact E33) end.
  rewrite (vad_bge0 _ 33 L E33x) in Hc by lia. apply Z.leb_le in Hc.
  assert (Ht0 : t = []) by (destruct t; [reflexivity | cbn [length] in Hc; lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_AFT.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  vad_md.
  vad_keep_win HFr KEEP4 (spZ regs - VAD_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  vad_entry_cut KEEP0 KEEP2 KEEP3 KEEP4 HRg HKP HSPL EE E32 HJ.
  apply KAFT. split; [exact HKP|]. split; [vad_entry_regs EE E32 E33|]. split; [exact HSPL|].
  rewrite Ht0. reflexivity.
- (* blez not taken: the search from entry 0; 0x8a5a0 .. 0x8a5b4 set s10, s11, s6, s2; 0x8a5b8 *)
  lazymatch type of Hc with context [sv_denot ?Ex (SOff 33 0)] =>
    assert (E33x : ew Ex 33 = w64 L) by (cbn [ew ewset Nat.eqb]; exact E33) end.
  rewrite (vad_bge0 _ 33 L E33x) in Hc by lia. apply Z.leb_gt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan VAD_LH.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  vad_md.
  vad_keep_win HFr KEEP4 (spZ regs - VAD_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  vad_entry_cut KEEP0 KEEP2 KEEP3 KEEP4 HRg HKP HSPL EE E32 HJ.
  apply KLH. split; [exact HKP|]. split; [vad_entry_regs EE E32 E33|]. split; [exact HSPL|].
  split; [lia|]. split; [reflexivity|].
  prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  split; [rewrite Q18, (EE 10%nat 10%bv eq_refl), H10; unfold w64; f_equal; lia|].
  split; [rewrite Q22, (EE 10%nat 10%bv eq_refl), H10; unfold w64; f_equal; lia|].
  split; [rewrite Q26, (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply vad_and1_al16; [lia | exact T4]|].
  rewrite Q27, E33. unfold w64. replace (L - Z.of_nat 0) with L by lia. apply vad_s11_pos. lia.
Qed.

End w.
End e.
End d.
End b.
