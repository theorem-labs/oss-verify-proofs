(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment E of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530 .. the jal of rec_clear at 0x86584: the frame, the size test, the shadow base), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s10.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the seed and the run from the entry) and A/ACh6.v (a segment closed by the statement of the point it leaves to). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s10.v, with its module paths and module names changed; 460 of its 527 lines of code are new or changed and 343 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/check_model.v (commit beed74b30c04): the walk of fuzz_segconf's
   check_model on image B (fuzz_segconf.asan-ubsan, 0x8718c = BASE + AF_check_model, 33 instructions), against
   check_model_contract (lib/B/Prog/check_model_c.v, image B's copy of the FINAL contract 6f783602b5e3). ADAPTED: B's code is
   A's 30 instructions at other addresses plus UBSan's alignment test of want (`andi a2,a1,3; bnez a2`, 0x87194 /
   0x87198) and its trap word (`unimp`, 0x871f8); the A walk's text, with B's module paths, B's addresses and one more
   stretch and branch for the test.

   Code (the neutral excerpt check_model.fuzz_segconf.asan-ubsan.s; listing slots 2291..2323):
     0x8718c addi sp,sp,-16; sd ra,8(sp)
     0x87194 andi a2,a1,3; 0x87198 bnez a2 -> 0x871f8 unimp (the UBSan trap)
     0x8719c auipc/ld: the GOT word object 0 (0xa3210), which holds object 12 (0xac7b8); ld: the shadow base
     0x871a8 the instrumented check of the 4-byte load at want + 0x20 (shadow byte, bnez to the slow block
             0x871fc-0x87204, whose failing arm calls errpath_load4 at 0x8720c)
     0x871bc lw a2,0x20(a1) (model_set f); a3 := (f = 0 ? 0 : want + 0x24); beq a0,a3 -> 0x871e4
     0x871d4 beqz a0 -> 0x871f0; 0x871d8 beqz a2 -> 0x871f0; 0x871dc jal wrapper_strcmp; 0x871e0 bnez a0 -> 0x871f0
     0x871e4 ld ra,8(sp); addi sp,sp,16; ret
     0x871f0 jal before_abort; 0x871f4 jal abort; 0x871f8 unimp
   The trap branch 0x87198 is refuted at the branch from check_model_pre's first conjunct, want mod 4 = 0 (want & 3 =
   0); the trap word's only other way in is the fall-through from `jal abort`, which no path reaches. The check
   passes by the shadow entry on [want + 0x20, want + 0x24) (range_addressable). Every branch to the abort pair is
   refuted from the premise: f = 0 forces got = NULL, and f = 1 with got <> want + 0x24 gives a non-NULL got whose
   text is the model's, so strcmp answers 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot PaSB PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegGlob SegInstB.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import check_model_lem check_model_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a field read through the world's view is the same field of the restricted memory *)
Lemma cm_val_mem : forall segs H (mem : word -> option byte) a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* the value the code forms at 0x871cc: want_p = (f = 0 ? 0 : want + 0x24) *)
Lemma cm_a3 : forall E f want, ew E 33 = Z_to_bv 64 f -> ew E 11 = Z_to_bv 64 want ->
  (f = 0 \/ f = 1) -> 0 <= want -> want + 36 < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 33 0) (SLit 1)) (SLit (-1))) (SOff 11 36)) =
  (if f =? 0 then 0 else want + 36).
Proof.
intros E f want H33 H11 Hf Hw0 Hw1.
rewrite !U_SAlu, (U_atom E 33 f H33) by (destruct Hf; lia).
rewrite (U_atom_off E 11 want 36 H11) by lia. rewrite !U_SLit.
destruct Hf as [-> | ->].
- lazymatch goal with |- context [zalu_raw 63 64 ALU_AND ?t _] =>
    let t' := eval vm_compute in t in replace t with t' by (vm_compute; reflexivity) end.
  cbn [zalu_raw]. rewrite Z.land_0_l. reflexivity.
- lazymatch goal with |- context [zalu_raw 63 64 ALU_AND ?t _] =>
    let t' := eval vm_compute in t in replace t with t' by (vm_compute; reflexivity) end.
  cbn [zalu_raw]. change (if 1 =? 0 then 0 else want + 36) with (want + 36).
  change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

(* the reads a stretch of the walk keeps: outside the stack window [lo, hi), the memory after the stretch (its
   frame_of fact) reads as the memory before it; composed with KO, the fact for the walk so far *)
Ltac cm_keep KO KN Usp :=
  lazymatch goal with
  | Hfr : frame_of _ _ (mrestrict ?H _) (mrestrict ?H ?m1) |- _ =>
    lazymatch type of KO with kept_out ?rd0 (aview ?sg ?H _) ?lo ?hi =>
      assert (KN : kept_out rd0 (aview sg H m1) lo hi)
      by (intros a Ha Hn; rewrite (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => lo <= a < hi) Hfr);
          [ exact (KO a Ha Hn)
          | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq0 | Hin];
                    [injection Hq0 as <- <- <-;
                     cbn [base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in Hrr;
                     repeat (rewrite ew_havoc_old in Hrr; [|cbv; lia]); rewrite ?Usp in Hrr; lia|]);
            destruct Hin
          | exact Ha | exact Hn ])
    end
  end.

(* the entry's registers 0..31 as an environment after the walk's fresh atoms (ewset) and a call's havoc *)
Ltac cm_agree HAE :=
  let HA1 := fresh "HA1" in let HA2 := fresh "HA2" in
  destruct HAE as [HA1 HA2]; split;
  [ intros n Hn; rewrite ?ew_havoc_old by lia; cbn [ew ewset];
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end;
    exact (HA1 n Hn)
  | exact HA2 ].

Definition CM_SB : Z := 0x7fff8000.
Definition CMx : sv := SOff 32 0.
Definition CMspan : Z * Z := (CM_SB, CM_SB + 2 ^ 44 - 1).
(* atoms: 32 the shadow base, 33 the flag word want->model_set; 11 is a1 = want, 10 is a0 = got *)
Definition cm_wantR : YP09.region :=
YP09.mkRegion (Some 11%nat) 32 36 0 0 [YP09.mkChunk 32 (CVal 4 (SOff 33 0))].
Definition cm_regions : smem := [stack_region 16; cm_wantR; got_regionP; bcell_regionP 32].
Definition cm_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 256) 0);
          (32%nat, mkAF CM_SB CM_SB 0); (33%nat, mkAF 0 1 0) ] [] [].
Definition ss_cm : sstate := mkSS AF_check_model sr_atoms cm_regions None cm_facts.
Definition cm_SH : list shent := [mkSHE 11 32 36].
Definition cm_extra (f : Z) : list word := map (Z_to_bv 64) [CM_SB; f].

(* image B's pure numbers for this walk, image B's instance file's (lib/B/Prog/SegInstB.v), under the names the
   proofs below use: SegInstB.STK_check_model is check_model's frame (16 bytes, `addi sp,sp,-16` 0x8718c) plus the
   strcmp wrapper's window (2 * ESTACK); SegInstB.RLO_A / RHI_A are image B's read-only window, lib/B/Prog/SegGlob.v
   SEG_RLO / SEG_RHI (0xa1c60 / 0xa3f08, B's .data.rel.ro start and .got end) *)
#[local] Notation STK_check_model_B := SegInstB.STK_check_model (only parsing).
#[local] Notation RLO_B := SegInstB.RLO_A (only parsing).
#[local] Notation RHI_B := SegInstB.RHI_A (only parsing).

(* UBSan's alignment test at 0x87194 (`andi a2,a1,3`) reads want & 3: zero when want mod 4 = 0 *)
Lemma cm_land3 : forall w, 0 <= w -> w mod 4 = 0 -> Z.land w 3 = 0.
Proof.
intros w Hw H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. exact H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition cm_E (regs : bvmap 5 word) (f : Z) : env := Eimg (Ereg regs (cm_extra f)).
Section e.
Variable B : asyms.
(* the per-binary record facts the walk reads: the GOT word and the cell of the shadow base, and the errno cell's
   environment the wrapper call asks (fuzz_command's PALib, SegPaLib.v) *)
Hypothesis TL : PALib B.
(* the strcmp wrapper at its trampoline (0x43aa0 on image B; the image-A wrapper interface, row 17, in image B's copy
   lib/B/Rt/RtString.v of commit 5b814360ea8f) *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* the read-only words a runtime entry reads, at any point of the walk: arodata_okP at the entry, carried by the
   journal's image clause (the walk writes no image byte) *)
Lemma cm_rom_at : forall rlo rhi STK sp0 ly S W mem md (W' : world SEGS) mem' md' lyc Sc k,
arodata_okP SEGS rlo rhi B (rdW W mem) ->
ajournal SEGS B STK sp0 [] ly S W mem md [] lyc Sc W' mem' md' k ->
rt_rom_view SEGS B W' mem'.
Proof using.
intros rlo rhi STK sp0 ly S W mem md W' mem' md' lyc Sc k HRO HJ a Hrom Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a).
- apply HRO; [left; exact Hrom | exact Ho | exact He].
- destruct Hrom as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr].
- exact Ho.
- exact He.
- apply fp_spares_closed; [intros (x & [] & _) | intros X; exact (inFP_nil a X)].
Qed.

(* the entry state: the frame window, want's flag word, the GOT word and the shadow-base cell, and the shadow
   entry that removes the one instrumented check *)
Lemma cm_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md want f,
AR SEGS B ly S W mem md ->
astk_ok STK_check_model_B ly (spZ regs) ->
(forall a, spZ regs - STK_check_model_B <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 11 = w64 want -> 4096 <= want -> want + 256 <= alloc_ceiling -> off_img want 256 -> in_app want 256 ->
sa_val (rdW W mem) (want + 32) 4 f -> 0 <= f <= 1 ->
range_addressable (rdW W mem) SHADOW_OFF (want + 32) 4 ->
st_ok_pi SEGS VAL (cm_E regs f) ss_cm
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_model)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CMx cm_SH (cm_E regs f) (mrestrict (w_H W) mem).
Proof using TL LAWS.
intros W regs mem ly S md want f HAR Hstk Hpres H11 Hw4 Hwc Hwoff Hia Hf Rf HRA.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_check_model_B = 8208) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
pose proof (pal_got_cell B TL) as HGC.
unfold kImgEnd in HgotR, HcellR.
set (E := cm_E regs f).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cm_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cm_extra f)) n)
  by (intros n Hn; subst E; unfold cm_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 want)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 CM_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold cm_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold cm_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cm. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold cm_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cm_regions, cm_wantR, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB 11%nat want E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ want 32 4 _ f); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (cm_val_mem SEGS _ mem _ 4 f Hf).
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CMx CM_SB);
      [cbn [sv_denot CMx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold CM_SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold cm_regions, cm_wantR, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 11%nat want E11) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, kImgEnd in *.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HGC Hw4 Hwc Hwoff. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E11, E32, E33, !unsigned_lit_small by (unfold CM_SB; lia).
    unfold CM_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0 WS Hw4 Hwc Rf. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, cm_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E CMx 11 (want + 32) 4 want 32 36 HRA).
  + unfold U, CMx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold CM_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hia. revert Hx Hia. clear. lia.
Qed.

(* The walk from the entry to the return, under the facts the contract gives, in the form the code reads them:
   want's alignment (UBSan's test at 0x87194), want's flag word f and its shadow, and, when f = 1 and got is not
   want + 0x24, got's and the model's text sx with the wrapper's read facts. *)
Lemma cm_core : forall rlo rhi ly S W (regs : bvmap 5 word) mem md ch (got want f : Z),
afn_pre SEGS B STK_check_model_B ly S W regs mem md ch ->
arodata_okP SEGS rlo rhi B (rdW W mem) ->
getr regs 10 = w64 got -> getr regs 11 = w64 want -> 0 <= got < 2 ^ 64 ->
4096 <= want -> want + 256 <= alloc_ceiling -> off_img want 256 -> in_app want 256 -> want mod 4 = 0 ->
sa_val (rdW W mem) (want + 32) 4 f -> (f = 0 \/ f = 1) ->
range_addressable (rdW W mem) SHADOW_OFF (want + 32) 4 ->
(f = 0 -> got = 0) ->
(f = 1 -> got <> want + 36 -> got <> 0 /\ exists sx : list byte,
   astr_at SEGS W mem got sx /\ astr_at SEGS W mem (want + 36) sx /\
   aread_ok SEGS (2 * ESTACK) W regs mem got (astr_len sx + 1) /\
   aread_ok SEGS (2 * ESTACK) W regs mem (want + 36) (astr_len sx + 1) /\
   atail_vis SEGS W mem (got + astr_len sx) /\ atail_vis SEGS W mem (want + 36 + astr_len sx) /\
   got + astr_len sx + 1 <= alloc_ceiling /\ want + 36 + astr_len sx + 1 <= alloc_ceiling) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_model) regs mem md)
(apost_base SEGS B STK_check_model_B [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
 kept_out (rdW W mem) (rdW W' mem') (spZ regs - STK_check_model_B) (spZ regs) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
Proof using TL ASTRCMP LAWS RUN BR RET.
intros rlo rhi ly S W regs mem md ch got want f HPRE HRO H10 H11 Rgot Hw4 Hwc Hwoff Hia Hal Hf Hf01 HRA Hf0 Hf1.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (WS : STK_check_model_B = 8208) by reflexivity.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (cm_entry W regs mem ly S md want f HAR Hstk Hpres H11 Hw4 Hwc Hwoff Hia Hf
  ltac:(destruct Hf01; lia) HRA) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_check_model_B [] ly S W regs mem md ch HPRE) as HJ.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (cm_E regs f) n = ew (Ereg regs (cm_extra f)) n)
  by (intros n Hn; unfold cm_E; apply Eimg_low; exact Hn).
assert (HED : ed (cm_E regs f) = ed (Ereg regs (cm_extra f))) by reflexivity.
assert (HEI : img_env VAL A_LIM (cm_E regs f)) by (unfold cm_E; apply Eimg_env).
remember (cm_E regs f) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 got) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 want) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 CM_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cm_extra f)) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
assert (Rf : 0 <= f < 2 ^ 64) by (destruct Hf01; lia).
assert (Rw : 0 <= want < 2 ^ 64) by lia.
unfold cfg_at, w64.
(* 0x8718c .. 0x87194: the frame, `sd ra,8(sp)`, then UBSan's alignment test of want: a2 := want & 3 *)
paj_run_tok RUN HS HJ SHOK CMspan.
{ awr_ok_tac. all: exact Usp. }
assert (KO : kept_out (rdW W mem) (rdW W mem) (spZ regs - STK_check_model_B) (spZ regs)) by (intros a _ _; reflexivity).
cm_keep KO KEEPu Usp. clear KO HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (U11 : ew Ex 11 = Z_to_bv 64 want) by (cbn [ew ewset Nat.eqb]; exact E11) end.
(* 0x87198 bnez a2 -> unimp 0x871f8 (B only: the UBSan trap branch): want & 3 = want mod 4 = 0 by check_model_pre's
   first conjunct (Hal, cm_land3), so the branch is not taken *)
psrr_branch_tok RUN BR HS SHOK CMspan.
{ exfalso. rewrite branch_ne_U in Hc.
  rewrite (U_and_lit _ _ 3 ltac:(lia)) in Hc. rewrite (U_atom _ 11 want U11 Rw), U_lit in Hc by lia.
  rewrite (cm_land3 want ltac:(lia) Hal) in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc U11.
(* 0x8719c .. 0x871d0: the shadow base, the check on want + 0x20 (removed by the shadow entry), the flag f,
   a3 := (f = 0 ? 0 : want + 0x24), then beq a0, a3 *)
paj_run_tok RUN HS HJ SHOK CMspan.
{ awr_ok_tac. all: exact Usp. }
cm_keep KEEPu KEEP0 Usp. clear KEEPu HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (X10 : ew Ex 10 = Z_to_bv 64 got) by (cbn [ew ewset Nat.eqb]; exact E10);
  assert (X11 : ew Ex 11 = Z_to_bv 64 want) by (cbn [ew ewset Nat.eqb]; exact E11);
  assert (X33 : ew Ex 33 = Z_to_bv 64 f) by (cbn [ew ewset Nat.eqb]; exact E33) end.
psrr_branch_tok RUN BR HS SHOK CMspan.
- (* got = want_p: 0x871e4 .. 0x871ec restore and return *)
  clear Hc. paj_run_tok RUN HS HJ SHOK CMspan.
  { awr_ok_tac. exact Usp. }
  cm_keep KEEP0 KEEPr Usp. clear HF HFr HG.
  prreg HS (1%bv : bv 5) F1.
  lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
    assert (HAE4 : env_agree 32 (Ereg regs (cm_extra f)) E4) by (pose proof HAE as HAEc; cm_agree HAEc) end.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
  split; [rewrite F1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cm_extra f) HS); [exact HAE4 | vm_compute; reflexivity]|].
  split; [exact KEEPr|].
  split; [apply Permutation_refl | split; reflexivity].
- (* got <> want_p *)
  assert (Hne : got <> (if f =? 0 then 0 else want + 36)).
  { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. intros Heq. apply Hc.
    rewrite (U_atom _ 10 got X10 Rgot).
    rewrite (cm_a3 _ f want X33 X11 Hf01 ltac:(lia) ltac:(lia)).
    exact Heq. }
  clear Hc. paj_run_tok RUN HS HJ SHOK CMspan.
  { awr_ok_tac. exact Usp. }
  cm_keep KEEP0 KEEP1 Usp. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK CMspan.
  + (* 0x871d4 beqz a0 taken: got = 0, so want_p <> 0, so f = 1, and the premise makes got <> 0 *)
    exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
    rewrite (U_atom _ 10 got X10 Rgot), U_lit in Hc by lia. subst got.
    destruct Hf01 as [-> | ->]; [exact (Hne eq_refl)|].
    destruct (Hf1 eq_refl ltac:(lia)) as [Hg _]. exact (Hg eq_refl).
  + assert (Hg0 : got <> 0).
    { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
      rewrite (U_atom _ 10 got X10 Rgot), U_lit in Hc by lia. exact Hc. }
    clear Hc. paj_run_tok RUN HS HJ SHOK CMspan.
    { awr_ok_tac. exact Usp. }
    cm_keep KEEP1 KEEP2 Usp. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK CMspan.
    * (* 0x871d8 beqz a2 taken: f = 0, so the premise makes got = 0 *)
      exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
      rewrite (U_atom _ 33 f X33 Rf), U_lit in Hc by lia.
      exact (Hg0 (Hf0 Hc)).
    * (* f = 1 and got is neither NULL nor want + 0x24: got and the model are the same text sx *)
      assert (Hf1' : f = 1).
      { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
        rewrite (U_atom _ 33 f X33 Rf), U_lit in Hc by lia.
        destruct Hf01; [contradiction | assumption]. }
      clear Hc. subst f.
      assert (Hne36 : got <> want + 36) by exact Hne.
      destruct (Hf1 eq_refl Hne36) as (_ & sx & SX1 & SX2 & RX1 & RX2 & TX1 & TX2 & BX1 & BX2).
      (* 0x871dc jal wrapper_strcmp: strcmp(got, want + 0x24) *)
      paj_run_tok RUN HS HJ SHOK CMspan.
      { awr_ok_tac. exact Usp. }
      cm_keep KEEP2 KEEP3 Usp. clear HF HFr HG.
      lazymatch type of HS with
      | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msc
      | st_ok _ _ _ (restrict _ ?m) => rename m into msc
      end.
      pmkst HS.
      prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
      prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
      lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdj _ => set (mdv1 := mdj) in HJ end.
      assert (HspT : spZ (ms_regs msc) = spZ regs + -16).
      { unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
      assert (P3' : getr (ms_regs msc) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
      assert (P4' : getr (ms_regs msc) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
      assert (P10' : getr (ms_regs msc) 10 = w64 got) by (rewrite P10, E10; reflexivity).
      assert (P11' : getr (ms_regs msc) 11 = w64 (want + 36))
        by (rewrite P11, E11; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
      assert (HraT : YK0s.ret_ok (getr (ms_regs msc) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
      assert (HEP : ecall_pre_stk SEGS B (2 * ESTACK) ly S W (ms_regs msc) (ms_mem msc) mdv1).
      { eapply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_check_model_B (spZ regs) [] ly S W mem md [] ly S W (ms_mem msc) _ 0
          (ms_regs msc) (-16) HJ HspT);
        [reflexivity | lia | unfold ESTACK; lia | rewrite WS; unfold ESTACK; lia | exact HraT | exact P3' | exact P4']. }
      assert (ROMc : rt_rom_view SEGS B W (ms_mem msc)) by (eapply cm_rom_at; [exact HRO | exact HJ]).
      assert (Hlo : spZ regs - STK_check_model_B < 2 ^ 64) by lia.
      assert (HKH : kHighShadowEnd <= spZ regs - STK_check_model_B) by (rewrite C2; lia).
      assert (L0 : 0 <= astr_len sx) by (unfold astr_len; lia).
      assert (SX1c : astr_at SEGS W (ms_mem msc) got sx).
      { apply astr_atR_view. apply (astr_atR_kept _ _ _ _ got sx KEEP3);
        [apply astr_atR_view; exact SX1 | lia | unfold astr_len in BX1; lia | exact Hlo]. }
      assert (SX2c : astr_at SEGS W (ms_mem msc) (want + 36) sx).
      { apply astr_atR_view. apply (astr_atR_kept _ _ _ _ (want + 36) sx KEEP3);
        [apply astr_atR_view; exact SX2 | lia | unfold astr_len in BX2; lia | exact Hlo]. }
      assert (TX1c : atail_vis SEGS W (ms_mem msc) (got + astr_len sx)).
      { apply (atail_vis_kept SEGS W mem (ms_mem msc) _ _ _ KEEP3 TX1); [lia | | exact Hlo].
        pose proof (Z.mod_pos_bound (got + astr_len sx) 8 ltac:(lia)). lia. }
      assert (TX2c : atail_vis SEGS W (ms_mem msc) (want + 36 + astr_len sx)).
      { apply (atail_vis_kept SEGS W mem (ms_mem msc) _ _ _ KEEP3 TX2); [lia | | exact Hlo].
        pose proof (Z.mod_pos_bound (want + 36 + astr_len sx) 8 ltac:(lia)). lia. }
      assert (RX1c : aread_ok SEGS (2 * ESTACK) W (ms_regs msc) (ms_mem msc) got (astr_len sx + 1)).
      { apply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) W regs (ms_regs msc) mem (ms_mem msc) _ _ got _ KEEP3 RX1);
        [lia | exact HKH | lia | rewrite HspT, WS; unfold ESTACK; lia | exact Hlo]. }
      assert (RX2c : aread_ok SEGS (2 * ESTACK) W (ms_regs msc) (ms_mem msc) (want + 36) (astr_len sx + 1)).
      { apply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) W regs (ms_regs msc) mem (ms_mem msc) _ _ (want + 36) _ KEEP3 RX2);
        [lia | exact HKH | lia | rewrite HspT, WS; unfold ESTACK; lia | exact Hlo]. }
      assert (HC : SRr SEGS W (cfg_at SEGS (SIG SS___interceptor_trampoline_strcmp) (ms_regs msc) (ms_mem msc) mdv1)
        (art_post SEGS B (2 * ESTACK) ly S W (ms_regs msc) (ms_mem msc) mdv1
          (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0 <-> sx = sx)))
        by (exact (ASTRCMP fx ly S W (ms_regs msc) (ms_mem msc) mdv1 got (want + 36) sx sx
             HEP P10' P11' ltac:(lia) ltac:(lia) SX1c SX2c RX1c RX2c TX1c TX2c ROMc)).
      eapply SRr_bind.
      { exact (aj_art_at SEGS B LAWS Hsegs (pal_env B TL) (2 * ESTACK) (fun _ => False)
          (SIG SS___interceptor_trampoline_strcmp) W (ms_regs msc) (ms_mem msc) STK_check_model_B (spZ regs) []
          ly S W mem md [] ly S mdv1 0 (-16) (getr (ms_regs msc) 1)
          (fun regs' _ => getr regs' 10 = w64 0 <-> sx = sx)
          HJ HspT ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite WS; unfold ESTACK; lia)
          eq_refl (fun a H => False_ind _ H) HC). }
      cbv beta. intros W2 c2 _ (HW2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQr2 & HKP2). subst W2 c2.
      rewrite P1.
      (* back at 0x871e0: the frame, want's flag word, the GOT word and the cell are outside the wrapper's window *)
      jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
      match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
      { cbn [ms_mem restrict].
        pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
        pose proof (HEI 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) as HV0.
        pose proof (HEI 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) as HV12.
        pose proof (pa_obj_img 0 ltac:(lia)) as HgR. pose proof (pa_obj_img 12 ltac:(lia)) as HcR.
        unfold kImgEnd in HgR, HcR. change (A_OBJ 0) with 241%nat in HgR. change (A_OBJ 12) with 253%nat in HcR.
        assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -16 - 2 * ESTACK <= a < spZ regs + -16) ->
          mbyte SEGS (mrestrict (w_H W) mem2) a = mbyte SEGS (mrestrict (w_H W) (ms_mem msc)) a)
          by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (HKP2 a Ha Hn (fun X => X))).
        repeat apply Forall_cons; try apply Forall_nil;
          split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb]; intros a Ha.
        - rewrite Usp in Ha. apply HK; unfold ESTACK; lia.
        - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite Usp in Ha. lia.
        - rewrite E11, unsigned_lit_small in Ha by lia. apply HK; unfold ESTACK; lia.
        - lia.
        - rewrite HV0 in Ha. apply HK; unfold ESTACK; lia.
        - lia.
        - rewrite HV12 in Ha. apply HK; unfold ESTACK; lia.
        - lia. }
      clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
      lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
        assert (HEIq : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]) end.
      apply (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0) in HS;
        [| cbn [ms_regs restrict mkst]; exact (proj2 HQr2 eq_refl) | reflexivity].
      lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m =>
        let ss' := eval vm_compute in ss in change ss with ss' in HS end.
      lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
        assert (SHOK2 : sh_ok SEGS CMx [] E2 (mrestrict (w_H W) mem2)) by constructor end.
      clear SHOK.
      (* 0x871e0 bnez a0 (a0 = 0: not taken), 0x871e4 .. 0x871ec restore and return *)
      assert (KEEP4 : kept_out (rdW W mem) (rdW W mem2) (spZ regs - STK_check_model_B) (spZ regs)).
      { intros a Ha Hn. rewrite (HKP2 a Ha) by (try (intros X; exact X); rewrite WS in Hn; unfold ESTACK; lia).
        exact (KEEP3 a Ha Hn). }
      paj_run_tok RUN HS HJ2 SHOK2 CMspan.
      { awr_ok_tac. exact Usp. }
      cm_keep KEEP4 KEEP5 Usp. clear HF HFr HG.
      prreg HS (1%bv : bv 5) F1.
      lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
        assert (HAE4 : env_agree 32 (Ereg regs (cm_extra 1)) E4) by (pose proof HAE as HAEc; cm_agree HAEc) end.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
      split; [rewrite F1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cm_extra 1) HS); [exact HAE4 | vm_compute; reflexivity]|].
      split; [exact KEEP5|].
      split; [apply Permutation_refl | split; reflexivity].
Qed.

(* a read range of the strcmp wrapper's contract, from the reader facts the contract states *)
Lemma cm_aread : forall W (regs : bvmap 5 word) mem x n,
  0 <= x -> x + n <= 2 ^ 63 -> 0 <= n < 2 ^ 32 ->
  (forall a, x <= a < x + n -> rdW W mem a <> None) ->
  x + n <= spZ regs - 2 * ESTACK ->
  amem_range x n -> range_addressable (rdW W mem) SHADOW_OFF x n -> shadow_hull_vis (rdW W mem) x n ->
  aread_ok SEGS (2 * ESTACK) W regs mem x n.
Proof using.
intros W regs mem x n H0 H1 H2 HM Hsp H3 H4 H5.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [intros a Ha; split; [exact (HM a Ha) | unfold ascratch_stk; lia]|].
split; [exact H3|]. split; [exact H4 | intros _; exact H5].
Qed.

Theorem check_model_walk :
  check_model_contract SEGS B (BASE + AF_check_model) SegInstB.STK_check_model SegInstB.RLO_A SegInstB.RHI_A.
Proof using TL ASTRCMP LAWS RUN BR RET.
unfold check_model_contract, check_model_pre, EV_check_model.
intros ly S W regs mem md ch got want o g HPRE HRO H10 Rgot H11 Rwant
  (Hal & (bs & HBS & HENC) & HHP & HADDR & HOS & HOM & HSAME) HEV.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_check_model_B = 8208) by reflexivity.
unfold seg_spec.MSEG_SIZE in HHP, HADDR.
(* where want lies: inside a live heap block *)
destruct HHP as (b & m & Hin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Hboff.
assert (Hwoff : off_img want 256) by (unfold off_img in *; lia).
assert (Hia : in_app want 256) by (apply (in_app_sub b (req_size m)); [exact Hbapp | lia | lia | lia]).
(* the flag word and the model text of want *)
pose proof (cm_flag _ _ _ _ HBS HENC) as HF. unfold seg_spec.MS_MODEL_SET in HF.
destruct (cm_model_strz _ _ _ _ HBS HENC) as [HMZ HML]. unfold seg_spec.MS_MODEL in HMZ.
pose proof HENC as (LEN & _).
assert (HMAP : forall a, want <= a < want + 256 -> rdW W mem a <> None).
{ intros a Ha. assert (Hi : (Z.to_nat (a - want) < length bs)%nat) by (rewrite LEN; lia).
  specialize (HBS _ Hi). rewrite Z2Nat.id in HBS by lia. replace (want + (a - want)) with a in HBS by lia.
  rewrite HBS. discriminate. }
destruct (cm_addr_sub _ _ _ (want + 32) 4 HADDR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & HRA32 & _).
eapply SRr_mono.
- apply (cm_core RLO_B RHI_B ly S W regs mem md ch got want (if SegModel.ms_model_set g then 1 else 0) HPRE HRO
    H10 H11 Rgot ltac:(lia) ltac:(lia) Hwoff Hia Hal HF ltac:(destruct (SegModel.ms_model_set g); auto) HRA32).
  + (* model_set = 0: got = NULL *)
    intros Hf0. destruct (SegModel.ms_model_set g); [discriminate|].
    destruct o as [s|]; [cbn [SegModel.same_text] in HSAME; discriminate|]. exact HOS.
  + (* model_set = 1 and got <> want + 0x24: got is the model's text *)
    intros Hf1 Hne. destruct (SegModel.ms_model_set g); [|discriminate].
    destruct o as [s|]; [|cbn [SegModel.same_text] in HSAME; discriminate].
    cbn [SegModel.same_text] in HSAME. apply Z.eqb_eq in HSAME.
    destruct HOS as (Hg0 & HSZ & HTL).
    destruct HOM as (Hlen32 & HHG & HAG).
    pose proof (cm_strcmp_eq s (SegModel.ms_model g) (proj2 HSZ) (proj2 HMZ) HSAME) as HEQ.
    rewrite <- HEQ in HMZ, HML.
    destruct (cm_strz_bytes _ _ _ _ _ HSZ) as (BX1 & NX & _).
    destruct (cm_strz_bytes _ _ _ _ _ HMZ) as (BX2 & _ & _).
    destruct HHG as (b' & m' & Hin' & Hg1 & Hg2).
    destruct (al_blocks _ _ LAWS ly S W mem md b' m' HAR Hin') as (_ & Hg4096 & Hgceil & _ & _ & _ & Hm').
    pose proof (req_size_pos m' ltac:(lia)) as [_ Hrq'].
    assert (HLX : astr_len (map (Z_to_bv 8) s) = Z.of_nat (length s)) by (unfold astr_len; rewrite length_map; reflexivity).
    destruct HAG as (HA0 & HA1 & HA2 & HA3 & HA4).
    destruct (cm_addr_sub _ _ _ (want + 36) (Z.of_nat (length s) + 1) HADDR ltac:(lia) ltac:(lia) ltac:(lia))
      as (HM0 & HM1 & HM2 & HM3 & HM4).
    split; [exact Hg0|]. exists (map (Z_to_bv 8) s). rewrite HLX.
    split; [split; [exact BX1 | exact NX]|].
    split; [split; [exact BX2 | exact NX]|].
    split.
    { apply cm_aread; [lia | lia | lia | exact (fun a Ha => cm_strz_mapped _ _ _ HSZ a ltac:(lia)) | rewrite WS in Hslo; unfold ESTACK; lia
      | exact HA2 | exact HA3 | apply HA4; lia]. }
    split.
    { apply cm_aread; [lia | lia | lia | exact (fun a Ha => cm_strz_mapped _ _ _ HMZ a ltac:(lia)) | rewrite WS in Hslo; unfold ESTACK; lia
      | exact HM2 | exact HM3 | exact HM4]. }
    split; [exact HTL|].
    split.
    { intros a Ha. pose proof (Z.mod_pos_bound (want + 36 + Z.of_nat (length s)) 8 ltac:(lia)). apply HMAP. lia. }
    split; lia.
- cbv beta. unfold apost_base.
  intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HJ3 & HP3 & HK3 & HPm & -> & ->).
  exists ly, S, regs3, mem3, md3. split; [exact Hc3|]. split; [exact HJ3|]. split; [exact HP3|].
  split; [intros a Ha Hn _; exact (HK3 a Ha Hn)|].
  split; [exact HPm|]. split; [reflexivity|]. destruct S; eexists; reflexivity.
Qed.
End e.
End f.
End d.
