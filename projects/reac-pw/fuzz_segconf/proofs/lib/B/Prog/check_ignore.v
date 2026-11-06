(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 207 of its 258 lines of code are new or changed and 318 lines of the source are left out. *)
(* the image-B port of lib/A/Prog/check_ignore.v (commit abff6ebfc45c): the walk of check_ignore
   on reac-pw/fuzz_segconf's image B (fuzz_segconf.asan-ubsan, entry 0x87210 = BASE + AF_check_ignore, BASE =
   seg_text 0x84dc0, AF_check_ignore 0x2450; 26 instructions, one instrumented check, no call on the path that
   returns), against image B's copy of check_ignore_contract (lib/B/Prog/check_ignore_c.v, the text of the FINAL contract
   6f783602b5e3) at A_check_ignore := BASE + AF_check_ignore and STK_check_ignore := SegInstB.STK_check_ignore (16,
   the frame; image B's instance file lib/B/Prog/SegInstB.v).

   Image B's code is image A's with the addresses moved and two added UBSan pieces
   (the unit record's Bwalks-G45-plans/plan-check_ignore.md has the A-to-B instruction map):
   - 0x87218 `andi a2,a1,3` / 0x8721c `bnez a2,0x87254`: the alignment test of want, to the UBSan trap `unimp` at
     0x87254. Refuted inside the first symbolic run: atom 11 (want) carries the fact `PTR 2` (want mod 2 ^ 2 = 0, from
     the contract's premise `want mod 4 = 0`), so the executor folds `andi a2,a1,3` to the literal 0
     (YP0m s_and_ptr_sound) and decides `bnez a2` not taken (PaRun decide_cond2_sound). No other edge reaches 0x87254.
   - 0x87274 `unimp`, after `jal abort` 0x87270: no branch targets it and the only fall-through into it is the
     return of abort, on the abort arm, which is dead (below); so no path reaches it.
   The rest is image A's walk at B's addresses:
   - 0x87210 takes a 16-byte frame and saves ra; 0x87220-0x87228 load the shadow base through the GOT word 0xa3210
     (A_OBJ 0) of the shadow cell 0xac7b8 (A_OBJ 12); 0x8722c-0x8723c check the shadow byte of want + 24 (the
     ignore field), with the slow block at 0x87258-0x87260 and the error path (a call of the 4-byte report entry) at
     0x87268; 0x87240 loads want->ignore; 0x87244 `bne a0,a1` goes to the no-return hook (0x8726c) and abort
     (0x87270) when got differs from it; 0x87248-0x87250 restore and return.
   - the check: the contract's sa_addr rd want MSEG_SIZE says the field's 4 bytes addressable, so the executor's
     token removes the check and the error path;
   - the field's region is apart from the frame and from the image's GOT word and shadow cell: want is inside a live
     heap block (the contract's sa_heap), below the stack window (afn_pre's astk_ok) and off the image's span
     (AR_client_img_law with PAImg's pa_img_cover);
   - the abort arm: the contract's premise got = b2z b and Bool.eqb b (ms_ignore g) = true makes the loaded field
     (flag_enc (ms_ignore g), the word 0 or 1) equal to got, so the branch to 0x8726c is refuted;
   - the post's sa_kept (window [sp - 16, sp), footprint none): each of the two runs gives frame_of over its
     symbolic regions, whose only write window is the frame [sp - 16, sp) (the GOT word, the shadow cell and the
     field are read-only regions), so every byte outside the frame reads at the return as at the entry
     (PaDenot.kept_of_frame, composed over the two runs). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase check_ignore_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the ignore field through a reader ---- *)
(* the 4 bytes of want->ignore (MS_IGNORE = 0x18) are the flag's 4 little-endian bytes, by mseg_enc *)
Lemma cig_field : forall rd want g, sa_mseg rd want g ->
  sa_val rd (want + 24) 4 (if SegModel.ms_ignore g then 1 else 0).
Proof.
intros rd want g (bs & HB & HE).
destruct HE as (Hlen & _ & _ & _ & Hig & _).
unfold seg_spec.flag_enc in Hig.
intros k Hk.
assert (HN : nth (24 + k) bs ZB0 = nth k (seg_spec.fldz seg_spec.MS_IGNORE 4 bs) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld, seg_spec.MS_IGNORE. change (Z.to_nat 0x18) with 24%nat. change (Z.to_nat 4) with 4%nat.
  rewrite nth_firstn. replace (k <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
  rewrite nth_skipn. f_equal; lia. }
specialize (HB (24 + k)%nat ltac:(rewrite Hlen; lia)).
replace (want + Z.of_nat (24 + k)) with (want + 24 + Z.of_nat k) in HB by lia.
rewrite HB, HN, Hig. f_equal.
destruct (SegModel.ms_ignore g); do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Qed.
(* an n-wide value read through the world's view is the same value of the restricted memory *)
Lemma cig_val_of_sa : forall segs H (mem : word -> option byte) a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.

(* ---- the symbolic entry state ---- *)
(* atoms: 0..31 the registers at the entry (10 got, 11 want), 32 the shadow base, 33 the value of want->ignore;
   A_OBJ 0 the GOT word of the shadow cell (image B 0xa3210), A_OBJ 12 the cell (image B 0xac7b8) (B's SegAddr.v
   seg_objs). Atom 11's fact PTR 2 carries want mod 4 = 0: it decides the UBSan alignment test at 0x87218/0x8721c. *)
Definition cig_Bx : sv := SOff 32 0.
Definition cig_mseg : YP09.region := YP09.mkRegion (Some 11%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 33 0))].
Definition cig_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; cig_mseg ].
Definition cig_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, PTR 2); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 1 0) ] [] [].
Definition ss_cig : sstate := mkSS AF_check_ignore sr_atoms cig_regions None cig_facts.
Definition cig_SH : list shent := [ mkSHE 11 24 28 ].
Definition cig_extra (v : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 v].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition EC (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs (cig_extra v)).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

(* a run's frame_of over regions whose one write window is the 16-byte frame at atom 2 (= sp at the entry, Usp)
   keeps every byte outside [sp - 16, sp) *)
Ltac cig_keep HFr K Usp :=
  lazymatch type of Usp with _ = ?sp =>
  lazymatch type of HFr with frame_of ?Ex _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  let Us := fresh "Us" in
  assert (Us : bv_unsigned (ew Ex 2) = sp) by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp);
  assert (K : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 16 <= x < sp) -> aview SEGS H m2 x = aview SEGS H m1 x)
  by (intros kx kHx kHn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => sp - 16 <= x < sp) HFr);
      [ intros kb kwlo kwhi ka kHin kHrr; vm_compute in kHin;
        repeat (destruct kHin as [kHq | kHin];
          [injection kHq as <- <- <-; cbn [base_val] in kHrr; rewrite ?Us in kHrr; lia|]);
        destruct kHin
      | exact kHx | exact kHn ]);
  clear Us end end.

(* a byte of a live block is off the image's span *)
Lemma cig_blk_off : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> a < 0x10000 \/ kImgEnd <= a.
Proof using fx rc SK PI B LAWS.
intros ly S W mem md p n a HAR Hin Ha.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Ha)))))
  as [Hz _].
pose proof (pa_img_cover ly S md (proj1 (proj2 HAR))) as [C1 C2].
unfold in_zr in Hz. lia.
Qed.

Lemma cig_entry : forall ly S W (regs : bvmap 5 word) mem md ch want v bk m,
afn_pre SEGS B 16 ly S W regs mem md ch ->
getr regs 11 = w64 want -> want mod 4 = 0 ->
In (bk, m) (ablocks B ly S) -> bk <= want -> want + 28 <= bk + m ->
range_addressable (rdW W mem) SHADOW_OFF (want + 24) 4 ->
sa_val (rdW W mem) (want + 24) 4 v -> 0 <= v <= 1 ->
st_ok_pi SEGS VAL (EC regs v) ss_cig
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_ignore)) mem (seg_rom SEGS)))
/\ sh_ok SEGS cig_Bx cig_SH (EC regs v) (mrestrict (w_H W) mem).
Proof using fx rc SK PI B LAWS TL.
intros ly S W regs mem md ch want v bk m HPRE H11 Hal4 Hin Hb1 Hb2 RA HV Rv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md bk m HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hpapp & _ & _ & Hkr).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
assert (Hoff : want + 28 <= 0x10000 \/ kImgEnd <= want + 24).
{ pose proof (cig_blk_off ly S W mem md bk m (want + 24) HAR Hin ltac:(lia)).
  pose proof (cig_blk_off ly S W mem md bk m (want + 27) HAR Hin ltac:(lia)). unfold kImgEnd in *. lia. }
pose proof (pa_obj_img 0%nat ltac:(lia)) as [G0a G0b].
pose proof (pa_obj_img 12%nat ltac:(lia)) as [G12a G12b].
pose proof (pal_got_cell B TL) as Hgc.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite restrict_mkst_fx.
set (E := EC regs v).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cig_extra v)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 want)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0).
{ intros n v0 Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold kImgEnd in G0b, G12b, Hoff.
split.
- unfold ss_cig. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cig_regions, stack_region, got_regionP, bcell_regionP, cig_mseg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r, SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 11%nat want E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ want 24 4 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (cig_val_of_sa SEGS (w_H W) mem _ 4 v HV).
  + apply pairwise_disjoint_of_extents. unfold cig_regions, stack_region, got_regionP, bcell_regionP, cig_mseg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12), (VB 11%nat want E11) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - Hslo Hshi H47 C1 Hceil Hstk0 Hpceil Hreq Hb1 Hb2 Hoff G0a G0b G12a G12b Hgc.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cig_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    clear - Hal16 Hslo Hshi H47 C1 Hceil Hstk0 Hpceil Hreq Hb1 Hb2 Hp4096 Rv Hal4. unfold SB.
    repeat split; first [lia | reflexivity].
- unfold sh_ok, cig_SH. constructor; [|constructor].
  assert (UB : U E cig_Bx = SB)
  by (unfold U, cig_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; apply unsigned_lit_small; unfold SB; lia).
  rewrite SB_SHADOW_OFF in UB.
  assert (U11 : U E (SOff 11 0) = want) by (apply U_atom; [exact E11 | lia]).
  apply (shent_ok_of_range SEGS (w_H W) mem E cig_Bx 11 (want + 24) 4 want 24 28 RA UB U11); [lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the walk from the entry to the return, under the facts the contract gives *)
Lemma cig_core : forall ly S W (regs : bvmap 5 word) mem md ch (want : Z) (b : bool) bk m,
afn_pre SEGS B 16 ly S W regs mem md ch ->
getr regs 10 = w64 (if b then 1 else 0) -> getr regs 11 = w64 want -> want mod 4 = 0 ->
In (bk, m) (ablocks B ly S) -> bk <= want -> want + 28 <= bk + m ->
range_addressable (rdW W mem) SHADOW_OFF (want + 24) 4 ->
sa_val (rdW W mem) (want + 24) 4 (if b then 1 else 0) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_check_ignore) regs mem md)
(apost_base SEGS B 16 [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => sa_kept SEGS W mem W' mem' regs 16 (fun _ => False) /\ sa_noalloc B ly S ly' S')).
Proof using fx rc SK PI B LAWS TL.
intros ly S W regs mem md ch want b bk m HPRE H10 H11 Hal4 Hin Hb1 Hb2 RA HV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
set (v := if b then 1 else 0) in *.
assert (Rv : 0 <= v <= 1) by (subst v; destruct b; lia).
destruct (cig_entry ly S W regs mem md ch want v bk m HPRE H11 Hal4 Hin Hb1 Hb2 RA HV Rv) as [HS SHOK].
pose proof (ajournal_init SEGS B 16 [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
unfold YK0s.ret_ok in Hra.
remember (EC regs v) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cig_extra v)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 v)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cig_extra v)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
unfold cfg_at. change (w64 (BASE + AF_check_ignore)) with (Z_to_bv 64 (BASE + AF_check_ignore)).
(* 0x87210 .. 0x87244: the frame; the UBSan alignment test of want (0x87218 andi a2,a1,3 folds to 0 by atom 11's
   fact PTR 2, so 0x8721c bnez a2 to the trap 0x87254 is decided not taken); the shadow base; the check on
   want->ignore (removed by the token: the field's shadow is addressable); the load of the field, up to bne a0,a1 *)
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
cig_keep HFr K1 Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* got <> want->ignore: the arm to the no-return hook (0x8726c) and abort (0x87270), then the trap word 0x87274;
     refuted, since both are v *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. apply Hc.
  lazymatch type of Hc with U ?Ex _ <> _ =>
    rewrite (U_atom Ex 10 v ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E10) ltac:(lia)),
            (U_atom Ex 33 v ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) end.
  reflexivity.
- (* 0x87248 .. 0x87250: restore ra, pop the frame, return *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
  cig_keep HFr K2 Usp. clear HF HFr HG.
  prreg HS (1%bv : bv 5) R1.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAEx : env_agree 32 (Ereg regs (cig_extra v)) Ex)
    by (first [exact HAE | destruct HAE as [HA HD]; split;
          [intros n Hn; rewrite ?ew_ewset_other by lia; apply HA; exact Hn | rewrite ?ed_ewset; exact HD]]) end.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  eexists _, _, _, _, _.
  split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cig_extra v) HS); [exact HAEx | vm_compute; reflexivity]|].
  (* every byte outside the frame [sp - 16, sp) reads as at the entry: the two runs' frame_of *)
  split; [intros ka Hka Hkn _; exact (eq_trans (K2 ka Hka Hkn) (K1 ka Hka Hkn))|].
  (* no call, no frame of the side stack, no allocation: the layout and the allocator state are the entry's *)
  unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
  exists (st_fs S). destruct S; reflexivity.
Qed.

(* the contract, at image B's entry BASE + AF_check_ignore (0x87210) and the window SegInstB.STK_check_ignore (16, the
   16-byte frame `addi sp,sp,-16` at 0x87210; no call on the live path) *)
Theorem check_ignore_walk : check_ignore_contract SEGS B (BASE + AF_check_ignore) SegInstB.STK_check_ignore.
Proof using fx rc SK PI B LAWS TL.
unfold check_ignore_contract, check_ignore_pre, SegInstB.STK_check_ignore.
intros ly S W regs mem md ch got want b g HPRE H10 Rgot H11 Rwant
  (Hal4 & HMS & (bk & m & Hin & Hb1 & Hb2) & HADDR & Hgot & Heq) HEV.
apply Bool.eqb_prop in Heq. subst got. unfold seg_spec.b2z in H10.
pose proof (cig_field _ want g HMS) as HV. rewrite <- Heq in HV.
unfold seg_spec.MSEG_SIZE in Hb2, HADDR.
destruct HADDR as (_ & _ & _ & RA & _).
exact (cig_core ly S W regs mem md ch want b bk m HPRE H10 H11 Hal4 Hin Hb1 ltac:(lia)
  (range_addressable_sub _ _ want 256 (want + 24) 4 RA ltac:(lia) ltac:(lia)) HV).
Qed.
End h.
End f.
End d.
