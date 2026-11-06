(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 100 of its 222 lines of code are new or changed and 2241 lines of the source are left out. *)
(* trim (reac_segconf.c:51-59, static) on the ASan+UBSan image B of reac-pw/fuzz_segconf (fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3; entry BASE + AF_trim = 0x89640, 324 bytes, 81 instructions; frame 32 bytes, no side-stack frame):
   the walk, trim_walk : trim_contract SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A, the image-A owner's contract
   lib/B/Prog/trim_c.v (G3 FINAL 6f783602b5e3, the unit owner's B copy) at image B's numbers: STK_trim, RLO_A, RHI_A from
   the image-B harness owner's lib/B/Prog/SegInstB.v (1f771e2f2066), the entry the listing term BASE + AF_trim. ADAPTED for the image-B G3 walk owner's
   image-B trim walk lane from the image-A G3 walk owner's image-A walk (commit 07dedd5b93c6: lib/A/Prog/trim_k.v,
    trim_t.v, trim_tr.v, trim_s.v) and the unit owner's UBSan walk lib/U/Prog/trim.v (commit
   523c6a205596), re-derived on image B's code (the neutral excerpt
   trim.fuzz_segconf.asan-ubsan.s, listing lib/B/Prog/SegList.v AF_trim = 0x4880).
   The pieces (each re-seeds a symbolic state at its cut and runs the token executor over the listing):
     trim.v    ENTRY 0x89640 .. 0x8967c (16 insns): the frame and its four slots, s1 = the shadow base (through the GOT
               word listing object 0 = 0xa3210, which holds the cell object 12 = 0xac7b8; PALib), s2 = 1 - p, the
               constants a1 = 0x20, a2 = the mask, a3 = -1, s0 = p; then LEAD at i = 0
     trim_l.v  LEAD  0x89680 .. 0x896bc (16 insns, check 1, trap 0x896a4)
     trim_s.v  AFTER 0x896c4 .. 0x896f0 (12 insns, the strlen call 0x896c8, trap 0x896d0)
     trim_tr.v TRAIL 0x896f4 .. 0x89738 (18 insns, check 2, trap 0x896f4)
     trim_f.v  FIN   0x8973c .. 0x8976c and 0x89774 .. 0x89780 (17 insns, check 3)
   UBSan trap sites (all three branch to the `unimp` at 0x89770; none is reached):
     0x896a4 `beq s0,a3`, a3 = -1 (s + 1 wraps): s0 = p + i <= p + |s| < 2 ^ 47 by trim_pre's sa_addr p (|s| + 1)
             (q + n <= 2 ^ 63 and the live-object bound of tr_cx_facts); decided by the executor from LEAD's seed fact.
     0x896d0 `bltu a1,a0`, a1 = s2 - 2 = 2 ^ 64 - 1 - s0, a0 = |s1| (s0 + |s1| wraps): s0 + |s1| = p + |s| < 2 ^ 47;
             trim_s.v tr_trap_ltu.
     0x896f4 `beq a2,a3`, a3 = 1 (e - 1 = 0): e >= s0 + 1 >= p + 1 >= 4097 (a live object lies at or above 4096);
             decided by the executor from TRAIL's seed fact.
   Inline ASan checks (error calls __asan_report_load1 at 0x896c0 and 0x89738, __asan_report_store1 at 0x89780; none
   is reached): check 1 load1 at p + i, check 2 load1 at e - 1, check 3 store1 at e = trim_end_addr p s; each address
   lies in [p, p + |s| + 1), whose shadow trim_pre's sa_addr makes addressable and the walk keeps to each cut.
   Section hypotheses: ASTRLEN (the image-A wrapper-layer owner's interface row 16, RtString.astrlen_realizes at the listing's strlen
   trampoline, image B 0x43a98) and the record hypothesis TL : PALib B (the shadow GOT word and cell, the errno cell's
   placement). LAWS is the base lemma YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
(* interface row 16's carrier (the image-B wrapper-layer owner, 5b814360ea8f): RtString.astrlen_realizes *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob trim_k trim_f trim_tr trim_s trim_l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- ENTRY, 0x89640: every register its own atom; the regions are the 32-byte frame below sp (written), the GOT word
   of the shadow-base cell (listing object 0, holding object 12's address) and the cell (object 12, holding SB, the
   extra atom 32) ---- *)
Definition tw_ss : sstate :=
  mkSS AF_trim sr_atoms [stack_region 32; got_regionP; bcell_regionP 32] None
    (mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0)] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the image-A wrapper-layer owner's interface row 16 (carrier lib/B/Rt/RtString.v), at the listing's strlen trampoline *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
(* the record hypothesis: the runtime library's facts at image B (lib/B/Prog/SegPaLib.v PALib) *)
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* the segments chained: FIN, TRAIL, AFTER, LEAD *)
Lemma tr_lead_all : TR_LEAD_stmt B.
Proof.
pose proof (tr_fin_ok B LAWS) as FIN.
pose proof (tr_trail_ok B LAWS FIN) as TRAIL.
pose proof (tr_after_ok B LAWS TL ASTRLEN TRAIL FIN) as AFTER.
exact (tr_lead_ok B LAWS AFTER).
Qed.

Theorem trim_walk : trim_contract SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Proof.
unfold trim_contract.
intros ly S W regs mem md ch p s HPRE HROD H10 Hp64 HTP HEV.
assert (HCX : tr_cx B ly S W regs mem md ch p s) by exact (conj HPRE (conj HROD (conj H10 (conj Hp64 (conj HTP HEV))))).
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16' & Hsp0 & Hsp47).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
pose proof (ajournal_init SEGS B STK_trim (tr_FP p s) ly S W regs mem md ch HPRE) as HJ0.
(* the entry state *)
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := Eimg (Ereg regs [w64 SB])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as Rg0. pose proof (pa_val_range (A_OBJ 12)) as Rg12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in HcellR, HgotR.
pose proof (pal_got_cell B TL) as HgcD.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E tw_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_trim)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold tw_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK. lia.
    + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia);
         reflexivity | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kImgEnd in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; try lia; exact Hal16. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HAE : env_agree 32 (Ereg regs [w64 SB]) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
unfold cfg_at. change (w64 (BASE + AF_trim)) with (Z_to_bv 64 (BASE + AF_trim)).
(* 0x89640 .. 0x8967c: the frame and its slots, the shadow base, s2 = 1 - p, the constants, s0 = p *)
paj_run_to_tok RUNTO HS HJ0 SHOK Bspan TR_LEAD.
{ awr_ok_tac; exact Usp. }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) Hfr
  ltac:(intros bq wlo whi aq Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                                             rewrite ?Usp, ?U241, ?U253 in Hrr; lia|]); destruct Hin)) as KE1 end.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the frame the prologue wrote *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict mkst] in HRg
end.
assert (HQ18 : rdword (rdW W (ms_mem ms)) (spZ regs - 32) = Some (bv_unsigned (getr regs 18))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 32) with (spZ regs + (-32)) by lia.
    replace (bv_unsigned (getr regs 18)) with
      (bv_unsigned (sv_denot E (SOff 18 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-32) 8%N (SOff 18 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
assert (HQ9 : rdword (rdW W (ms_mem ms)) (spZ regs - 24) = Some (bv_unsigned (getr regs 9))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 24) with (spZ regs + (-24)) by lia.
    replace (bv_unsigned (getr regs 9)) with
      (bv_unsigned (sv_denot E (SOff 9 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-24) 8%N (SOff 9 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
assert (HQ8 : rdword (rdW W (ms_mem ms)) (spZ regs - 16) = Some (bv_unsigned (getr regs 8))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
    replace (bv_unsigned (getr regs 8)) with
      (bv_unsigned (sv_denot E (SOff 8 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
assert (HQ1 : rdword (rdW W (ms_mem ms)) (spZ regs - 8) = Some (bv_unsigned (getr regs 1))).
{ apply (rdword_of_val_mem SEGS).
  - replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
    replace (bv_unsigned (getr regs 1)) with (bv_unsigned (sv_denot E (SOff 1 0)) mod 2 ^ (8 * Z.of_N 8))
      by (cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_small; apply u64_range).
    exact (field_of_region_any E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) HRg Usp
             ltac:(cbn; tauto) ltac:(cbn; lia)).
  - apply u64_range. }
(* the registers at LEAD *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TR_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKEPT.
cbn [ms_regs restrict mkst] in HKEPT.
lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
  assert (HAEn : env_agree 32 (Ereg regs [w64 SB]) En) by (env_agree_chain HAE) end.
assert (E10n : ew _ 10 = Z_to_bv 64 p) by (rewrite (proj1 HAEn 10%nat ltac:(lia)); exact E10).
pose proof (proj1 HAEn 2%nat ltac:(lia)) as E2n.
prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (18%bv : bv 5) P18. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
eapply (tr_lead_all ly S W regs mem md ch p s rg mm mdn 0%nat HCX) end.
- (* tr_mid at LEAD *)
  split; [exact HJ0|].
  split; [intros a Ha Hn; apply KE1; [exact Ha | rewrite HSTK in Hn; lia]|].
  split; [intros a Ha Hp Hi; lazymatch goal with HG : mem_grows _ _ |- _ => exact (apresent_grows _ _ _ a HG Hp) end|].
  split; [exact HQ1|]. split; [exact HQ8|]. split; [exact HQ9|]. exact HQ18.
- (* tr_regs *)
  split; [|split].
  + first [ rewrite P2; cbn [sv_denot]; try rewrite E2n; try rewrite (EE 2%nat 2%bv eq_refl); unfold w64, spZ;
            first [reflexivity | f_equal; lia]
          | match type of P2 with ?t => idtac "P2" t end; fail ].
  + first [ rewrite P9; cbn [sv_denot];
            repeat match goal with H : ew ?Ex ?n = _ |- context [ew ?Ex ?n] => rewrite H end;
            rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | unfold w64; f_equal; lia]
          | match type of P9 with ?t => idtac "P9" t end; match type of E32 with ?t => idtac "E32" t end; fail ].
  + exact HKEPT.
- lia.
- first [ rewrite P8; cbn [sv_denot]; repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
          unfold w64; first [reflexivity | f_equal; lia]
        | match type of P8 with ?t => idtac "P8" t end; fail ].
- first [ rewrite P10; cbn [sv_denot]; repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
          unfold w64; first [reflexivity | f_equal; lia]
        | match type of P10 with ?t => idtac "P10" t end; fail ].
- first [ rewrite P18; cbn [sv_denot];
          repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
          rewrite ?w64_off, ?md_mul_lit, ?alu64_add_lit, ?alu64_sub_lit;
          unfold w64; first [reflexivity | f_equal; lia]
        | match type of P18 with ?t => idtac "P18" t end; fail ].
- first [exact P11 | rewrite P11; vm_compute; reflexivity | match type of P11 with ?t => idtac "P11" t end; fail].
- first [exact P12 | rewrite P12; vm_compute; reflexivity | match type of P12 with ?t => idtac "P12" t end; fail].
- first [exact P13 | rewrite P13; vm_compute; reflexivity | match type of P13 with ?t => idtac "P13" t end; fail].
Qed.

End e.
End f.
End d.
