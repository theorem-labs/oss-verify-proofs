(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 207 of its 252 lines of code are new or changed and 408 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the point K4 of its walk (0x8a36c,
   after the strlen wrapper), written for image B (image A's walk has no K4 file at commit
   ceb7e39832b2). From K4 (a0 = strlen of the segment, s4 = plen = di, s5 = v):
     0x8a36c addi a0,a0,-16; 0x8a370 li a1,-17; 0x8a374 bltu a0,a1 -> 0x8a320 (return 0): not taken, length s < 16
       (split_pre), vs_len_test; so the premise vs_KR_stmt goes unused (this stretch never reaches the epilogue);
     0x8a378 mv a0,s1 (parent); 0x8a37c mv a1,s2 (segment); 0x8a380 mv a2,s4 (di);
     0x8a384 jal: the memory-checking runtime's checked memcpy (listing target SS___asan_memcpy, B 0x5596c), through
       aintrin_realizes OCpy (lib/B/YG0d.v) and aj_intrin_atS (lib/B/Prog/PaCall.v), back at K5 (0x8a388).
   No UBSan trap branch and no instrumented check lies in this stretch. The checked memcpy's premises: the source
   [segment, segment + di) is readable (sa_str) and outside the call's stack window (sa_loc), with its shadow
   (sa_addr segment (length s + 1)); the destination [parent, parent + di) is in the footprint (split_W, as
   split_copy s = Some di, vs_copy_some), writable by the journal (vs_dst_awr from sa_dst), with its shadow
   (sa_addr parent 16); the two are apart (sa_disj segment (cstr_span segment s) parent 16); di < 16. Both shadows
   are read at the call state through the stretch's keep: memory outside the stack window is the entry's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the shadow base s6 = atom 22 = SB, and the span of the shadow band *)
Definition vs4_Bx : sv := SOff 22 0.
Definition vs4_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the seeded state at K4: a0 = strlen of the segment, atom 10, in [0, 15] *)
Definition vs4_fs : list (nat * afact) := [(10%nat, mkAF 0 15 0)].

(* the shadow hull of a prefix of a range lies in the range's *)
Lemma vs4_hull_sub : forall (rd : reader) x n n', shadow_hull_vis rd x n -> 0 < n' <= n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' H Hn s Hs. apply H.
assert (M : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8).
{ unfold shadow_addr. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the kept registers of the body move across a call that preserves the callee-saved registers *)
Lemma vs4_regs_pres : forall e r1 r2, vs_regs e r1 -> aregs_preserved r1 r2 -> vs_regs e r2.
Proof using.
intros e r1 r2 (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27) HP.
assert (P : forall z, acallee_saved z -> getr r2 (Z_to_bv 5 z) = getr r1 (Z_to_bv 5 z)) by exact HP.
split; [unfold spZ; change (getr r2 2) with (getr r2 (Z_to_bv 5 2)); rewrite (P 2) by (unfold acallee_saved; lia); exact Hsp|].
split; [change (getr r2 3) with (getr r2 (Z_to_bv 5 3)); rewrite (P 3) by (unfold acallee_saved; lia); exact G3|].
split; [change (getr r2 4) with (getr r2 (Z_to_bv 5 4)); rewrite (P 4) by (unfold acallee_saved; lia); exact G4|].
split; [change (getr r2 8) with (getr r2 (Z_to_bv 5 8)); rewrite (P 8) by (unfold acallee_saved; lia); exact G8|].
split; [change (getr r2 9) with (getr r2 (Z_to_bv 5 9)); rewrite (P 9) by (unfold acallee_saved; lia); exact G9|].
split; [change (getr r2 18) with (getr r2 (Z_to_bv 5 18)); rewrite (P 18) by (unfold acallee_saved; lia); exact G18|].
split; [change (getr r2 19) with (getr r2 (Z_to_bv 5 19)); rewrite (P 19) by (unfold acallee_saved; lia); exact G19|].
split; [change (getr r2 22) with (getr r2 (Z_to_bv 5 22)); rewrite (P 22) by (unfold acallee_saved; lia); exact G22|].
intros r Hr. rewrite (P r) by (unfold acallee_saved; lia). exact (G27 r Hr).
Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis MEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* where an object of sa_loc lies: below the allocator's ceiling, so below every stack window *)
Lemma vs4_loc : forall ly S W mem md q n, AR SEGS B ly S W mem md -> 0 < n -> sa_loc SEGS B ly S q n ->
  0 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR Hn [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | Himg]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B0 & B1 & _ & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2). lia.
- pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (Himg q ltac:(lia)) as (Hq & _). destruct (Himg (q + n - 1) ltac:(lia)) as (Hq' & _).
  apply pa_segs_low in Hq. apply pa_segs_low in Hq'. lia.
Qed.

Lemma vs_K4 : vs_KR_stmt B gotw guard -> vs_K5_stmt B gotw guard -> vs_K4_stmt B gotw guard.
Proof using MEMCPY.
intros HKR HK5. unfold vs_K4_stmt.
intros e regs' mem' md' di v HE HC Hdi Hdi0 Hne Hdig Hv Hvr R10 R20 R21.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
pose proof HC as (HJ & HR & HSL & HKP & HPP).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
assert (HVS : VS_STK = 12352) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof pa_segs_low as Hsegs.
unfold e_sp in *.
(* the model: the copy split makes is di bytes, di < length s < 16 *)
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
assert (Hcopy : split_copy (e_s e) = Some di)
  by (apply vs_copy_some; [exact Hnul | exact Hlen | exact Hdi | exact Hdi0 | exact Hne | exact Hdig | unfold vs_tail in Hv; lia]).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
(* where parent and the segment lie *)
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & Pplace).
destruct (vs4_loc (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_seg e) (Z.of_nat (length (e_s e)) + 1) HAR
  ltac:(lia) Hsloc) as (Slo & Shi).
pose proof Hpadd as (Pa0 & Pa1 & Pam & Para & Phull).
pose proof Hsadd as (Sa0 & Sa1 & Sam & Sra & Shull).
(* the seeded state at K4 *)
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (HAE : env_agree 32 (Ereg regs' (vs_xs (e_regs e) ++ [])) E)
  by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K4 vs4_fs)
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K4)) mem' (seg_rom SEGS)))).
{ apply vs_seedK.
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - lia.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - exact G22.
  - unfold vs4_fs. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite (EV 10%nat 10%bv eq_refl), R10.
    unfold w64. rewrite !unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; first [exact I | lia]. }
assert (SHOK0 : sh_ok SEGS vs4_Bx [] E (mrestrict (w_H (e_W e)) mem')) by (unfold sh_ok; apply Forall_nil).
unfold vs_goal, vs_cfg.
(* 0x8a36c addi a0,a0,-16; 0x8a370 li a1,-17: the run stops at the branch 0x8a374 `bltu a0,a1`, which the seed fact
   of a0 does not decide (a0 - 16 wraps) *)
paj_run_tok RUN HS HJ SHOK0 vs4_Bspan.
{ vs_awr_ro. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv1 := mdq) in *; clearbody mdv1 end.
(* the stretch writes no memory *)
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as KA1 end.
lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGR1 end.
clear HF HFr.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK0 vs4_Bspan.
{ (* 0x8a374 `bltu a0,a1` taken (to 0x8a320, return 0): refuted by vs_len_test, length s < 16 (split_pre) *)
  exfalso. rewrite branch_ltu_U, U_SOff, U_SLit, (EV 10%nat 10%bv eq_refl), R10 in Hc.
  unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  apply Z.ltb_lt in Hc. unfold zcanon, M64 in Hc.
  pose proof (vs_len_test (Z.of_nat (length (e_s e))) ltac:(lia)) as HT. apply Z.ltb_ge in HT.
  replace (Z.of_nat (length (e_s e)) + -16) with (Z.of_nat (length (e_s e)) - 16) in Hc by lia.
  rewrite (Z.mod_small 18446744073709551599 (2 ^ 64)) in Hc by lia. lia. }
(* not taken: 0x8a378 mv a0,s1 (parent); 0x8a37c mv a1,s2 (segment); 0x8a380 mv a2,s4 (di); the run stops at the
   call of the checked memcpy, 0x8a384 *)
paj_run_tok RUN HS HJ SHOK0 vs4_Bspan.
{ vs_awr_ro. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv := mdq) in *; clearbody mdv end.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ (ms_mem ms1)) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as KA2 end.
lazymatch goal with Hg : mem_grows (mrestrict _ (ms_mem ms1)) _ |- _ => rename Hg into HGR2 end.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> rdW (e_W e) (ms_mem ms) a = rdW (e_W e) mem' a)
  by (intros a Ha Hf; rewrite (KA2 a Ha Hf); exact (KA1 a Ha Hf)).
assert (HGR : mem_grows (mrestrict (w_H (e_W e)) mem') (mrestrict (w_H (e_W e)) (ms_mem ms)))
  by exact (mem_grows_trans _ _ _ HGR1 HGR2).
pmkst HS.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs' (vs_xs (e_regs e) ++ []) HS HAE ltac:(vm_compute; reflexivity)) as HPA.
cbn [ms_regs restrict] in HPA.
(* memory outside the stack window is the entry's at the call *)
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (e_regs e) - VS_STK <= a < spZ (e_regs e)) ->
  rdW (e_W e) (ms_mem ms) a = rdW (e_W e) (e_mem e) a).
{ intros a Ha Hw. rewrite (KA a Ha (fun x => x)). exact (HKP a Ha Hw (fun x => x)). }
assert (P10 : getr (ms_regs ms) 10 = w64 (e_parent e)) by (rewrite U10, (EV 9%nat 9%bv eq_refl); exact G9).
assert (P11 : getr (ms_regs ms) 11 = w64 (e_seg e)) by (rewrite U11, (EV 18%nat 18%bv eq_refl); exact G18).
assert (P12 : getr (ms_regs ms) 12 = w64 (Z.of_nat di)) by (rewrite U12, (EV 20%nat 20%bv eq_refl); exact R20).
assert (Psp : spZ (ms_regs ms) = spZ (e_regs e) + -64)
  by (unfold spZ at 1; rewrite U2, (EV 2%nat 2%bv eq_refl); change (bv_unsigned (getr regs' 2)) with (spZ regs'); lia).
assert (P3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite U3, (EV 3%nat 3%bv eq_refl), G3; exact Hgp).
assert (P4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite U4, (EV 4%nat 4%bv eq_refl), G4; exact Htp).
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + VS_K5))) by (apply ret_ok_codeptr_v; [unfold VS_K5; lia | reflexivity]).
(* 0x8a384 jal: the checked memcpy of the di bytes at segment to parent *)
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIG SS___asan_memcpy) (MEMCPY fx) (e_W e) (ms_regs ms) (ms_mem ms)
    VS_STK (spZ (e_regs e)) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] (e_ly e) (e_S e) mdv 0
    (e_parent e) (e_seg e) (Z.of_nat di) (-64) (Z_to_bv 64 (BASE + VS_K5))
    HJ P10 P11 P12 ltac:(lia) ltac:(lia) ltac:(lia) Psp ltac:(reflexivity) ltac:(lia) ltac:(lia) P3 P4 U1 HraT).
  - (* the destination: a footprint byte (split_W, split_copy s = Some di) the journal may write (sa_dst), outside
       the call's window *)
    intros a Ha. split.
    + apply (vs_dst_awr B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) VS_STK (e_FP e) (e_ly e) (e_S e) []
        (e_parent e) 16 a HAR Hpdst eq_refl (Permutation_refl _)); [| lia].
      unfold e_FP, split_W. rewrite Hcopy. exists (e_parent e, e_parent e + Z.of_nat di + 1).
      split; [apply in_or_app; left; left; reflexivity | cbn [fst snd]; lia].
    + destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia.
  - (* writable at the call state: present in every arm of sa_dst *)
    intros a Ha _ _. pose proof (proj1 HJ) as HARm.
    destruct Hpdst as [((cid & pos & Hin & Hcid & F1 & F2) & _) | [((b & m & Hin & F1 & F2) & _) | (F1 & F2 & Fpres & _)]].
    + destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARm Hin) as (_ & _ & Fp & _).
      apply (apresent_writable SEGS). exact (proj1 (Fp a ltac:(lia))).
    + destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARm Hin) as (_ & _ & _ & _ & Bp & _ & Bm).
      pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2].
      apply (apresent_writable SEGS). exact (proj1 (Bp a ltac:(lia))).
    + apply (apresent_writable SEGS). eapply apresent_grows; [exact HGR|]. apply HPP.
      replace a with (e_parent e + (a - e_parent e)) by lia. apply Fpres. lia.
  - unfold amem_range in *; lia.
  - apply (range_addressable_kept_win (rdW (e_W e) (e_mem e)) _ (spZ (e_regs e) - VS_STK) (spZ (e_regs e)));
      [exact KT | lia | lia | lia |].
    apply (range_addressable_sub _ _ (e_parent e) 16); [exact Para | lia | lia].
  - intros Hpos. apply (shadow_hull_vis_kept_win (rdW (e_W e) (e_mem e)) _ (spZ (e_regs e) - VS_STK) (spZ (e_regs e)));
      [exact KT | lia | lia | lia | exact Hpos |].
    apply (vs4_hull_sub _ _ 16); [exact (Phull ltac:(lia)) | lia].
  - (* the source: readable (sa_str), apart from parent (sa_disj), its shadow (sa_addr) *)
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite (KT a ltac:(lia) ltac:(lia)).
        replace a with (e_seg e + Z.of_nat (Z.to_nat (a - e_seg e))) by lia.
        rewrite (proj1 (proj1 Hstr) (Z.to_nat (a - e_seg e)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
      - rewrite Psp. lia. }
    split.
    { unfold sa_disj, seg_spec.cstr_span in Hpdisj.
      pose proof (Z.mod_pos_bound (- (e_seg e + Z.of_nat (length (e_s e)) + 1)) 8 ltac:(lia)) as Hm8. lia. }
    split; [unfold amem_range in *; lia|].
    split.
    { apply (range_addressable_kept_win (rdW (e_W e) (e_mem e)) _ (spZ (e_regs e) - VS_STK) (spZ (e_regs e)));
        [exact KT | lia | lia | lia |].
      apply (range_addressable_sub _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [exact Sra | lia | lia]. }
    intros Hpos. apply (shadow_hull_vis_kept_win (rdW (e_W e) (e_mem e)) _ (spZ (e_regs e) - VS_STK) (spZ (e_regs e)));
      [exact KT | lia | lia | lia | exact Hpos |].
    apply (vs4_hull_sub _ _ (Z.of_nat (length (e_s e)) + 1)); [exact (Shull ltac:(lia)) | lia]. }
(* back at K5 (0x8a388) *)
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
assert (HP12 : aregs_preserved regs' regs2) by exact (aregs_preserved_trans _ _ _ HPA HP2).
assert (PR : forall z, acallee_saved z -> getr regs2 (Z_to_bv 5 z) = getr regs' (Z_to_bv 5 z)) by exact HP12.
(* every byte outside parent's di bytes and the call's window reads as at K4 *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (e_parent e <= a < e_parent e + Z.of_nat di) ->
  ~ (spZ (e_regs e) - 64 - 4096 <= a < spZ (e_regs e) - 64) -> rdW (e_W e) mem2 a = rdW (e_W e) mem' a).
{ intros a Ha H1 H2. rewrite (HKC a Ha H1 ltac:(lia)). exact (KA a Ha (fun x => x)). }
apply (HK5 e regs2 mem2 md2 di v HE).
- unfold vs_ctxW, e_sp.
  split; [exact HJ2|]. split; [exact (vs4_regs_pres e regs' regs2 HR HP12)|]. split.
  { apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha. apply KM; [lia | | lia].
    destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia. }
  split.
  { intros a Ha Hw Hpa. rewrite (KM a Ha Hpa ltac:(lia)). exact (HKP a Ha Hw (fun x => x)). }
  intros a Hpa. apply HPRS. eapply apresent_grows; [exact HGR|]. exact (HPP a Hpa).
- exact Hdi.
- exact Hdi0.
- exact Hne.
- exact Hdig.
- exact Hv.
- exact Hvr.
- change (getr regs2 20) with (getr regs2 (Z_to_bv 5 20)). rewrite (PR 20) by (unfold acallee_saved; lia). exact R20.
- change (getr regs2 21) with (getr regs2 (Z_to_bv 5 21)). rewrite (PR 21) by (unfold acallee_saved; lia). exact R21.
- (* parent[i] = s[i] for i < di: the copy, the stretch's keep, sa_str *)
  intros i Hi.
  assert (HC1 : rdW (e_W e) mem2 (e_parent e + Z.of_nat i) = rdW (e_W e) (ms_mem ms) (e_seg e + Z.of_nat i))
    by exact (HCPY (Z.of_nat i) ltac:(lia)).
  rewrite HC1, (KT (e_seg e + Z.of_nat i) ltac:(lia) ltac:(lia)).
  rewrite (proj1 (proj1 Hstr) i ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite app_nth1 by lia. reflexivity.
Qed.
End e.
End f.
End d.
