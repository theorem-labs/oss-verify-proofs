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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 291 of its 330 lines of code are new or changed and 414 lines of the source are left out. *)
(* Segment 3 of the image-B walk of reac_segconf_declared (fuzz_segconf.asan-ubsan, entry 0x89e7c; the interface is
   reac_segconf_declared_d.v): the image-B port of lib/A/Prog/reac_segconf_declared_s3.v (commit
   6121a10279e4), in its design (a read-only run to the call, cl_callS_wide, a re-seeded run after it) over image B's
   code, which differs from A's (ADAPTED): from the cut KA (0x8a048) at pass i, where reac_declared_vlan_split
   returned 1 with (p, v),
     0x8a048 .. 0x8a050 mv s11,s7; mv s7,s4; mv s4,s5   (image B's register shuffle around the call)
     0x8a054 lhu a4,0(s10)                             vid, at F + 64 (no instrumented check: the frame's own slot)
     0x8a058 .. 0x8a060 ld a0/a1/a2,56/64/72(s1)       tab / max / n
     0x8a064 mv s5,s3; mv a3,s3                         parent = F + 32
     0x8a06c jal reac_declared_vlan_add                 through cl_callS_wide (PaNoChain.v), the Section hypothesis ADD
   and from its return (0x8a070) to KT (0x8a0b4) at pass i or to KX (0x8a0fc) with the result -1: the second half,
   reac_segconf_declared_s3b.v (dcs3_tail), with the UBSan trap branch 0x8a084 `bne addw, add` decided by the run
   (added <= 31, add's answer 0 or 1). The premises of the call are reac_segconf_declared_s3a.v's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaSB PaCall PaNoChain
PaLibG PaLibF PaCallRun SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem reac_segconf_declared_s3a reac_segconf_declared_s3b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the two-byte zero-extending load of the vid (image A's dcs3_zext16) *)
Lemma dcs3_zext16 : forall v, 0 <= v < 65536 ->
  zext 64 (bv_extract 0 16 (Z_to_bv 64 v)) = Z_to_bv 64 v.
Proof.
intros v Hv. apply bv_eq.
rewrite (zext64_unsigned (bv_extract 0 16 (Z_to_bv 64 v)) ltac:(lia)).
rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. cbn [Z.of_N].
repeat (rewrite (Z.mod_small v) by lia). reflexivity.
Qed.
Lemma dcs3_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Ltac dcs3_cs := cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] =>
    let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.
(* the symbolic state at KA: the three argument slots tab / max / n at 56/64/72(s1) (atoms 32, 33, 34) and the vid
   halfword at s10 = F + 64 (atom 35); both read-only *)
Definition dcs3_s1R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 80 0 0
    [YP09.mkChunk 56 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 (SOff 34 0))].
Definition dcs3_vidR : YP09.region := YP09.mkRegion (Some 26%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 2 (SOff 35 0))].
Definition dcs3_ssA : sstate := mkSS DC_KA sr_atoms [dcs3_s1R; dcs3_vidR] None (mkFacts [] [] []).

Lemma dcs3_val_mem : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma dcs3_aview_ext : forall segs H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition dcs3_EA (regs : bvmap 5 word) (tab max n v : Z) : env := Eimg (Ereg regs [w64 tab; w64 max; w64 n; w64 v]).
Lemma dcs3_reader_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof using.
intros E rs H m m' Hro HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Ha). pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
(* the symbolic state at KA from the cut's facts *)
Lemma dcs3_seedA : forall (W : world SEGS) mem (regs : bvmap 5 word) s1 F tab max n v,
  getr regs 9 = w64 s1 -> getr regs 26 = w64 (F + 64) ->
  0 <= s1 -> s1 + 80 <= 2 ^ 64 -> 0 <= F -> F + 66 <= s1 + 56 ->
  0 <= tab < 2 ^ 64 -> 0 <= max < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= v < 65536 ->
  rdword (rdW W mem) (s1 + 56) = Some tab -> rdword (rdW W mem) (s1 + 64) = Some max ->
  rdword (rdW W mem) (s1 + 72) = Some n -> sa_val (rdW W mem) (F + 64) 2 v ->
  st_ok_pi SEGS VAL (dcs3_EA regs tab max n v) dcs3_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DC_KA)) mem (seg_rom SEGS))).
Proof using.
intros W mem regs s1 F tab max n v H9 H26 Hs0 Hs1 HF0 HF1 Ht Hm Hn Hv R56 R64 R72 RV.
set (E := dcs3_EA regs tab max n v).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm0. subst E. unfold dcs3_EA. apply ew_Eimg_Ereg_nat. exact Hm0. }
assert (X : forall j, (j < 4)%nat -> ew E (32 + j) = nth j [w64 tab; w64 max; w64 n; w64 v] (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold dcs3_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U9 : base_val E (Some 9%nat) = s1).
{ cbn [base_val]. rewrite (EEo 9%nat 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U26 : base_val E (Some 26%nat) = F + 64).
{ cbn [base_val]. rewrite (EEo 26%nat 26%bv eq_refl), H26. unfold w64. apply unsigned_lit_small. lia. }
assert (D : forall j z, (j < 4)%nat -> nth j [w64 tab; w64 max; w64 n; w64 v] (Z_to_bv 64 0) = w64 z ->
  sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 z).
{ intros j z Hj Hz. cbn [sv_denot]. rewrite (X j Hj), Hz, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite restrict_mkst_fx. unfold dcs3_ssA. apply pa_entry_st_ok_full.
- subst E. unfold dcs3_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs3_s1R, dcs3_vidR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ s1 56 8 (SOff 32 0) tab); [exact (D 0%nat tab ltac:(lia) eq_refl) | cbn; lia | lia |].
      apply (val_mem_of_rdword SEGS). exact R56.
    * apply (chunk_ok_val SEGS E _ s1 64 8 (SOff 33 0) max); [exact (D 1%nat max ltac:(lia) eq_refl) | cbn; lia | lia |].
      apply (val_mem_of_rdword SEGS). exact R64.
    * apply (chunk_ok_val SEGS E _ s1 72 8 (SOff 34 0) n); [exact (D 2%nat n ltac:(lia) eq_refl) | cbn; lia | lia |].
      apply (val_mem_of_rdword SEGS). exact R72.
  + rewrite U26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ (F + 64) 0 2 (SOff 35 0) v); [exact (D 3%nat v ltac:(lia) eq_refl) | cbn; lia | lia |].
    rewrite Z.add_0_r. exact (dcs3_val_mem SEGS (w_H W) mem _ 2%nat v RV).
- apply pairwise_disjoint_of_extents. unfold dcs3_s1R, dcs3_vidR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U9, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  split; [split; [right; lia | exact I] | split; exact I].
- split; [exact I | split; exact I].
Qed.
Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Hypothesis SIGP : seg_sig_prog.
Hypothesis ADD : forall fx0 : YK11.FPState, @reac_declared_vlan_add_contract fx0 rc SK SEGS B
  (BASE + AF_reac_declared_vlan_add) DC_STK_ADD RLO RHI.
Hypothesis RO_IMG : dc_ro_imgP RLO RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Lemma dc_S3 : dc_S3P B DC_STK RLO RHI GOTW GUARD.
Proof using ADD RO RO_IMG SIGP.
intros c i HPRE HKT HKX. unfold from_KA, dc_from.
intros ti added p v ly3 S3 W3 regs3 mem3 md3
  (HFI & HUN & HTAB & Hi & HLOOP & HLR & HLS & Hign & Hspl & HPZ & HVID & SH4 & SH5 & SH8).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F27 FSV F32 F40 FTB FMX FN FFL].
pose proof HLR as (R24 & R22 & R25 & R23 & R20 & R19 & R26 & R21 & R18).
pose proof HLS as (L48 & L80 & L88).
pose proof HUN as [HPERM HLY [fs3 HFS]]. subst ly3.
pose proof HPRE as [HAFN HROD0 HA0 HC64 HA1 HT64 HA2 HM64 HA3 HN64 HDP HROOM HNEV0].
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
change (spZ (x_regs c)) with (dc_sp0 c) in Hstk, Hpres, Hch.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HB0. pose proof (pa_base_lo (PL := PL_seg)) as HBLO.
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfrs & Hnev3 & _).
assert (HinF : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (x_ly c) S3 W3 mem3 md3 1 (x_fpos c) HAR3 HinF) as (HFa0 & HFac & HFapp).
assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HFa0, HFac, HFapp. rewrite F128 in HFac, HFapp.
destruct (dcl_split_some _ _ _ Hspl) as (Hv16 & Hp15).
pose proof DC_STK_values as (DSP & DA & DS).
assert (Ea1 : dc_a1 c = x_tab c) by (unfold dc_a1; rewrite HA1; unfold w64; apply unsigned_lit_small; lia).
assert (Ea2 : dc_a2 c = x_max c) by (unfold dc_a2; rewrite HA2; unfold w64; apply unsigned_lit_small; lia).
assert (Ea3 : dc_a3 c = x_n c) by (unfold dc_a3; rewrite HA3; unfold w64; apply unsigned_lit_small; lia).
pose proof FTB as FTB'. pose proof FMX as FMX'. pose proof FN as FN'.
rewrite Ea1 in FTB'. rewrite Ea2 in FMX'. rewrite Ea3 in FN'.
pose proof HTAB as (HTr & HTn & HTB0 & HTm).
destruct (dcl_add_len ti (x_max c) p v HTm) as [Hl1 Hl3].
pose proof (dcs3_len_fin c i ti added p v Hi HLOOP Hign Hspl HTm) as Hlfin.
(* 0x8a048 .. 0x8a06c: the register moves, the load of vid, the reloads of tab / max / n, a3 := parent, jal add *)
pose proof (dcs3_seedA W3 mem3 regs3 (dc_s1 c) (dc_F c) (x_tab c) (x_max c) (x_n c) v F9 R26
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HT64 HM64 HN64 Hv16 FTB' FMX' FN' HVID) as HS.
assert (HEI : img_env VAL A_LIM (dcs3_EA regs3 (x_tab c) (x_max c) (x_n c) v)) by (unfold dcs3_EA; apply Eimg_env).
unfold cfg_at, w64.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv.
assert (UQ : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ apply (dcs3_reader_ro (dcs3_EA regs3 (x_tab c) (x_max c) (x_n c) v) (ss_mem dcs3_ssA) (w_H W3) mem3 (ms_mem ms));
    [|exact HFr].
  unfold dcs3_ssA, dcs3_s1R, dcs3_vidR. cbn [ss_mem].
  apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
clear HF HFr HG.
assert (EEA : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr ->
  ew (dcs3_EA regs3 (x_tab c) (x_max c) (x_n c) v) m = getr regs3 rr)
  by (intros m rr Hm0; unfold dcs3_EA; apply ew_Eimg_Ereg_nat; exact Hm0).
assert (XA : forall j, (j < 4)%nat -> ew (dcs3_EA regs3 (x_tab c) (x_max c) (x_n c) v) (32 + j) =
  nth j [w64 (x_tab c); w64 (x_max c); w64 (x_n c); w64 v] (Z_to_bv 64 0))
  by (intros j Hj; unfold dcs3_EA; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rewrite (EEA 2%nat 2%bv eq_refl), F2 in Q2. rewrite (EEA 3%nat 3%bv eq_refl), F3 in Q3.
rewrite (EEA 4%nat 4%bv eq_refl), F4 in Q4. rewrite (EEA 8%nat 8%bv eq_refl), F8 in Q8.
rewrite (EEA 9%nat 9%bv eq_refl), F9 in Q9.
pose proof (XA 0%nat ltac:(lia)) as X32. pose proof (XA 1%nat ltac:(lia)) as X33.
pose proof (XA 2%nat ltac:(lia)) as X34. pose proof (XA 3%nat ltac:(lia)) as X35.
cbn [Nat.add nth] in X32, X33, X34, X35.
rewrite X32 in Q10. rewrite X33 in Q11. rewrite X34 in Q12. rewrite X35 in Q14.
rewrite (EEA 19%nat 19%bv eq_refl), R19 in Q13.
rewrite (EEA 18%nat 18%bv eq_refl), R18 in Q18. rewrite (EEA 19%nat 19%bv eq_refl), R19 in Q19.
rewrite (EEA 21%nat 21%bv eq_refl), R21 in Q20. rewrite (EEA 19%nat 19%bv eq_refl), R19 in Q21.
rewrite (EEA 22%nat 22%bv eq_refl), R22 in Q22. rewrite (EEA 20%nat 20%bv eq_refl), R20 in Q23.
rewrite (EEA 24%nat 24%bv eq_refl), R24 in Q24. rewrite (EEA 25%nat 25%bv eq_refl), R25 in Q25.
rewrite (EEA 26%nat 26%bv eq_refl), R26 in Q26. rewrite (EEA 23%nat 23%bv eq_refl), R23 in Q27.
assert (Q14' : getr (ms_regs ms) 14 = w64 v) by (rewrite Q14; unfold w64; apply dcs3_zext16; lia).
assert (HSP : spZ (ms_regs ms) = dc_s1 c) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (HS0 : s0Z (ms_regs ms) = dc_sp0 c) by (unfold s0Z; rewrite Q8; unfold w64; apply unsigned_lit_small; lia).
(* the call-site facts over the memory of the call (the run read only) *)
assert (HTABc : dc_tab c ti W3 (ms_mem ms)) by exact (dcs3_tab_ext c ti W3 W3 mem3 (ms_mem ms) (fun x _ => UQ x) HTAB).
assert (HPZc : sa_strz (rdW W3 (ms_mem ms)) (dc_F c + 32) p) by exact (dcs3_strz_ext _ _ _ _ UQ HPZ).
assert (SH4c : rdW W3 (ms_mem ms) (SB + dc_F c / 8 + 4) = Some 0) by (rewrite UQ; exact SH4).
assert (SH5c : rdW W3 (ms_mem ms) (SB + dc_F c / 8 + 5) = Some 0) by (rewrite UQ; exact SH5).
assert (H8 : rdword (rdW W3 (ms_mem ms)) (dc_sp0 c - 8) = Some (bv_unsigned (getr (x_regs c) 1))).
{ pose proof (FSV 0%nat 1 eq_refl) as H. replace (dc_sp0 c - 8 - 8 * Z.of_nat 0) with (dc_sp0 c - 8) in H by lia.
  rewrite (dcs3_rdword_ext _ _ _ UQ). exact H. }
assert (H16 : rdword (rdW W3 (ms_mem ms)) (dc_sp0 c - 16) = Some (bv_unsigned (getr (x_regs c) 8))).
{ pose proof (FSV 1%nat 8 eq_refl) as H. replace (dc_sp0 c - 8 - 8 * Z.of_nat 1) with (dc_sp0 c - 16) in H by lia.
  rewrite (dcs3_rdword_ext _ _ _ UQ). exact H. }
pose proof (dcs3_add_pre B RLO RHI GOTW GUARD c S3 W3 (ms_mem ms) mdv 0 ti p v (ms_regs ms) HPRE HJ HUN HTABc HSP
  HPZc Hp15 SH4c SH5c Hv16) as HADDP.
pose proof (dcs3_rod B RLO RHI GOTW GUARD RO_IMG c S3 W3 (ms_mem ms) mdv 0 HPRE HJ HUN) as HROD.
destruct (dcs3_chain B RLO RHI GOTW GUARD c S3 W3 (ms_mem ms) mdv 0 ti HPRE HJ HUN HTABc H8 H16) as (ch1 & HCH).
assert (Ho16 : (dc_s1 c - dc_sp0 c) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (dc_sp0 c - 224 - dc_sp0 c) with (-224) by lia | replace (dc_sp0 c - 240 - dc_sp0 c) with (-240) by lia];
  reflexivity. }
assert (HNEV : st_nev S3 + EV_reac_declared_vlan_add <= EV_MAX).
{ unfold EV_reac_declared_vlan_add. unfold EV_reac_segconf_declared in HNEV0. lia. }
assert (HSIG : SIGMA SS_reac_declared_vlan_add = BASE + AF_reac_declared_vlan_add).
{ rewrite (SIGP SS_reac_declared_vlan_add ltac:(cbv [seg_prog_syms In]; tauto)).
  first [reflexivity | f_equal; vm_compute; reflexivity]. }
pmkst HS. rewrite HSIG.
(* the call of reac_declared_vlan_add at 0x8a06c *)
eapply SRr_bind.
{ refine (cl_callS_wide B LAWS W3 (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_reac_declared_vlan_add)) DC_STK
    (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)] (x_ly c) S3 mdv 0
    DC_STK_ADD (vtab_W (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) EV_reac_declared_vlan_add
    (dc_s1 c - dc_sp0 c) (getr (ms_regs ms) 1) ch1
    (fun ly' S' W' regs' mem' md' =>
      getr regs' 10 = w64 (fst (vlan_add ti (x_max c) p v)) /\
      sa_rtab (aview SEGS (w_H W') mem') (x_tab c) (snd (vlan_add ti (x_max c) p v)) /\
      sa_val (aview SEGS (w_H W') mem') (x_n c) 4 (Z.of_nat (length (snd (vlan_add ti (x_max c) p v)))) /\
      (sa_guardtab (aview SEGS (w_H W3) (ms_mem ms)) (x_tab c) (x_max c) ->
        sa_guardtab (aview SEGS (w_H W') mem') (x_tab c) (x_max c)) /\
      sa_kept SEGS W3 (ms_mem ms) W' mem' (ms_regs ms) DC_STK_ADD
        (vtab_E (x_tab c) (x_n c) ti (snd (vlan_add ti (x_max c) p v))) /\
      sa_noalloc B (x_ly c) S3 ly' S')
    HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - rewrite HSP. lia.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - replace (dc_sp0 c + (dc_s1 c - dc_sp0 c)) with (dc_s1 c) by lia. rewrite HS0. exact HCH.
  - intros HPRE1.
    exact (ADD fx (x_ly c) S3 W3 (ms_regs ms) (ms_mem ms) mdv ch1 (x_tab c) (x_max c) (x_n c) (dc_F c + 32) v ti p
      HPRE1 HROD Q10 HT64 Q11 HM64 Q12 HN64 Q13 ltac:(lia) Q14' ltac:(lia) HADDP HNEV).
  - intros a Ha. exact (dcs3_awr B RLO RHI GOTW GUARD c S3 W3 (ms_mem ms) mdv 0 ti _ a HPRE HJ HUN HTB0 Hlfin Hl3 Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    exact (dcs3_vis B RLO RHI GOTW GUARD c S3 W3 (ms_mem ms) mdv 0 ti _ a HPRE HJ HUN Hl3 Ha Hw). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (A0 & RT & NV & _ & KEPT & (NP & NL & f2 & NF)). subst ly2.
(* the post-call state, for the tail *)
assert (CSV : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (dcs3_pres (ms_regs ms) regs2 r HP2 Hr)).
assert (KP : forall a, dcs3_safe c a -> (dc_s1 c <= a \/ a < dc_s1 c - DC_STK_ADD) -> 0 <= a < 2 ^ 64 ->
  rdW W2 mem2 a = rdW W3 mem3 a).
{ intros a Hs Hw Hr. rewrite (KEPT a Hr); [apply UQ | rewrite HSP; lia |].
  exact (dcs3_safe_E B RLO RHI GOTW GUARD c S3 W3 (ms_mem ms) mdv 0 a ti _ HPRE HJ HUN Hl3 Hs). }
assert (RK : forall a, (forall k, 0 <= k < 8 -> dcs3_safe c (a + k) /\
    (dc_s1 c <= a + k \/ a + k < dc_s1 c - DC_STK_ADD) /\ 0 <= a + k < 2 ^ 64) ->
  rdword (rdW W2 mem2) a = rdword (rdW W3 mem3) a).
{ intros a Ha. apply rdword_ext. intros k Hk. destruct (Ha k Hk) as (Hs & Hw & Hr). exact (KP _ Hs Hw Hr). }
rewrite Q1.
apply (dcs3_tail B RLO RHI GOTW GUARD c i ti added p v S2 W2 regs2 mem2 md2 HPRE HKT HKX).
apply mkDCS3R.
- exact HJ2.
- constructor; [exact (Permutation_trans NP HPERM) | reflexivity | exists f2; rewrite NF, HFS; reflexivity].
- split; [exact RT|]. split; [exact NV|]. split; [lia | exact Hl3].
- exact HTB0.
- exact Hi.
- exact HLOOP.
- exact Hign.
- exact Hspl.
- exact A0.
- rewrite (CSV 2%bv ltac:(dcs3_cs)). exact Q2.
- rewrite (CSV 3%bv ltac:(dcs3_cs)). exact Q3.
- rewrite (CSV 4%bv ltac:(dcs3_cs)). exact Q4.
- rewrite (CSV 8%bv ltac:(dcs3_cs)). exact Q8.
- rewrite (CSV 9%bv ltac:(dcs3_cs)). exact Q9.
- rewrite (CSV 18%bv ltac:(dcs3_cs)). exact Q18.
- rewrite (CSV 19%bv ltac:(dcs3_cs)). exact Q19.
- rewrite (CSV 20%bv ltac:(dcs3_cs)). exact Q20.
- rewrite (CSV 21%bv ltac:(dcs3_cs)). exact Q21.
- rewrite (CSV 22%bv ltac:(dcs3_cs)). exact Q22.
- rewrite (CSV 23%bv ltac:(dcs3_cs)). exact Q23.
- rewrite (CSV 24%bv ltac:(dcs3_cs)). exact Q24.
- rewrite (CSV 25%bv ltac:(dcs3_cs)). exact Q25.
- rewrite (CSV 26%bv ltac:(dcs3_cs)). exact Q26.
- rewrite (CSV 27%bv ltac:(dcs3_cs)). exact Q27.
- intros j r Hj. rewrite RK; [exact (FSV j r Hj)|].
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some dc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
    change (length dc_saved) with 13%nat in Hl. exact Hl. }
  intros k Hk. unfold dcs3_safe. lia.
- rewrite RK; [exact F32 | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact F40 | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact FTB | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact FMX | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact FN | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact FFL | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact L48 | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact L80 | intros k Hk; unfold dcs3_safe; lia].
- rewrite RK; [exact L88 | intros k Hk; unfold dcs3_safe; lia].
Qed.
End e.
End f.
End d.
