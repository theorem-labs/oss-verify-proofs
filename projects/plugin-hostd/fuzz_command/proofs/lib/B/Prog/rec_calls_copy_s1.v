(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the symbolic states, seeds and model facts of the rec_calls_copy walk on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/rec_calls_copy.v), ported from the ASan walk's
   lib/A/Prog/rec_calls_copy_s1.v. What differs from A: the 160-byte frame (0 = &g_rec, 8 and 16 the two UBSan
   predicates of dst, both 1, 24 = dst, 32 = i, 40 = 48 = &g_rec.calls[i].args, the saved registers at 152 .. 56),
   the cut points of the B code (0x89cc4, 0x89d7c, 0x89e14, 0x89e90), and the inner loop's registers: the code
   recomputes each argument slot as a cursor plus the byte offset s7 = 8a, which the inner state names by three
   aliases (cursor + s7 = the source slot, s10 + s7 = s11 + s7 = the copy's slot); ~cursor in s0 and ~(dst[i].args)
   in s5 carry the facts that decide the two UBSan wrap checks. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdBase CmdRep CmdObj CmdAddr CmdGlob xmalloc_c rec_calls_copy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- the cut points of the walk (offsets of the listing, BASE-relative) ---- *)
Definition RCC_OUTER : Z := 14228.   (* 0x89cc4, the outer loop head (the index check of g_rec.calls[i]) *)
Definition RCC_INNER : Z := 14412.   (* 0x89d7c, the inner loop head (the wrap check of g_rec.calls[i].args + 8a) *)
Definition RCC_LATCH : Z := 14564.   (* 0x89e14, the outer latch *)
Definition RCC_RET   : Z := 14688.   (* 0x89e90, the epilogue *)
Definition RCC_SLRET : Z := 14460.   (* 0x89dac, the return of the strlen wrapper *)
Definition RCC_XMRET : Z := 14472.   (* 0x89db8, the return of xmalloc *)
Definition RCC_MCRET : Z := 14488.   (* 0x89dc8, the return of __asan_memcpy *)

(* ---- the atoms of the walk: 0..31 are the registers at the cut point, 32..54 the extra words ---- *)
Definition rcc_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition rcc_extra (regs : bvmap 5 word) (dst GA DA GA0 na nc fn sa iI : Z) : list word :=
map (Z_to_bv 64) [SB; dst; GA; DA; GA0; na; nc; fn; sa; iI]
++ map (fun r => getr regs (Z_to_bv 5 r)) rcc_saved.
Definition rcc_Bx : sv := SOff 32 0.
Definition rcc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the bitwise complement the UBSan wrap checks compare against (`not s0,a0`, `not s5,a1`) *)
Definition NOTW (v : Z) : Z := 2 ^ 64 - 1 - v.

(* ---- the regions of the symbolic states ---- *)
(* the 160-byte frame: 0 = &g_rec, 8 = (dst mod 8 = 0 && dst != 0), 16 = (dst != 0), 24 = dst, 32 = i,
   40 = 48 = &g_rec.calls[i].args, 56 .. 152 the thirteen saved registers (ra at 152, s11 at 56) *)
Definition rcc_sav (j : nat) : YP09.chunk := YP09.mkChunk (152 - 8 * Z.of_nat j) (CVal 8 (SOff (42 + j) 0)).
Definition rcc_stk (i : Z) : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 160 0 160
([YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 44) 0));
  YP09.mkChunk 8 (CVal 8 (SLit 1));
  YP09.mkChunk 16 (CVal 8 (SLit 1));
  YP09.mkChunk 24 (CVal 8 (SOff 33 0));
  YP09.mkChunk 40 (CVal 8 (SOff (A_OBJ 44) (24 + 56 * i)));
  YP09.mkChunk 48 (CVal 8 (SOff (A_OBJ 44) (24 + 56 * i)))] ++ map rcc_sav (seq 0 13)).
(* the frame as the latch and the inner loop see it: i (atom 41) and the cursor (atom 36) as atoms *)
Definition rcc_stkl : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 160 0 160
([YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 44) 0));
  YP09.mkChunk 8 (CVal 8 (SLit 1));
  YP09.mkChunk 16 (CVal 8 (SLit 1));
  YP09.mkChunk 24 (CVal 8 (SOff 33 0));
  YP09.mkChunk 32 (CVal 8 (SOff 41 0));
  YP09.mkChunk 40 (CVal 8 (SOff 36 0));
  YP09.mkChunk 48 (CVal 8 (SOff 36 0))] ++ map rcc_sav (seq 0 13)).
(* the frame as the epilogue reads it: only the thirteen saved registers *)
Definition rcc_stkr : YP09.region := YP09.mkRegion (Some 2%nat) 0 160 0 0 (map rcc_sav (seq 0 13)).
Definition rcc_nc : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 38 0))].
Definition rcc_src (i : Z) : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) (16 + 56 * i) (24 + 56 * i) 0 0
[YP09.mkChunk (16 + 56 * i) (CVal 4 (SOff 39 0)); YP09.mkChunk (20 + 56 * i) (CVal 4 (SOff 37 0))].
Definition rcc_dst0 (i : Z) : YP09.region :=
YP09.mkRegion (Some 33%nat) (56 * i) (56 * i + 8) (56 * i) (56 * i + 8) [].
(* the inner loop: dst[i].nargs through s1 (register 9), the source argument slot (atom 34), the copy's argument
   slot (atom 35) *)
Definition rcc_dsti : YP09.region := YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition rcc_ga : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 40 0))].
Definition rcc_da : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 8 [].

(* ---- the facts of the symbolic states ---- *)
Definition rcc_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (38%nat, mkAF 0 2 0)] [] [].
Definition rcc_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 0x7fffff800000 3);
         (37%nat, mkAF 0 6 0); (38%nat, mkAF 0 2 0); (39%nat, mkAF 0 26 0);
         (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition rcc_facts_l : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (36%nat, mkAF (A_G_REC + 24) (A_G_REC + 80) 3);
         (38%nat, mkAF 0 2 0); (41%nat, mkAF 0 1 0); (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] [] [].
Definition rcc_facts_i : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
         (8%nat, mkAF (NOTW (A_G_REC + 80)) (NOTW (A_G_REC + 24)) 0);
         (9%nat, mkAF 4100 0x7fffff800000 2);
         (21%nat, mkAF (NOTW 0x7fffff800000) (NOTW 4104) 0);
         (22%nat, mkAF 0 5 0); (23%nat, mkAF 0 40 3);
         (26%nat, mkAF 4104 0x7fffff800000 3); (27%nat, mkAF 4104 0x7fffff800000 3);
         (32%nat, mkAF SB SB 0); (34%nat, mkAF (A_G_REC + 24) (A_G_REC + 128) 3);
         (35%nat, mkAF 4096 0x7fffff800000 3); (36%nat, mkAF (A_G_REC + 24) (A_G_REC + 80) 3);
         (37%nat, mkAF 0 6 0); (41%nat, mkAF 0 1 0); (A_OBJ 44, mkAF A_G_REC A_G_REC 3)] []
        [(SAlu ALU_ADD (SOff 36 0) (SOff 23 0), SOff 34 0);
         (SAlu ALU_ADD (SOff 26 0) (SOff 23 0), SOff 35 0);
         (SAlu ALU_ADD (SOff 27 0) (SOff 23 0), SOff 35 0)].

(* ---- the shadow-check entries: the slots whose shadow the record gives as usable ---- *)
Definition rcc_SH_o (i : Z) : list shent := [mkSHE (A_OBJ 44) (16 + 56 * i) (72 + 56 * i); mkSHE 33 (56 * i) (56 * i + 56)].
Definition rcc_SHi : list shent := [mkSHE 9 (-4) 52; mkSHE 34 0 8; mkSHE 35 0 8].
Definition rcc_SHa : list shent := [mkSHE 9 (-4) 52; mkSHE 35 0 8].

(* ---- the register maps at the cut points ---- *)
Definition shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 32 0).
Definition rcc_regs_o (i : Z) : list sv := Eval cbv -[Z.mul Z.add] in
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 12 (SOff (A_OBJ 44) 0)) 14 (SLit i)) 24 (SOff 32 0))
  26 (SOff 33 (8 + 56 * i))) 27 (SOff 33 (8 + 56 * i)).
Definition rcc_regs_i : list sv := Eval cbv -[shx] in
sr_set (sr_set sr_atoms 24 (SOff 32 0)) 25 (shx (SOff 9 0)).
Definition rcc_regs_r : list sv := Eval cbv in sr_set sr_atoms 11 (SOff 38 0).

Definition rcc_ss0 : sstate :=
mkSS AF_rec_calls_copy sr_atoms [stack_region 160; got_regionP; bcell_regionP 32; rcc_nc] None rcc_facts0.
Definition rcc_facts_r : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* aval_mem (the contracts' reader form) and val_mem (the symbolic state's form) *)
Lemma rcc_val_of_aval : forall H (m : word -> option byte) a n v,
aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hm; [|discriminate].
cbn in Hb. injection Hb as Hb. f_equal. apply bv_eq. rewrite Hb. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. unfold le_byte.
symmetry. apply Z.mod_mod. lia.
Qed.
Lemma rcc_aval_kept : forall (rd rd' : reader) a n v,
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk Hv k Hkn. rewrite Hk by lia. exact (Hv k Hkn). Qed.
Lemma rcc_aval_of_val : forall H (m : word -> option byte) a n v, 0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv Hm k Hk. unfold aview. rewrite (Hm k Hk). cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* the environment of a cut point: the registers there, then the words the walk names *)
Definition rcc_E (regs1 regs : bvmap 5 word) (dst GA DA GA0 na nc fn sa iI : Z) : env :=
Eimg (Ereg regs1 (rcc_extra regs dst GA DA GA0 na nc fn sa iI)).

Section e0.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis HVAL : cmd_val_objs.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Lemma rcc_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (HVAL 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma rcc_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md (R : rstate) O (dst nc : Z),
AR SEGS B ly S W mem md ->
astk_ok REC_CALLS_COPY_STK ly (spZ regs) ->
(forall a, spZ regs - REC_CALLS_COPY_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
rec_repA B ly S (rdW W mem) R O -> nc = Z.of_nat (length (r_calls R)) -> (length (r_calls R) <= 2)%nat ->
st_ok_pi SEGS VAL (rcc_E regs regs dst 0 0 0 0 nc 0 0 0) rcc_ss0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rec_calls_copy)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md R O dst nc HAR Hstk Hpres HREP Hnc Hlen.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REC_CALLS_COPY_STK = 16560) by reflexivity.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof rcc_grec_val as HGV.
assert (HGOT : VAL (A_OBJ 0) = 679760) by (rewrite (HVAL 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (HCELL : VAL (A_OBJ 12) = 724024) by (rewrite (HVAL 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
set (E := rcc_E regs regs dst 0 0 0 0 nc 0 0 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rcc_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, rcc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (rcc_extra regs dst 0 0 0 0 nc 0 0 0) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, rcc_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (change 32%nat with (32 + 0)%nat; rewrite EX by lia; reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 nc) by (change 38%nat with (32 + 6)%nat; rewrite EX by lia; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 679760)
  by (rewrite <- HGOT; unfold E, rcc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 724024)
  by (rewrite <- HCELL; unfold E, rcc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC)
  by (rewrite <- HGV; unfold E, rcc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Hnc2 : 0 <= nc <= 2) by lia.
destruct HREP as (Q & HREP & _). destruct HREP as (_ & _ & _ & HG1 & _).
destruct HG1 as (_ & _ & HNC & _).
rewrite restrict_mkst_fx. unfold rcc_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP, rcc_nc.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite E241, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 679760 0 8 (SOff (A_OBJ 12) 0) 724024);
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. rewrite <- HCELL. rewrite <- HGOT. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + cbn [base_val]. rewrite E253, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 724024 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SB; zside | zside |].
    rewrite Z.add_0_r. rewrite <- HCELL. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + cbn [base_val]. rewrite E285, unsigned_lit_small by (unfold A_G_REC; lia).
    split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff 38 0) nc);
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    apply (rcc_val_of_aval (w_H W) mem (A_G_REC + 8) 4 nc). rewrite Hnc. exact HNC.
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, rcc_nc, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, E241, E253, E285.
  rewrite !unsigned_lit_small by (unfold A_G_REC; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC in *. revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
  intros. repeat split; lia.
- split; [|split; exact I]. cbn [rcc_facts0 f_atoms atoms_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E38, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
End e0.

(* the words the outer head reads in the frame of the call: &g_rec, the two UBSan predicates of dst, dst, the
   two copies of the argument cursor, then the thirteen registers the prologue saved *)
Definition rcc_frame (rd : reader) (sp1 dst GS : Z) (regs : bvmap 5 word) : Prop :=
aval_mem rd sp1 8 A_G_REC /\ aval_mem rd (sp1 + 8) 8 1 /\ aval_mem rd (sp1 + 16) 8 1 /\
aval_mem rd (sp1 + 24) 8 dst /\ aval_mem rd (sp1 + 40) 8 GS /\ aval_mem rd (sp1 + 48) 8 GS /\
(forall j r, nth_error rcc_saved j = Some r ->
 aval_mem rd (sp1 + 152 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).

Section e1.
Variable B : asyms.
Variable regs1 regs : bvmap 5 word.
Variables dst GA DA GA0 na nc fn sa iI : Z.
#[local] Notation E := (rcc_E regs1 regs dst GA DA GA0 na nc fn sa iI).
Hypothesis HVAL : cmd_val_objs.
Lemma rcc_EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (rcc_extra regs dst GA DA GA0 na nc fn sa iI) (Z_to_bv 64 0).
Proof. intros j Hj. unfold rcc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma rcc_EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r.
Proof.
intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold rcc_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma rcc_E32 : ew E 32 = Z_to_bv 64 SB.
Proof. change 32%nat with (32 + 0)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E33 : ew E 33 = Z_to_bv 64 dst.
Proof. change 33%nat with (32 + 1)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E34 : ew E 34 = Z_to_bv 64 GA.
Proof. change 34%nat with (32 + 2)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E35 : ew E 35 = Z_to_bv 64 DA.
Proof. change 35%nat with (32 + 3)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E36 : ew E 36 = Z_to_bv 64 GA0.
Proof. change 36%nat with (32 + 4)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E37 : ew E 37 = Z_to_bv 64 na.
Proof. change 37%nat with (32 + 5)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E38 : ew E 38 = Z_to_bv 64 nc.
Proof. change 38%nat with (32 + 6)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E39 : ew E 39 = Z_to_bv 64 fn.
Proof. change 39%nat with (32 + 7)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E40 : ew E 40 = Z_to_bv 64 sa.
Proof. change 40%nat with (32 + 8)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E41 : ew E 41 = Z_to_bv 64 iI.
Proof. change 41%nat with (32 + 9)%nat. rewrite rcc_EX by lia. reflexivity. Qed.
Lemma rcc_E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC.
Proof.
rewrite <- (rcc_grec_val HVAL). unfold rcc_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia.
Qed.
Lemma rcc_E285' : ew E 285%nat = Z_to_bv 64 A_G_REC.
Proof. exact rcc_E285. Qed.
Lemma rcc_Esav : forall j, (j < 13)%nat -> ew E (42 + j) = getr regs (Z_to_bv 5 (nth j rcc_saved 0)).
Proof.
intros j Hj. change (42 + j)%nat with (32 + (10 + j))%nat. rewrite rcc_EX by lia.
unfold rcc_extra. rewrite app_nth2 by (rewrite length_map; cbn [length]; lia).
rewrite length_map. cbn [length]. replace (10 + j - 10)%nat with j by lia.
unfold rcc_saved. do 13 (destruct j as [|j]; [cbn [map nth]; reflexivity|]). exfalso; lia.
Qed.
(* the saved-register chunks of the frame at sp1 *)
Lemma rcc_savs_ok : forall (W : world SEGS) mem sp1,
0 <= sp1 -> sp1 + 160 < 2 ^ 64 ->
(forall j r, nth_error rcc_saved j = Some r ->
 aval_mem (aview SEGS (w_H W) mem) (sp1 + 152 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) sp1) (map rcc_sav (seq 0 13)).
Proof.
intros W mem sp1 Hlo Hhi FS.
apply Forall_map. apply Forall_forall. intros j Hj.
assert (Hj13 : (j < 13)%nat) by (apply in_seq in Hj; lia).
assert (Hnth : nth_error rcc_saved j = Some (nth j rcc_saved 0))
  by (apply nth_error_nth'; unfold rcc_saved; cbn [length]; lia).
unfold rcc_sav.
apply (chunk_ok_val SEGS E _ sp1 (152 - 8 * Z.of_nat j) 8 (SOff (42 + j) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 (nth j rcc_saved 0)))));
[cbn [sv_denot]; rewrite (rcc_Esav j Hj13), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j rcc_saved 0)))) as HR;
  change (bv_modulus 64) with (2 ^ 64) in HR; zside
| zside | ].
replace (sp1 + (152 - 8 * Z.of_nat j)) with (sp1 + 152 - 8 * Z.of_nat j) by lia.
apply rcc_val_of_aval. exact (FS j (nth j rcc_saved 0) Hnth).
Qed.
(* the symbolic frame of the outer head *)
Lemma rcc_stk_ok : forall (W : world SEGS) mem i sp1,
getr regs1 2 = w64 sp1 -> 0 <= sp1 -> sp1 + 160 < 2 ^ 64 ->
0 <= i -> 56 * i <= 840 -> 0 <= dst < 2 ^ 64 ->
(forall o, 0 <= o < 160 -> writable_at SEGS (mrestrict (w_H W) mem) (sp1 + o)) ->
rcc_frame (aview SEGS (w_H W) mem) sp1 dst (A_G_REC + 24 + 56 * i) regs ->
region_ok SEGS E (mrestrict (w_H W) mem) (rcc_stk i).
Proof.
intros W mem i sp1 Hsp Hlo Hhi Hi Hi2 Hd0 Hwr (F0 & F8 & F16 & F24 & F40 & F48 & FS).
assert (E2 : bv_unsigned (ew E 2) = sp1).
{ rewrite (rcc_EE 2%nat 2%bv eq_refl), Hsp. unfold w64. apply unsigned_lit_small. lia. }
unfold rcc_stk, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [exact Hwr|].
apply Forall_app. split; [|exact (rcc_savs_ok W mem sp1 Hlo Hhi FS)].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ sp1 0 8 (SOff (A_OBJ 44) 0) A_G_REC);
  [cbn [sv_denot]; rewrite rcc_E285, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | unfold A_G_REC; zside | zside | rewrite Z.add_0_r; apply rcc_val_of_aval; exact F0].
- apply (chunk_ok_val SEGS E _ sp1 8 8 (SLit 1) 1); [reflexivity | zside | zside | apply rcc_val_of_aval; exact F8].
- apply (chunk_ok_val SEGS E _ sp1 16 8 (SLit 1) 1); [reflexivity | zside | zside | apply rcc_val_of_aval; exact F16].
- apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 33 0) dst);
  [cbn [sv_denot]; rewrite rcc_E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside | apply rcc_val_of_aval; exact F24].
- apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff (A_OBJ 44) (24 + 56 * i)) (A_G_REC + 24 + 56 * i));
  [cbn [sv_denot]; rewrite rcc_E285; unfold w64; rewrite unsigned_lit_small by (unfold A_G_REC; zside);
   f_equal; lia | unfold A_G_REC; zside | zside | apply rcc_val_of_aval; exact F40].
- apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff (A_OBJ 44) (24 + 56 * i)) (A_G_REC + 24 + 56 * i));
  [cbn [sv_denot]; rewrite rcc_E285; unfold w64; rewrite unsigned_lit_small by (unfold A_G_REC; zside);
   f_equal; lia | unfold A_G_REC; zside | zside | apply rcc_val_of_aval; exact F48].
Qed.
(* the frame as the latch and the inner loop see it: slot 32 = i (atom 41), the cursor = GA0 (atom 36) *)
Lemma rcc_stkl_ok : forall (W : world SEGS) mem sp1,
getr regs1 2 = w64 sp1 -> 0 <= sp1 -> sp1 + 160 < 2 ^ 64 ->
0 <= dst < 2 ^ 64 -> 0 <= iI < 2 ^ 64 -> 0 <= GA0 < 2 ^ 64 ->
(forall o, 0 <= o < 160 -> writable_at SEGS (mrestrict (w_H W) mem) (sp1 + o)) ->
rcc_frame (aview SEGS (w_H W) mem) sp1 dst GA0 regs -> aval_mem (aview SEGS (w_H W) mem) (sp1 + 32) 8 iI ->
region_ok SEGS E (mrestrict (w_H W) mem) rcc_stkl.
Proof.
intros W mem sp1 Hsp Hlo Hhi Hd0 Hi0 Hg0 Hwr (F0 & F8 & F16 & F24 & F40 & F48 & FS) F32.
assert (E2 : bv_unsigned (ew E 2) = sp1).
{ rewrite (rcc_EE 2%nat 2%bv eq_refl), Hsp. unfold w64. apply unsigned_lit_small. lia. }
unfold rcc_stkl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [exact Hwr|].
apply Forall_app. split; [|exact (rcc_savs_ok W mem sp1 Hlo Hhi FS)].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ sp1 0 8 (SOff (A_OBJ 44) 0) A_G_REC);
  [cbn [sv_denot]; rewrite rcc_E285, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | unfold A_G_REC; zside | zside | rewrite Z.add_0_r; apply rcc_val_of_aval; exact F0].
- apply (chunk_ok_val SEGS E _ sp1 8 8 (SLit 1) 1); [reflexivity | zside | zside | apply rcc_val_of_aval; exact F8].
- apply (chunk_ok_val SEGS E _ sp1 16 8 (SLit 1) 1); [reflexivity | zside | zside | apply rcc_val_of_aval; exact F16].
- apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 33 0) dst);
  [cbn [sv_denot]; rewrite rcc_E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside | apply rcc_val_of_aval; exact F24].
- apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 41 0) iI);
  [cbn [sv_denot]; rewrite rcc_E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside | apply rcc_val_of_aval; exact F32].
- apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 36 0) GA0);
  [cbn [sv_denot]; rewrite rcc_E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside | apply rcc_val_of_aval; exact F40].
- apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 36 0) GA0);
  [cbn [sv_denot]; rewrite rcc_E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside | apply rcc_val_of_aval; exact F48].
Qed.
(* the epilogue's read-only view of the frame: the thirteen saved registers *)
Lemma rcc_stkr_ok : forall (W : world SEGS) mem sp1,
getr regs1 2 = w64 sp1 -> 0 <= sp1 -> sp1 + 160 < 2 ^ 64 ->
(forall j r, nth_error rcc_saved j = Some r ->
 aval_mem (aview SEGS (w_H W) mem) (sp1 + 152 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
region_ok SEGS E (mrestrict (w_H W) mem) rcc_stkr.
Proof.
intros W mem sp1 Hsp Hlo Hhi FS.
assert (E2 : bv_unsigned (ew E 2) = sp1).
{ rewrite (rcc_EE 2%nat 2%bv eq_refl), Hsp. unfold w64. apply unsigned_lit_small. lia. }
unfold rcc_stkr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
exact (rcc_savs_ok W mem sp1 Hlo Hhi FS).
Qed.
(* the source call slot and the recorder's call count *)
Lemma rcc_src_ok : forall (W : world SEGS) mem i,
0 <= i -> 16 + 56 * i + 8 <= 960 -> 0 <= fn < 2 ^ 31 -> 0 <= na < 2 ^ 31 ->
aval_mem (aview SEGS (w_H W) mem) (A_G_REC + 16 + 56 * i) 4 fn ->
aval_mem (aview SEGS (w_H W) mem) (A_G_REC + 20 + 56 * i) 4 na ->
region_ok SEGS E (mrestrict (w_H W) mem) (rcc_src i).
Proof.
intros W mem i Hi Hhi Hfn Hna Ffn Fna.
unfold rcc_src, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite rcc_E285, unsigned_lit_small by (unfold A_G_REC; lia).
split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ A_G_REC (16 + 56 * i) 4 (SOff 39 0) fn);
  [cbn [sv_denot]; rewrite rcc_E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  replace (A_G_REC + (16 + 56 * i)) with (A_G_REC + 16 + 56 * i) by lia. apply rcc_val_of_aval; exact Ffn.
- apply (chunk_ok_val SEGS E _ A_G_REC (20 + 56 * i) 4 (SOff 37 0) na);
  [cbn [sv_denot]; rewrite rcc_E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  replace (A_G_REC + (20 + 56 * i)) with (A_G_REC + 20 + 56 * i) by lia. apply rcc_val_of_aval; exact Fna.
Qed.
Lemma rcc_nc_ok : forall (W : world SEGS) mem,
0 <= nc < 2 ^ 31 -> aval_mem (aview SEGS (w_H W) mem) (A_G_REC + 8) 4 nc ->
region_ok SEGS E (mrestrict (w_H W) mem) rcc_nc.
Proof.
intros W mem Hnc Fnc.
unfold rcc_nc, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite rcc_E285, unsigned_lit_small by (unfold A_G_REC; lia).
split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff 38 0) nc);
[cbn [sv_denot]; rewrite rcc_E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply rcc_val_of_aval; exact Fnc.
Qed.
(* the source argument slot *)
Lemma rcc_ga_ok : forall (W : world SEGS) mem,
0 <= GA -> GA + 8 < 2 ^ 64 -> 0 <= sa < 2 ^ 64 ->
aval_mem (aview SEGS (w_H W) mem) GA 8 sa ->
region_ok SEGS E (mrestrict (w_H W) mem) rcc_ga.
Proof.
intros W mem H0 H1 H2 F.
unfold rcc_ga, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite rcc_E34, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ GA 0 8 (SOff 40 0) sa);
[cbn [sv_denot]; rewrite rcc_E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. apply rcc_val_of_aval; exact F.
Qed.
(* the copy table's slot i: the two scalar fields the outer body writes *)
Lemma rcc_dst0_ok : forall (W : world SEGS) mem i,
0 <= dst -> 0 <= i -> dst + 56 * i + 8 < 2 ^ 64 ->
(forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (dst + 56 * i + o)) ->
region_ok SEGS E (mrestrict (w_H W) mem) (rcc_dst0 i).
Proof.
intros W mem i H0 Hi H1 Hw.
unfold rcc_dst0, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite rcc_E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. replace (dst + o) with (dst + 56 * i + (o - 56 * i)) by lia. apply Hw. lia.
Qed.
Lemma rcc_da_ok : forall (W : world SEGS) mem,
0 <= DA -> DA + 8 < 2 ^ 64 ->
(forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (DA + o)) ->
region_ok SEGS E (mrestrict (w_H W) mem) rcc_da.
Proof.
intros W mem H0 H1 Hw.
unfold rcc_da, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite rcc_E35, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [exact Hw | apply Forall_nil].
Qed.
(* dst[i].nargs, read by the inner loop through s1 *)
Lemma rcc_dsti_ok : forall (W : world SEGS) mem X,
getr regs1 9 = w64 X -> 0 <= X -> X + 4 < 2 ^ 64 -> 0 <= na < 2 ^ 31 ->
aval_mem (aview SEGS (w_H W) mem) X 4 na ->
region_ok SEGS E (mrestrict (w_H W) mem) rcc_dsti.
Proof.
intros W mem X R9 H0 H1 Hna F.
unfold rcc_dsti, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (rcc_EE 9%nat 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ X 0 4 (SOff 37 0) na);
[cbn [sv_denot]; rewrite rcc_E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. apply rcc_val_of_aval; exact F.
Qed.

(* the facts the symbolic states carry *)
Lemma rcc_facts_ok : forall sp1,
bv_unsigned (ew E 2) = sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
4096 <= dst <= 0x7fffff800000 -> dst mod 8 = 0 ->
0 <= na <= 6 -> 0 <= nc <= 2 -> 0 <= fn <= 26 ->
facts_ok E rcc_facts.
Proof.
intros sp1 Hsp Hr Hm Hd Hd8 Hna Hnc Hfn.
split; [|split; exact I]. cbn [rcc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hsp, rcc_E32, rcc_E33, rcc_E37, rcc_E38, rcc_E39, rcc_E285.
rewrite !unsigned_lit_small by (unfold SB, A_G_REC in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold A_G_REC in *.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
Lemma rcc_facts_l_ok : forall sp1,
bv_unsigned (ew E 2) = sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
A_G_REC + 24 <= GA0 <= A_G_REC + 80 -> GA0 mod 8 = 0 -> 0 <= nc <= 2 -> 0 <= iI <= 1 ->
facts_ok E rcc_facts_l.
Proof.
intros sp1 Hsp Hr Hm Hg Hg8 Hnc Hi.
split; [|split; exact I]. cbn [rcc_facts_l f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hsp, rcc_E32, rcc_E36, rcc_E38, rcc_E41, rcc_E285.
rewrite !unsigned_lit_small by (unfold SB, A_G_REC in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold A_G_REC in *.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
Lemma rcc_facts_r_ok : forall sp1,
bv_unsigned (ew E 2) = sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 -> facts_ok E rcc_facts_r.
Proof.
intros sp1 Hsp Hr Hm. split; [|split; exact I]. cbn [rcc_facts_r f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hsp. change (2 ^ 4) with 16. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
(* the facts of the inner loop's states: the registers at the head, the two argument slots, and the three sums the
   loop forms (the source cursor + 8a, s10 + 8a, s11 + 8a) *)
Lemma rcc_facts_i_ok : forall sp1 X G a D,
bv_unsigned (ew E 2) = sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
getr regs1 8 = w64 (NOTW G) -> getr regs1 9 = w64 X -> getr regs1 21 = w64 (NOTW D) ->
getr regs1 22 = w64 a -> getr regs1 23 = w64 (8 * a) -> getr regs1 26 = w64 D -> getr regs1 27 = w64 D ->
A_G_REC + 24 <= G <= A_G_REC + 80 -> G mod 8 = 0 -> GA0 = G -> GA = G + 8 * a ->
4100 <= X <= 0x7fffff800000 -> X mod 4 = 0 -> 4104 <= D -> D + 8 * a <= 0x7fffff800000 -> D mod 8 = 0 -> DA = D + 8 * a ->
0 <= a <= 5 -> 0 <= na <= 6 -> 0 <= iI <= 1 ->
facts_ok E rcc_facts_i.
Proof.
intros sp1 X G a D Hsp Hr Hm R8 R9 R21 R22 R23 R26 R27 HG HG8 EG0 EGA HX HX4 HD HD' HD8 EDA Ha Hna Hi.
assert (W8 : ew E 8 = Z_to_bv 64 (NOTW G)) by (rewrite (rcc_EE 8%nat 8%bv eq_refl); exact R8).
assert (W9 : ew E 9 = Z_to_bv 64 X) by (rewrite (rcc_EE 9%nat 9%bv eq_refl); exact R9).
assert (W21 : ew E 21 = Z_to_bv 64 (NOTW D)) by (rewrite (rcc_EE 21%nat 21%bv eq_refl); exact R21).
assert (W22 : ew E 22 = Z_to_bv 64 a) by (rewrite (rcc_EE 22%nat 22%bv eq_refl); exact R22).
assert (W23 : ew E 23 = Z_to_bv 64 (8 * a)) by (rewrite (rcc_EE 23%nat 23%bv eq_refl); exact R23).
assert (W26 : ew E 26 = Z_to_bv 64 D) by (rewrite (rcc_EE 26%nat 26%bv eq_refl); exact R26).
assert (W27 : ew E 27 = Z_to_bv 64 D) by (rewrite (rcc_EE 27%nat 27%bv eq_refl); exact R27).
split; [|split; [exact I|]].
- cbn [rcc_facts_i f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Hsp, W8, W9, W21, W22, W23, W26, W27, rcc_E32, rcc_E34, rcc_E35, rcc_E36, rcc_E37, rcc_E41, rcc_E285.
  subst GA0 GA DA. unfold NOTW in *.
  rewrite !unsigned_lit_small by (unfold SB, A_G_REC in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (M1 : (G + 8 * a) mod 8 = 0) by (replace (G + 8 * a) with (G + a * 8) by lia; rewrite Z_mod_plus_full; exact HG8).
  assert (M2 : (D + 8 * a) mod 8 = 0) by (replace (D + 8 * a) with (D + a * 8) by lia; rewrite Z_mod_plus_full; exact HD8).
  assert (M3 : (8 * a) mod 8 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
  unfold A_G_REC in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | exact M1 | exact M2 | exact M3 | lia | reflexivity].
- cbn [rcc_facts_i f_alias alias_ok].
  assert (HA : forall (m n t : nat) (u v : Z), ew E m = Z_to_bv 64 u -> ew E n = Z_to_bv 64 v ->
    ew E t = Z_to_bv 64 (u + v) -> sv_denot E (SAlu ALU_ADD (SOff m 0) (SOff n 0)) = sv_denot E (SOff t 0)).
  { intros m n t u v Hm' Hn' Ht'. cbn [sv_denot]. rewrite Hm', Hn', Ht', !Z.add_0_r, !Z_to_bv_bv_unsigned.
    apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity. }
  split; [apply (HA 36%nat 23%nat 34%nat G (8 * a)); [rewrite <- EG0; exact rcc_E36 | exact W23 | rewrite <- EGA; exact rcc_E34]|].
  split; [apply (HA 26%nat 23%nat 35%nat D (8 * a)); [exact W26 | exact W23 | rewrite <- EDA; exact rcc_E35]|].
  split; [apply (HA 27%nat 23%nat 35%nat D (8 * a)); [exact W27 | exact W23 | rewrite <- EDA; exact rcc_E35]|].
  exact I.
Qed.
(* the register map at the outer loop head *)
Lemma rcc_regs_o_ok : forall i,
getr regs1 12 = w64 A_G_REC -> getr regs1 14 = w64 i -> getr regs1 24 = w64 SB ->
getr regs1 26 = w64 (dst + 8 + 56 * i) -> getr regs1 27 = w64 (dst + 8 + 56 * i) ->
0 <= i -> 56 * i <= 840 -> 0 <= dst -> dst + 8 + 56 * i < 2 ^ 64 ->
regs_ok E (rcc_regs_o i) regs1.
Proof.
intros i R12 R14 R24 R26 R27 Hi Hi2 Hd0 Hd1.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
 [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
     let v := eval cbv -[Z.mul Z.add] in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot];
   first
   [ exact R14
   | rewrite rcc_E285', unsigned_lit_small by (unfold A_G_REC; lia); rewrite Z.add_0_r; exact R12
   | rewrite rcc_E33, unsigned_lit_small by lia; first [rewrite R26 | rewrite R27]; unfold w64; f_equal; lia
   | rewrite rcc_E32, unsigned_lit_small by (unfold SB; lia); rewrite Z.add_0_r; exact R24
   | apply getr_zero
   | symmetry; apply getr_zero
   | reflexivity
   | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply rcc_EE; reflexivity ]
 | ]); try (destruct Hr; fail).
Qed.
(* the register map at the inner loop head *)
Lemma rcc_regs_i_ok : forall X,
getr regs1 9 = w64 X -> getr regs1 24 = w64 SB -> getr regs1 25 = w64 (SB + X / 8) ->
0 <= X < 2 ^ 47 ->
regs_ok E rcc_regs_i regs1.
Proof.
intros X R9 R24 R25 HX.
assert (E9 : ew E 9 = Z_to_bv 64 X) by (rewrite (rcc_EE 9%nat 9%bv eq_refl); exact R9).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
 [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
     let v := eval cbv -[shx] in (sr_get a rr2) in change (sr_get a rr2) with v end;
   unfold shx;
   first
   [ rewrite (denot_shx E 9 32 0 X SB E9 rcc_E32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia));
     rewrite Z.add_0_r; exact R25
   | cbn [sv_denot];
     first
     [ rewrite rcc_E32, unsigned_lit_small by (unfold SB; lia); rewrite Z.add_0_r; exact R24
     | apply getr_zero | symmetry; apply getr_zero | reflexivity
     | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply rcc_EE; reflexivity ] ]
 | ]); try (destruct Hr; fail).
Qed.
(* the register map at the epilogue *)
Lemma rcc_regs_r_ok : getr regs1 11 = w64 nc -> 0 <= nc <= 2 -> regs_ok E rcc_regs_r regs1.
Proof.
intros R11 Hnc.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
 [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
     let v := eval cbv in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot];
   first
   [ rewrite rcc_E38, unsigned_lit_small by lia; rewrite Z.add_0_r; exact R11
   | apply getr_zero | symmetry; apply getr_zero | reflexivity
   | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply rcc_EE; reflexivity ]
 | ]); try (destruct Hr; fail).
Qed.
End e1.

(* ---- the arguments copied so far: their list, and the sums the meter, the live bytes and the events take ---- *)
Definition zsum (f : list byte -> Z) (l : list (list byte)) : Z := fold_right (fun x acc => f x + acc) 0 l.
Lemma zsum_app : forall f l1 l2, zsum f (l1 ++ l2) = zsum f l1 + zsum f l2.
Proof. intros f l1 l2. unfold zsum. induction l1 as [|x l1 IH]; cbn [app fold_right]; [reflexivity | rewrite IH; lia]. Qed.
Lemma zsum_nonneg : forall f l, (forall x, 0 <= f x) -> 0 <= zsum f l.
Proof. intros f l Hf. unfold zsum. induction l as [|x l IH]; cbn [fold_right]; [lia | specialize (Hf x); lia]. Qed.
Lemma zsum_one : forall f x, zsum f [x] = f x.
Proof. intros f x. unfold zsum. cbn [fold_right]. lia. Qed.
Lemma zsum_cons : forall f x l, zsum f (x :: l) = f x + zsum f l.
Proof. reflexivity. Qed.
Lemma rcc_firstn_S : forall {A} (l : list A) i x, nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
- injection H as <-. reflexivity.
- rewrite (IH i x H). reflexivity.
Qed.
Lemma rcc_skipn_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
- injection H as <-. reflexivity.
- exact (IH i x H).
Qed.
Lemma rcc_args_app : forall c1 c2, PRcc.rcc_args (c1 ++ c2) = PRcc.rcc_args c1 ++ PRcc.rcc_args c2.
Proof. intros c1 c2. unfold PRcc.rcc_args. rewrite map_app, concat_app. reflexivity. Qed.
Lemma rcc_args_firstn_S : forall (cs : list rcall) i (c : rcall), nth_error cs i = Some c ->
PRcc.rcc_args (firstn (S i) cs) = PRcc.rcc_args (firstn i cs) ++ snd c.
Proof.
intros cs i c H. rewrite (rcc_firstn_S cs i c H), rcc_args_app. f_equal.
unfold PRcc.rcc_args. cbn [map concat]. apply app_nil_r.
Qed.
(* the argument list of the calls, cut at argument a of call i *)
Lemma rcc_args_at : forall (cs : list rcall) i (c : rcall) a x, nth_error cs i = Some c -> nth_error (snd c) a = Some x ->
PRcc.rcc_args cs = (PRcc.rcc_args (firstn i cs) ++ firstn a (snd c)) ++ x :: (skipn (S a) (snd c) ++ PRcc.rcc_args (skipn (S i) cs)).
Proof.
intros cs i c a x Hc Hx.
assert (E2 : snd c = firstn a (snd c) ++ x :: skipn (S a) (snd c))
  by (rewrite <- (rcc_skipn_nth (snd c) a x Hx); symmetry; apply firstn_skipn).
transitivity (PRcc.rcc_args (firstn (S i) cs) ++ PRcc.rcc_args (skipn (S i) cs)).
{ rewrite <- rcc_args_app. rewrite firstn_skipn. reflexivity. }
rewrite (rcc_args_firstn_S cs i c Hc). rewrite E2 at 1.
rewrite <- !app_assoc. reflexivity.
Qed.
Lemma rcc_ev_len : forall (cs : list rcall), fold_right (fun c acc => Z.of_nat (length (snd c)) + acc) 0 cs = Z.of_nat (length (PRcc.rcc_args cs)).
Proof.
intros cs. induction cs as [|c cs IH]; [reflexivity|]. cbn [fold_right].
replace (PRcc.rcc_args (c :: cs)) with (snd c ++ PRcc.rcc_args cs) by reflexivity.
rewrite length_app, Nat2Z.inj_add, IH. reflexivity.
Qed.
(* ---- the recorder kept: its two statics unchanged and its blocks still live with their bytes (the blocks only
   grow: the walk allocates and frees nothing of its own); the reader-level parts of lib/B/Prog/rec_calls_free_rep.v *)
Definition rcc_inrec (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Lemma rcc_aval_keep : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite (K k Hk). exact (H k Hk). Qed.
Lemma rcc_bytes_keep : forall (rd rd' : reader) p l, abytes_atR rd p l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (p + i) = rd (p + i)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H K i Hi. rewrite (K (Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma rcc_str_keep : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H Hn] K. split; [|exact Hn].
apply (rcc_bytes_keep rd _ _ _ H). intros i Hi. apply K. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.
Lemma rcc_call_keep : forall bl bl' (rd rd' : reader) a c P,
acall_at bl rd a c P ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn, In pn P -> In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hargs) K KP.
unfold acall_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
split; [apply (rcc_aval_keep rd _ _ _ _ Hb0); intros k Hk; apply K; lia|].
split; [apply (rcc_aval_keep rd _ _ _ _ Hb1); intros k Hk; apply K; lia|].
split; [exact Hnd|].
intros k s pn Es Ep. destruct (Hargs k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
destruct (KP pn (nth_error_In P k Ep) Hin) as [Hin' Kp].
split; [apply (rcc_aval_keep rd _ _ _ _ Hs); intros j Hj; apply K; lia|].
split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|].
apply (rcc_str_keep rd _ _ _ Hstr). intros i Hi. apply Kp. lia.
Qed.
Lemma rcc_answer_keep : forall bl bl' (rd rd' : reader) gr t q,
aanswer_at bl rd gr t q ->
(forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
(forall pn, In pn (oblk q) -> In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H K KB.
destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
- destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (KB pn (or_introl eq_refl) N3) as [Kin Kp].
  split; [apply (rcc_aval_keep rd _ _ _ _ N1); intros k Hk; apply K; lia|].
  split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|exact N6].
  apply (rcc_str_keep rd _ _ _ N5). intros i Hi. apply Kp. lia.
- apply (rcc_aval_keep rd _ _ _ _ H). intros k Hk. apply K. lia.
Qed.
Lemma rcc_reply_keep : forall bl bl' (rd rd' : reader) gr y q,
areply_at bl rd gr y q ->
(forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
(forall pn, In pn (oblk q) -> In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H K KB.
destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
unfold OFF_REPLY, OFF_REPLY_SIZE in *.
- destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct (KB pn (or_introl eq_refl) P5) as [Kin Kp].
  split; [apply (rcc_aval_keep rd _ _ _ _ P1); intros k Hk; apply K; lia|].
  split; [apply (rcc_aval_keep rd _ _ _ _ P2); intros k Hk; apply K; lia|].
  split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
  apply (rcc_bytes_keep rd _ _ _ P7). intros i Hi. apply Kp. lia.
- destruct H as [P1 P2].
  split; [apply (rcc_aval_keep rd _ _ _ _ P1); intros k Hk; apply K; lia|].
  apply (rcc_aval_keep rd _ _ _ _ P2). intros k Hk. apply K. lia.
Qed.
Lemma rcc_scalars_keep : forall (rd rd' : reader) gr R, ag1_scalars rd gr R ->
(forall x, gr <= x < gr + 16 \/ gr + 912 <= x < gr + 960 -> rd' x = rd x) -> ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
unfold ag1_scalars. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
split; [apply (rcc_aval_keep rd _ _ _ _ X1); intros k Hk; apply K; lia|].
split; [apply (rcc_aval_keep rd _ _ _ _ X2); intros k Hk; apply K; lia|].
split; [apply (rcc_aval_keep rd _ _ _ _ X3); intros k Hk; apply K; lia|].
split; [apply (rcc_aval_keep rd _ _ _ _ X4); intros k Hk; apply K; lia|].
split; [apply (rcc_aval_keep rd _ _ _ _ X5); intros k Hk; apply K; lia|].
exact X6.
Qed.
(* the recorder at a later state: its statics unchanged, its blocks still live and unchanged *)
Lemma rcc_rep_grow : forall B ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O -> (forall a, rcc_inrec a -> rd' a = rd a) ->
(forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
(forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros B ly S ly' S' rd rd' R O (Q & HA & HO) K HIN HK. exists Q. split; [|exact HO].
destruct HA as (H1 & H2 & H3 & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; exact Hx).
assert (KB : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S) ->
  In pn (ablocks B ly' S') /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros [p n] _ Hb. split; [exact (HIN _ Hb)|]. intros i Hi. exact (HK p n i Hb Hi). }
unfold arep_at. refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj _ (conj _ HW))))))).
- unfold ag1_calls. refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
  + apply (rcc_aval_keep rd _ _ _ _ C3). intros k Hk. apply KG. unfold OFF_NCALLS, REC_SIZE. lia.
  + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (rcc_call_keep (ablocks B ly S) (ablocks B ly' S') rd rd' _ c P Hc).
    * intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    * intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. left.
      apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn].
  + apply (rcc_call_keep (ablocks B ly S) (ablocks B ly' S') rd rd' _ _ _ C5).
    * intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
    * intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
      apply in_or_app. left. exact Hpn.
- apply (rcc_answer_keep (ablocks B ly S) (ablocks B ly' S') rd rd' _ _ _ HAn).
  + intros x Hx. apply KG. unfold OFF_ANSWER, REC_SIZE in *. lia.
  + intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. left. exact Hpn.
- apply (rcc_reply_keep (ablocks B ly S) (ablocks B ly' S') rd rd' _ _ _ HRp).
  + intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right. exact Hpn.
- apply (rcc_scalars_keep rd _ _ _ HX). intros x Hx. apply KG. unfold REC_SIZE. lia.
Qed.
End f.
End d.
