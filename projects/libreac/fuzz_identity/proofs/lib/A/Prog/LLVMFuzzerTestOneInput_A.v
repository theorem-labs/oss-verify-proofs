(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Segment A of LLVMFuzzerTestOneInput's ASan walk: the prologue, 0x8070c..0x8098c (160 slots).

   seg_A of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v (the boundary layer): from the contract's
   pre-condition at the entry slot to inv_A_end at 0x8098c, after B's old first two slots (0x80984 `sd s4,24(s1)`,
   0x80988 `sd a6,80(s1)`), which ecommon's mf+24 and mf+80 need.

   The walk runs the engine of IdentPaLib.v / IdentFrame.v (cgif AChf.v's pattern) from the contract's
   pre-condition (ajournal_init):
   - 0x8070c..0x8074c: the 320-byte machine frame and the thirteen saved registers (a plain run);
   - 0x8074c `andi sp,sp,-32`: mf = 32 * ((sp0 - 320) / 32) becomes atom 60, the saved registers' region is cut
     to [sp0 - 104, sp0) and the machine frame's region [mf, mf + 216) is added;
   - 0x80750..0x80780: the shadow base and the use-after-return flag (the flag cell holds 1, so 0x80778 falls
     through), and the call of __asan_stack_malloc_4 (YC85 aj_stack_malloc_atS);
   - 0x80784..0x8098c: the class-4 frame (atom 516; its flag word, atom 528; its shadow, atom 529, named by the
     alias of SF >> 3 + SHADOW_OFF), 0x80798 `bnez s4` (decided by SF >= 4096), the three description words,
     the 96 shadow bytes that poison the frame, 0x8097c `beqz a3` (a3 = n >> 26, decided by the contract's
     n < 2^26), and the two stores of SF at mf+24 and mf+80.
   The boundary's memory facts are read from the final symbolic state's regions; the input bytes are kept by
   the journal (the entry's journal has no FP, and the class-4 frame changes no heap block). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Ltac get_region HS i HR :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?rg =>
      pose proof (st_ok_region_nth E (abs_ss val ss) ms i rg HS ltac:(vm_compute; reflexivity)) as HR end end.
Ltac nss HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss3 ?d =>
  let v := eval vm_compute in ss3 in change (st_ok_pi a b c v d) in HS end.
Lemma U_srl26 : forall E n, ew E 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> U E (SAlu ALU_SRL (SOff 11 0) (SLit 26)) = 0.
Proof.
intros E n Hn Hr. rewrite U_SAlu, U_SLit, U_SOff, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia). change (Z.land (zcanon 26) 63) with 26.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Ltac awrA B2' B60' RF3 B529 Hmf WS fpos F d :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite B2'; clear; lia | cbn [YP09.r_wlo]; clear - WS; lia | cbn [YP09.r_whi]; clear; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat d);
    [reflexivity | rewrite B60'; clear; lia | cbn [YP09.r_wlo]; clear - Hmf WS; lia
    | cbn [YP09.r_whi]; clear - Hmf; lia |]
  | eapply awr_ok_cons_gen;
    [reflexivity | first [exact RF3 | exact B529]
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 4, fpos;
      split; [left; reflexivity | unfold in_zr, shadow_addr; cbn [fst snd]; fold F;
              change (fs_frame_bytes 4) with 1024; change (1024 / 8) with 128;
              first [left; clear - Ha; lia | right; clear - Ha; lia]]
    | ] ].
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASM4 : astack_malloc_realizes SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis HXM : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XM_LIB n.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HBuar := palf_got_uar B TLF.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* The entry's own window: the 320-byte frame and the 16 bytes the 32-alignment of sp may take. *)
Definition LF_FRAME : Z := 336.
(* Atom 32 is the shadow base, atom 33 the use-after-return flag cell (as_uar_cell B). *)
Definition lf_extra : list word := map (Z_to_bv 64) [SHADOW_OFF; as_uar_cell B].
Definition lf_regions : smem :=
[stack_region LF_FRAME; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33].
Definition lf_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 4096 (2 ^ 47) 2)] [] [].
Definition ss_lf : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms lf_regions None lf_facts.
Definition LE (regs : bvmap 5 word) : env := Eimg (Ereg regs lf_extra).

Lemma segA_entry : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B LLVMF_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (LE regs) ss_lf
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_LLVMFuzzerTestOneInputP) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBuar in Kguar.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 30 ltac:(lia)) as HcellR.
pose proof (pa_obj_img 0 ltac:(lia)) as HuarR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (palf_uar_img B TLF) as HuarC. pose proof (palf_sep B TLF) as Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := LE regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs lf_extra) n)
by (intros n Hn; subst E; unfold LE; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold LE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
by (subst E; unfold LE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eu : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold LE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 30)) as Vc.
pose proof (pa_val_range (A_OBJ 0)) as Vu.
unfold ss_lf, A_LLVMFuzzerTestOneInputP. apply pa_entry_st_ok_full.
- subst E. unfold LE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lf_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. unfold LF_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
intros a Ha. apply (apresent_writable SEGS). apply Hpres. clear - Ha Hstk0 Hceil C1 WS. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ec) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eu) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - HuarC C5; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 33%nat (as_uar_cell B) E33) by (clear - HuarC C5; lia).
split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
[reflexivity | clear - HuarC C5; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold lf_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Ec) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eu) by lia.
rewrite (VB 33%nat (as_uar_cell B) E33) by (clear - HuarC C5; lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LF_FRAME.
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HgotR HcellR HuarR HgcD HuarC Hsep. clear. intros.
repeat split; lia.
- unfold facts_ok, lf_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [| split; [exact I | exact I]].
split; [| split; [| split; [| exact I]]].
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
split; [clear - Hslo Hshi H47 Hceil C1 WS Hstk0; split; lia|].
split; [change (2 ^ 4) with 16; exact Hal16 | lia].
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32.
rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
split; [split; lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33.
rewrite unsigned_lit_small by (clear - HuarC C5; lia).
split; [clear - HuarC C5; split; lia|].
split; [change (2 ^ 2) with 4; exact (palf_uar_al B TLF) | lia].
Qed.

Theorem seg_A_holds : seg_A B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_A. intros g W2 c2 [EW Ec] HPRE. subst W2 c2.
pose proof HPRE as HPRE0.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE0.
destruct HPRE0 as (HAFN & Hra & H10 & H11 & Hinp & Hlen & Hbytes & Hfr0 & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta & Hmo).
destruct g as [ly S W mem md regs p n pl M].
cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M] in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (ajournal_init SEGS B LLVMF_STK [] ly S W regs mem md [] HAFN) as HJ.
pose proof HAFN as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : 16720 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
pose proof (segA_entry ly S W regs mem md [] HAFN) as HS.
remember (LE regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold LE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_LLVMFuzzerTestOneInputP) with (Z_to_bv 64 A_LLVMFuzzerTestOneInputP).
paj_run_to_sh RUNTOP HS HJ 0x44.
{ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp; clear; lia | cbn [YP09.r_wlo]; clear - WS; lia
    | cbn [YP09.r_whi]; clear; lia |] ]. }
(* 0x8074c andi sp,sp,-32: mf = 32 * ((sp0 - 320) / 32), a fresh atom 60, 32-aligned. *)
set (mf := 32 * ((spZ regs + -320) / 32)).
destruct (sp1_facts (spZ regs + -320) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hmfr & Hmfal & Hmfal16).
fold mf in Hmfr, Hmfal, Hmfal16.
assert (Hmf : spZ regs - 336 <= mf <= spZ regs - 320) by lia. clear Hmfr.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_restrict_reg (w_H W) Ev ssx msx (2%bv : bv 5) HS) as R2;
  change (sr_get (ss_regs ssx) (2%bv : bv 5)) with (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32))) in R2;
  rewrite (denot_and_m32 Ev 2 (spZ regs) (-320) ltac:(rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) in R2;
  fold mf in R2;
  pose proof (st_ok_pi_havoc_hi 60 Ev ssx (restrict (w_H W) msx) [Z_to_bv 64 mf] HS ltac:(vm_compute; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
set (E1 := havoc E 60 [Z_to_bv 64 mf]) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (AG1 : forall k, (k < 60)%nat -> ew E1 k = ew E k) by (intros k Hk; apply ew_havoc_old; exact Hk).
assert (AG1' : forall k, (61 <= k)%nat -> ew E1 k = ew E k) by (intros k Hk; apply ew_havoc_above; cbn; lia).
assert (E60 : ew E1 60 = Z_to_bv 64 mf) by exact (ew_havoc_new E 60 [Z_to_bv 64 mf] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp E1 ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact E1 ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3
end.
clear HS. rename HS3 into HS. nss HS.
assert (VB1 : forall k v, k <> 60%nat -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E1 (Some k) = v).
{ intros k v Hne Hk Hv. cbn [base_val]. destruct (Nat.lt_ge_cases k 60) as [Hl | Hl].
  - rewrite (AG1 k Hl), Hk. apply unsigned_lit_small. exact Hv.
  - rewrite (AG1' k ltac:(lia)), Hk. apply unsigned_lit_small. exact Hv. }
assert (B60 : base_val E1 (Some 60%nat) = mf) by (cbn [base_val]; rewrite E60; apply unsigned_lit_small; lia).
assert (B2 : base_val E1 (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite (AG1 2%nat ltac:(lia)); exact Usp).
assert (U60 : bv_unsigned (ew E1 60) = mf) by exact B60.
assert (U2 : bv_unsigned (ew E1 2) = spZ regs) by exact B2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let rs := eval cbn [ss_mem] in (ss_mem ssx) in
  lazymatch rs with ?r0 :: ?rest =>
  pose proof (st_ok_pi_submem E1 ssx (restrict (w_H W) msx) (trim_lo r0 (-104) :: rest) HS
    ltac:(cbn [ss_mem]; apply submem_keep; [apply subregion_trim_lo | apply submem_refl]) ltac:(vm_compute; reflexivity)) as HS3 end
end.
clear HS. rename HS3 into HS. nss HS.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 30 ltac:(lia)) as HcellR.
pose proof (pa_obj_img 0 ltac:(lia)) as HuarR.
pose proof (palf_uar_img B TLF) as HuarC.
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
  by (subst E; unfold LE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  assert (HD : all_disjoint E1 (YP09.mkRegion (Some 60%nat) 0 216 0 216 []) (ss_mem ssx)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi extent_of_region].
  rewrite B60, B2, (VB1 242%nat (VAL (A_OBJ 1)) ltac:(lia) EO1 ltac:(pose proof (pa_val_range (A_OBJ 1)); lia)),
    (VB1 271%nat (VAL (A_OBJ 30)) ltac:(lia) EO30 ltac:(pose proof (pa_val_range (A_OBJ 30)); lia)),
    (VB1 241%nat (VAL (A_OBJ 0)) ltac:(lia) EO0 ltac:(pose proof (pa_val_range (A_OBJ 0)); lia)),
    (VB1 33%nat (as_uar_cell B) ltac:(lia) E33 ltac:(lia)).
  clear - Hmf Hceil Hslo Hstk0 WS C1 Hshi H47 HgotR HcellR HuarR HuarC.
  repeat split; lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_add_region E1 ssx (restrict (w_H W) msx) (YP09.mkRegion (Some 60%nat) 0 216 0 216 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst]; rewrite B60;
          split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; apply (apresent_writable SEGS); apply Hpres1; clear - Ho Hmf Hceil Hslo Hstk0 WS C1; lia) HD) as HS3
end.
clear HS HD. rename HS3 into HS. nss HS.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite U2; clear; lia | cbn [YP09.r_wlo]; clear - WS; lia
    | cbn [YP09.r_whi]; clear; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (mf - spZ regs));
    [reflexivity | rewrite U60; clear; lia | cbn [YP09.r_wlo]; clear - Hmf WS; lia
    | cbn [YP09.r_whi]; clear - Hmf; lia |] ]. }
(* 0x80780: the class-4 frame (YC85 aj_stack_malloc_atS). *)
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
rewrite E60 in Rsp. rewrite (AG1 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Hgp in Rgp.
rewrite (AG1 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Htp in Rtp.
pmkst HS. rewrite (palf_sm4 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 4 ASM4 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    LLVMF_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (mf - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite Rsp, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hmfal16, Hal16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
lazymatch type of HK with acall_kept _ _ _ _ _ ?mT _ _ _ _ _ =>
  assert (HKm : forall a, mf <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mT a) end.
{ intros a Ha. apply (proj1 HK); [clear - Ha Hmf Hceil Hslo Hstk0 WS C1; lia | lia]. }
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite B60; intros a Ha.
    + apply (mbyte_of_aview SEGS); apply HKm; lia.
    + intros _; apply (apresent_writable SEGS); apply HJpres2; clear - Ha Hmf Hceil Hslo Hstk0 WS C1; lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite B2; intros a Ha.
    + apply (mbyte_of_aview SEGS); apply HKm; lia.
    + intros _; apply (apresent_writable SEGS); apply HJpres2; clear - Ha Hmf Hceil Hslo Hstk0 WS C1; lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
(* The class-4 frame the call returned, its flag word and its shadow. *)
assert (Hfin2 : In (4, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HFal & [HFa0 HFapp] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B ly S2 W mem2 md2 4 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 4 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng & HFLnum).
change (fs_frame_bytes 4) with 1024 in *.
set (F := frame_addr ly 4 fpos) in *. set (FL := flag_addr ly 4 fpos) in *.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
set (E2v := havoc E1 512 (map (getr regs2) CLOB)) in HS.
assert (HEI2 : img_env VAL A_LIM E2v) by (apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (AG2 : forall k, (k < 512)%nat -> ew E2v k = ew E1 k) by (intros k Hk; apply ew_havoc_old; exact Hk).
assert (E516 : ew E2v 516 = Z_to_bv 64 F).
{ transitivity (getr regs2 (10%bv : bv 5));
  [exact (ew_havoc_new E1 512 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)) | rewrite Ha0; reflexivity]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 E2v ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
set (E3v := havoc E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)]) in HS.
assert (HEI3 : img_env VAL A_LIM E3v) by (apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (AG3 : forall k, (k < 528)%nat -> ew E3v k = ew E2v k) by (intros k Hk; apply ew_havoc_old; exact Hk).
assert (E528 : ew E3v 528 = Z_to_bv 64 FL)
  by exact (ew_havoc_new E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E529 : ew E3v 529 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by exact (ew_havoc_new E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; unfold LE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E32' : ew E3v 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (AG3 32%nat ltac:(lia)), (AG2 32%nat ltac:(lia)), (AG1 32%nat ltac:(lia)); exact E32).
assert (E516' : ew E3v 516 = Z_to_bv 64 F) by (rewrite (AG3 516%nat ltac:(lia)); exact E516).
assert (RF3 : bv_unsigned (ew E3v 516) = F) by (rewrite E516'; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 516 (HPTR 6) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF3; change (2 ^ 6) with 64; lia)) as HS3 end.
clear HS. rename HS3 into HS. nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 528 (HPTR 0) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528;
          rewrite (unsigned_lit_small FL) by (clear - HFLnum C1; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - HFLnum C1; lia)) as HS3 end.
clear HS. rename HS3 into HS. nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 529 (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 17592186044416) 3) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SHADOW_OFF; lia); change (2 ^ 3) with 8; unfold SHADOW_OFF;
          split; [lia|]; split; [rewrite HF8; replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia; apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS. nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_alias E3v ssv msv _ _ HS (shadow_decl_ok E3v 516 32 529 F SHADOW_OFF
    ltac:(rewrite <- RF3; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) E32' E529)) as HS3 end.
clear HS. rename HS3 into HS. nss HS.
assert (B516 : base_val E3v (Some 516%nat) = F) by (cbn [base_val]; exact RF3).
assert (B529 : base_val E3v (Some 529%nat) = SHADOW_OFF + F / 8)
  by (cbn [base_val]; rewrite E529; apply unsigned_lit_small; unfold SHADOW_OFF; clear - HF8lo HF8hi; lia).
assert (B2' : base_val E3v (Some 2%nat) = spZ regs)
  by (cbn [base_val]; rewrite (AG3 2%nat ltac:(lia)), (AG2 2%nat ltac:(lia)); exact B2).
assert (B60' : base_val E3v (Some 60%nat) = mf)
  by (cbn [base_val]; rewrite (AG3 60%nat ltac:(lia)), (AG2 60%nat ltac:(lia)); exact B60).
lazymatch type of HS with st_ok_pi _ _ _ ?ssv _ =>
  assert (HDF : all_disjoint E3v (fframe_region 516 528 4 []) (ss_mem ssv)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, fframe_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite B516, B2', B60'. change (fs_frame_bytes 4) with 1024.
  clear - HF4096 HFceil Hmf Hslo Hceil Hstk0 WS C1 Hshi H47.
  repeat split; lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv (restrict _ ?msv) =>
  pose proof (st_ok_pi_add_region E3v ssv (restrict (w_H W) msv) (fframe_region 516 528 4 []) HS eq_refl
    ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
          rewrite B516; change (fs_frame_bytes 4) with 1024;
          split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFpres (F + o) ltac:(clear - Ho; lia)))
          | apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val SEGS E3v _ F 1016 8 _ FL);
            [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | clear - HFLnum C1; zside | zside
            | replace (F + 1016) with (F + 1024 - 8) by (clear; lia); exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ]) HDF) as HS3
end.
clear HS HDF. rename HS3 into HS. nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv _ =>
  assert (HDS : all_disjoint E3v (fshadow_region 529 4 0 128 []) (ss_mem ssv)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, fframe_region, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite B529, B516, B2', B60'. change (fs_frame_bytes 4 / 8) with 128. change (fs_frame_bytes 4) with 1024.
  clear - HF4096 HFceil HF8lo HF8hi HFapp HF8 HFq Hmf Hslo Hceil Hstk0 WS C1 Hshi H47.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as [HFa | [HFa HFa2]].
  all: unfold SHADOW_OFF; repeat split; first [exact I | left; lia | right; lia]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv (restrict _ ?msv) =>
  pose proof (st_ok_pi_add_region E3v ssv (restrict (w_H W) msv) (fshadow_region 529 4 0 128 []) HS eq_refl
    ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
          rewrite B529; change (fs_frame_bytes 4 / 8) with 128;
          split; [clear - HF8lo; unfold SHADOW_OFF; lia|]; split; [clear - HF8hi; unfold SHADOW_OFF; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres;
            exact (proj1 (HFSpres o ltac:(change (1024 / 8) with 128; clear - Ho; lia)))
          | apply Forall_nil ]) HDS) as HS3
end.
clear HS HDS. rename HS3 into HS. nss HS.
assert (SHF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
assert (U2' : bv_unsigned (ew E3v 2) = spZ regs) by exact B2'.
assert (U60' : bv_unsigned (ew E3v 60) = mf) by exact B60'.
paj_run_sh RUNP HS HJ2.
{ awrA U2' U60' RF3 B529 Hmf WS fpos F (mf - spZ regs). }
clear HF HFr HG.
(* 0x8097c beqz a3, a3 = n >> 26: the contract's n < 2^26 takes it. *)
assert (E11 : ew E3v 11 = Z_to_bv 64 n)
  by (rewrite (AG3 11%nat ltac:(lia)), (AG2 11%nat ltac:(lia)), (AG1 11%nat ltac:(lia)), (EE 11%nat 11%bv eq_refl); exact H11).
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hinp as [[-> _] | [Hn _]]; lia).
psrr_branch_pi RUNP BR HS.
2: { exfalso. rewrite branch_eq_U, (U_srl26 E3v n E11 Hn26), U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
paj_run_to_sh RUNTOP HS HJ2 0x280.
{ awrA U2' U60' RF3 B529 Hmf WS fpos F (mf - spZ regs). }
(* 0x8098c: the boundary. *)
clear HF HFr HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18. prreg HS (26%bv : bv 5) Q26. prreg HS (16%bv : bv 5) Q16.
rewrite (AG3 60%nat ltac:(lia)), (AG2 60%nat ltac:(lia)), E60 in Q2, Q9.
rewrite (AG3 2%nat ltac:(lia)), (AG2 2%nat ltac:(lia)), (AG1 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl) in Q8.
rewrite (AG3 3%nat ltac:(lia)), (AG2 3%nat ltac:(lia)), (AG1 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Hgp in Q3.
rewrite (AG3 4%nat ltac:(lia)), (AG2 4%nat ltac:(lia)), (AG1 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Htp in Q4.
rewrite E529 in Q19. rewrite E11 in Q18. rewrite E516' in Q16.
rewrite (AG3 10%nat ltac:(lia)), (AG2 10%nat ltac:(lia)), (AG1 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl), H10 in Q26.
get_region HS 1%nat RFR. get_region HS 2%nat RMF. get_region HS 3%nat RST.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) ?mdX) _ =>
  set (regsF := ms_regs msX) in *; set (memF := ms_mem msX) in *; set (mdF := mdX) in * end.
cbn [ms_mem restrict] in RFR, RMF, RST.
assert (UF : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v) by (intros; apply unsigned_lit_small; lia).
assert (HFrng : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (MF : forall o, In (YP09.mkChunk o (CVal 8 (SOff 516 0)))
  [YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 24 (CVal 8 (SOff 516 0)); YP09.mkChunk 192 (CVal 8 (SOff 516 0))] ->
  val_mem SEGS (rd W memF) (mf + o) 8 F).
{ intros o Hin. apply (field_of_region E3v _ 60 mf _ _ _ _ _ o 8 (SOff 516 0) F RMF U60').
  - cbn [In] in Hin |- *. destruct Hin as [<- | [<- | [<- | []]]]; auto.
  - cbn [sv_denot]. rewrite E516', Z.add_0_r, UF by exact HFrng. reflexivity.
  - zside.
  - zside. }
assert (M176 : val_mem SEGS (rd W memF) (mf + 176) 8 SHADOW_OFF).
{ apply (field_of_region E3v _ 60 mf _ _ _ _ _ 176 8 (SOff 32 0) SHADOW_OFF RMF U60').
  - cbn [In]. auto.
  - cbn [sv_denot]. rewrite E32', Z.add_0_r, UF by (unfold SHADOW_OFF; lia). reflexivity.
  - unfold SHADOW_OFF; zside.
  - zside. }
lazymatch type of RST with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
assert (SV : forall (r : nat) (rr : bv 5) o, Z.of_nat r = bv_unsigned rr -> (r < 32)%nat ->
   In (YP09.mkChunk o (CVal 8 (SOff r 0))) cs -> val_mem SEGS (rd W memF) (spZ regs + o) 8 (bv_unsigned (getr regs rr))) end.
{ intros r rr o Hr Hr32 Hin.
  apply (field_of_region E3v _ 2 (spZ regs) _ _ _ _ _ o 8 (SOff r 0) _ RST U2' Hin).
  - cbn [sv_denot]. rewrite (AG3 r ltac:(lia)), (AG2 r ltac:(lia)), (AG1 r ltac:(lia)), (EE r rr Hr), Z.add_0_r.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs rr)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. zside.
  - zside. }
assert (FR : forall o e v, In (YP09.mkChunk o (CVal 8 e))
  [YP09.mkChunk 16 (CVal 8 (SOff 244 0)); YP09.mkChunk 8 (CVal 8 (SOff 243 0));
   YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 1016 (CVal 8 (SOff 528 0))] ->
  sv_denot E3v e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem SEGS (rd W memF) (F + o) 8 v).
{ intros o e v Hin He Hv. apply (field_of_region E3v _ 516 F _ _ _ _ _ o 8 e v RFR RF3); [| exact He | zside | zside].
  cbn [In] in Hin |- *. destruct Hin as [Q | [Q | [Q | [Q | []]]]]; injection Q as <- <-; auto 6. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [Efd Efs].
assert (HIN : garr8 SEGS (rd W memF) p (map (fun b : byte => bv_unsigned b) pl)).
{ destruct Hinp as [[Hn0 _] | [Hnpos Hinb]].
  - assert (Epl : pl = []) by (destruct pl; [reflexivity | cbn in Hlen; lia]). rewrite Epl. apply garr8_nil.
  - apply (garr8_frame SEGS _ _ p _ Hbytes). intros a Ha. rewrite length_map, <- Hlen in Ha.
    apply (mbyte_of_aview SEGS).
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J10 & _).
    replace a with (p + (a - p)) by lia.
    pose proof (req_size_pos n ltac:(lia)) as Hrq.
    apply (J10 p n (a - p) Hinb ltac:(rewrite Eab; exact Hinb) ltac:(lia)).
    intros (r & Hr & _). destruct Hr. }
apply SRr_ret. exists fpos, mf.
unfold inv_A_end, acut.
exists ly, S2, regsF, memF, mdF.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs2, Hfr0; reflexivity|].
split; [unfold EV_LLVMF; lia|].
split; [rewrite ES2, Z.mul_0_l; apply (mo_le_set_fs_r MT MTF); exact (mle_start MT S MTL)|].
split; [rewrite ES2, Z.sub_0_r; apply (mo_ok_set_fs MT MTF); exact (mo_ok_le MT MTL S _ _ Hmo (HXM n))|].
split.
- unfold ecommon. cbn [e_sp0 e_regs e_ly e_S e_W e_mem e_md e_p e_n e_pl e_M SFa]. fold F FL.
  split; [exact Q2|]. split; [exact Q9|]. split; [rewrite Q8; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [exact Hmf|]. split; [exact Hmfal|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Q19|].
  split; [apply MF; cbn [In]; auto|].
  split; [apply MF; cbn [In]; auto|].
  split; [exact M176|].
  split; [replace (spZ regs - 8) with (spZ regs + -8) by lia; rewrite <- Hra; exact (SV 1%nat 1%bv (-8) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 16) with (spZ regs + -16) by lia; exact (SV 8%nat 8%bv (-16) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 24) with (spZ regs + -24) by lia; exact (SV 9%nat 9%bv (-24) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 32) with (spZ regs + -32) by lia; exact (SV 18%nat 18%bv (-32) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 40) with (spZ regs + -40) by lia; exact (SV 19%nat 19%bv (-40) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 48) with (spZ regs + -48) by lia; exact (SV 20%nat 20%bv (-48) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 56) with (spZ regs + -56) by lia; exact (SV 21%nat 21%bv (-56) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 64) with (spZ regs + -64) by lia; exact (SV 22%nat 22%bv (-64) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 72) with (spZ regs + -72) by lia; exact (SV 23%nat 23%bv (-72) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 80) with (spZ regs + -80) by lia; exact (SV 24%nat 24%bv (-80) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 88) with (spZ regs + -88) by lia; exact (SV 25%nat 25%bv (-88) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 96) with (spZ regs + -96) by lia; exact (SV 26%nat 26%bv (-96) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [replace (spZ regs - 104) with (spZ regs + -104) by lia; exact (SV 27%nat 27%bv (-104) eq_refl ltac:(lia) ltac:(cbn [In]; auto 20))|].
  split; [apply MF; cbn [In]; auto|].
  split; [apply (FR 1016 (SOff 528 0) FL); [cbn [In]; auto 6 | cbn [sv_denot]; rewrite E528, Z.add_0_r, UF by (clear - HFLnum C1; lia); reflexivity | clear - HFLnum C1; lia]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HIN.
- cbn [e_sp0 e_regs e_ly e_S e_W e_mem e_md e_p e_n e_pl e_M SFa]. fold F FL.
  split; [pose proof (FR 0 (SLit 1102416563) 0x41b58ab3 ltac:(cbn [In]; auto 6) eq_refl ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|].
  split; [apply (FR 8 (SOff 243 0)); [cbn [In]; auto 6 | cbn [sv_denot]; rewrite (img_env_atomP E3v 243 HEI3 ltac:(unfold A_TEXT, A_LIM; lia)), Z.add_0_r, UF by (pose proof (pa_val_range (A_OBJ 2)); exact H); reflexivity | pose proof (pa_val_range (A_OBJ 2)); exact H]|].
  split; [apply (FR 16 (SOff 244 0)); [cbn [In]; auto 6 | cbn [sv_denot]; rewrite (img_env_atomP E3v 244 HEI3 ltac:(unfold A_TEXT, A_LIM; lia)), Z.add_0_r, UF by (pose proof (pa_val_range (A_OBJ 3)); exact H); reflexivity | pose proof (pa_val_range (A_OBJ 3)); exact H]|].
  split; [apply (FR 1016 (SOff 528 0) FL); [cbn [In]; auto 6 | cbn [sv_denot]; rewrite E528, Z.add_0_r, UF by (clear - HFLnum C1; lia); reflexivity | clear - HFLnum C1; lia]|].
  split; [unfold hblocks; cbn [app]; split; [rewrite Eab; apply Permutation_refl | constructor]|].
  split; [exact Q16|]. split; [exact Q18|]. exact Q26.
Qed.
End c.
End b.
End a.
