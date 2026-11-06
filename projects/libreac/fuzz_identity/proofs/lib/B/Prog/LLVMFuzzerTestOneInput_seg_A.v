(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Segment A of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B, fuzz_identity.asan-ubsan 0x80774 .. 0x809f4):
   seg_A of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v, from the contract's pre-condition at the entry slot to inv_A_end.

   The pieces, each a lemma of its own:
   - sa_entry: the symbolic state at the entry slot (the stack window, the two GOT slots, the shadow-base cell and
     the use-after-return flag cell, which holds 1).
   - sa_part1: the prologue (0x80774 .. 0x807bc: the 320-byte frame, the thirteen saves, sp aligned down to 32),
     the machine frame mf as a new atom, the run to the call at 0x807e8 (the flag test 0x807e0 is decided by the
     flag cell), and __asan_stack_malloc_4 through YC85's aj_stack_malloc_atS; it ends at the return slot 0x807ec
     in sa_ret.
   - sa_part2: from sa_ret, the frame F returned in a0 (at least 4096, so the test 0x80800 skips the machine-stack
     fallback 0x80804 .. 0x8081c), the frame address at mf+192, the three description words, the frame's
     shadow (0x80860 .. 0x809e0), the size test 0x809e4 (n < 2 ^ 26 by e_pre, so it falls through), and the two
     stores mf+16 and mf+64 (0x809ec, 0x809f0); it ends at 0x809f4 in sa_end.
   - sa_end_inv: sa_end gives inv_A_end. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- small facts: sp after andi sp,sp,-32 (cgif lib/A/ACja.v), a read-only trim of a region ---------------- *)
Lemma sa_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma sa_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma sa_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite sa_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sa_U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros E e. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Definition sa_trim (lo : Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo (YP09.r_hi r) 0 0 (List.filter (fun c => lo <=? YP09.c_off c) (YP09.r_chunks r)).
Lemma sa_subregion_trim : forall r lo, r_lo r <= lo -> subregion (sa_trim lo r) r.
Proof.
intros r lo Hlo. unfold subregion, sa_trim. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
intros c Hc. apply List.filter_In in Hc. exact (proj1 Hc).
Qed.
Ltac sa_norm_ss HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The entry's own window below sp0 that the prologue writes: the 320-byte frame and up to 16 bytes of the
   32-alignment of sp (0x80774 addi sp,sp,-320; 0x807b4 andi sp,sp,-32). *)
Definition sa_FRAME : Z := 336.
Definition sa_regions0 : smem :=
[stack_region sa_FRAME; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33].
Section c.
(* The boundary file's Section c, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* The contract's hypotheses this segment uses (LLVMFuzzerTestOneInput.v), with the contract's statements. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis HXM : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XM_LIB n.
Hypothesis ASM4 : astack_malloc_realizes SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
#[local] Notation epre := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).

Definition sa_extra : list word := map (Z_to_bv 64) [SB; as_uar_cell B].
Definition sa_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 (2 ^ 47) 2)] [] [].
Definition sa_ss0 : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms sa_regions0 None sa_facts0.
Definition sa_E0 (regs : bvmap 5 word) : env := Eimg (Ereg regs sa_extra).

(* ---- the symbolic state at the entry slot ------------------------------------------------------------------ *)
Lemma sa_entry : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B LLVMF_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (sa_E0 regs) sa_ss0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_LLVMFuzzerTestOneInputP) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : 336 + ESTACK <= LLVMF_STK) by (unfold STK_LLVMF, ESTACK, ASTACK in *; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL), <- SB_SHADOW_OFF in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 31 ltac:(lia)) as HcellR.
pose proof (pa_obj_img 0 ltac:(lia)) as HuarR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (palf_uar_img B TLF) as HuarC. pose proof (palf_sep B TLF) as Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := sa_E0 regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs sa_extra) n)
by (intros n Hn; subst E; unfold sa_E0; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold sa_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
by (subst E; unfold sa_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eu : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold sa_E0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 31)) as Vc.
pose proof (pa_val_range (A_OBJ 0)) as Vu.
unfold sa_ss0, A_LLVMFuzzerTestOneInputP. apply pa_entry_st_ok_full.
- subst E. unfold sa_E0. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sa_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. unfold sa_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
intros a Ha. apply (apresent_writable SEGS). apply Hpres. clear - Ha Hstk0 Hceil C1 WS Hes. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
[cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) Ec) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
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
unfold sa_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) Ec) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eu) by lia.
rewrite (VB 33%nat (as_uar_cell B) E33) by (clear - HuarC C5; lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold sa_FRAME.
revert Hslo Hshi H47 Hceil C1 WS Hes Hstk0 HgotR HcellR HuarR HgcD HuarC Hsep. clear. intros.
repeat split; lia.
- unfold facts_ok, sa_facts0. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
repeat match goal with |- _ /\ _ => split end; try exact I; unfold afact_ok; cbn [af_lo af_hi af_al2].
all: try rewrite E2; try rewrite E32; try rewrite E33.
all: rewrite ?unsigned_lit_small by (first [unfold SB; lia | clear - HuarC C5; lia]).
all: change (2 ^ 4) with 16; change (2 ^ 2) with 4; rewrite ?Z.pow_0_r, ?Z.mod_1_r.
all: try change (bv_unsigned (getr regs 2)) with (spZ regs).
all: repeat match goal with |- _ /\ _ => split end; try exact Hal16; try exact (palf_uar_al B TLF);
  unfold SB; lia.
Qed.

(* ---- the return slot of __asan_stack_malloc_4 (0x807ec) ---------------------------------------------------- *)
(* The class-4 frame (4, pos) is taken and is the journal's own; F = SFa g pos is in a0; the machine frame mf is
   in sp and s1 (0x807b4, 0x807b8), sp0 in s0 (0x807b0); n in s2 (0x807bc) and p in s9 (0x807d8); the shadow base
   at mf+168 (0x807dc); the thirteen saves of the prologue (0x8077c .. 0x807ac); the flag word at F+1016. *)
Definition sa_ret (g : ectx) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = e_W g /\ exists S2 regs2 mem2 md2 pos mf,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x78)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
(e_ly g) S2 (e_W g) mem2 md2 0 /\
ablocks B (e_ly g) S2 = ablocks B (e_ly g) (e_S g) /\ (exists f, S2 = set_fs f (e_S g)) /\
rdword (aview SEGS (w_H (e_W g)) mem2) (SFa g pos + fs_frame_bytes 4 - 8) = Some (flag_addr (e_ly g) 4 pos) /\
e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
getr regs2 2 = w64 mf /\ getr regs2 9 = w64 mf /\ getr regs2 8 = getr (e_regs g) 2 /\
getr regs2 10 = w64 (SFa g pos) /\ getr regs2 18 = getr (e_regs g) 11 /\ getr regs2 25 = getr (e_regs g) 10 /\
getr regs2 3 = getr (e_regs g) 3 /\ getr regs2 4 = getr (e_regs g) 4 /\
val_mem SEGS (rd (e_W g) mem2) (mf + 168) 8 SB /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 8) 8 (bv_unsigned (getr (e_regs g) 1)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 16) 8 (bv_unsigned (getr (e_regs g) 8)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)).

(* A field of a region whose chunk is an atom with a known value. *)
Lemma sa_fld : forall E m n bse cs lo hi wlo whi od (w : N) i v,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
In (YP09.mkChunk od (CVal w (SOff i 0))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
Z.of_N w <= 8 ->
val_mem SEGS m (bse + od) (N.to_nat w) v.
Proof.
intros E m n bse cs lo hi wlo whi od w i v Hr Hb Hc Hi Hv Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i 0) v Hr Hb Hc); [|exact Hv | exact Hw].
cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma sa_regv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x) /\ 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
intros x. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Ltac sa_in := cbn [In]; repeat first [left; reflexivity | right].
Ltac sa_rreg_by HS r v pf H :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ex ?ss (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (H : getr (ms_regs ms) r = v) by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)
end.
Ltac sa_reg0 HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [sv_denot] in Hr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr
end.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- entry -> the call of __asan_stack_malloc_4 -> its return ---------------------------------------------- *)
Lemma sa_part1 : forall g, epre g ->
SRr SEGS (e_W g) (cfg_at SEGS A_LLVMFuzzerTestOneInputP (e_regs g) (e_mem g) (e_md g)) (sa_ret g).
Proof.
intros [ly S W mem md regs p n pl M] Hpre.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in Hpre.
cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M] in Hpre |- *.
destruct Hpre as (HPRE & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof (sa_entry ly S W regs mem md [] HPRE) as HS.
pose proof (ajournal_init SEGS B LLVMF_STK [] ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : 336 + ESTACK <= LLVMF_STK) by (unfold STK_LLVMF, ESTACK, ASTACK in *; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HEI : img_env VAL A_LIM (sa_E0 regs)) by (unfold sa_E0; apply Eimg_env).
set (E := sa_E0 regs) in HS, HEI.
assert (EE : forall nn (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
  by (intros nn r Hn Hnr; subst E; unfold sa_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ nn r Hnr)).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv ltac:(lia) eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Rsp : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (bv_unsigned_in_range _ (getr regs 2))).
unfold cfg_at. change (w64 A_LLVMFuzzerTestOneInputP) with (Z_to_bv 64 A_LLVMFuzzerTestOneInputP).
(* ---- 0x80774 .. 0x807bc: the frame, the saves, sp aligned ---- *)
paj_run_to_sh RUNTOP HS HJ 0x48.
{ unfold sa_ss0, sa_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, sa_FRAME;
  cbn [ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [reflexivity | rewrite E2, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* ---- 0x807bc: the machine frame mf becomes atom 512; the save area is read-only from here ---- *)
set (mf := 32 * ((spZ regs - 320) / 32)).
destruct (sa_sp1_facts (spZ regs - 320) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hmfr & Hmfal & Hmfal16).
fold mf in Hmfr, Hmfal, Hmfal16.
sa_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 mf) (sa_denot_and_m32 E 2 (spZ regs) (-320) E2 ltac:(lia) ltac:(lia) ltac:(lia)) R2.
sa_rreg_by HS (9%bv : bv 5) (Z_to_bv 64 mf)
  (eq_trans (U_inj E _ _ (sa_U_add0 E _)) (sa_denot_and_m32 E 2 (spZ regs) (-320) E2 ltac:(lia) ltac:(lia) ltac:(lia))) R9.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_havoc_hi 512 Ex ssx msx [Z_to_bv 64 mf] HS ltac:(vm_compute; reflexivity)) as HS1 end.
clear HS. rename HS1 into HS.
remember (havoc E 512 [Z_to_bv 64 mf]) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (AG1 : forall nn, (nn < 512)%nat -> ew E1 nn = ew E nn) by (intros nn Hnn; rewrite HE1, ew_havoc_old by lia; reflexivity).
assert (X512 : ew E1 512 = Z_to_bv 64 mf)
  by (rewrite HE1; change 512%nat with (512 + 0)%nat; rewrite (ew_havoc_new E 512 _ 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (D512 : sv_denot E1 (SOff 512 0) = Z_to_bv 64 mf) by (cbn [sv_denot]; rewrite X512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (2%bv : bv 5) (SOff 512 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict mkst]; rewrite D512; symmetry; exact R2)) as HS1 end.
clear HS. rename HS1 into HS. sa_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (9%bv : bv 5) (SOff 512 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict mkst]; rewrite D512; symmetry; exact R9)) as HS1 end.
clear HS. rename HS1 into HS. sa_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  lazymatch rs with ?r0 :: ?rest =>
  pose proof (st_ok_pi_submem Ex ssx msx (sa_trim (-104) r0 :: rest) HS
    ltac:(cbn [ss_mem]; apply submem_keep; [apply sa_subregion_trim; cbn; lia | apply submem_refl])
    ltac:(vm_compute; reflexivity)) as HS1 end end.
clear HS. rename HS1 into HS. sa_norm_ss HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite AG1, E2 by lia; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew E1 512) = mf) by (rewrite X512; apply unsigned_lit_small; lia).
assert (Eg1 : ew E1 242 = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E1 (A_OBJ 1) HEI1); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eg31 : ew E1 272 = Z_to_bv 64 (VAL (A_OBJ 31))) by (apply (img_env_atomP E1 (A_OBJ 31) HEI1); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eg0 : ew E1 241 = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply (img_env_atomP E1 (A_OBJ 0) HEI1); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E32 : ew E1 32 = Z_to_bv 64 SB)
  by (rewrite AG1 by lia; subst E; unfold sa_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E1 33 = Z_to_bv 64 (as_uar_cell B))
  by (rewrite AG1 by lia; subst E; unfold sa_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EE1 : forall nn (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E1 nn = getr regs r)
  by (intros nn r Hn Hnr; rewrite AG1 by lia; exact (EE nn r Hn Hnr)).
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 31 ltac:(lia)) as HcellR.
pose proof (pa_obj_img 0 ltac:(lia)) as HuarR. pose proof (palf_uar_img B TLF) as HuarC.
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 31)) as Vc. pose proof (pa_val_range (A_OBJ 0)) as Vu.
assert (F512 : afact_ok E1 512 (mkAF (2 ^ 46 - 336) (2 ^ 47) 5))
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U512; change (2 ^ 5) with 32; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ex ssx msx 512 _ HS F512) as HS1 end.
clear HS. rename HS1 into HS. sa_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ex ssx msx (YP09.mkRegion (Some 512%nat) 0 216 0 216 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite U512; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); apply Hpres1; lia)
    ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?U512, ?Usp1, ?Eg1, ?Eg31, ?Eg0, ?E33, ?unsigned_lit_small by lia;
      repeat split; lia)) as HS1 end.
clear HS. rename HS1 into HS. sa_norm_ss HS.
(* ---- 0x807bc .. 0x807e8: the GOT loads, the flag test (the flag cell holds 1), the shadow base to mf+168 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ cbn [ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 512%nat (mf - spZ regs));
  [reflexivity | rewrite U512; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* ---- the state at the call ---- *)
lazymatch goal with HSc : st_ok _ _ _ (restrict _ ?msA) |- _ => rename msA into msC end.
sa_reg0 HS (1%bv : bv 5) R1. rewrite (img_env_codeptr E1 HEI1) in R1.
sa_reg0 HS (2%bv : bv 5) Q2. rewrite X512 in Q2.
sa_reg0 HS (3%bv : bv 5) Q3. rewrite (EE1 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
sa_reg0 HS (4%bv : bv 5) Q4. rewrite (EE1 4%nat 4%bv ltac:(lia) eq_refl) in Q4.
sa_reg0 HS (8%bv : bv 5) Q8. rewrite (EE1 2%nat 2%bv ltac:(lia) eq_refl) in Q8.
sa_reg0 HS (9%bv : bv 5) Q9. rewrite X512 in Q9.
sa_reg0 HS (18%bv : bv 5) Q18. rewrite (EE1 11%nat 11%bv ltac:(lia) eq_refl) in Q18.
sa_reg0 HS (25%bv : bv 5) Q25. rewrite (EE1 10%nat 10%bv ltac:(lia) eq_refl) in Q25.
pose proof (st_ok_region_nth E1 _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E1 _ _ 1 _ HS eq_refl) as RG1.
cbn [ms_mem restrict] in RG0, RG1.
assert (VS : forall (i : nat) (r : bv 5) od, (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
   In (YP09.mkChunk od (CVal 8 (SOff i 0)))
     [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
      YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
      YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
      YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
      YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
      YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
      YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
   val_mem SEGS (mrestrict (w_H W) (ms_mem msC)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
{ intros i r od Hi Hir Hc. rewrite <- Usp1.
  apply (sa_fld E1 _ 2 _ _ (-104) 0 0 0 od 8%N i (bv_unsigned (getr regs r)) RG1 eq_refl Hc);
  [rewrite (EE1 i r Hi Hir); exact (proj1 (sa_regv _)) | exact (proj2 (sa_regv _)) | lia]. }
pose proof (VS 1%nat 1%bv (-8) ltac:(lia) eq_refl ltac:(sa_in)) as V1.
pose proof (VS 8%nat 8%bv (-16) ltac:(lia) eq_refl ltac:(sa_in)) as V8.
pose proof (VS 9%nat 9%bv (-24) ltac:(lia) eq_refl ltac:(sa_in)) as V9.
pose proof (VS 18%nat 18%bv (-32) ltac:(lia) eq_refl ltac:(sa_in)) as V18.
pose proof (VS 19%nat 19%bv (-40) ltac:(lia) eq_refl ltac:(sa_in)) as V19.
pose proof (VS 20%nat 20%bv (-48) ltac:(lia) eq_refl ltac:(sa_in)) as V20.
pose proof (VS 21%nat 21%bv (-56) ltac:(lia) eq_refl ltac:(sa_in)) as V21.
pose proof (VS 22%nat 22%bv (-64) ltac:(lia) eq_refl ltac:(sa_in)) as V22.
pose proof (VS 23%nat 23%bv (-72) ltac:(lia) eq_refl ltac:(sa_in)) as V23.
pose proof (VS 24%nat 24%bv (-80) ltac:(lia) eq_refl ltac:(sa_in)) as V24.
pose proof (VS 25%nat 25%bv (-88) ltac:(lia) eq_refl ltac:(sa_in)) as V25.
pose proof (VS 26%nat 26%bv (-96) ltac:(lia) eq_refl ltac:(sa_in)) as V26.
pose proof (VS 27%nat 27%bv (-104) ltac:(lia) eq_refl ltac:(sa_in)) as V27.
clear VS.
assert (VSB : val_mem SEGS (mrestrict (w_H W) (ms_mem msC)) (mf + 168) 8 SB).
{ rewrite <- U512.
  apply (sa_fld E1 _ 512 _ _ 0 216 0 216 168 8%N 32%nat SB RG0 eq_refl ltac:(sa_in) E32); [unfold SB; cbn; lia | lia]. }
clear RG0 RG1.
(* ---- __asan_stack_malloc_4 (YC85 aj_stack_malloc_atS) ---- *)
pmkst HS. rewrite (palf_sm4 B TLF).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 4 ASM4 ltac:(lia) W (ms_regs msC) (ms_mem msC)
    LLVMF_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (mf - spZ regs) _ HJ).
  - unfold spZ at 1. rewrite Q2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hmfal16, Hal16. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Q3. exact Hgp.
  - rewrite Q4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. cbn. change (fs_frames 4) with 1024. lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 &
  Hz & Hflag & HK & _ & HfS2).
apply SRr_ret.
unfold sa_ret, e_sp0, SFa. cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M].
rewrite Hes in HK. replace (spZ regs + (mf - spZ regs) - 4096) with (mf - 4096) in HK by lia.
replace (spZ regs + (mf - spZ regs)) with mf in HK by lia.
assert (KV : forall a nn vv, alloc_ceiling <= a -> a + Z.of_nat nn <= 2 ^ 64 -> (mf <= a \/ a + Z.of_nat nn <= mf - 4096) ->
   val_mem SEGS (mrestrict (w_H W) (ms_mem msC)) a nn vv -> val_mem SEGS (mrestrict (w_H W) mem2) a nn vv).
{ intros a nn vv H1 H2 H3 Hvv. apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem msC) mem2 a nn vv); [|exact Hvv].
  intros kk Hk. apply (proj1 HK); [clear - H1 H2 Hk C1; lia | clear - H3 Hk; lia]. }
assert (CS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs msC) (Z_to_bv 5 r)) by exact HP2.
assert (P2 : getr regs2 2 = getr (ms_regs msC) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs msC) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs msC) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs msC) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs msC) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr (ms_regs msC) 18) by exact (CS 18 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr (ms_regs msC) 25) by exact (CS 25 ltac:(unfold acallee_saved; lia)).
clear CS.
assert (KSV : forall od vv, -104 <= od <= -8 ->
   val_mem SEGS (mrestrict (w_H W) (ms_mem msC)) (spZ regs + od) 8 vv ->
   val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - - od) 8 vv).
{ intros od vv Hod Hvv. replace (spZ regs - - od) with (spZ regs + od) by lia.
  apply KV; [clear - Hod Hstk0 Hceil Hslo WS Hes; lia | cbn; clear - Hod Rsp Hshi H47; lia | left; clear - Hmfr Hod; lia | exact Hvv]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos, mf.
split; [reflexivity|].
split; [exact HJ2|].
split; [exact Eab|].
split; [exact HfS2|].
split; [exact Hflag|].
split; [lia|]. split; [exact Hmfal|].
split; [rewrite P2; exact Q2|]. split; [rewrite P9; exact Q9|]. split; [rewrite P8; exact Q8|].
split; [exact Ha0|].
split; [rewrite P18; exact Q18|]. split; [rewrite P25; exact Q25|].
split; [rewrite P3; exact Q3|]. split; [rewrite P4; exact Q4|].
split; [apply KV; [clear - Hmfr Hstk0 Hceil Hslo WS Hes; lia | cbn; clear - Hmfr Rsp Hshi H47; lia | left; lia | exact VSB]|].
split; [exact (KSV (-8) _ ltac:(lia) V1)|].
split; [exact (KSV (-16) _ ltac:(lia) V8)|].
split; [exact (KSV (-24) _ ltac:(lia) V9)|].
split; [exact (KSV (-32) _ ltac:(lia) V18)|].
split; [exact (KSV (-40) _ ltac:(lia) V19)|].
split; [exact (KSV (-48) _ ltac:(lia) V20)|].
split; [exact (KSV (-56) _ ltac:(lia) V21)|].
split; [exact (KSV (-64) _ ltac:(lia) V22)|].
split; [exact (KSV (-72) _ ltac:(lia) V23)|].
split; [exact (KSV (-80) _ ltac:(lia) V24)|].
split; [exact (KSV (-88) _ ltac:(lia) V25)|].
split; [exact (KSV (-96) _ ltac:(lia) V26)|].
exact (KSV (-104) _ ltac:(lia) V27).
Qed.

(* ---- the symbolic state at 0x807ec ------------------------------------------------------------------------------
   Atoms: 0..31 the registers at the return slot (9 = s1 = mf, 10 = a0 = F, 18 = s2 = n), 32 = SB, 33 = F's shadow
   SB + F / 8. Regions: the machine frame below the save area (s1-based: 0x807ec, 0x80820, 0x809ec, 0x809f0), the
   frame's three description words (0x8084c .. 0x80854) and the first 96 bytes of its shadow (0x80860 .. 0x809e0).
   The alias says that s7 = (a6 >> 3) + a7 (0x8085c) is atom 33. *)
Definition sa_rmf : YP09.region := YP09.mkRegion (Some 9%nat) 0 216 0 216 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition sa_rfr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition sa_rsh : YP09.region := YP09.mkRegion (Some 33%nat) 0 96 0 96 [].
Definition sa_rs2 : smem := [sa_rmf; sa_rfr; sa_rsh].
Definition sa_shexp : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0).
Definition sa_facts2 : facts :=
mkFacts [(9%nat, mkAF (2 ^ 46 - 336) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 6);
         (33%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (32%nat, mkAF SB SB 0); (18%nat, mkAF 0 (2 ^ 26 - 1) 0)] []
  [(sa_shexp, SOff 33 0)].
Definition sa_ss2 : sstate := mkSS 0x78 sr_atoms sa_rs2 None sa_facts2.
Definition sa_extra2 (F : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 (SB + F / 8)].

Lemma sa_start2 : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (W : world SEGS) mf F n,
getr regs2 9 = w64 mf -> getr regs2 10 = w64 F -> getr regs2 18 = w64 n ->
alloc_ceiling <= mf -> mf <= 2 ^ 47 - 320 -> mf mod 32 = 0 ->
4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 -> F mod 64 = 0 ->
0 <= n < 2 ^ 26 ->
(forall o, 0 <= o < 216 -> apresent (w_H W) mem2 (mf + o)) ->
(forall o, 0 <= o < 24 -> apresent (w_H W) mem2 (F + o)) ->
(forall o, 0 <= o < 96 -> apresent (w_H W) mem2 (SB + F / 8 + o)) ->
val_mem SEGS (rd W mem2) (mf + 168) 8 SB ->
st_ok_pi SEGS VAL (Eimg (Ereg regs2 (sa_extra2 F))) sa_ss2
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 0x78)) mem2 (seg_rom SEGS))).
Proof.
intros regs2 mem2 W mf F n R9 R10 R18 Hmf0 Hmf1 Hmf32 HF0 HFc HFapp HF64 Hn HPmf HPF HPS VSB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (DF : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite DF at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.div_mul. lia. }
assert (HF8r : 512 <= F / 8 <= 2 ^ 44 - 128) by (rewrite HF8; lia).
remember (Eimg (Ereg regs2 (sa_extra2 F))) as E eqn:HE.
assert (EL : forall (i : nat) (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r)
  by (intros i r Hi; rewrite HE; exact (ew_Eimg_Ereg_nat regs2 _ i r Hi)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
pose proof (EL 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EL 10%nat 10%bv eq_refl) as E10. rewrite R10 in E10.
pose proof (EL 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = n) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = SB + F / 8) by (rewrite E33; apply unsigned_lit_small; unfold SB; lia).
unfold sa_ss2. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sa_rs2, sa_rmf, sa_rfr, sa_rsh.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply HPmf. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SB); [| unfold SB; cbn; lia | cbn; lia | exact VSB].
      cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HPF. lia.
  + rewrite U33. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
- apply pairwise_disjoint_of_extents. unfold sa_rs2, sa_rmf, sa_rfr, sa_rsh.
  cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, ASAN_CEIL, SB in *. rewrite C3 in HFapp.
  repeat split; lia.
- unfold facts_ok, sa_facts2. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  repeat match goal with |- _ /\ _ => split end; try exact I.
  6: { unfold sa_shexp. apply (shadow_decl_ok E 10 32 33 F SB E10 ltac:(lia) E32 E33). }
  all: unfold afact_ok; cbn [af_lo af_hi af_al2].
  all: rewrite ?U9, ?U10, ?U18, ?U32, ?U33.
  all: change (2 ^ 5) with 32; change (2 ^ 6) with 64; change (2 ^ 3) with 8; rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  all: repeat match goal with |- _ /\ _ => split end; try lia; try (unfold SB; lia).
  all: rewrite HF8; unfold SB; replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
  all: apply Z_mod_mult.
Qed.

(* ---- the end of segment A (0x809f4) ------------------------------------------------------------------------- *)
(* After the stores at 0x809ec (sd s4,16(s1)) and 0x809f0 (sd a6,64(s1)): the frame address is at mf+16, mf+64 and
   mf+192 and in a6 and s4; the frame's shadow address is in s7 (0x8085c); the three description words; the flag
   word; the saves; n in s2, p in s9. *)
Definition sa_end (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = e_W g /\ exists S2 regs2 mem2 md2,
c2 = cfg_at SEGS (BASE + 0x280) regs2 mem2 md2 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
(e_ly g) S2 (e_W g) mem2 md2 0 /\
ablocks B (e_ly g) S2 = ablocks B (e_ly g) (e_S g) /\ (exists f, S2 = set_fs f (e_S g)) /\
e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
getr regs2 2 = w64 mf /\ getr regs2 9 = w64 mf /\ getr regs2 8 = getr (e_regs g) 2 /\
getr regs2 3 = getr (e_regs g) 3 /\ getr regs2 4 = getr (e_regs g) 4 /\
getr regs2 16 = w64 (SFa g pos) /\ getr regs2 20 = w64 (SFa g pos) /\
getr regs2 23 = w64 (shadow_addr (SFa g pos)) /\
getr regs2 18 = getr (e_regs g) 11 /\ getr regs2 25 = getr (e_regs g) 10 /\
val_mem SEGS (rd (e_W g) mem2) (mf + 16) 8 (SFa g pos) /\
val_mem SEGS (rd (e_W g) mem2) (mf + 64) 8 (SFa g pos) /\
val_mem SEGS (rd (e_W g) mem2) (mf + 192) 8 (SFa g pos) /\
val_mem SEGS (rd (e_W g) mem2) (mf + 168) 8 SB /\
val_mem SEGS (rd (e_W g) mem2) (SFa g pos) 8 0x41b58ab3 /\
val_mem SEGS (rd (e_W g) mem2) (SFa g pos + 8) 8 (VAL (A_OBJ 2)) /\
val_mem SEGS (rd (e_W g) mem2) (SFa g pos + 16) 8 (VAL (A_OBJ 3)) /\
val_mem SEGS (rd (e_W g) mem2) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 8) 8 (bv_unsigned (getr (e_regs g) 1)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 16) 8 (bv_unsigned (getr (e_regs g) 8)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem SEGS (rd (e_W g) mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)).

(* A byte of the class-4 frame (4, pos) or of its shadow may be written by the frame's owner. *)
Lemma sa_awr_frame4 : forall STK sp0 FP bl0 blc ly own pos a,
(frame_addr ly 4 pos <= a < frame_addr ly 4 pos + 1024 \/
 shadow_addr (frame_addr ly 4 pos) <= a < shadow_addr (frame_addr ly 4 pos) + 128) ->
awr_byte STK sp0 FP bl0 blc ly ((4, pos) :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. change (1024 / 8) with 128. exact Ha.
Qed.
(* A run keeps every byte outside its write windows. *)
Lemma sa_vm_kept : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) a nn v,
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall k, 0 <= k < Z.of_nat nn -> 0 <= a + k < 2 ^ 64 /\ ~ in_wrange E rs (a + k)) ->
val_mem SEGS (mrestrict H m1) a nn v -> val_mem SEGS (mrestrict H m2) a nn v.
Proof.
intros E rs H m1 m2 a nn v HF Hk Hv. apply (val_mem_kept SEGS H H m1 m2 a nn v); [|exact Hv].
intros k Hkk. destruct (Hk k Hkk) as [Hr Hn]. apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by exact Hr. exact Hn.
Qed.
(* The size test at 0x809e4: n >> 26 is 0 when n < 2 ^ 26. *)
Lemma sa_U_srl26 : forall E n, U E (SOff 18 0) = n -> 0 <= n < 2 ^ 26 -> U E (SAlu ALU_SRL (SOff 18 0) (SLit 26)) = 0.
Proof.
intros E n Hn Hr. rewrite U_SAlu, U_SLit, Hn. cbn [zalu_raw]. rewrite (zcanon_id 26) by (unfold M64; lia).
change (Z.land 26 63) with 26. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Ltac sa_regpi HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [sv_denot] in Hr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr
end.
Let BR := paj_branch (PI := PI).

Lemma sa_part2 : forall g W2 c2, epre g -> sa_ret g W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 => exists pos mf, sa_end g pos mf W3 c3).
Proof.
intros [ly S W mem md regs p n pl M] W2 c2 Hpre Hret.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in Hpre.
unfold sa_ret, e_sp0, SFa in Hret.
cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M] in Hpre, Hret |- *.
destruct Hpre as (HPRE & Hra & H10 & H11 & Hnp & Hlen & Hpl & Hfr0 & Hnev0 & Hbb0 & _ & _ & _ & _ & _ & Hmo0).
destruct Hret as (-> & S2 & regs2 & mem2 & md2 & pos & mf & -> & HJ2 & Eab & HfS2 & Hflag & Hmf & Hmf32 &
  R2 & R9 & R8 & R10 & R18 & R25 & R3 & R4 & VSB & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : 336 + ESTACK <= LLVMF_STK) by (unfold STK_LLVMF, ESTACK, ASTACK in *; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hnp as [[-> _] | [Hn _]]; lia).
assert (Rsp : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (bv_unsigned_in_range _ (getr regs 2))).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite Hfr0 in Hfrs2. cbn [app] in Hfrs2.
assert (Hin2 : In (4, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S2 W mem2 md2 4 pos HAR2 Hin2) as (HF0 & HFc & HFapp).
destruct (frame_al64 SEGS B ly S2 W mem2 md2 4 pos HAR2 Hin2) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS ly S2 W mem2 md2 4 pos HAR2 Hin2) as (_ & _ & HFp & HSp).
change (fs_frame_bytes 4) with 1024 in HFc, HFapp, HFp, HSp, Hflag. change (1024 / 8) with 128 in HSp.
unfold shadow_addr in HSp. rewrite <- SB_SHADOW_OFF in HSp.
set (F := frame_addr ly 4 pos) in *.
assert (DF : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)).
{ rewrite DF at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.div_mul. lia. }
assert (HF8r : 512 <= F / 8 <= 2 ^ 44 - 128) by (rewrite HF8; lia).
assert (Hmfc : alloc_ceiling <= mf) by lia.
assert (R18n : getr regs2 18 = w64 n) by (rewrite R18; exact H11).
pose proof (sa_start2 regs2 mem2 W mf F n R9 R10 R18n Hmfc ltac:(lia) Hmf32 HF0 HFc HFapp HF64 Hn26
  (fun o Ho => Hpres2 (mf + o) ltac:(lia)) (fun o Ho => proj1 (HFp (F + o) ltac:(lia))) (fun o Ho => proj1 (HSp o ltac:(lia))) VSB) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 (sa_extra2 F)))) by apply Eimg_env.
set (E := Eimg (Ereg regs2 (sa_extra2 F))) in HS, HEI.
assert (EL : forall (i : nat) (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r)
  by (intros i r Hi; subst E; exact (ew_Eimg_Ereg_nat regs2 _ i r Hi)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SB + F / 8)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E9 : ew E 9 = Z_to_bv 64 mf) by (rewrite (EL 9%nat 9%bv eq_refl), R9; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EL 10%nat 10%bv eq_refl), R10; reflexivity).
assert (E18 : ew E 18 = Z_to_bv 64 n) by (rewrite (EL 18%nat 18%bv eq_refl), R18n; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SB + F / 8) by (rewrite E33; apply unsigned_lit_small; unfold SB; lia).
assert (Hwr : forall a, (mf <= a < mf + 216 \/ F <= a < F + 24 \/ SB + F / 8 <= a < SB + F / 8 + 96) ->
   awr_byte LLVMF_STK (spZ regs) [] (ablocks B ly S) (ablocks B ly S2) ly [(4, pos)] a).
{ intros a [Ha | Ha]; [left; lia|]. apply sa_awr_frame4. fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. lia. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 0x78)) mem2 (seg_rom SEGS))) in HJ2.
(* ---- 0x807ec .. 0x809e4: the fallback test, mf+192, the description words, the frame's shadow ---- *)
paj_run_sh RUNP HS HJ2.
{ intros a (r & Hin & Ha). apply Hwr. unfold sa_ss2, sa_rs2, sa_rmf, sa_rfr, sa_rsh in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?U9, ?U10, ?U33 in Ha; lia. }
rename HF into HF1, HFr into HFr1, HG into HG1.
(* ---- 0x809e4: the size test, n < 2 ^ 26 (e_pre) ---- *)
psrr_branch_pi RUNP BR HS.
2: { exfalso. revert Hc. rewrite !denot_lit_U.
     rewrite (sa_U_srl26 E n (U_atom E 18 n E18 ltac:(lia)) Hn26), U_SLit. cbn. discriminate. }
(* ---- 0x809ec .. 0x809f4: mf+16, mf+64 ---- *)
paj_run_to_sh RUNTOP HS HJ2 0x280.
{ intros a (r & Hin & Ha). apply Hwr. cbn [ss_mem In add_cond set_facts] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9, ?U10, ?U33 in Ha; lia |]).
  destruct Hin. }
(* ---- the state at 0x809f4 ---- *)
lazymatch type of HFr1 with frame_of _ _ _ (mrestrict _ (ms_mem ?m1)) => rename m1 into msM end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m3) => rename m3 into msE end.
sa_regpi HS (2%bv : bv 5) Q2. rewrite (EL 2%nat 2%bv eq_refl), R2 in Q2.
sa_regpi HS (3%bv : bv 5) Q3. rewrite (EL 3%nat 3%bv eq_refl), R3 in Q3.
sa_regpi HS (4%bv : bv 5) Q4. rewrite (EL 4%nat 4%bv eq_refl), R4 in Q4.
sa_regpi HS (8%bv : bv 5) Q8. rewrite (EL 8%nat 8%bv eq_refl), R8 in Q8.
sa_regpi HS (9%bv : bv 5) Q9. rewrite (EL 9%nat 9%bv eq_refl), R9 in Q9.
sa_regpi HS (16%bv : bv 5) Q16. rewrite E10 in Q16.
sa_regpi HS (20%bv : bv 5) Q20. rewrite E10 in Q20.
sa_regpi HS (23%bv : bv 5) Q23. rewrite E33 in Q23.
sa_regpi HS (18%bv : bv 5) Q18. rewrite (EL 18%nat 18%bv eq_refl), R18 in Q18.
sa_regpi HS (25%bv : bv 5) Q25. rewrite (EL 25%nat 25%bv eq_refl), R25 in Q25.
pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS eq_refl) as RG1.
cbn [ms_mem restrict] in RG0, RG1.
assert (E243 : ew E 243 = Z_to_bv 64 (VAL (A_OBJ 2))) by (apply (img_env_atomP E (A_OBJ 2) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E244 : ew E 244 = Z_to_bv 64 (VAL (A_OBJ 3))) by (apply (img_env_atomP E (A_OBJ 3) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 2)) as Vo2. pose proof (pa_val_range (A_OBJ 3)) as Vo3.
assert (W64 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (mf + 64) 8 F)
  by (rewrite <- U9; apply (sa_fld E _ 9 _ _ 0 216 0 216 64 8%N 10%nat F RG0 eq_refl ltac:(sa_in) E10); [cbn; lia | lia]).
assert (W16 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (mf + 16) 8 F)
  by (rewrite <- U9; apply (sa_fld E _ 9 _ _ 0 216 0 216 16 8%N 10%nat F RG0 eq_refl ltac:(sa_in) E10); [cbn; lia | lia]).
assert (W192 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (mf + 192) 8 F)
  by (rewrite <- U9; apply (sa_fld E _ 9 _ _ 0 216 0 216 192 8%N 10%nat F RG0 eq_refl ltac:(sa_in) E10); [cbn; lia | lia]).
assert (W168 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (mf + 168) 8 SB)
  by (rewrite <- U9; apply (sa_fld E _ 9 _ _ 0 216 0 216 168 8%N 32%nat SB RG0 eq_refl ltac:(sa_in) E32); [unfold SB; cbn; lia | lia]).
assert (WF8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (F + 8) 8 (VAL (A_OBJ 2)))
  by (rewrite <- U10; apply (sa_fld E _ 10 _ _ 0 24 0 24 8 8%N 243%nat _ RG1 eq_refl ltac:(sa_in) E243); [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Vo2 | lia]).
assert (WF16 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (F + 16) 8 (VAL (A_OBJ 3)))
  by (rewrite <- U10; apply (sa_fld E _ 10 _ _ 0 24 0 24 16 8%N 244%nat _ RG1 eq_refl ltac:(sa_in) E244); [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Vo3 | lia]).
assert (WF0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msE)) (F + 0) 8 0x41b58ab3)
  by (rewrite <- U10; apply (field_of_region E _ 10 _ _ 0 24 0 24 0 8%N (SLit 1102416563) 1102416563 RG1 eq_refl ltac:(sa_in));
      [reflexivity | cbn; lia | lia]).
rewrite Z.add_0_r in WF0. clear RG0 RG1.
assert (KEEP : forall a nn v, (forall k, 0 <= k < Z.of_nat nn -> 0 <= a + k < 2 ^ 64 /\ ~ (mf <= a + k < mf + 216) /\
     ~ (F <= a + k < F + 24) /\ ~ (SB + F / 8 <= a + k < SB + F / 8 + 96)) ->
   val_mem SEGS (rd W mem2) a nn v -> val_mem SEGS (rd W (ms_mem msE)) a nn v).
{ intros a nn v Hk Hv.
  apply (sa_vm_kept E _ _ (ms_mem msM) _ a nn v HFr);
  [| apply (sa_vm_kept E _ _ mem2 (ms_mem msM) a nn v HFr1); [| exact Hv]];
  intros k Hkk; destruct (Hk k Hkk) as (Hr & N1 & N2 & N3); (split; [exact Hr|]);
  intros (r & Hin & Ha); cbn [ss_mem In add_cond set_facts sa_ss2 sa_rs2] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [sa_rmf sa_rfr sa_rsh YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9, ?U10, ?U33 in Ha;
     clear - N1 N2 N3 Ha; lia |]);
  destruct Hin. }
assert (KSV : forall od v, -104 <= od <= -8 ->
   val_mem SEGS (rd W mem2) (spZ regs + od) 8 v -> val_mem SEGS (rd W (ms_mem msE)) (spZ regs - - od) 8 v).
{ intros od v Hod Hv. replace (spZ regs - - od) with (spZ regs + od) by lia. apply KEEP; [|exact Hv].
  intros k Hk. cbn in Hk. unfold in_app, kLowShadowBeg, ASAN_CEIL, SB in *. rewrite C3 in HFapp.
  clear - Hk Hod Hmf Hmfc HF0 HFc HFapp HF8r Rsp C1. lia. }
pmkst HS. apply SRr_ret. exists pos, mf.
unfold sa_end, e_sp0, SFa. cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M]. fold F.
split; [reflexivity|]. exists S2, (ms_regs msE), (ms_mem msE). eexists.
split; [reflexivity|].
split; [exact HJ2|].
split; [exact Eab|]. split; [exact HfS2|].
split; [exact Hmf|]. split; [exact Hmf32|].
split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|]. split; [exact Q3|]. split; [exact Q4|].
split; [exact Q16|]. split; [exact Q20|].
split; [unfold shadow_addr; rewrite <- SB_SHADOW_OFF; exact Q23|].
split; [exact Q18|]. split; [exact Q25|].
split; [exact W16|]. split; [exact W64|]. split; [exact W192|]. split; [exact W168|].
split; [exact WF0|]. split; [exact WF8|]. split; [exact WF16|].
split.
{ apply KEEP; [| replace (F + 1016) with (F + 1024 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)].
  intros k Hk. cbn in Hk. unfold in_app, kLowShadowBeg, ASAN_CEIL, SB in *. rewrite C3 in HFapp.
  clear - Hk Hmf Hmfc HF0 HFc HFapp HF8r C1. lia. }
split; [exact (KSV (-8) _ ltac:(lia) V1)|].
split; [exact (KSV (-16) _ ltac:(lia) V8)|].
split; [exact (KSV (-24) _ ltac:(lia) V9)|].
split; [exact (KSV (-32) _ ltac:(lia) V18)|].
split; [exact (KSV (-40) _ ltac:(lia) V19)|].
split; [exact (KSV (-48) _ ltac:(lia) V20)|].
split; [exact (KSV (-56) _ ltac:(lia) V21)|].
split; [exact (KSV (-64) _ ltac:(lia) V22)|].
split; [exact (KSV (-72) _ ltac:(lia) V23)|].
split; [exact (KSV (-80) _ ltac:(lia) V24)|].
split; [exact (KSV (-88) _ ltac:(lia) V25)|].
split; [exact (KSV (-96) _ ltac:(lia) V26)|].
exact (KSV (-104) _ ltac:(lia) V27).
Qed.

(* ---- sa_end is the boundary inv_A_end (+0x280) ------------------------------------------------------------- *)
Lemma sa_end_inv : forall g pos mf W2 c2, epre g -> sa_end g pos mf W2 c2 ->
inv_A_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
  arodata_okS g pos mf W2 c2.
Proof.
intros g pos mf W2 c2 Hpre Hend.
pose proof Hpre as Hpre0.
destruct g as [ly S W mem md regs p n pl M].
unfold e_pre, tLLVMFuzzerTestOneInput_pre in Hpre.
unfold sa_end, e_sp0, SFa in Hend.
cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M] in Hpre, Hend.
destruct Hpre as (HPRE & Hra & H10 & H11 & Hnp & Hlen & Hpl & Hfr0 & Hnev0 & Hbb0 & _ & _ & _ & _ & _ & Hmo0).
destruct Hend as (-> & S2 & regs2 & mem2 & md2 & -> & HJ & Eab & (f & ES2) & Hmf & Hmf32 &
  Q2 & Q9 & Q8 & Q3 & Q4 & Q16 & Q20 & Q23 & Q18 & Q25 & W16 & W64 & W192 & W168 & WF0 & WF8 & WF16 & WFL &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & Hblk & _).
rewrite Hfr0, app_nil_r in Hfrs.
unfold inv_A_end, acut, ecommon, hblocks, sh_reg, e_sp0, SFa, MEV.
cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M].
exists ly, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HJ|].
split; [exact Hfrs|].
split; [unfold EV_LLVMF; lia|].
split.
{ replace (0 * (mo_malloc MT 256 + mo_free MT)) with 0 by ring. rewrite ES2.
  apply (mo_le_set_fs_r MT MTF). apply (mo_le_refl MT MTL). }
split.
{ rewrite ES2. apply (mo_ok_set_fs MT MTF). apply (mo_ok_le MT MTL S _ (XM_LIB n) Hmo0).
  pose proof (HXM n) as Hx. clear - Hx. lia. }
split.
{ split; [exact Q2|]. split; [exact Q9|]. split; [rewrite Q8; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [exact Hmf|]. split; [exact Hmf32|].
  split; [rewrite Q3; exact Hgp|]. split; [rewrite Q4; exact Htp|].
  split; [exact W16|]. split; [exact W64|]. split; [exact W192|].
  split; [rewrite <- SB_SHADOW_OFF; exact W168|].
  split; [unfold raZ in Hra; rewrite <- Hra; exact V1|].
  split; [exact V8|]. split; [exact V9|]. split; [exact V18|]. split; [exact V19|]. split; [exact V20|].
  split; [exact V21|]. split; [exact V22|]. split; [exact V23|]. split; [exact V24|]. split; [exact V25|].
  split; [exact V26|]. split; [exact V27|].
  split; [exact WFL|].
  split; [exact Hpre0|].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hfds & Hfs).
  split; [intros fd; rewrite Hfds; reflexivity|]. split; [exact Hfs|].
  unfold bytes_at8. apply (garr8_frame SEGS (rd W mem) (rd W mem2) p _ Hpl).
  intros a Ha. rewrite length_map, <- Hlen in Ha.
  destruct Hnp as [[-> _] | [Hn Hin]]; [lia|].
  apply (mbyte_of_aview SEGS). replace a with (p + (a - p)) by lia.
  apply (Hblk p n (a - p) Hin ltac:(rewrite Eab; exact Hin)); [pose proof (req_size_pos n ltac:(lia)); lia|].
  intros (r & Hr & _). destruct Hr. }
split; [exact WF0|]. split; [exact WF8|]. split; [exact WF16|].
split; [split; [rewrite Eab; apply Permutation_refl | apply Forall_nil]|].
split; [exact Q23|]. split; [exact Q16|].
split; [rewrite Q18; exact H11|]. rewrite Q25; exact H10.
Qed.

(* ---- the segment ------------------------------------------------------------------------------------------- *)
Lemma seg_A :
seg_A_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
intros g W2 c2 (-> & ->) Hpre.
apply (SRr_bind SEGS _ _ _ _ (sa_part1 g Hpre)). intros W3 c3 _ Hret.
apply (SRr_bind SEGS _ _ _ _ (sa_part2 g W3 c3 Hpre Hret)). intros W4 c4 _ (pos & mf & Hend).
apply SRr_ret. exists pos, mf. exact (sa_end_inv g pos mf W4 c4 Hpre Hend).
Qed.

Check (seg_A :
seg_A_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).

End c.
End b.
End a.

Print Assumptions seg_A.
