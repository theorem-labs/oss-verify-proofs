(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACik.v:90-93, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v; 204 of its 288 lines of code are new or changed and 571 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), the piece +0x188c .. +0x1910
   (0x82000 .. 0x82084): the copy of the literal " out)" (object 11) into `exp_dp`, around the loop
   j_lit3_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v). The statement is j_lit3_glue_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v.

   The code before the loop (BASE + 0x188c .. BASE + 0x18a4), a plain run with no checked access and no store:
     0x82000 x11 := 0                       the index i
     0x82004 x13 := the word at mf+200      ld, the length of `exp_dp` so far (j_L3)
     0x82008 x16 := 32                      the literal's first byte, ' '
     0x8200c x10 := pc-relative address     (with 0x82010) x14 := the literal's address, object 11
     0x82014 x12 := x26 + x13               &exp_dp + ld
     0x82018 x15 := 5                       the literal's length
   and it falls into the loop head 0x8201c (BASE + 0x18a8), which is j_lit3_stmt's head cut with i = 0. The
   loop's exit 0x82084 (BASE + 0x1910) is jc9's own slot; there `exp_dp` holds j_dp3 ++ " out)", which is
   SlotModel.n_EXP_DP (LLVMFuzzerTestOneInput_seg_J_model.m2_dp_full). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at 0x82000 (+0x188c): one read-only region, the counter word mf+200 (base s1, atom 9),
   holding ld (atom 32). *)
Definition jl3_mf : YP09.region := YP09.mkRegion (Some 9%nat) 200 208 200 200
[YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition ss_jl3 : sstate := mkSS 0x188c sr_atoms [jl3_mf] None (mkFacts [] [] []).

(* The model: the display before the literal, its length, and the whole display after it. *)
Lemma jl3_len3 : forall inp, Z.of_nat (length (j_dp3 inp)) = j_L3 inp.
Proof. intro inp. exact (LLVMFuzzerTestOneInput_seg_J_model.m2_len3 inp). Qed.
Lemma jl3_dp_full : forall inp, j_dp3 inp ++ j_lit_out = SlotModel.n_EXP_DP inp.
Proof. intro inp. exact (LLVMFuzzerTestOneInput_seg_J_model.m2_dp_full inp). Qed.
Lemma jl3_L3_bound : forall inp, SlotModel.n_wok inp = true -> 0 <= j_L3 inp /\ j_L3 inp + 5 <= 38.
Proof.
intros inp Hw.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_n_ld_le inp Hw) as H1.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_len_dp inp) as H2.
pose proof (jl3_len3 inp) as H3.
change (j_L3 inp) with (LLVMFuzzerTestOneInput_seg_J_model.m2_L3 inp) in H3 |- *.
unfold SlotModel.n_ld in H1. clear - H1 H2 H3. lia.
Qed.
Lemma jl3_lit_nonul : ~ In (RcIdentModel.zb 0) j_lit_out.
Proof.
apply LLVMFuzzerTestOneInput_seg_J_model.m2_NZ_notin, LLVMFuzzerTestOneInput_seg_J_model.m2_NZ_b.
vm_compute. reflexivity.
Qed.
Lemma jl3_lit_bytes : map (fun b : byte => bv_unsigned b) (j_lit_out ++ [RcIdentModel.zb 0]) = [32; 111; 117; 116; 41; 0].
Proof. vm_compute. reflexivity. Qed.
(* A register is in a literal list. Unlike `tauto`, it never touches the context, so no unused Section
   variable (XN_LIB, a Z -> Z read as an implication) ends up in the closed lemmas. *)
Local Ltac jl3_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
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
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* The image facts (the literal's bytes), as lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v states them for
   j_img. *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation JC8 := (jc8 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC9 := (jc9 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- a run that writes nothing keeps every fact of the cut ------------------------------------------------ *)
Lemma jl3_ecommon_moved : forall g pos mf ly2 S2 (W2 : world SEGS) regs2 regs3 mem2 mem3 md2 md3,
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 regs3 mem2 mem3 md2 md3 HC EQR RK Efds Efs.
unfold ecommon, bytes_at8 in *. rewrite EQR, Efds, Efs.
rewrite (RK 2%bv ltac:(jl3_in)), (RK 3%bv ltac:(jl3_in)), (RK 4%bv ltac:(jl3_in)),
(RK 8%bv ltac:(jl3_in)), (RK 9%bv ltac:(jl3_in)).
exact HC.
Qed.
Lemma jl3_jkeep_moved : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 regs3 mem2 mem3,
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs3 mem3.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 regs3 mem2 mem3 HK EQR RK.
assert (EQV : aview SEGS (w_H W2) mem3 = aview SEGS (w_H W2) mem2) by (unfold aview; rewrite EQR; reflexivity).
unfold jkeep, sh_reg, id_at, sh_zero, sh_blk, bytes_at8 in *. rewrite EQV, EQR.
rewrite (RK 21%bv ltac:(jl3_in)), (RK 23%bv ltac:(jl3_in)), (RK 24%bv ltac:(jl3_in)).
exact HK.
Qed.
Lemma jl3_jdp_regs_moved : forall g pos regs2 regs3,
jdp_regs g pos regs2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
jdp_regs g pos regs3.
Proof.
intros g pos regs2 regs3 HD RK. unfold jdp_regs in *.
rewrite (RK 6%bv ltac:(jl3_in)), (RK 18%bv ltac:(jl3_in)), (RK 25%bv ltac:(jl3_in)),
(RK 26%bv ltac:(jl3_in)).
exact HD.
Qed.
Lemma jl3_jdp_mem_moved : forall g pos (W2 : world SEGS) mem2 mem3 l,
jdp_mem g pos W2 mem2 l -> mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 -> jdp_mem g pos W2 mem3 l.
Proof.
intros g pos W2 mem2 mem3 l HD EQR.
assert (EQV : aview SEGS (w_H W2) mem3 = aview SEGS (w_H W2) mem2) by (unfold aview; rewrite EQR; reflexivity).
unfold jdp_mem, sh_zero, bytes_at8 in *. rewrite EQV, EQR. exact HD.
Qed.
Lemma jl3_bytes_moved : forall (W2 : world SEGS) mem2 mem3 a l,
bytes_at8 W2 mem2 a l -> mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 -> bytes_at8 W2 mem3 a l.
Proof. intros W2 mem2 mem3 a l H EQR. unfold bytes_at8 in *. rewrite EQR. exact H. Qed.

(* ---- 0x82000 .. 0x8201c: from jc8 to the loop's head with i = 0 ------------------------------------------ *)
Lemma jl3_head : forall (g : ectx) pos mf nm tk dp (W2 : world SEGS) c2,
AR_laws SEGS B -> globs_marked SEGS B G -> In (VAL (A_OBJ 11), 6) G ->
JC8 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x18a8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
j_lit_pre B g pos mf nm tk dp (VAL (A_OBJ 11)) j_lit_out
(j_dp3 (e_pl g) ++ firstn (Z.to_nat 0) j_lit_out) ly2 S2 W2 regs2 mem2 /\
0 <= 0 < 5 /\
getr regs2 11 = w64 0 /\
getr regs2 12 = w64 (SFa g pos + V_dp + j_L3 (e_pl g)) /\
getr regs2 13 = w64 (j_L3 (e_pl g)) /\
getr regs2 14 = w64 (VAL (A_OBJ 11)) /\
getr regs2 15 = w64 5 /\
getr regs2 16 = w64 (bv_unsigned (nth (Z.to_nat 0) j_lit_out (RcIdentModel.zb 0))))).
Proof.
intros g pos mf nm tk dp W2 c2 LAWS HGM HG11 Hc8 Hwok.
destruct Hc8 as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & HDR & HDM & R27 & V200 & HNM).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ &
_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & H0STK & Hceil & Hslo & Hshi & H47 & _).
assert (Hmfr : 0 <= mf /\ mf + 208 <= 2 ^ 64) by (clear - Hmfb Hceil Hslo Hshi H47 H0STK C1; lia).
destruct (jl3_L3_bound (e_pl g) Hwok) as [HL3a HL3b].
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
(* the environment: atom 32 = ld (mf+200) *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (j_L3 (e_pl g))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (j_L3 (e_pl g)))
by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E252 : ew E 252%nat = Z_to_bv 64 (VAL (A_OBJ 11)))
by (rewrite HE; exact (Eimg_img _ (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (j_L3 (e_pl g))]) E)
by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmfr. lia. }
(* the symbolic state at 0x82000 *)
assert (HS : st_ok_pi SEGS VAL E ss_jl3
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x188c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jl3. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold jl3_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [clear - Hmfr; lia|]. split; [clear - Hmfr; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 200 8 (SOff 32 0) (j_L3 (e_pl g)));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - HL3a HL3b; lia | clear - Hmfr; lia | exact V200].
  - apply pairwise_disjoint_of_extents. unfold jl3_mf, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x188c)) with (Z_to_bv 64 (BASE + 0x188c)).
paj_run_to_sh RUNTOP HS HJ 0x18a8.
{ cbn [ss_mem ss_jl3]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo jl3_mf]; clear - Hmfr; lia | apply awr_ok_nil]. }
(* the run writes nothing: its one region is read-only *)
cbn [ms_mem] in HFr.
assert (EQR : mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2).
{ apply functional_extensionality. intros x. apply HFr. intros (r & Hin & Hr).
  cbn [ss_mem ss_jl3 In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi jl3_mf] in Hr. clear - Hr. lia. }
clear HF HFr HG.
(* the registers at 0x8201c *)
assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr (ms_regs ms) r = getr regs2 r).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    eapply (regs_kept_of_st_ok_pi E ssx (restrict (w_H W2) ms) regs2 _
      [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS AGE);
    vm_compute; reflexivity end. }
pose proof HDR as (_ & _ & _ & R26).
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (16%bv : bv 5) Q16.
rewrite (EE 26%nat 26%bv eq_refl), R26, E32 in Q12. unfold w64 in Q12. rewrite alu64_add_lit in Q12.
rewrite E32 in Q13. rewrite E252 in Q14.
(* the literal: its bytes (llvmf_img, object 11), its shadow (a registered global) and where it is *)
pose proof HJ as (HAR3 & _).
pose proof (@j_img _ _ _ B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS G RO HRO HIMG g pos _ ly2 S2 W2 (ms_mem ms) _ HJ HPRE) as HIM.
destruct HIM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO11 & _).
pose proof (HGM ly2 S2 W2 (ms_mem ms) _ (VAL (A_OBJ 11)) 6 HG11 HAR3) as HSH11.
assert (HOI : IMG_LO <= VAL (A_OBJ 11) /\ VAL (A_OBJ 11) + 8 <= IMG_TOP) by (apply pa_obj_img; clear - Hmfr; lia).
destruct HOI as [HOI1 HOI2].
(* the loop's head cut, i = 0 *)
apply SRr_ret. unfold acut. pmkst HS.
exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split; [exact (jl3_ecommon_moved g pos mf ly2 S2 W2 regs2 (ms_regs ms) mem2 (ms_mem ms) md2 _ HC EQR RK
(j_wvb_fds md2 mat) (j_wvb_fs md2 mat))|].
split.
{ unfold j_lit_pre. change (firstn (Z.to_nat 0) j_lit_out) with (@nil byte). rewrite app_nil_r.
  split; [exact (jl3_jkeep_moved g pos mf nm tk dp ly2 S2 W2 regs2 (ms_regs ms) mem2 (ms_mem ms) HK EQR RK)|].
  split; [exact (jl3_jdp_regs_moved g pos regs2 (ms_regs ms) HDR RK)|].
  split; [exact (jl3_jdp_mem_moved g pos W2 mem2 (ms_mem ms) _ HDM EQR)|].
  split; [exact (jl3_bytes_moved W2 mem2 (ms_mem ms) _ _ HNM EQR)|].
  split; [rewrite (RK 27%bv ltac:(jl3_in)); exact R27|].
  split; [exact Hwok|].
  split; [rewrite jl3_len3; change (Z.of_nat (length j_lit_out)) with 5; unfold N_dp; clear - HL3b; lia|].
  split; [unfold bytes_at8; rewrite jl3_lit_bytes; exact HO11|].
  split; [change (Z.of_nat (length j_lit_out) + 1) with 6; exact HSH11|].
  split; [exact HOI1|].
  split; [change (Z.of_nat (length j_lit_out)) with 5; clear - HOI2; lia|].
  exact jl3_lit_nonul. }
split; [clear - HL3a; lia|].
split; [exact Q11|].
split; [exact Q12|].
split; [exact Q13|].
split; [exact Q14|].
split; [exact Q15|].
rewrite Q16. reflexivity.
Qed.

(* ---- 0x82084: the loop's exit is jc9 ----------------------------------------------------------------------- *)
Lemma jl3_exit : forall (g : ectx) pos mf nm tk dp (W2 : world SEGS) c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1910)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp3 (e_pl g) ++ j_lit_out) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 11 = w64 5 /\
getr regs2 12 = w64 (SFa g pos + V_dp + j_L3 (e_pl g)) /\
getr regs2 13 = w64 (j_L3 (e_pl g))) W2 c2 ->
JC9 g pos mf nm tk dp W2 c2.
Proof.
intros g pos mf nm tk dp W2 c2
(ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfrs & Hk & MLE & MOK & HC & HK & HDR & HDM & HNM & R27 & R11 & R12 & R13).
rewrite jl3_dp_full in HDM.
exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|]. split; [exact HC|].
split; [exact HK|]. split; [exact HDR|]. split; [exact HDM|]. split; [exact R27|].
split; [exact R11|]. split; [exact R12|]. split; [exact R13|]. exact HNM.
Qed.

(* ---- the piece: jc8 -> (0x82000 .. 0x8201c) -> the loop j_lit3_stmt -> jc9 ------------------------------ *)
Lemma j_lit3_glue : j_lit3_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
intros LAWS HGM HG11 LOOP g pos mf nm tk dp W2 c2 Hc8 Hwok.
eapply SRr_bind; [exact (jl3_head g pos mf nm tk dp W2 c2 LAWS HGM HG11 Hc8 Hwok)|].
intros W3 c3 _ H3.
eapply SRr_mono; [exact (LOOP LAWS g pos mf nm tk dp 0 W3 c3 H3)|].
intros W4 c4 _ H4. exact (jl3_exit g pos mf nm tk dp W4 c4 H4).
Qed.

End c.
End b.
End a.

