(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACik.v:90-93, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v; 309 of its 392 lines of code are new or changed and 572 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), the piece +0x1524 .. +0x15c4
   (0x81c98 .. 0x81d38): the entry and the exit of the stem copy. j_stemcpy_glue_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v.
   0x81c98 loads the stem address st from mf+136 into x5. 0x81c9c..0x81ca8 read the shadow byte of st (x6 holds
   the shadow base); a non-zero byte goes to the slow test at 0x82644, which comes back to 0x81cac when the byte
   is addressable. 0x81cac loads the stem's first byte into x15; 0x81cb0 jumps to 0x81d34 (x27 := 0, the empty
   stem) when it is NUL, and otherwise 0x81cb4..0x81cc4 set up the copy loop, whose head 0x81cc8 is
   j_stemcpy_stmt's (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v) at j = 0. Nothing in the range writes
   memory.
   The walk is two symbolic runs. The first (one slot, 0x81c98) has only the machine-frame word mf+136 in its
   memory. The second starts at 0x81c9c from a new state whose one region is the stem's first byte, based at
   x5's own atom: the stem and the machine frame cannot be both regions of one state, since nothing says they
   are apart. The shadow test of the second run is the token engine's; its one obligation, that the byte at st
   is addressable, is jstem's range_addressable. *)
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

(* The first run's state at 0x81c98 (+0x1524): the machine-frame word mf+136 (s1 = atom 9), read-only, holding
   the stem address (atom 32). *)
Definition jg_mfr : YP09.region :=
YP09.mkRegion (Some 9%nat) 136 144 136 136 [YP09.mkChunk 136 (CVal 8 (SOff 32 0))].
Definition ss_g1 : sstate := mkSS 0x1524 sr_atoms [jg_mfr] None (mkFacts [] [] []).
(* The second run's state at 0x81c9c (+0x1528): the stem's first byte (atom 32), based at x5 = st, read-only;
   st is a low or high application address (amem_range), x6 is the shadow base. *)
Definition jg_str : YP09.region :=
YP09.mkRegion (Some 5%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition jg_facts : facts :=
mkFacts [(5%nat, mkAF 1 (2 ^ 47 - 1) 0); (6%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_g2 : sstate := mkSS 0x1528 sr_atoms [jg_str] None jg_facts.
Definition jg_Bx : sv := SOff 6 0.
Definition jg_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The registers the cut predicates read and the range keeps. *)
Definition jg_keep : list (bv 5) := [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv].

Lemma jg_nwr_ro : forall E rs a, forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ~ in_wrange E rs a.
Proof.
intros E rs a Hok (r & Hin & Ha). rewrite forallb_forall in Hok. specialize (Hok r Hin). apply Z.leb_le in Hok. lia.
Qed.
Lemma jg_awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs STK sp0 FP bl0 blc ly own Hok a Ha. exfalso. exact (jg_nwr_ro E rs a Hok Ha). Qed.

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
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC4 := (jc4 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

(* What jc3 carries that the range keeps, at any state: ecommon, jkeep, the four registers, the shadows and
   bytes of the frame variables, the counter, and the stem (jstem without its call-crossing disjunct). *)
Definition jg_body (g : ectx) (pos mf nm tk dp st : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\ getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 st (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0]) /\
(st + Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1 <= SFa g pos + V_nm \/
SFa g pos + V_nm + N_nm <= st) /\
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF st
(Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1) /\
amem_range st (Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1) /\ 0 < st.

(* A run that writes nothing and keeps the registers of jg_keep keeps jg_body. *)
Lemma jg_mv : forall (g : ectx) pos mf nm tk dp st ly2 S2 (W2 : world SEGS) regs mem md regs' mem' md',
jg_body g pos mf nm tk dp st ly2 S2 W2 regs mem md ->
mrestrict (w_H W2) mem' = mrestrict (w_H W2) mem ->
(forall r, In r jg_keep -> getr regs' r = getr regs r) ->
m_fds md' = m_fds md -> m_fs md' = m_fs md ->
jg_body g pos mf nm tk dp st ly2 S2 W2 regs' mem' md'.
Proof.
intros g pos mf nm tk dp st ly2 S2 W2 regs mem md regs' mem' md' HB EQR RK Efds Efs.
assert (EQV : aview SEGS (w_H W2) mem' = aview SEGS (w_H W2) mem) by (unfold aview; rewrite EQR; reflexivity).
unfold jg_body, ecommon, jkeep, id_at, sh_zero, sh_blk, bytes_at8, sh_reg in *.
rewrite EQV, EQR, Efds, Efs.
rewrite !RK by (cbn [jg_keep In]; repeat (first [left; reflexivity | right])).
exact HB.
Qed.

(* The first run's start: st_ok of ss_g1 from the cut's registers and mf+136. *)
Lemma jg_entry1 : forall (W : world SEGS) regs mem mf st,
getr regs 9 = w64 mf -> 0 <= mf -> mf + 144 <= 2 ^ 64 -> 0 <= st < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (mf + 136) 8 st ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 st])) ss_g1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1524)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf st R9 Hm0 Hm1 Hst V136.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 st])).
assert (E9 : ew E 9 = getr regs 9)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 st)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9, R9; apply unsigned_lit_small; lia).
unfold ss_g1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold jg_mfr, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ mf 136 8 (SOff 32 0) st);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact V136].
- apply pairwise_disjoint_of_extents. unfold jg_mfr, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

(* The second run's start: st_ok of ss_g2 from x5 = st, x6 = the shadow base and the stem's first byte b0. The
   shadow test needs no entry of its own (its obligation is discharged at the run), so sh_ok is of []. *)
Lemma jg_entry2 : forall (W : world SEGS) regs mem st b0,
getr regs 5 = w64 st -> getr regs 6 = w64 SHADOW_OFF -> 1 <= st <= 2 ^ 47 - 1 -> 0 <= b0 < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) st 1 b0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 b0])) ss_g2
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1528)) mem (seg_rom SEGS))) /\
sh_ok SEGS jg_Bx [] (Eimg (Ereg regs [Z_to_bv 64 b0])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem st b0 R5 R6 Hst Hb0 Vb0.
split; [|apply Forall_nil].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 b0])).
assert (E5 : ew E 5 = getr regs 5)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 5 5%bv eq_refl)).
assert (E6 : ew E 6 = getr regs 6)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 6 6%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 b0)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U5 : bv_unsigned (ew E 5) = st) by (rewrite E5, R5; apply unsigned_lit_small; lia).
assert (U6 : bv_unsigned (ew E 6) = SHADOW_OFF)
by (rewrite E6, R6; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = b0) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_g2. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold jg_str, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U5. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ st 0 1 (SOff 32 0) b0);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
  rewrite Z.add_0_r. exact Vb0.
- apply pairwise_disjoint_of_extents. unfold jg_str, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
- unfold facts_ok, jg_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U5, U6, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* jc4 from jg_body, x27 and the bytes of exp_nm. *)
Lemma jg_mk_jc4 : forall (g : ectx) pos mf nm tk dp st ly2 S2 (W2 : world SEGS) regs4 mem4 md4,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem4 md4 (4 * Z.of_nat (m_nrec g) + 7) ->
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
jg_body g pos mf nm tk dp st ly2 S2 W2 regs4 mem4 md4 ->
getr regs4 27 = w64 (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) ->
bytes_at8 W2 mem4 (SFa g pos + V_nm) (SlotModel.n_stem (e_pl g)) ->
JC4 g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x15c4) regs4 mem4 md4).
Proof.
intros g pos mf nm tk dp st ly2 S2 W2 regs4 mem4 md4 HJ Hfrs Hk MLE MOK HB R27 HNM.
destruct HB as (HC & HK & R6 & R18 & R25 & R26 & Znm & Zdp & Zw4 & Bw4 & Vn2 & _).
unfold jc4, acut. exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|]. split; [exact HC|].
exact (conj HK (conj R6 (conj R18 (conj R25 (conj R26 (conj R27 (conj Znm (conj Zdp (conj Zw4
(conj Bw4 (conj Vn2 HNM))))))))))).
Qed.

(* The env_agree of an env the token run extended (atoms above 32 only). *)
Ltac jg_agree HAE :=
split; [ let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn;
repeat (rewrite ew_ewset_other by (clear - Hnn; lia)); exact (proj1 HAE nn Hnn)
| cbn [ed ewset]; exact (proj2 HAE) ].

(* The memory after the runs is the memory at the start of the second run: no run has a write window. *)
Ltac jg_eqr :=
apply functional_extensionality; let xq := fresh "xq" in intros xq;
repeat lazymatch goal with
| Hf : frame_of _ _ (mrestrict ?Hw ?ma) (mrestrict ?Hw ?mb) |- mrestrict ?Hw ?mb xq = _ =>
  rewrite (Hf xq ltac:(apply jg_nwr_ro; vm_compute; reflexivity)); clear Hf
end; reflexivity.

(* +0x1528 .. +0x15c4: the shadow test, the first-byte test, the empty-stem path and the loop. *)
Lemma jg_two : AR_laws SEGS B ->
j_stemcpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp st ly2 S2 (W2 : world SEGS) regs3 mem3 md3,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
jg_body g pos mf nm tk dp st ly2 S2 W2 regs3 mem3 md3 ->
getr regs3 5 = w64 st ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x1528)) mem3 (seg_rom SEGS)) md3) (JC4 g pos mf nm tk dp).
Proof.
intros LAWS HLOOP g pos mf nm tk dp st ly2 S2 W2 regs3 mem3 md3 HJ Hfrs Hk MLE MOK HB R5 Hwok.
pose proof HB as (_ & _ & R6 & _ & R25 & _ & _ & _ & _ & _ & _ & Hbst & Hdisj & Hra & Hamr & Hst0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstb : 1 <= st <= 2 ^ 47 - 1)
by (clear - Hamr Hst0 C3 C4 C5; unfold amem_range in Hamr; rewrite C4, C5, C3 in Hamr; lia).
remember (nth 0 (map (fun b : byte => bv_unsigned b) (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0])) 0)
as b0 eqn:Eb0.
assert (Vb0 : val_mem SEGS (mrestrict (w_H W2) mem3) st 1 b0 /\ 0 <= b0 < 256).
{ rewrite Eb0. clear - Hbst. unfold bytes_at8 in Hbst.
  assert (Hl : (0 < length (map (fun b : byte => bv_unsigned b)
    (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0])))%nat)
  by (rewrite length_map, length_app; cbn [length]; lia).
  destruct (Hbst 0%nat Hl) as [Hv Hr]. rewrite Z.add_0_r in Hv. exact (conj Hv Hr). }
destruct Vb0 as [Vb0 Hb0r].
remember (Eimg (Ereg regs3 [Z_to_bv 64 b0])) as E eqn:HE.
destruct (jg_entry2 W2 regs3 mem3 st b0 R5 R6 Hstb Hb0r Vb0) as [HS SHOK].
rewrite <- HE in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs3 [Z_to_bv 64 b0]) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E5 : ew E 5 = Z_to_bv 64 st)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 5 5%bv eq_refl); exact R5).
assert (E6 : ew E 6 = Z_to_bv 64 SHADOW_OFF)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 6 6%bv eq_refl); exact R6).
assert (E25 : ew E 25 = getr regs3 25)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 25 25%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 b0)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 b0]) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
pose proof (paj_run B LAWS) as RUN.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK jg_Bspan.
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ => apply jg_awr_ro; vm_compute; reflexivity
| |- range_addressable _ _ _ _ =>
  unfold jg_Bx; cbn [ms_mem mkst]; rewrite <- (aview_rd_of SEGS);
  rewrite (U_atom E 6 SHADOW_OFF E6) by (unfold SHADOW_OFF; lia);
  rewrite (U_atom E 5 st E5) by (clear - Hstb; lia);
  apply (range_addressable_sub _ _ st (Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1));
  [exact Hra | clear; lia | clear; lia]
| |- _ => idtac
end.
psrr_branch_tok RUN BR HS SHOK jg_Bspan.
- (* the byte is NUL: the empty stem, 0x81d34 *)
  lazymatch goal with HS1 : st_ok_pi _ _ ?E1 _ _ |- _ =>
    assert (X32 : ew E1 32 = Z_to_bv 64 b0) by (cbn [ew ewset Nat.eqb]; exact E32);
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      rewrite (jb_eq_lit E1 32 b0 0 X32) in Hc by (clear - Hb0r; lia); apply Z.eqb_eq in Hc end;
    assert (HAE1 : env_agree 32 (Ereg regs3 [Z_to_bv 64 b0]) E1) by (jg_agree HAE)
  end.
  assert (Hnil : SlotModel.n_stem (e_pl g) = []).
  { pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_stem_nz (e_pl g)) as Hnz.
    rewrite Eb0 in Hc. clear - Hc Hnz. revert Hc Hnz.
    destruct (SlotModel.n_stem (e_pl g)) as [|b sl]; intros Hc Hnz; [reflexivity|].
    exfalso. apply (Hnz b (or_introl eq_refl)). exact Hc. }
  paj_run_to_sh RUNTOP HS HJ 0x15c4; [apply jg_awr_ro; vm_compute; reflexivity |].
  lazymatch goal with HS1 : st_ok_pi _ _ ?E1 ?ss1 (restrict _ ?ms1) |- _ =>
    prreg HS1 (27%bv : bv 5) R27;
    assert (RK : forall r, In r jg_keep -> getr (ms_regs ms1) r = getr regs3 r)
    by (eapply (regs_kept_of_st_ok_pi E1 ss1 (restrict (w_H W2) ms1) regs3 _ jg_keep HS1 HAE1);
        vm_compute; reflexivity);
    assert (EQR : mrestrict (w_H W2) (ms_mem ms1) = mrestrict (w_H W2) mem3) by jg_eqr;
    pmkst HS1;
    apply SRr_ret;
    apply (jg_mk_jc4 g pos mf nm tk dp st ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ HJ Hfrs Hk MLE MOK);
    [ apply (jg_mv g pos mf nm tk dp st ly2 S2 W2 regs3 mem3 md3 _ _ _ HB EQR RK);
      [rewrite ?j_wvb_fds; reflexivity | rewrite ?j_wvb_fs; reflexivity]
    | rewrite Hnil; cbn [length]; exact R27
    | rewrite Hnil; exact (garr8_nil SEGS _ _) ]
  end.
- (* the byte is not NUL: the loop's head 0x81cc8 at j = 0 *)
  lazymatch goal with HS1 : st_ok_pi _ _ ?E1 _ _ |- _ =>
    assert (X32 : ew E1 32 = Z_to_bv 64 b0) by (cbn [ew ewset Nat.eqb]; exact E32);
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      rewrite (jb_eq_lit E1 32 b0 0 X32) in Hc by (clear - Hb0r; lia); apply Z.eqb_neq in Hc end;
    assert (HAE1 : env_agree 32 (Ereg regs3 [Z_to_bv 64 b0]) E1) by (jg_agree HAE)
  end.
  assert (Hne : b0 = bv_unsigned (nth 0 (SlotModel.n_stem (e_pl g)) (RcIdentModel.zb 0)) /\
    (0 < length (SlotModel.n_stem (e_pl g)))%nat).
  { rewrite Eb0 in Hc |- *. clear - Hc. revert Hc.
    destruct (SlotModel.n_stem (e_pl g)) as [|b sl]; intros Hc; [exfalso; apply Hc; reflexivity|].
    split; [reflexivity | cbn [length]; lia]. }
  destruct Hne as [Eb0' Hlen].
  pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_stem_len (e_pl g)) as H16.
  pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_stem_nonul (e_pl g)) as Hnn.
  paj_run_to_sh RUNTOP HS HJ 0x1554; [apply jg_awr_ro; vm_compute; reflexivity |].
  lazymatch goal with HS1 : st_ok_pi _ _ ?E1 ?ss1 (restrict _ ?ms1) |- _ =>
    prreg HS1 (5%bv : bv 5) Q5; prreg HS1 (10%bv : bv 5) Q10; prreg HS1 (11%bv : bv 5) Q11;
    prreg HS1 (12%bv : bv 5) Q12; prreg HS1 (13%bv : bv 5) Q13; prreg HS1 (14%bv : bv 5) Q14;
    prreg HS1 (15%bv : bv 5) Q15;
    assert (RK : forall r, In r jg_keep -> getr (ms_regs ms1) r = getr regs3 r)
    by (eapply (regs_kept_of_st_ok_pi E1 ss1 (restrict (w_H W2) ms1) regs3 _ jg_keep HS1 HAE1);
        vm_compute; reflexivity);
    assert (EQR : mrestrict (w_H W2) (ms_mem ms1) = mrestrict (w_H W2) mem3) by jg_eqr;
    pmkst HS1;
    lazymatch goal with |- SRr _ _ (mkCfg _ ?md4) _ =>
      assert (HB4 : jg_body g pos mf nm tk dp st ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) md4)
      by (apply (jg_mv g pos mf nm tk dp st ly2 S2 W2 regs3 mem3 md3 _ _ _ HB EQR RK);
          [rewrite ?j_wvb_fds; reflexivity | rewrite ?j_wvb_fs; reflexivity]);
      unfold jc4;
      apply (HLOOP LAWS g pos mf nm tk dp st (SlotModel.n_stem (e_pl g)) 0 W2);
      unfold acut; exists ly2, S2, (ms_regs ms1), (ms_mem ms1), md4
    end
  end.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|].
  destruct HB4 as (HC4 & HK4 & R64 & R184 & R254 & R264 & Znm4 & Zdp4 & Zw44 & Bw44 & Vn24 & Hbst4 & Hdisj4
    & Hra4 & Hamr4 & Hst04).
  split; [exact HC4|].
  split; [exact HK4|]. split; [exact R64|]. split; [exact R184|]. split; [exact R254|]. split; [exact R264|].
  split; [exact Znm4|]. split; [exact Zdp4|]. split; [exact Zw44|]. split; [exact Bw44|]. split; [exact Vn24|].
  split; [exact Hwok|]. split; [exact Hbst4|]. split; [exact Hra4|]. split; [exact Hamr4|].
  split; [exact Hst04|]. split; [clear - H16; lia|]. split; [exact Hnn|]. split; [exact Hdisj4|].
  split; [clear - Hlen; lia|]. split; [exact (garr8_nil SEGS _ _)|].
  split; [rewrite Z.add_0_r, Q5, E5; reflexivity|].
  split; [rewrite Z.add_0_r, Q10, E5, unsigned_lit_small by (clear - Hstb; lia); reflexivity|].
  split; [rewrite Z.add_0_r, Q11, E25; exact R25|].
  split; [rewrite Z.add_0_r, Q14, E25; exact R25|].
  split; [first [exact Q12 | rewrite Q12; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]|].
  split; [first [exact Q13 | rewrite Q13; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]|].
  rewrite Q15, E32, Eb0'. reflexivity.
Qed.

(* +0x1524 .. +0x15c4. *)
Lemma j_stemcpy_glue : j_stemcpy_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold j_stemcpy_glue_stmt. intros LAWS HLOOP g pos mf nm tk dp st W2 c2 Hc3 Hwok.
destruct Hc3 as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & R6 & R18 & R25 & R26 & Znm & Zdp & Zw4 & Bw4 & Vn2 & _ & V136 & HST).
destruct HST as (_ & Hbst & Hdisj & Hra & Hamr & Hst0).
assert (HB : jg_body g pos mf nm tk dp st ly2 S2 W2 regs2 mem2 md2)
by exact (conj HC (conj HK (conj R6 (conj R18 (conj R25 (conj R26 (conj Znm (conj Zdp (conj Zw4 (conj Bw4
(conj Vn2 (conj Hbst (conj Hdisj (conj Hra (conj Hamr Hst0))))))))))))))).
pose proof HC as (_ & Rs1 & _ & Hmfb & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & H0stk & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hmf : 0 <= mf /\ mf + 144 <= 2 ^ 64) by (clear - Hmfb H0stk Hceil Hslo Hshi H47 C1; lia).
assert (Hstb : 0 <= st < 2 ^ 64)
by (clear - Hamr Hst0 C3 C4 C5; unfold amem_range in Hamr; rewrite C4, C5, C3 in Hamr; lia).
remember (Eimg (Ereg regs2 [Z_to_bv 64 st])) as E eqn:HE.
pose proof (jg_entry1 W2 regs2 mem2 mf st Rs1 (proj1 Hmf) (proj2 Hmf) Hstb V136) as HS.
rewrite <- HE in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E32 : ew E 32 = Z_to_bv 64 st)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 st]) E)
by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1524)) with (Z_to_bv 64 (BASE + 0x1524)).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
paj_run_to_sh RUNTOP HS HJ 0x1528; [apply jg_awr_ro; vm_compute; reflexivity |].
lazymatch goal with HS1 : st_ok_pi _ _ _ ?ss1 (restrict _ ?ms1) |- _ =>
  prreg HS1 (5%bv : bv 5) R5; rewrite E32 in R5;
  assert (RK : forall r, In r jg_keep -> getr (ms_regs ms1) r = getr regs2 r)
  by (eapply (regs_kept_of_st_ok_pi E ss1 (restrict (w_H W2) ms1) regs2 _ jg_keep HS1 HAE);
      vm_compute; reflexivity);
  assert (EQR : mrestrict (w_H W2) (ms_mem ms1) = mrestrict (w_H W2) mem2) by jg_eqr;
  pmkst HS1;
  apply (jg_two LAWS HLOOP g pos mf nm tk dp st ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ HJ Hfrs Hk MLE MOK);
  [ apply (jg_mv g pos mf nm tk dp st ly2 S2 W2 regs2 mem2 md2 _ _ _ HB EQR RK);
    [rewrite ?j_wvb_fds; reflexivity | rewrite ?j_wvb_fs; reflexivity]
  | exact R5 | exact Hwok ]
end.
Qed.

End c.
End b.
End a.
