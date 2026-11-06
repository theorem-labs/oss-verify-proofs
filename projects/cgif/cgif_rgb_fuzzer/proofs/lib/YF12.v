(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g YQ0k YK0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF8x YF0k YF0q YF0o YF1g YF7y YF2q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF12a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, ASTACK, QSTACK, RSTACK, DSTACK, DRSTACK, KSTACK, LFRAME, TFX_IMG_END, kBatchBytes, kBatchSlots, kBatchClass, SHADOW_OFF, TFX_TP, TFX_TSD, A_QUAR, A_ALLOCATOR, A_RChunk, A_CDealloc, o_quar, kQuarantineMax, kQuarantineMin, kQuarantineCacheMax in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section WK. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 : Z).
Variables (own small : bool).
Variable mat0 : list word.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x34140 + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis FH : free_hyps W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small.
Hypothesis GATE : forall PB k, 0 < k -> SHAv map <= PB -> PB + k <= SHEv map len ->
madvise_dontneed_ok (m_vmmaps md0) (Z_to_bv 64 PB) (Z_to_bv 64 k) = true.
Local Notation XW := (YF2q.XW ly map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E0 := (YF2q.E0 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation Er := (YF2q.Er ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E2 := (YF2q.E2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation E1 := (YF2q.E1 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqT := (YF2q.EqT ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqC := (YF2q.EqC ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqMAP := (YF2q.EqMAP ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqLEN := (YF2q.EqLEN ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqIDX := (YF2q.EqIDX ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqN := (YF2q.EqN ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQ := (YF2q.EqQ ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQI := (YF2q.EqQI ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqQL := (YF2q.EqQL ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqLAST := (YF2q.EqLAST ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ1 := (YF2q.EqJ1 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ2 := (YF2q.EqJ2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ3 := (YF2q.EqJ3 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ4 := (YF2q.EqJ4 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ5 := (YF2q.EqJ5 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqJ6 := (YF2q.EqJ6 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqSHB := (YF2q.EqSHB ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqSHA := (YF2q.EqSHA ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqCNT := (YF2q.EqCNT ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqRA := (YF2q.EqRA ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqS0 := (YF2q.EqS0 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqS1 := (YF2q.EqS1 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqS2 := (YF2q.EqS2 ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation EqSHE := (YF2q.EqSHE ly regs0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2).
Local Notation R_MAPH := (YF2q.R_MAPH own).
Local Notation R_STK := YF2q.R_STK.
Local Notation R_MW0 := YF2q.R_MW0.
Local Notation R_MW1 := YF2q.R_MW1.
Local Notation R_NS := YF2q.R_NS.
Local Notation R_J12 := YF2q.R_J12.
Local Notation R_J34 := YF2q.R_J34.
Local Notation R_QI := YF2q.R_QI.
Local Notation R_CTX := YF2q.R_CTX.
Local Notation R_JST := YF2q.R_JST.
Local Notation R_LASTH := YF2q.R_LASTH.
Local Notation R_QL := YF2q.R_QL.
Local Notation COMMON := YF2q.COMMON.
Local Notation REG0 := (YF2q.REG0 own).
Local Notation FFD := (YF2q.FFD small).
Local Notation SR0 := YF2q.SR0.
Local Notation SS0 := (YF2q.SS0 own small).
Local Notation LYB := (YF2q.LYB W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation derived_ranges := (YF2q.derived_ranges W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation WIN := (YF2q.WIN ly regs0 qi lst).
Local Notation WINS := (YF2q.WINS map len).
Local Notation WINM := (YF2q.WINM map len).
Local Notation WIN2 := (YF2q.WIN2 ly regs0 map len qi lst).
Local Notation WIN3 := (YF2q.WIN3 ly regs0 map len qi lst).
Local Notation win_sub := YF2q.win_sub.
Local Notation win_sub_sound := (YF2q.win_sub_sound ly regs0).
Local Notation WSK0 := (YF2q.WSK0 own).
Local Notation within := YF2q.within.
Local Notation within_mono := YF2q.within_mono.
Local Notation windows_within := (YF2q.windows_within ly regs0).
Local Notation frame_within := (YF2q.frame_within ly regs0).
Local Notation MEQP := (YF2q.MEQP mem0).
Local Notation MEQP_frame := (YF2q.MEQP_frame ly regs0 mem0).
Local Notation MEQP_weaken := (YF2q.MEQP_weaken mem0).
Local Notation MEQP_0 := (YF2q.MEQP_0 mem0).
Local Notation WIN_WIN2 := (YF2q.WIN_WIN2 ly regs0 map len qi lst).
Local Notation WIN2_WIN3 := (YF2q.WIN2_WIN3 ly regs0 map len qi lst).
Local Notation WINS_WIN2 := (YF2q.WINS_WIN2 ly regs0 map len qi lst).
Local Notation WSK0_within := (YF2q.WSK0_within W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation WIN_not_WINS := (YF2q.WIN_not_WINS W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation SHD := (YF2q.SHD map len).
Local Notation SHD_frame := (YF2q.SHD_frame W ly regs0 mem0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small FH).
Local Notation SREGS := YF2q.SREGS.
Local Notation at_RET := (YF2q.at_RET W ly regs0 mem0 map len idx n qi lst vra vs0 vs1 vs2 own).
Local Notation at_MUN := (YF2q.at_MUN W ly regs0 mem0 md0 map len idx n qi lst vra vs0 vs1 vs2 own).
Ltac open_FH := pose proof FH as FH_; destruct FH_ as [LY IMG Htp Hra Hregs Hsp Hsp_al Hpres Hsaved Hmap Hdisj Hmaph Harr Hq Hqi Hql Hlst Hown Hlsth Hns Hjunk Hmut Htsd Hjst Hsh_pres SEED].
Ltac off_by tac :=
first [ img_apply off_img_high; tac | unfold off_img; unfold TFX_IMG_LO; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; tac ].
Ltac meq_acc KW :=
match goal with
| M : MEQP ?D ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQP_frame D E _ rs ma mb KW ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename M2 into M
end.
Ltac acc2 KW K :=
lazymatch goal with
| Mq : MEQP ?D ?ma, Sh : SHD ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let Mq2 := fresh "MQ" in let Sh2 := fresh "SHz" in
pose proof (MEQP_frame D E _ rs ma mb KW ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) HFx Mq) as Mq2;
pose proof (SHD_frame E _ rs ma mb K ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) HFx Sh) as Sh2;
clear Mq Sh HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end; rename Mq2 into MQ; rename Sh2 into SH
end.
Ltac zbranch Hc :=
first [ rewrite branch_geu_U in Hc | rewrite branch_ltu_U in Hc | rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc ];
revert Hc; rewrite !U_zev by img_refl; cbn [zev zalu_raw zmd_raw]; unfold zalu_raw, zmd_raw;
rewrite ?Z.add_0_r;
repeat match goal with R : rho_of _ ?k = _ |- context [rho_of _ ?k] => rewrite R end;
numconst; zcanon_simp; land_lits; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end;
zcanon_simp; intros Hc.
Ltac zdec Hbr := zbranch Hbr; unfold zcanon, M64 in Hbr;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hbr;
first [apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr | apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.leb_le in Hbr | apply Z.leb_gt in Hbr];
try unfold sp0 in *; zlia.
Ltac uncond HS := unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Ltac nt HS := lazymatch goal with Hbr : branch_taken _ _ _ = _ |- _ => clear Hbr end; uncond HS.
Ltac evalS HS := lazymatch type of HS with st_ok _ _ ?ss _ => let ss' := img_ev constr:(ss) in img_change ss with ss' in HS end.
Ltac dbg HS := lazymatch type of HS with st_ok _ _ ?ss _ => let pc := img_ev (ss_pc ss) in idtac "PC" pc;
let r := img_ev (sym_step_sh tfxsegs tfxtbl_rtM ss) in lazymatch r with SStop ?why => idtac "WHY" why | _ => idtac "notstuck" end end.
Ltac chunk_index cs off k :=
lazymatch cs with
| (YQ0b.mkChunk ?o _) :: ?t => let e := img_ev (o =? off) in
lazymatch e with true => k | false => chunk_index t off (S k) end
end.
Ltac memvo HS i off :=
lazymatch type of HS with st_ok _ _ ?ss _ =>
let r := img_ev (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rg =>
let cs := img_ev (YQ0b.r_chunks rg) in
let j := chunk_index cs off 0%nat in memv HS i j end end.
Ltac wordeq_prep := img_apply bv_eq; unfold w64; rewrite ?Z_to_bv_unsigned; repeat (rewrite alu64_unsigned; cbn [zalu_raw]);
repeat match goal with R : rho_of _ ?k = _ |- context [bv_unsigned (ew _ ?k)] => unfold rho_of in R; rewrite R end;
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; img_change (bv_modulus 64) with 18446744073709551616;
repeat match goal with |- context [?a mod ?b] => is_zlit a; is_zlit b; let c := img_ev (a mod b) in img_change (a mod b) with c end;
repeat match goal with |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := img_ev (Z.land a b) in img_change (Z.land a b) with c end;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by zlia;
repeat match goal with |- context [2 ^ ?k] => is_zlit k; let c := img_ev (2 ^ k) in img_change (2 ^ k) with c end.
Ltac reg_atom HS r k := let Q := fresh "Q" in rreg HS r Q; rewrite Q; first [ img_exact (Er k r eq_refl) | cbn [sv_denot]; rewrite (Er k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ].
Ltac jword HS i off := eexists; memvo HS i off; [img_refl | img_try (symmetry; img_apply Z_to_bv_bv_unsigned) | img_try (img_apply u64_range)].
Ltac pin_prep :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |].
Ltac qw_split1 HS iW :=
let VW := fresh "VW" in
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) =>
assert (VW : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msx)) (A_ALLOCATOR + 680) 4 1) by (img_try (memv HS iW 0%nat; [img_refl | img_refl | img_try (zlia)]));
apply (proj1 (val_mem4_bytes _ _ _)) in VW; destruct VW as (VW0 & VW1 & VW2 & VW3);
img_change (YP0g.le_byte 1 4 0) with 1 in VW0; img_change (YP0g.le_byte 1 4 1) with 0 in VW1;
img_change (YP0g.le_byte 1 4 2) with 0 in VW2; img_change (YP0g.le_byte 1 4 3) with 0 in VW3;
eapply (st_ok_set_region E _ _ iW _ R_MW1) in HS;
[ | img_refl | img_try (repeat split; img_refl) | img_refl
| img_try (img_apply Forall_cons; [ eapply chunk_ok_val; [img_refl | cbn; zlia | cbn; zlia | img_apply (proj2 (val_mem1_byte _ _ _)); rewrite Z.add_0_l; img_exact VW0 ]
| img_apply Forall_cons; [ img_apply chunk_ok_zero_mb; img_exact (bytes3_of _ _ _ VW1 VW2 VW3) | img_apply Forall_nil ] ]) ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW0 VW1 VW2 VW3
end.
Ltac qw_join0 HS iW :=
let VW := fresh "VW" in let VZ := fresh "VZ" in
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ ?msx) =>
assert (VW : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msx)) (A_ALLOCATOR + 680) 1 0) by (img_try (memv HS iW 0%nat; [img_refl | img_refl | img_try (zlia)]));
apply (proj1 (val_mem1_byte _ _ _)) in VW; img_change (YP0g.le_byte 0 1 0) with 0 in VW;
assert (VZ : forall a, A_ALLOCATOR + 681 <= a < A_ALLOCATOR + 681 + 3 -> mbyte tfxsegs (mrestrict (w_H W) (ms_mem msx)) a = Some (Z_to_bv 8 0))
by (img_try (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msx iW _ 1 _ _ a HS); [img_refl | img_refl | cbn [base_val YQ0b.r_base]; unfold A_ALLOCATOR in Ha |- *; clear - Ha; zlia]));
eapply (st_ok_set_region E _ _ iW _ R_MW0) in HS;
[ | img_refl | img_try (repeat split; img_refl) | img_refl
| img_try (img_apply Forall_cons; [ img_apply chunk_ok_zero_mb; refine (bytes4_of _ _ _ VW (VZ _ _) (VZ _ _) (VZ _ _)); unfold A_ALLOCATOR; zlia | img_apply Forall_nil ]) ];
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts smem_upd] in HS; clear VW VZ
end.
Ltac rrege HS r Hr :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss (restrict ?H ?ms) =>
let e := img_ev (sr_get (ss_regs ss) r) in
let v := eval cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in (sv_denot E e) in
let v := simp_off0 v in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = v)
by (img_try (refine (eq_trans (st_ok_ecall_restrict_reg H E ss ms r HS) _);
change (sv_denot E e = v);
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl))
end.
Lemma segGD_f : own = false -> small = true -> SRr tfxsegs W cfg0 at_MUN.
Proof. first [ exact (YF12a.segGD_f W ly regs0 mem0 md0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small mat0 FH GATE) | exact (YF12a.segGD_f W ly regs0 mem0 md0 map len idx n q qi ql lst j1 j2 j3 j4 j5 j6 vra vs0 vs1 vs2 own small mat0 FH) ]. Qed.
Lemma segGD_t_lo : own = true -> small = true -> map < kLowMemEnd -> SRr tfxsegs W cfg0 at_MUN.
Proof.
intros OWN SM ZARM. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB. pose proof derived_ranges as DR.
rewrite OWN, SM in HS. rewrite SM in Hmap. rewrite OWN in Hown, Hql, Hlsth.
destruct Hsp as [S1 S2]. destruct Hregs as (R10 & R11 & R12 & R1 & R8 & R9 & R18).
destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6). destruct Harr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). destruct Hlst as (X1 & X2 & X3).
pose proof DR as (_ & _ & _ & _ & dK1 & dK2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dSH1 & dSH2 & dSH3 & dL8 & dM8 & dCNT & dJ1 & dJ2 & dJ3 & dJ4 & dJ5 & dJ6 & dV1 & dV2 & dV3 & dV4).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
evalS HS.
pose proof (MEQP_0 WIN) as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_within E0 HE0) as K0. rewrite OWN in K0.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (R32 : rho_of E0 32%nat = T) by (img_try (unfold rho_of; rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - L1 L2; numconst; zlia)).
assert (R33 : rho_of E0 33%nat = ly_C ly) by (img_try (unfold rho_of; rewrite EqC; unfold w64; img_apply unsigned_lit_small; clear - L4 L5; numconst; zlia)).
assert (R34 : rho_of E0 34%nat = map) by (img_try (unfold rho_of; rewrite EqMAP; unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia)).
assert (R35 : rho_of E0 35%nat = len) by (img_try (unfold rho_of; rewrite EqLEN; unfold w64; img_apply unsigned_lit_small; clear - P4; numconst; zlia)).
assert (R36 : rho_of E0 36%nat = idx) by (img_try (unfold rho_of; rewrite EqIDX; unfold w64; img_apply unsigned_lit_small; clear - A1 A2; zlia)).
assert (R37 : rho_of E0 37%nat = n) by (img_try (unfold rho_of; rewrite EqN; unfold w64; img_apply unsigned_lit_small; clear - A1 A2; zlia)).
assert (R38 : rho_of E0 38%nat = q) by (img_try (unfold rho_of; rewrite EqQ; unfold w64; img_apply unsigned_lit_small; clear - A5 A6; numconst; zlia)).
assert (R39 : rho_of E0 39%nat = qi) by (img_try (unfold rho_of; rewrite EqQI; unfold w64; img_apply unsigned_lit_small; clear - A1 A2 A3 A5 A6; numconst; zlia)).
assert (R40 : rho_of E0 40%nat = ql) by (img_try (unfold rho_of; rewrite EqQL; unfold w64; img_apply unsigned_lit_small; clear - A1 A2 A4 A5 A6; numconst; zlia)).
assert (R41 : rho_of E0 41%nat = lst) by (img_try (unfold rho_of; rewrite EqLAST; unfold w64; img_apply unsigned_lit_small; clear - X1 X2; numconst; zlia)).
assert (R42 : rho_of E0 42%nat = j1) by (img_try (unfold rho_of; rewrite EqJ1; unfold w64; img_apply unsigned_lit_small; img_exact dJ1)).
assert (R43 : rho_of E0 43%nat = j2) by (img_try (unfold rho_of; rewrite EqJ2; unfold w64; img_apply unsigned_lit_small; img_exact dJ2)).
assert (R44 : rho_of E0 44%nat = j3) by (img_try (unfold rho_of; rewrite EqJ3; unfold w64; img_apply unsigned_lit_small; img_exact dJ3)).
assert (R45 : rho_of E0 45%nat = j4) by (img_try (unfold rho_of; rewrite EqJ4; unfold w64; img_apply unsigned_lit_small; img_exact dJ4)).
assert (R46 : rho_of E0 46%nat = j5) by (img_try (unfold rho_of; rewrite EqJ5; unfold w64; img_apply unsigned_lit_small; img_exact dJ5)).
assert (R47 : rho_of E0 47%nat = j6) by (img_try (unfold rho_of; rewrite EqJ6; unfold w64; img_apply unsigned_lit_small; img_exact dJ6)).
assert (R48 : rho_of E0 48%nat = SHADOW_OFF) by (img_try (unfold rho_of; rewrite EqSHB; img_refl)).
assert (R49 : rho_of E0 49%nat = SHAv map) by (img_try (unfold rho_of; rewrite EqSHA; unfold w64; img_apply unsigned_lit_small; clear - dSH1 dSH3; zlia)).
assert (R50 : rho_of E0 50%nat = CNTv len) by (img_try (unfold rho_of; rewrite EqCNT; unfold w64; img_apply unsigned_lit_small; clear - dCNT; zlia)).
assert (R55 : rho_of E0 55%nat = SHEv map len) by (img_try (unfold rho_of; rewrite EqSHE; unfold w64; img_apply unsigned_lit_small; unfold SHEv; clear - dSH1 dSH2 dCNT; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 39%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R36, ?R38, ?R39, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id idx) by (img_try (clear - A1 A2; unfold M64; zlia)); rewrite !Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 3) with 8;
clear - A1 A2 A3 A5 A6; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0.
srr_branch_sh tfxtbl_rtM_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R36 R37 A1 A2; zdec Hbr end. } nt HS.
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 39%nat 8)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R37, ?R38, ?R39, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id n) by (img_try (clear - A1 A2; unfold M64; zlia)); rewrite !Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 3) with 8;
destruct Hown as [OW1 OW2]; clear - A1 A2 A3 A5 A6 OW1; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x34218 + D_150). meq_acc K0.
qw_split1 HS 2%nat.
srr_run_to_sh tfxtbl_rtM_ok HS (0x3421c + D_150). meq_acc K0.
qw_join0 HS 2%nat.
assert (ZLO : map + len <= kLowShadowBeg) by (img_try (clear - ZARM P1; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *; img_lia)).
apply (st_ok_add_atom tfxsegs E0 _ _ 34%nat (mkAF 4096 (kLowShadowBeg - 8192) 12)) in HS.
2:{ pose proof R34 as RR. unfold rho_of in RR. split; [|img_try (split)]; cbn [af_lo af_hi af_al2];
[ img_try (rewrite RR; clear - P1 ZLO P4; unfold zone3, kLowShadowBeg in *; img_lia) | img_try (rewrite RR; img_change (2 ^ 12) with 4096; img_exact P3) | img_lia ]. }
evalS HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x5452c + D_2c4). meq_acc K0.
srr_branch_sh tfxtbl_rtM_ok HS. 2:{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr R34 R35 R48 ZLO P1 P4; unfold kLowShadowBeg in ZLO; zdec Hbr end. } nt HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x54594 + D_2c4). meq_acc K0.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 49%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R34, ?R48, ?R49, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id map) by (img_try (clear - P1 P2 P4; unfold M64; numconst; zlia)); rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold SHAv in *; clear - P1 P2 P4 dSH1 dSH3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 50%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R34, ?R35, ?R50, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold CNTv in *; clear - P1 P2 P4 dL8 dM8 dCNT; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0. dbg HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
assert (SHPRES : forall a, SHAv map <= a < SHAv map + CNTv len -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha dSH1 dSH2; zlia)).
img_apply (apresent_same (w_H W) mem0).
- img_apply MQ. rewrite unsigned_lit_small by img_exact Ra. intros Hx. img_exact (WIN_not_WINS a Hx Ha).
- img_apply Hsh_pres. img_exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch_nw W 56%nat E0 _ _ _ (SHAv map) (CNTv len) (0x34234 + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite EqSHA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - dCNT; zlia) | img_try (clear - dSH1; numconst; zlia) | img_try (clear - dSH1 dSH2; numconst; zlia) | img_refl | img_try (zlia)
| img_try (img_exact SHPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | ].
1-2: cbn [ss_mem In] in Hr; unfold rho_of in R32, R33, R34, R39, R40, R41; repeat (destruct Hr as [<-|Hr];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?BV2, ?R32, ?R33, ?R34, ?R39, ?R40, ?R41;
unfold T, sp0 in *; clear - dK1 dK2 L1 L2 L4 L5 P1 P2 P4 A1 A2 A3 A4 A5 A6 X1 X2 dSH1 dSH2 dSH3; unfold GDEPTH; numconst; first [zlia | match goal with |- ?g => idtac "REGFAIL" g end] |]); destruct Hr.
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS. evalS HS.
lazymatch type of HS with st_ok _ ?E _ _ => set (E5 := E) in HS end.
assert (HE5 : forall k, (k < 56)%nat -> ew E5 k = ew E0 k) by (img_try (intros k Hk; (subst E5; cbv beta); rewrite ew_havoc_old by zlia; img_refl)).
assert (HE5' : forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) by (img_try (intros k Hk; img_apply HE5; unfold aHAVf in Hk; zlia)).
pose proof (WSK0_within E5 HE5') as K5. rewrite OWN in K5.
assert (MQ5 : MEQP WIN2 mem5).
{ intros x Hx. rewrite (Hfr5 x) by (img_try (intros Hs; img_apply Hx; img_apply WINS_WIN2; img_exact Hs)). img_apply MQ. intros Hw; img_apply Hx; img_exact (WIN_WIN2 _ Hw). }
assert (SH5 : SHD mem5).
{ intros x Hx. rewrite (Hfill x Hx), RA1m. img_refl. }
pose proof (within_mono _ _ E5 _ WIN_WIN2 K5) as KW5.
clear MQ Hfr5 Hfill SHPRES. rename MQ5 into MQ. rename SH5 into SH.
assert (HR5 : forall k, (k < 56)%nat -> rho_of E5 k = rho_of E0 k) by (img_try (intros k Hk; unfold rho_of; rewrite (HE5 k Hk); img_refl)).
assert (Q32 : rho_of E5 32%nat = T) by (img_try (rewrite (HR5 32%nat ltac:(zlia)); img_exact R32)).
assert (Q33 : rho_of E5 33%nat = ly_C ly) by (img_try (rewrite (HR5 33%nat ltac:(zlia)); img_exact R33)).
assert (Q34 : rho_of E5 34%nat = map) by (img_try (rewrite (HR5 34%nat ltac:(zlia)); img_exact R34)).
assert (Q35 : rho_of E5 35%nat = len) by (img_try (rewrite (HR5 35%nat ltac:(zlia)); img_exact R35)).
assert (Q48 : rho_of E5 48%nat = SHADOW_OFF) by (img_try (rewrite (HR5 48%nat ltac:(zlia)); img_exact R48)).
assert (Q49 : rho_of E5 49%nat = SHAv map) by (img_try (rewrite (HR5 49%nat ltac:(zlia)); img_exact R49)).
assert (Q50 : rho_of E5 50%nat = CNTv len) by (img_try (rewrite (HR5 50%nat ltac:(zlia)); img_exact R50)).
assert (Q55 : rho_of E5 55%nat = SHEv map len) by (img_try (rewrite (HR5 55%nat ltac:(zlia)); img_exact R55)).
srr_run_to_sh tfxtbl_rtM_ok HS (0x52e2c + D_2c4). acc2 KW5 K5.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 49%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Q34, ?Q48, ?Q49, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id map) by (img_try (clear - P1 P2 P4; unfold M64; numconst; zlia)); rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold SHAv in *; clear - P1 P2 P4 dSH1 dSH3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x52e74 + D_2c4). acc2 KW5 K5.
srr_branch_sh tfxtbl_rtM_ok HS. 2:{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr Q34 Q35 Q48 ZLO P1 P4; unfold kLowShadowBeg in ZLO; zdec Hbr end. } nt HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x52e38 + D_2c4). acc2 KW5 K5.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 55%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Q34, ?Q35, ?Q48, ?Q55, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold SHEv, SHAv, CNTv in *; clear - P1 P2 P4 dSH1 dSH2 dSH3 dL8 dM8 dCNT; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW5 K5.
eassert (JOIN : forall (E' : env) regs6 mem6 mat6, (forall k, (k < 56)%nat -> ew E' k = ew E0 k) -> MEQP WIN2 mem6 ->
SHD mem6 ->
st_ok tfxsegs E' _ (restrict (w_H W) (mkst regs6 (Z_to_bv 64 (0x34240 + D_150)) mem6 (seg_rom tfxsegs))) ->
SRr tfxsegs W (mkCfg (mkst regs6 (Z_to_bv 64 (0x34240 + D_150)) mem6 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat6 md0)) at_MUN).
2: { assert (USHA : 0 <= SHAv map + 4095 < 2 ^ 64) by (img_try (clear - dSH1 dSH3; zlia)). assert (USHE : 0 <= SHEv map len < 2 ^ 64) by (img_try (unfold SHEv; clear - dSH1 dSH2 dCNT; zlia)).
destruct (Z_lt_le_dec (SHAv map + 4095 - (SHAv map + 4095) mod 4096) (SHEv map len - SHEv map len mod 4096)) as [LTc|GEc].
- srr_branch_sh tfxtbl_rtM_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr Q49 Q55 USHA USHE LTc; zbranch Hbr;
rewrite ?(zcanon_id (SHEv map len)) in Hbr by (img_try (unfold M64; zlia)); rewrite !land_m4096 in Hbr by zlia; unfold zcanon, M64 in Hbr;
apply Bool.negb_true_iff in Hbr; apply Z.ltb_ge in Hbr; zlia end. }
nt HS.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW5 K5.
set (PB := SHAv map + 4095 - (SHAv map + 4095) mod 4096) in *. set (PE := SHEv map len - SHEv map len mod 4096) in *.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ =>
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
pose proof (st_ok_ecall_full_shape (w_H W) E5 ssM msx HS eq_refl) as SHP; cbn [ss_pc] in SHP; rename msx into msE end end.
rrege HS (17%bv : bv 5) Q17. rrege HS (12%bv : bv 5) Q12.
assert (RPB : SHAv map <= PB <= SHAv map + 4095 /\ PB mod 4096 = 0).
{ (subst PB; cbv beta). clear. pose proof (Z.mod_pos_bound (SHAv map + 4095) 4096 ltac:(img_lia)) as X. split; [img_lia|].
pose proof (Z.div_mod (SHAv map + 4095) 4096 ltac:(img_lia)) as Y. replace (SHAv map + 4095 - (SHAv map + 4095) mod 4096) with ((SHAv map + 4095) / 4096 * 4096) by img_lia. img_apply Z_mod_mult. }
assert (RPE : 0 <= PE <= SHEv map len /\ PE mod 4096 = 0).
{ (subst PE; cbv beta). clear - USHE. pose proof (Z.mod_pos_bound (SHEv map len) 4096 ltac:(img_lia)) as X. split; [img_lia|].
pose proof (Z.div_mod (SHEv map len) 4096 ltac:(img_lia)) as Y. replace (SHEv map len - SHEv map len mod 4096) with (SHEv map len / 4096 * 4096) by img_lia. img_apply Z_mod_mult. }
assert (V10 : getr (ms_regs msE) 10 = Z_to_bv 64 PB).
{ lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
refine (eq_trans (st_ok_ecall_restrict_reg (w_H W) E5 ssM msE 10%bv HS) _);
let e := img_ev (sr_get (ss_regs ssM) 10%bv) in img_change (sr_get (ss_regs ssM) 10%bv) with e end.
rewrite denot_lit_U. f_equal. rewrite U_zev by img_refl. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw. rewrite Q49.
rewrite (zcanon_id (SHAv map + 4095)) by (img_try (unfold M64; clear - USHA; img_lia)). img_change (zcanon 18446744073709547520) with 18446744073709547520.
rewrite land_m4096 by (img_try (clear - USHA; img_lia)). fold PB. img_apply zcanon_id. unfold M64. clear - RPB USHA. img_lia. }
assert (V11 : getr (ms_regs msE) 11 = Z_to_bv 64 (PE - PB)).
{ lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
refine (eq_trans (st_ok_ecall_restrict_reg (w_H W) E5 ssM msE 11%bv HS) _);
let e := img_ev (sr_get (ss_regs ssM) 11%bv) in img_change (sr_get (ss_regs ssM) 11%bv) with e end.
rewrite denot_lit_U. f_equal. rewrite U_zev by img_refl. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw. rewrite Q49, Q55, Z.add_0_r.
rewrite (zcanon_id (SHAv map + 4095)), (zcanon_id (SHEv map len)) by (img_try (unfold M64; clear - USHA USHE; img_lia)). img_change (zcanon 18446744073709547520) with 18446744073709547520.
rewrite !land_m4096 by (img_try (clear - USHA USHE; img_lia)). fold PB. fold PE. rewrite (zcanon_id PB), (zcanon_id PE) by (img_try (unfold M64; clear - RPB RPE USHA USHE; img_lia)). img_apply zcanon_id. unfold M64. clear - RPB RPE USHA USHE LTc. img_lia. }
assert (NAL : (PE - PB) mod 4096 = 0) by (img_try (rewrite Zminus_mod, (proj2 RPE), (proj2 RPB); img_refl)).
assert (ZF : YK0v.zfill (Z_to_bv 64 PB) (Z_to_bv 64 (PE - PB)) (ms_mem msE) = ms_mem msE).
{ img_apply FunctionalExtensionality.functional_extensionality. intros x. unfold YK0v.zfill, YK02.zmem.
rewrite !unsigned_lit_small by (img_try (clear - RPB RPE USHA USHE LTc; img_lia)).
destruct (Z.leb_spec PB (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (PB + (PE - PB))); cbn [andb]; try img_refl.
symmetry. img_apply SH. unfold YF2q.WINS. unfold SHEv in RPE. clear - RPB RPE H H1. img_lia. }
rewrite SHP.
img_apply (SRr_madvise_pg tfxsegs W (ms_regs msE) (Z_to_bv 64 (412876 + D_2c4)) (ms_mem msE) (seg_rom tfxsegs) _ PB (PE - PB) _ Q17 V10 V11 Q12);
[img_try (clear - RPB USHA; img_lia) | img_try (img_exact (proj2 RPB)) | img_try (clear - LTc; img_lia) | img_try (img_exact NAL) | img_try (clear - RPB RPE USHA USHE; img_lia) | img_try (img_apply GATE; clear - RPB RPE LTc; img_lia) |].
rewrite ZF, YA06.madvise_next_wvb.
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
assert (KEPT : Forall (region_kept tfxsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (ms_mem msE))) (ss_mem ssM))
by (img_try (img_apply Forall_forall; intros r _; img_apply region_kept_ext; intros z _; img_refl)) end.
pose proof (st_node_cont (w_H W) E5 _ msE (SLit 0) 0 (412880 + D_2c4) (ms_mem msE) HS eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) KEPT) as HS2.
clear HS KEPT Q17 Q12 V10 V11 ZF SHP. rename HS2 into HS. evalS HS.
img_change (v_addi (Z_to_bv 64 (412876 + D_2c4)) 4) with (Z_to_bv 64 (412880 + D_2c4)).
srr_run_to_sh tfxtbl_rtM_ok HS (0x34240 + D_150). acc2 KW5 K5.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS. evalS HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E5 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR; rewrite HshR;
apply (st_ok_forget 62%nat E5 _ (w_H W) msx [10; 11; 12; 13; 17]%bv) in HS; [| img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl];
evalS HS; cbn [ss_pc] in HS;
refine (JOIN _ _ _ _ _ MQ SH HS) end.
intros k Hk. rewrite ew_havoc_old by zlia. img_apply HE5. img_exact Hk.
- srr_branch_sh tfxtbl_rtM_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr Q49 Q55 USHA USHE GEc; zbranch Hbr;
rewrite ?(zcanon_id (SHEv map len)) in Hbr by (img_try (unfold M64; zlia)); rewrite !land_m4096 in Hbr by zlia; unfold zcanon, M64 in Hbr;
apply Bool.negb_false_iff in Hbr; apply Z.ltb_lt in Hbr; zlia end. }
nt HS. srr_run_to_sh tfxtbl_rtM_ok HS (0x34240 + D_150). acc2 KW5 K5.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS. evalS HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E5 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR; rewrite HshR;
apply (st_ok_forget 62%nat E5 _ (w_H W) msx [10; 11; 12; 13; 17]%bv) in HS; [| img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl];
evalS HS; cbn [ss_pc] in HS;
refine (JOIN _ _ _ _ _ MQ SH HS) end.
intros k Hk. rewrite ew_havoc_old by zlia. img_apply HE5. img_exact Hk. }
clear MQ SH HS KW5 K5 HE5 HE5' HR5 Q32 Q33 Q34 Q35 Q48 Q49 Q50 Q55. (subst E5; cbv beta).
intros E6 regs6 mem6 mat6 HE6 MQ SH HS.
assert (HE6' : forall k, (k < aHAVf)%nat -> ew E6 k = ew E0 k) by (img_try (intros k Hk; img_apply HE6; unfold aHAVf in Hk; zlia)).
pose proof (WSK0_within E6 HE6') as K6. rewrite OWN in K6. pose proof (within_mono _ _ E6 _ WIN_WIN2 K6) as KW6.
assert (HR6 : forall k, (k < 56)%nat -> rho_of E6 k = rho_of E0 k) by (img_try (intros k Hk; unfold rho_of; rewrite (HE6 k Hk); img_refl)).
assert (Q32 : rho_of E6 32%nat = T) by (img_try (rewrite (HR6 32%nat ltac:(zlia)); img_exact R32)).
assert (Q33 : rho_of E6 33%nat = ly_C ly) by (img_try (rewrite (HR6 33%nat ltac:(zlia)); img_exact R33)).
assert (Q34 : rho_of E6 34%nat = map) by (img_try (rewrite (HR6 34%nat ltac:(zlia)); img_exact R34)).
assert (Q35 : rho_of E6 35%nat = len) by (img_try (rewrite (HR6 35%nat ltac:(zlia)); img_exact R35)).
assert (Q46 : rho_of E6 46%nat = j5) by (img_try (rewrite (HR6 46%nat ltac:(zlia)); img_exact R46)).
assert (Q47 : rho_of E6 47%nat = j6) by (img_try (rewrite (HR6 47%nat ltac:(zlia)); img_exact R47)).
srr_run_to_sh tfxtbl_rtM_ok HS (0x64c90 + D_2c4). acc2 KW6 K6.
lazymatch type of HS with st_ok _ _ ?ss _ => let m := img_ev (ss_mem ss) in
lazymatch m with ?r0 :: ?rest => apply (st_ok_drop_regions _ _ _ [r0] rest) in HS; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW6 K6.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ =>
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
pose proof (st_ok_ecall_full_shape (w_H W) E6 ssM msx HS eq_refl) as SHP;
img_apply SRr_ret; split; [img_refl|]; exists (ms_regs msx), (ms_mem msx), mt; rename msx into msE end end.
split. { rewrite SHP at 1. img_refl. }
split. { idtac "A7". rrege HS (17%bv : bv 5) Q17. rewrite Q17. img_refl. }
assert (BV6 : forall (k : nat) v, (k < 56)%nat -> ew E0 k = w64 v -> ew E6 k = w64 v) by (img_try (intros k v Hk Hv; rewrite (HE6 k Hk); img_exact Hv)).
split. { idtac "A0". rrege HS (10%bv : bv 5) Q10. rewrite Q10. cbn [sv_denot]. rewrite (BV6 34%nat map ltac:(img_try (zlia)) EqMAP). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned. img_refl. }
split. { idtac "A1". rrege HS (11%bv : bv 5) Q11. rewrite Q11. cbn [sv_denot]. rewrite (BV6 35%nat len ltac:(img_try (zlia)) EqLEN). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned. img_refl. }
cbv zeta.
assert (PV2 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite (HE6 2%nat ltac:(zlia)), E2; img_refl)).
assert (PV32 : bv_unsigned (ew E6 32) = T) by (img_try (rewrite (HE6 32%nat ltac:(zlia)); img_exact R32)).
assert (PV33 : bv_unsigned (ew E6 33) = ly_C ly) by (img_try (rewrite (HE6 33%nat ltac:(zlia)); img_exact R33)).
assert (PV39 : bv_unsigned (ew E6 39) = qi) by (img_try (rewrite (HE6 39%nat ltac:(zlia)); img_exact R39)).
assert (PV40 : bv_unsigned (ew E6 40) = ql) by (img_try (rewrite (HE6 40%nat ltac:(zlia)); img_exact R40)).
assert (PV41 : bv_unsigned (ew E6 41) = lst) by (img_try (rewrite (HE6 41%nat ltac:(zlia)); img_exact R41)).
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
assert (KEPT : Forall (region_kept tfxsegs E6 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (unfill (w64 map) (w64 len) (ms_mem msE)))) (ss_mem ssM)) end.
{ assert (UM : bv_unsigned (w64 map) = map) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia)).
assert (UL : bv_unsigned (w64 len) = len) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - P4; numconst; zlia)).
img_apply Forall_forall. intros r Hr. img_apply region_kept_ext. intros z Hz. revert Hz.
cbn [ss_mem In] in Hr; repeat (destruct Hr as [<-|Hr];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?PV2, ?PV32, ?PV33, ?PV39, ?PV40, ?PV41;
unfold T, sp0 in *; clear - dK1 dK2 L1 L2 L4 L5 L7 S1 P1 P2 P4 A1 A2 A3 A4 A5 A6 A8 X1 X2 Hown Hdisj UM UL; unfold GDEPTH; numconst; intros Hz;
img_apply mrestrict_unfill_out; rewrite ?UM, ?UL; first [zlia | match goal with |- ?g => idtac "KEPTFAIL" g; match type of Hz with ?t => idtac "HZ" t end end] |]); destruct Hr. }
pose proof (st_node_cont (w_H W) E6 _ msE (SLit 0) 0 (0x64c98 + D_2c4) (unfill (w64 map) (w64 len) (ms_mem msE)) HS eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) KEPT) as HS2.
clear HS KEPT. rename HS2 into HS. evalS HS. img_change (Z_to_bv 64 0) with (w64 0) in HS. img_change (Z_to_bv 64 (0x64c98 + D_2c4)) with (w64 (0x64c98 + D_2c4)) in HS.
assert (MQ7 : MEQP WIN3 (unfill (w64 map) (w64 len) (ms_mem msE))).
{ intros x Hx. unfold WIN3 in Hx. rewrite unfill_out by (img_try (unfold w64; rewrite !unsigned_lit_small by (clear - P1 P2 P4; numconst; zlia); unfold WINM in Hx; clear - Hx; zlia)).
img_apply MQ. unfold WIN2. clear - Hx. tauto. }
assert (SH7 : SHD (unfill (w64 map) (w64 len) (ms_mem msE))).
{ intros x Hx. rewrite unfill_out by (img_try (unfold w64; rewrite !unsigned_lit_small by (clear - P1 P2 P4; numconst; zlia); unfold WINS in Hx; clear - Hx P1 dSH1 dSH2; numconst; zlia)).
img_exact (SH x Hx). }
clear MQ SH. rename MQ7 into MQ. rename SH7 into SH.
pose proof (within_mono _ _ E6 _ (fun a Ha => WIN2_WIN3 a (WIN_WIN2 a Ha)) K6) as KW7.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW7 K6.
eapply (SRr_ret_at tfxsegs tfxtbl_rtM tfxtbl_rtM_ok Hwx W E6); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite ?wvb_collapse. split; [img_refl|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx), mat'; rename msx into msR end.
assert (Er6 : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E6 k = getr regs0 r).
{ intros k r Hk. rewrite (HE6 k) by (img_try (pose proof (u5_range r); zlia)). img_exact (Er k r Hk). }
split. { idtac "PCv". rreg HS (1%bv : bv 5) Q1. rewrite Q1. cbn [sv_denot]. rewrite (BV6 51%nat vra ltac:(img_try (zlia)) EqRA). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
unfold YK0s.ret_ok, w64 in Hra. rewrite Hra. img_refl. }
split. { idtac "SREGS". intros r Hr; cbn [YF2q.SREGS In] in Hr.
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with |- getr _ ?r = getr regs0 ?r =>
let RR := fresh "RR" in rreg HS r RR; rewrite RR; let k := img_ev (Z.to_nat (bv_unsigned r)) in
first [ img_exact (Er6 k r eq_refl) | cbn [sv_denot]; rewrite (Er6 k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned | rewrite Htp; img_refl ] end. }
split. { idtac "F2". rreg HS (2%bv : bv 5) Q2; rewrite Q2; first [ img_exact (Er6 2%nat 2%bv eq_refl) | cbn [sv_denot]; rewrite (Er6 2%nat 2%bv eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ]. }
split. { idtac "F8". rreg HS (8%bv : bv 5) Q8; rewrite Q8; cbn [sv_denot]; rewrite (BV6 52%nat vs0 ltac:(img_try (zlia)) EqS0); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl. }
split. { idtac "F9". rreg HS (9%bv : bv 5) Q9; rewrite Q9; cbn [sv_denot]; rewrite (BV6 53%nat vs1 ltac:(img_try (zlia)) EqS1); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl. }
split. { idtac "F18". rreg HS (18%bv : bv 5) Q18; rewrite Q18; cbn [sv_denot]; rewrite (BV6 54%nat vs2 ltac:(img_try (zlia)) EqS2); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl. }
split. { img_exact MQ. }
split. { img_exact SH. }
split. { idtac "PRES". intros a Ha.
eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV2; clear - Ha; unfold GDEPTH in *; zlia) | img_try (off_by ltac:(clear - Ha S1 L7 Usp; unfold GDEPTH in *; numconst; unfold KSTACK in *; zlia)) ]. }
split. { idtac "PRES2". intros a [Ha|Ha].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 5 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV39; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha A1 A2 A3 A5 A6; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 7 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV32; unfold T in *; clear - Ha; numconst; zlia) | img_try (off_by ltac:(unfold T in *; clear - Ha L1 L2; numconst; zlia)) ]. }
cbv zeta.
split. { idtac "MUT". img_apply (proj2 (val_mem4_bytes _ _ _)). img_change (YP0g.le_byte 0 4 0) with 0. img_change (YP0g.le_byte 0 4 1) with 0. img_change (YP0g.le_byte 0 4 2) with 0. img_change (YP0g.le_byte 0 4 3) with 0.
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ _) =>
assert (VZ : forall a, A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 680 + 4 -> mbyte tfxsegs (mrestrict (w_H W) (ms_mem msR)) a = Some (Z_to_bv 8 0))
by (img_try (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msR 1 _ 0 _ _ a HS); [img_refl | img_refl | cbn [base_val YQ0b.r_base]; unfold A_ALLOCATOR in Ha |- *; clear - Ha; zlia])) end.
repeat split; img_apply VZ; unfold A_ALLOCATOR; zlia. }
split. { idtac "NS". memvo HS 2%nat (A_ALLOCATOR + 120); [img_refl | img_try (cbn [sv_denot]; rewrite (BV6 37%nat n ltac:(zlia) EqN); unfold w64; rewrite ?Zbv_add_unsigned; f_equal; rewrite unsigned_lit_small by (clear - A1 A2; zlia); zlia) | img_try (clear - A1 A2; zlia)]. }
split. { idtac "SRT". memvo HS 2%nat (A_ALLOCATOR + 128); [img_refl | img_refl | img_try (zlia)]. }
split. { idtac "JW1". jword HS 3%nat (A_ALLOCATOR + 144). }
split. { jword HS 3%nat (A_ALLOCATOR + 152). }
split. { jword HS 4%nat (A_ALLOCATOR + 704). }
split. { jword HS 4%nat (A_ALLOCATOR + 712). }
split. { idtac "QI". destruct Hown as [OW1 OW2]. rewrite OW2. memvo HS 5%nat 0; [img_try (cbn [base_val YQ0b.r_base]; rewrite PV39; zlia) | img_try (cbn [sv_denot]; rewrite (BV6 34%nat map ltac:(zlia) EqMAP); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl) | img_try (clear - P1 P2 P4; numconst; zlia)]. }
idtac "OWNT". intros X. rewrite OWN in X. discriminate X.
Qed.
Lemma segGD_t_hi : own = true -> small = true -> kLowMemEnd <= map -> SRr tfxsegs W cfg0 at_MUN.
Proof.
intros OWN SM ZARM. open_FH. pose proof Hwx_tfa as Hwx. pose proof SEED as HS. pose proof LYB as LB. pose proof derived_ranges as DR.
rewrite OWN, SM in HS. rewrite SM in Hmap. rewrite OWN in Hown, Hql, Hlsth.
destruct Hsp as [S1 S2]. destruct Hregs as (R10 & R11 & R12 & R1 & R8 & R9 & R18).
destruct Hmap as (P1 & P2 & P3 & P4 & P5 & P6). destruct Harr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). destruct Hlst as (X1 & X2 & X3).
pose proof DR as (_ & _ & _ & _ & dK1 & dK2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & dSH1 & dSH2 & dSH3 & dL8 & dM8 & dCNT & dJ1 & dJ2 & dJ3 & dJ4 & dJ5 & dJ6 & dV1 & dV2 & dV3 & dV4).
pose proof LB as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
evalS HS.
pose proof (MEQP_0 WIN) as MQ.
assert (HE0 : forall k, (k < aHAVf)%nat -> ew E0 k = ew E0 k) by (img_try (intros; img_refl)).
pose proof (WSK0_within E0 HE0) as K0. rewrite OWN in K0.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (R32 : rho_of E0 32%nat = T) by (img_try (unfold rho_of; rewrite EqT; unfold w64; img_apply unsigned_lit_small; clear - L1 L2; numconst; zlia)).
assert (R33 : rho_of E0 33%nat = ly_C ly) by (img_try (unfold rho_of; rewrite EqC; unfold w64; img_apply unsigned_lit_small; clear - L4 L5; numconst; zlia)).
assert (R34 : rho_of E0 34%nat = map) by (img_try (unfold rho_of; rewrite EqMAP; unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia)).
assert (R35 : rho_of E0 35%nat = len) by (img_try (unfold rho_of; rewrite EqLEN; unfold w64; img_apply unsigned_lit_small; clear - P4; numconst; zlia)).
assert (R36 : rho_of E0 36%nat = idx) by (img_try (unfold rho_of; rewrite EqIDX; unfold w64; img_apply unsigned_lit_small; clear - A1 A2; zlia)).
assert (R37 : rho_of E0 37%nat = n) by (img_try (unfold rho_of; rewrite EqN; unfold w64; img_apply unsigned_lit_small; clear - A1 A2; zlia)).
assert (R38 : rho_of E0 38%nat = q) by (img_try (unfold rho_of; rewrite EqQ; unfold w64; img_apply unsigned_lit_small; clear - A5 A6; numconst; zlia)).
assert (R39 : rho_of E0 39%nat = qi) by (img_try (unfold rho_of; rewrite EqQI; unfold w64; img_apply unsigned_lit_small; clear - A1 A2 A3 A5 A6; numconst; zlia)).
assert (R40 : rho_of E0 40%nat = ql) by (img_try (unfold rho_of; rewrite EqQL; unfold w64; img_apply unsigned_lit_small; clear - A1 A2 A4 A5 A6; numconst; zlia)).
assert (R41 : rho_of E0 41%nat = lst) by (img_try (unfold rho_of; rewrite EqLAST; unfold w64; img_apply unsigned_lit_small; clear - X1 X2; numconst; zlia)).
assert (R42 : rho_of E0 42%nat = j1) by (img_try (unfold rho_of; rewrite EqJ1; unfold w64; img_apply unsigned_lit_small; img_exact dJ1)).
assert (R43 : rho_of E0 43%nat = j2) by (img_try (unfold rho_of; rewrite EqJ2; unfold w64; img_apply unsigned_lit_small; img_exact dJ2)).
assert (R44 : rho_of E0 44%nat = j3) by (img_try (unfold rho_of; rewrite EqJ3; unfold w64; img_apply unsigned_lit_small; img_exact dJ3)).
assert (R45 : rho_of E0 45%nat = j4) by (img_try (unfold rho_of; rewrite EqJ4; unfold w64; img_apply unsigned_lit_small; img_exact dJ4)).
assert (R46 : rho_of E0 46%nat = j5) by (img_try (unfold rho_of; rewrite EqJ5; unfold w64; img_apply unsigned_lit_small; img_exact dJ5)).
assert (R47 : rho_of E0 47%nat = j6) by (img_try (unfold rho_of; rewrite EqJ6; unfold w64; img_apply unsigned_lit_small; img_exact dJ6)).
assert (R48 : rho_of E0 48%nat = SHADOW_OFF) by (img_try (unfold rho_of; rewrite EqSHB; img_refl)).
assert (R49 : rho_of E0 49%nat = SHAv map) by (img_try (unfold rho_of; rewrite EqSHA; unfold w64; img_apply unsigned_lit_small; clear - dSH1 dSH3; zlia)).
assert (R50 : rho_of E0 50%nat = CNTv len) by (img_try (unfold rho_of; rewrite EqCNT; unfold w64; img_apply unsigned_lit_small; clear - dCNT; zlia)).
assert (R55 : rho_of E0 55%nat = SHEv map len) by (img_try (unfold rho_of; rewrite EqSHE; unfold w64; img_apply unsigned_lit_small; unfold SHEv; clear - dSH1 dSH2 dCNT; zlia)).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite E2; img_refl)).
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 39%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R36, ?R38, ?R39, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id idx) by (img_try (clear - A1 A2; unfold M64; zlia)); rewrite !Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 3) with 8;
clear - A1 A2 A3 A5 A6; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0.
srr_branch_sh tfxtbl_rtM_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R36 R37 A1 A2; zdec Hbr end. } nt HS.
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0.
apply (st_ok_pin_regU _ _ _ 15%bv (SOff 39%nat 8)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R37, ?R38, ?R39, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id n) by (img_try (clear - A1 A2; unfold M64; zlia)); rewrite !Z.shiftl_mul_pow2 by zlia; img_change (2 ^ 3) with 8;
destruct Hown as [OW1 OW2]; clear - A1 A2 A3 A5 A6 OW1; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x34218 + D_150). meq_acc K0.
qw_split1 HS 2%nat.
srr_run_to_sh tfxtbl_rtM_ok HS (0x3421c + D_150). meq_acc K0.
qw_join0 HS 2%nat.
assert (ZHI : kHighMemBeg <= map) by (img_try (clear - ZARM P1 P4; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kLowMemEnd in *; img_lia)).
apply (st_ok_add_atom tfxsegs E0 _ _ 34%nat (mkAF kHighMemBeg (CEIL_MAX - 8192) 12)) in HS.
2:{ pose proof R34 as RR. unfold rho_of in RR. split; [|img_try (split)]; cbn [af_lo af_hi af_al2];
[ img_try (rewrite RR; clear - ZHI P2 P4; ceil; unfold ASAN_CEIL in *; img_lia) | img_try (rewrite RR; img_change (2 ^ 12) with 4096; img_exact P3) | img_lia ]. }
evalS HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x54568 + D_2c4). meq_acc K0.
srr_branch_sh tfxtbl_rtM_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr R34 R35 P1 P2 P4 ZHI; zdec Hbr end. } nt HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x54594 + D_2c4). meq_acc K0.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 49%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R34, ?R48, ?R49, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id map) by (img_try (clear - P1 P2 P4; unfold M64; numconst; zlia)); rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold SHAv in *; clear - P1 P2 P4 dSH1 dSH3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff 50%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?R34, ?R35, ?R50, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold CNTv in *; clear - P1 P2 P4 dL8 dM8 dCNT; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtM_ok HS. meq_acc K0. dbg HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msM end.
assert (SHPRES : forall a, SHAv map <= a < SHAv map + CNTv len -> apresent (w_H W) (ms_mem msM) a).
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (img_try (clear - Ha dSH1 dSH2; zlia)).
img_apply (apresent_same (w_H W) mem0).
- img_apply MQ. rewrite unsigned_lit_small by img_exact Ra. intros Hx. img_exact (WIN_not_WINS a Hx Ha).
- img_apply Hsh_pres. img_exact Ha. }
rreg HS (11%bv : bv 5) RA1m.
eapply (memset_stretch_nw W 56%nat E0 _ _ _ (SHAv map) (CNTv len) (0x34234 + D_150));
[ img_try (img_exact HS) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)
| img_try (rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite EqSHA; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl)
| img_try (rreg HS (12%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite EqCNT; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; img_refl)
| img_try (rreg HS (1%bv : bv 5) R; rewrite R; img_refl)
| img_try (clear - dCNT; zlia) | img_try (clear - dSH1; numconst; zlia) | img_try (clear - dSH1 dSH2; numconst; zlia) | img_refl | img_try (zlia)
| img_try (img_exact SHPRES)
| img_try (intros r Hr) | img_try (intros r a Hr) | ].
1-2: cbn [ss_mem In] in Hr; unfold rho_of in R32, R33, R34, R39, R40, R41; repeat (destruct Hr as [<-|Hr];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?BV2, ?R32, ?R33, ?R34, ?R39, ?R40, ?R41;
unfold T, sp0 in *; clear - dK1 dK2 L1 L2 L4 L5 P1 P2 P4 A1 A2 A3 A4 A5 A6 X1 X2 dSH1 dSH2 dSH3; unfold GDEPTH; numconst; first [zlia | match goal with |- ?g => idtac "REGFAIL" g end] |]); destruct Hr.
intros regs5 mem5 mat5 HS5 H10c Hfr5 Hpr5 Hfill. clear HS. rename HS5 into HS. evalS HS.
lazymatch type of HS with st_ok _ ?E _ _ => set (E5 := E) in HS end.
assert (HE5 : forall k, (k < 56)%nat -> ew E5 k = ew E0 k) by (img_try (intros k Hk; (subst E5; cbv beta); rewrite ew_havoc_old by zlia; img_refl)).
assert (HE5' : forall k, (k < aHAVf)%nat -> ew E5 k = ew E0 k) by (img_try (intros k Hk; img_apply HE5; unfold aHAVf in Hk; zlia)).
pose proof (WSK0_within E5 HE5') as K5. rewrite OWN in K5.
assert (MQ5 : MEQP WIN2 mem5).
{ intros x Hx. rewrite (Hfr5 x) by (img_try (intros Hs; img_apply Hx; img_apply WINS_WIN2; img_exact Hs)). img_apply MQ. intros Hw; img_apply Hx; img_exact (WIN_WIN2 _ Hw). }
assert (SH5 : SHD mem5).
{ intros x Hx. rewrite (Hfill x Hx), RA1m. img_refl. }
pose proof (within_mono _ _ E5 _ WIN_WIN2 K5) as KW5.
clear MQ Hfr5 Hfill SHPRES. rename MQ5 into MQ. rename SH5 into SH.
assert (HR5 : forall k, (k < 56)%nat -> rho_of E5 k = rho_of E0 k) by (img_try (intros k Hk; unfold rho_of; rewrite (HE5 k Hk); img_refl)).
assert (Q32 : rho_of E5 32%nat = T) by (img_try (rewrite (HR5 32%nat ltac:(zlia)); img_exact R32)).
assert (Q33 : rho_of E5 33%nat = ly_C ly) by (img_try (rewrite (HR5 33%nat ltac:(zlia)); img_exact R33)).
assert (Q34 : rho_of E5 34%nat = map) by (img_try (rewrite (HR5 34%nat ltac:(zlia)); img_exact R34)).
assert (Q35 : rho_of E5 35%nat = len) by (img_try (rewrite (HR5 35%nat ltac:(zlia)); img_exact R35)).
assert (Q48 : rho_of E5 48%nat = SHADOW_OFF) by (img_try (rewrite (HR5 48%nat ltac:(zlia)); img_exact R48)).
assert (Q49 : rho_of E5 49%nat = SHAv map) by (img_try (rewrite (HR5 49%nat ltac:(zlia)); img_exact R49)).
assert (Q50 : rho_of E5 50%nat = CNTv len) by (img_try (rewrite (HR5 50%nat ltac:(zlia)); img_exact R50)).
assert (Q55 : rho_of E5 55%nat = SHEv map len) by (img_try (rewrite (HR5 55%nat ltac:(zlia)); img_exact R55)).
srr_run_to_sh tfxtbl_rtM_ok HS (0x52e2c + D_2c4). acc2 KW5 K5.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 49%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Q34, ?Q48, ?Q49, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite (zcanon_id map) by (img_try (clear - P1 P2 P4; unfold M64; numconst; zlia)); rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold SHAv in *; clear - P1 P2 P4 dSH1 dSH3; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x52eb0 + D_2c4). acc2 KW5 K5.
srr_branch_sh tfxtbl_rtM_ok HS. { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr Q34 Q35 P1 P2 P4 ZHI; zdec Hbr end. } nt HS.
srr_run_to_sh tfxtbl_rtM_ok HS (0x52e38 + D_2c4). acc2 KW5 K5.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff 55%nat 0)) in HS;
[ | intros X; discriminate
| pin_prep; cbn [zev zalu_raw]; unfold zalu_raw; rewrite ?Q34, ?Q35, ?Q48, ?Q55, ?Z.add_0_r; land_lits;
repeat match goal with |- context [Z.land (zcanon ?k) 63] => let cc := img_ev (Z.land (zcanon k) 63) in img_change (Z.land (zcanon k) 63) with cc end;
rewrite !Z.shiftr_div_pow2 by zlia; img_change (2 ^ 3) with 8;
unfold SHEv, SHAv, CNTv in *; clear - P1 P2 P4 dSH1 dSH2 dSH3 dL8 dM8 dCNT; numconst; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW5 K5.
eassert (JOIN : forall (E' : env) regs6 mem6 mat6, (forall k, (k < 56)%nat -> ew E' k = ew E0 k) -> MEQP WIN2 mem6 ->
SHD mem6 ->
st_ok tfxsegs E' _ (restrict (w_H W) (mkst regs6 (Z_to_bv 64 (0x34240 + D_150)) mem6 (seg_rom tfxsegs))) ->
SRr tfxsegs W (mkCfg (mkst regs6 (Z_to_bv 64 (0x34240 + D_150)) mem6 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat6 md0)) at_MUN).
2: { assert (USHA : 0 <= SHAv map + 4095 < 2 ^ 64) by (img_try (clear - dSH1 dSH3; zlia)). assert (USHE : 0 <= SHEv map len < 2 ^ 64) by (img_try (unfold SHEv; clear - dSH1 dSH2 dCNT; zlia)).
destruct (Z_lt_le_dec (SHAv map + 4095 - (SHAv map + 4095) mod 4096) (SHEv map len - SHEv map len mod 4096)) as [LTc|GEc].
- srr_branch_sh tfxtbl_rtM_ok HS.
{ exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = true |- _ => clear - Hbr Q49 Q55 USHA USHE LTc; zbranch Hbr;
rewrite ?(zcanon_id (SHEv map len)) in Hbr by (img_try (unfold M64; zlia)); rewrite !land_m4096 in Hbr by zlia; unfold zcanon, M64 in Hbr;
apply Bool.negb_true_iff in Hbr; apply Z.ltb_ge in Hbr; zlia end. }
nt HS.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW5 K5.
set (PB := SHAv map + 4095 - (SHAv map + 4095) mod 4096) in *. set (PE := SHEv map len - SHEv map len mod 4096) in *.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ =>
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
pose proof (st_ok_ecall_full_shape (w_H W) E5 ssM msx HS eq_refl) as SHP; cbn [ss_pc] in SHP; rename msx into msE end end.
rrege HS (17%bv : bv 5) Q17. rrege HS (12%bv : bv 5) Q12.
assert (RPB : SHAv map <= PB <= SHAv map + 4095 /\ PB mod 4096 = 0).
{ (subst PB; cbv beta). clear. pose proof (Z.mod_pos_bound (SHAv map + 4095) 4096 ltac:(img_lia)) as X. split; [img_lia|].
pose proof (Z.div_mod (SHAv map + 4095) 4096 ltac:(img_lia)) as Y. replace (SHAv map + 4095 - (SHAv map + 4095) mod 4096) with ((SHAv map + 4095) / 4096 * 4096) by img_lia. img_apply Z_mod_mult. }
assert (RPE : 0 <= PE <= SHEv map len /\ PE mod 4096 = 0).
{ (subst PE; cbv beta). clear - USHE. pose proof (Z.mod_pos_bound (SHEv map len) 4096 ltac:(img_lia)) as X. split; [img_lia|].
pose proof (Z.div_mod (SHEv map len) 4096 ltac:(img_lia)) as Y. replace (SHEv map len - SHEv map len mod 4096) with (SHEv map len / 4096 * 4096) by img_lia. img_apply Z_mod_mult. }
assert (V10 : getr (ms_regs msE) 10 = Z_to_bv 64 PB).
{ lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
refine (eq_trans (st_ok_ecall_restrict_reg (w_H W) E5 ssM msE 10%bv HS) _);
let e := img_ev (sr_get (ss_regs ssM) 10%bv) in img_change (sr_get (ss_regs ssM) 10%bv) with e end.
rewrite denot_lit_U. f_equal. rewrite U_zev by img_refl. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw. rewrite Q49.
rewrite (zcanon_id (SHAv map + 4095)) by (img_try (unfold M64; clear - USHA; img_lia)). img_change (zcanon 18446744073709547520) with 18446744073709547520.
rewrite land_m4096 by (img_try (clear - USHA; img_lia)). fold PB. img_apply zcanon_id. unfold M64. clear - RPB USHA. img_lia. }
assert (V11 : getr (ms_regs msE) 11 = Z_to_bv 64 (PE - PB)).
{ lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
refine (eq_trans (st_ok_ecall_restrict_reg (w_H W) E5 ssM msE 11%bv HS) _);
let e := img_ev (sr_get (ss_regs ssM) 11%bv) in img_change (sr_get (ss_regs ssM) 11%bv) with e end.
rewrite denot_lit_U. f_equal. rewrite U_zev by img_refl. cbn [zev zalu_raw zmd_raw]. unfold zalu_raw. rewrite Q49, Q55, Z.add_0_r.
rewrite (zcanon_id (SHAv map + 4095)), (zcanon_id (SHEv map len)) by (img_try (unfold M64; clear - USHA USHE; img_lia)). img_change (zcanon 18446744073709547520) with 18446744073709547520.
rewrite !land_m4096 by (img_try (clear - USHA USHE; img_lia)). fold PB. fold PE. rewrite (zcanon_id PB), (zcanon_id PE) by (img_try (unfold M64; clear - RPB RPE USHA USHE; img_lia)). img_apply zcanon_id. unfold M64. clear - RPB RPE USHA USHE LTc. img_lia. }
assert (NAL : (PE - PB) mod 4096 = 0) by (img_try (rewrite Zminus_mod, (proj2 RPE), (proj2 RPB); img_refl)).
assert (ZF : YK0v.zfill (Z_to_bv 64 PB) (Z_to_bv 64 (PE - PB)) (ms_mem msE) = ms_mem msE).
{ img_apply FunctionalExtensionality.functional_extensionality. intros x. unfold YK0v.zfill, YK02.zmem.
rewrite !unsigned_lit_small by (img_try (clear - RPB RPE USHA USHE LTc; img_lia)).
destruct (Z.leb_spec PB (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (PB + (PE - PB))); cbn [andb]; try img_refl.
symmetry. img_apply SH. unfold YF2q.WINS. unfold SHEv in RPE. clear - RPB RPE H H1. img_lia. }
rewrite SHP.
img_apply (SRr_madvise_pg tfxsegs W (ms_regs msE) (Z_to_bv 64 (412876 + D_2c4)) (ms_mem msE) (seg_rom tfxsegs) _ PB (PE - PB) _ Q17 V10 V11 Q12);
[img_try (clear - RPB USHA; img_lia) | img_try (img_exact (proj2 RPB)) | img_try (clear - LTc; img_lia) | img_try (img_exact NAL) | img_try (clear - RPB RPE USHA USHE; img_lia) | img_try (img_apply GATE; clear - RPB RPE LTc; img_lia) |].
rewrite ZF, YA06.madvise_next_wvb.
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
assert (KEPT : Forall (region_kept tfxsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (ms_mem msE))) (ss_mem ssM))
by (img_try (img_apply Forall_forall; intros r _; img_apply region_kept_ext; intros z _; img_refl)) end.
pose proof (st_node_cont (w_H W) E5 _ msE (SLit 0) 0 (412880 + D_2c4) (ms_mem msE) HS eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) KEPT) as HS2.
clear HS KEPT Q17 Q12 V10 V11 ZF SHP. rename HS2 into HS. evalS HS.
img_change (v_addi (Z_to_bv 64 (412876 + D_2c4)) 4) with (Z_to_bv 64 (412880 + D_2c4)).
srr_run_to_sh tfxtbl_rtM_ok HS (0x34240 + D_150). acc2 KW5 K5.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS. evalS HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E5 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR; rewrite HshR;
apply (st_ok_forget 62%nat E5 _ (w_H W) msx [10; 11; 12; 13; 17]%bv) in HS; [| img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl];
evalS HS; cbn [ss_pc] in HS;
refine (JOIN _ _ _ _ _ MQ SH HS) end.
intros k Hk. rewrite ew_havoc_old by zlia. img_apply HE5. img_exact Hk.
- srr_branch_sh tfxtbl_rtM_ok HS.
2: { exfalso. lazymatch goal with Hbr : branch_taken _ _ _ = false |- _ => clear - Hbr Q49 Q55 USHA USHE GEc; zbranch Hbr;
rewrite ?(zcanon_id (SHEv map len)) in Hbr by (img_try (unfold M64; zlia)); rewrite !land_m4096 in Hbr by zlia; unfold zcanon, M64 in Hbr;
apply Bool.negb_false_iff in Hbr; apply Z.ltb_lt in Hbr; zlia end. }
nt HS. srr_run_to_sh tfxtbl_rtM_ok HS (0x34240 + D_150). acc2 KW5 K5.
apply (YQ04.st_ok_prune tfxsegs _ _ _ [] []) in HS. evalS HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E5 _ _ HS eq_refl) as HshR; cbn [ss_pc] in HshR; rewrite HshR;
apply (st_ok_forget 62%nat E5 _ (w_H W) msx [10; 11; 12; 13; 17]%bv) in HS; [| img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl | img_try ((img_case; vm_compute); img_refl) | img_refl | img_refl];
evalS HS; cbn [ss_pc] in HS;
refine (JOIN _ _ _ _ _ MQ SH HS) end.
intros k Hk. rewrite ew_havoc_old by zlia. img_apply HE5. img_exact Hk. }
clear MQ SH HS KW5 K5 HE5 HE5' HR5 Q32 Q33 Q34 Q35 Q48 Q49 Q50 Q55. (subst E5; cbv beta).
intros E6 regs6 mem6 mat6 HE6 MQ SH HS.
assert (HE6' : forall k, (k < aHAVf)%nat -> ew E6 k = ew E0 k) by (img_try (intros k Hk; img_apply HE6; unfold aHAVf in Hk; zlia)).
pose proof (WSK0_within E6 HE6') as K6. rewrite OWN in K6. pose proof (within_mono _ _ E6 _ WIN_WIN2 K6) as KW6.
assert (HR6 : forall k, (k < 56)%nat -> rho_of E6 k = rho_of E0 k) by (img_try (intros k Hk; unfold rho_of; rewrite (HE6 k Hk); img_refl)).
assert (Q32 : rho_of E6 32%nat = T) by (img_try (rewrite (HR6 32%nat ltac:(zlia)); img_exact R32)).
assert (Q33 : rho_of E6 33%nat = ly_C ly) by (img_try (rewrite (HR6 33%nat ltac:(zlia)); img_exact R33)).
assert (Q34 : rho_of E6 34%nat = map) by (img_try (rewrite (HR6 34%nat ltac:(zlia)); img_exact R34)).
assert (Q35 : rho_of E6 35%nat = len) by (img_try (rewrite (HR6 35%nat ltac:(zlia)); img_exact R35)).
assert (Q46 : rho_of E6 46%nat = j5) by (img_try (rewrite (HR6 46%nat ltac:(zlia)); img_exact R46)).
assert (Q47 : rho_of E6 47%nat = j6) by (img_try (rewrite (HR6 47%nat ltac:(zlia)); img_exact R47)).
srr_run_to_sh tfxtbl_rtM_ok HS (0x64c90 + D_2c4). acc2 KW6 K6.
lazymatch type of HS with st_ok _ _ ?ss _ => let m := img_ev (ss_mem ss) in
lazymatch m with ?r0 :: ?rest => apply (st_ok_drop_regions _ _ _ [r0] rest) in HS; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW6 K6.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ =>
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
pose proof (st_ok_ecall_full_shape (w_H W) E6 ssM msx HS eq_refl) as SHP;
img_apply SRr_ret; split; [img_refl|]; exists (ms_regs msx), (ms_mem msx), mt; rename msx into msE end end.
split. { rewrite SHP at 1. img_refl. }
split. { idtac "A7". rrege HS (17%bv : bv 5) Q17. rewrite Q17. img_refl. }
assert (BV6 : forall (k : nat) v, (k < 56)%nat -> ew E0 k = w64 v -> ew E6 k = w64 v) by (img_try (intros k v Hk Hv; rewrite (HE6 k Hk); img_exact Hv)).
split. { idtac "A0". rrege HS (10%bv : bv 5) Q10. rewrite Q10. cbn [sv_denot]. rewrite (BV6 34%nat map ltac:(img_try (zlia)) EqMAP). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned. img_refl. }
split. { idtac "A1". rrege HS (11%bv : bv 5) Q11. rewrite Q11. cbn [sv_denot]. rewrite (BV6 35%nat len ltac:(img_try (zlia)) EqLEN). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned. img_refl. }
cbv zeta.
assert (PV2 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite (HE6 2%nat ltac:(zlia)), E2; img_refl)).
assert (PV32 : bv_unsigned (ew E6 32) = T) by (img_try (rewrite (HE6 32%nat ltac:(zlia)); img_exact R32)).
assert (PV33 : bv_unsigned (ew E6 33) = ly_C ly) by (img_try (rewrite (HE6 33%nat ltac:(zlia)); img_exact R33)).
assert (PV39 : bv_unsigned (ew E6 39) = qi) by (img_try (rewrite (HE6 39%nat ltac:(zlia)); img_exact R39)).
assert (PV40 : bv_unsigned (ew E6 40) = ql) by (img_try (rewrite (HE6 40%nat ltac:(zlia)); img_exact R40)).
assert (PV41 : bv_unsigned (ew E6 41) = lst) by (img_try (rewrite (HE6 41%nat ltac:(zlia)); img_exact R41)).
lazymatch type of HS with st_ok_ecall _ _ ?ssM (restrict _ _) =>
assert (KEPT : Forall (region_kept tfxsegs E6 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (unfill (w64 map) (w64 len) (ms_mem msE)))) (ss_mem ssM)) end.
{ assert (UM : bv_unsigned (w64 map) = map) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P4; numconst; zlia)).
assert (UL : bv_unsigned (w64 len) = len) by (img_try (unfold w64; img_apply unsigned_lit_small; clear - P4; numconst; zlia)).
img_apply Forall_forall. intros r Hr. img_apply region_kept_ext. intros z Hz. revert Hz.
cbn [ss_mem In] in Hr; repeat (destruct Hr as [<-|Hr];
[ cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite ?PV2, ?PV32, ?PV33, ?PV39, ?PV40, ?PV41;
unfold T, sp0 in *; clear - dK1 dK2 L1 L2 L4 L5 L7 S1 P1 P2 P4 A1 A2 A3 A4 A5 A6 A8 X1 X2 Hown Hdisj UM UL; unfold GDEPTH; numconst; intros Hz;
img_apply mrestrict_unfill_out; rewrite ?UM, ?UL; first [zlia | match goal with |- ?g => idtac "KEPTFAIL" g; match type of Hz with ?t => idtac "HZ" t end end] |]); destruct Hr. }
pose proof (st_node_cont (w_H W) E6 _ msE (SLit 0) 0 (0x64c98 + D_2c4) (unfill (w64 map) (w64 len) (ms_mem msE)) HS eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) KEPT) as HS2.
clear HS KEPT. rename HS2 into HS. evalS HS. img_change (Z_to_bv 64 0) with (w64 0) in HS. img_change (Z_to_bv 64 (0x64c98 + D_2c4)) with (w64 (0x64c98 + D_2c4)) in HS.
assert (MQ7 : MEQP WIN3 (unfill (w64 map) (w64 len) (ms_mem msE))).
{ intros x Hx. unfold WIN3 in Hx. rewrite unfill_out by (img_try (unfold w64; rewrite !unsigned_lit_small by (clear - P1 P2 P4; numconst; zlia); unfold WINM in Hx; clear - Hx; zlia)).
img_apply MQ. unfold WIN2. clear - Hx. tauto. }
assert (SH7 : SHD (unfill (w64 map) (w64 len) (ms_mem msE))).
{ intros x Hx. rewrite unfill_out by (img_try (unfold w64; rewrite !unsigned_lit_small by (clear - P1 P2 P4; numconst; zlia); unfold WINS in Hx; clear - Hx P1 dSH1 dSH2; numconst; zlia)).
img_exact (SH x Hx). }
clear MQ SH. rename MQ7 into MQ. rename SH7 into SH.
pose proof (within_mono _ _ E6 _ (fun a Ha => WIN2_WIN3 a (WIN_WIN2 a Ha)) K6) as KW7.
srr_run_sh tfxtbl_rtM_ok HS. acc2 KW7 K6.
eapply (SRr_ret_at tfxsegs tfxtbl_rtM tfxtbl_rtM_ok Hwx W E6); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite ?wvb_collapse. split; [img_refl|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx), mat'; rename msx into msR end.
assert (Er6 : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E6 k = getr regs0 r).
{ intros k r Hk. rewrite (HE6 k) by (img_try (pose proof (u5_range r); zlia)). img_exact (Er k r Hk). }
split. { idtac "PCv". rreg HS (1%bv : bv 5) Q1. rewrite Q1. cbn [sv_denot]. rewrite (BV6 51%nat vra ltac:(img_try (zlia)) EqRA). unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
unfold YK0s.ret_ok, w64 in Hra. rewrite Hra. img_refl. }
split. { idtac "SREGS". intros r Hr; cbn [YF2q.SREGS In] in Hr.
repeat (destruct Hr as [<-|Hr]; [| ]); try contradiction;
lazymatch goal with |- getr _ ?r = getr regs0 ?r =>
let RR := fresh "RR" in rreg HS r RR; rewrite RR; let k := img_ev (Z.to_nat (bv_unsigned r)) in
first [ img_exact (Er6 k r eq_refl) | cbn [sv_denot]; rewrite (Er6 k r eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned | rewrite Htp; img_refl ] end. }
split. { idtac "F2". rreg HS (2%bv : bv 5) Q2; rewrite Q2; first [ img_exact (Er6 2%nat 2%bv eq_refl) | cbn [sv_denot]; rewrite (Er6 2%nat 2%bv eq_refl), ?Z.add_0_r; img_apply Z_to_bv_bv_unsigned ]. }
split. { idtac "F8". rreg HS (8%bv : bv 5) Q8; rewrite Q8; cbn [sv_denot]; rewrite (BV6 52%nat vs0 ltac:(img_try (zlia)) EqS0); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl. }
split. { idtac "F9". rreg HS (9%bv : bv 5) Q9; rewrite Q9; cbn [sv_denot]; rewrite (BV6 53%nat vs1 ltac:(img_try (zlia)) EqS1); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl. }
split. { idtac "F18". rreg HS (18%bv : bv 5) Q18; rewrite Q18; cbn [sv_denot]; rewrite (BV6 54%nat vs2 ltac:(img_try (zlia)) EqS2); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl. }
split. { img_exact MQ. }
split. { img_exact SH. }
split. { idtac "PRES". intros a Ha.
eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 0 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV2; clear - Ha; unfold GDEPTH in *; zlia) | img_try (off_by ltac:(clear - Ha S1 L7 Usp; unfold GDEPTH in *; numconst; unfold KSTACK in *; zlia)) ]. }
split. { idtac "PRES2". intros a [Ha|Ha].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 5 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV39; clear - Ha; zlia) | img_try (off_by ltac:(clear - Ha A1 A2 A3 A5 A6; numconst; zlia)) ].
- eapply (st_ok_window_apresent_off (w_H W) E6 _ _ 7 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite PV32; unfold T in *; clear - Ha; numconst; zlia) | img_try (off_by ltac:(unfold T in *; clear - Ha L1 L2; numconst; zlia)) ]. }
cbv zeta.
split. { idtac "MUT". img_apply (proj2 (val_mem4_bytes _ _ _)). img_change (YP0g.le_byte 0 4 0) with 0. img_change (YP0g.le_byte 0 4 1) with 0. img_change (YP0g.le_byte 0 4 2) with 0. img_change (YP0g.le_byte 0 4 3) with 0.
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ _) =>
assert (VZ : forall a, A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 680 + 4 -> mbyte tfxsegs (mrestrict (w_H W) (ms_mem msR)) a = Some (Z_to_bv 8 0))
by (img_try (intros a Ha; eapply (st_ok_chunk_zero (w_H W) E ss msR 1 _ 0 _ _ a HS); [img_refl | img_refl | cbn [base_val YQ0b.r_base]; unfold A_ALLOCATOR in Ha |- *; clear - Ha; zlia])) end.
repeat split; img_apply VZ; unfold A_ALLOCATOR; zlia. }
split. { idtac "NS". memvo HS 2%nat (A_ALLOCATOR + 120); [img_refl | img_try (cbn [sv_denot]; rewrite (BV6 37%nat n ltac:(zlia) EqN); unfold w64; rewrite ?Zbv_add_unsigned; f_equal; rewrite unsigned_lit_small by (clear - A1 A2; zlia); zlia) | img_try (clear - A1 A2; zlia)]. }
split. { idtac "SRT". memvo HS 2%nat (A_ALLOCATOR + 128); [img_refl | img_refl | img_try (zlia)]. }
split. { idtac "JW1". jword HS 3%nat (A_ALLOCATOR + 144). }
split. { jword HS 3%nat (A_ALLOCATOR + 152). }
split. { jword HS 4%nat (A_ALLOCATOR + 704). }
split. { jword HS 4%nat (A_ALLOCATOR + 712). }
split. { idtac "QI". destruct Hown as [OW1 OW2]. rewrite OW2. memvo HS 5%nat 0; [img_try (cbn [base_val YQ0b.r_base]; rewrite PV39; zlia) | img_try (cbn [sv_denot]; rewrite (BV6 34%nat map ltac:(zlia) EqMAP); unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; img_refl) | img_try (clear - P1 P2 P4; numconst; zlia)]. }
idtac "OWNT". intros X. rewrite OWN in X. discriminate X.
Qed.
Lemma segGD_t : own = true -> small = true -> SRr tfxsegs W cfg0 at_MUN.
Proof. intros OWN SM. destruct (Z_lt_le_dec map kLowMemEnd) as [ZARM|ZARM]; [img_try (img_exact (segGD_t_lo OWN SM ZARM)) | img_try (img_exact (segGD_t_hi OWN SM ZARM))]. Qed.
Lemma segGD : small = true -> SRr tfxsegs W cfg0 at_MUN.
Proof. intros SM. destruct (Bool.bool_dec own true) as [O|O]; [img_try (img_exact (segGD_t O SM)) | img_try (apply Bool.not_true_is_false in O; img_exact (segGD_f O SM))]. Qed.
End WK.
End d.
