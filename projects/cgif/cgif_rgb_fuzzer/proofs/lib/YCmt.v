(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCoi YCoj YCok YCn9 YCna YCol YCo5 YCo6 YCo7 YCo9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqh YCo8.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis COLHASH : tcolhash_spec B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_tra.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_SM_store_e : rga_fromA B ss_SMT (fun _ => INV_SMT B) -> forall n, rga_from B ss_SMH (INV_SM B n) -> rga_from B ss_SMSe (INV_SM B (S n)).
Proof.
intros RSMT n IH.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt & Hix & Hnix & R715 & R716 & R717 & R718 & R719).
destruct Hk0 as [Hk0 Hbud].
unfold ss_SMSe in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hcnt0 & _) & _).
assert (HT24 : 0 < ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hcnt64 : 0 <= ht_cnt Ht < 2 ^ 64) by (clear - Hcnt0 HT24; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Hcht_sz : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> 0 <= sz)
by (intros b sz Hb; cbn [cht_blocks In] in Hb; clear - Hb HT24; destruct Hb as [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]; injection Hq as _ <-; lia).
assert (Hfim_l : In (fim, N) lrest) by (subst lrest; apply in_or_app; right; apply in_or_app; left; right; left; reflexivity).
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hfim_l]).
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as HrqN.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim N HAR3 Hfim_in3) as (Hfim4096 & Hfimzone & Hfimceil & Hfim16).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim N 7 fpos HAR3 Hfim_in3 Hfin3) as HdF_fim.
unfold zdisjoint in HdF_fim. cbn [fst snd] in HdF_fim. change (fs_frame_bytes 7) with 8192 in HdF_fim. rewrite EFA3 in HdF_fim. fold F in HdF_fim.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim N cid pos HAR3 Hfim_in3 HfinS3) as HdC_fim.
unfold zdisjoint in HdC_fim. cbn [fst snd] in HdC_fim. rewrite EFA3 in HdC_fim.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fim, N) HAR3 HPrt3 ltac:(right; exact Hfim_l)) as HzR_fim.
unfold zdisjoint, block_rng in HzR_fim. cbn [fst snd] in HzR_fim. change (req_size RGB_SIZE) with 64 in HzR_fim.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (fim, N) HAR3 HPtb3 ltac:(right; exact Hfim_l)) as HzT_fim.
unfold zdisjoint, block_rng in HzT_fim. cbn [fst snd] in HzT_fim. change (req_size 48) with 48 in HzT_fim.
assert (HzA_fim : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> b + req_size sz <= fim \/ fim + req_size N <= b).
{ intros b sz Hb.
assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx (ht_T Ht) ++ ((fim, N) :: (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (b, sz) (fim, N) HAR3 HPx Hb ltac:(left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. exact Dd. }
assert (Hfcell_rng : 4096 <= fim + ix /\ fim + ix + 1 <= alloc_ceiling) by (clear - Hfim4096 Hfimceil HrqN Hix; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fim N (proj1 HJ3) Hfim_in3) as (_ & _ & _ & _ & Hfimpres & _).
pose proof (ast_ok_add_region trbsegs E _ _
(YQ0b.mkRegion (Some 721%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite R719, unsigned_lit_small by (clear - Hfcell_rng C1; lia);
split; [clear - Hfcell_rng; lia|]; split; [clear - Hfcell_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hfimpres (fim + ix + o) ltac:(clear - Ho Hix HrqN; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hfcell_rng Hceil Hslo FFS Hix HrqN; lia
| destruct Hfimzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hix HrqN HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_fim Hix HrqN; lia
| clear - HdC_fim Hix HrqN Hflo Hfhi; lia
| clear - HzR_fim Hix HrqN; lia
| clear - HzT_fim Hix HrqN; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (23%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (23%bv : bv 5) (SOff 721 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (23%bv : bv 5) HS); change (sv_denot Ev (SOff 721 0) = sv_denot Ev e);
cbn [sv_denot]; rewrite R715, R719; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
pose proof (st_ok_add_fact trbsegs E _ _ 721%nat (mkAF 4096 140737479966720 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite R719, unsigned_lit_small by (clear - Hfcell_rng C1; lia); change (2 ^ 0) with 1;
split; [clear - Hfcell_rng C1; lia|]; split; [apply Z.mod_1_r | clear; lia])) as HS3.
clear HS; rename HS3 into HS.
norm_ss HS.
assert (HU721 : U E (SOff 721 0) = fim + ix) by (apply (U_atom E 721 (fim + ix) R719); clear - Hfcell_rng C1; lia).
assert (HU184 : U E (SOff 184 0) = fim) by (apply (U_atom E 184 fim Rfim); clear - Hfim4096 Hfimceil HrqN C1; lia).
m_add_cond HS BC_GEU (SOff 721 0) (SOff 184 0) ltac:(eapply (ub_geu_cond _ _ _ _ _ HU721 HU184); clear - Hix; lia).
m_add_cond HS BC_NE (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SOff 721 0) (SLit 1))) (SLit 0) ltac:(eapply (ub_nz_cond _ _ _ HU721); clear - Hfcell_rng; lia).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83718.
all: try (unfold GBx; m_obl_cell HJ3 R719 E44 Hfim_in3 ltac:(idtac; first [clear - Hfcell_rng C1; lia | clear - Hix HrqN; lia])).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(m_awr_cell 721%nat R719 fim Afim Hfim_in3 ltac:(idtac; first [clear - Hfcell_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hix HrqN; lia end])).
m_run_keptG HFr AG (fun a : Z => (m_ZsP F r a \/ tb <= a < tb + 48) \/ fim + ix <= a < fim + ix + 1) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HarrC : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
pose proof (HzA_fim b sz Hb) as Dz.
apply (UN0 (b + i) Hq1). intros [Hz | Hz]; [exact (Hq2 Hz) | clear - Hz Dz Hi Hrqb Hix HrqN; lia]. }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (tl (ss_mem ssx)) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
+
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx10 : ew Ex 720 = Z_to_bv 64 (N - ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R718) end.
rewrite YO3v.branch_ne_U in Hc. rewrite (U_atom_off _ 720 (N - ix) (-1) Rx10), U_SLit in Hc by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. clear Rx10.
assert (Hix1 : 0 <= ix + 1 < N) by (clear - Hc Hix; lia).
assert (Hnix1 : Z.of_nat n = N - (ix + 1)) by (clear - Hnix; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83578.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rx19 : ew Ex 721 = Z_to_bv 64 (fim + ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R719);
assert (Rx16 : ew Ex 718 = Z_to_bv 64 (fmt * ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R716);
assert (Rx18 : ew Ex 720 = Z_to_bv 64 (N - ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R718);
assert (Rx46 : ew Ex 46 = Z_to_bv 64 fmt) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E46);
assert (Rx42 : ew Ex 42 = Z_to_bv 64 beffmt) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E42) end.
assert (Hpx : 0 <= fmt * ix < 2 ^ 31 /\ fmt * ix + fmt < 2 ^ 31) by (clear - Hfmt Hix HN; unfold RGB_NMAX in HN; nia).
rregU HS (23%bv : bv 5) (fim + (ix + 1)) ltac:(rewrite (U_atom_off _ 721 (fim + ix) 1 Rx19) by (clear - Hfcell_rng C1; lia); clear; lia) Q20.
rregU HS (25%bv : bv 5) (fim + (ix + 1)) ltac:(rewrite (U_atom_off _ 721 (fim + ix) 1 Rx19) by (clear - Hfcell_rng C1; lia); clear; lia) QS.
rregU HS (20%bv : bv 5) (fmt * (ix + 1))
ltac:(replace (fmt * (ix + 1)) with (fmt * ix + fmt) by (clear; lia);
apply U_add_small_q; [apply (U_atom _ 718 _ Rx16); clear - Hpx; lia | apply (m_U_zext8_sext32 _ 46 fmt Rx46); clear - Hfmt; lia
| clear - Hpx; lia | clear - Hfmt; lia | clear - Hpx; lia]) Q23.
m_rregUself HS (21%bv : bv 5) Q24.
rregU HS (18%bv : bv 5) (N - (ix + 1)) ltac:(rewrite (U_atom_off _ 720 (N - ix) (-1) Rx18) by (clear - Hix HN; unfold RGB_NMAX in HN; lia); clear; lia) Q26.
lazymatch type of Q24 with _ = Z_to_bv 64 ?w =>
assert (Hw24 : bef <> 0 -> Z_to_bv 64 w = Z_to_bv 64 (beffmt * (ix + 1))) end.
{ intros Hb. f_equal. destruct Hbef as [Hq | Hbf]; [exfalso; exact (Hb Hq)|].
assert (Hpy : 0 <= beffmt * ix < 2 ^ 31 /\ beffmt * ix + beffmt < 2 ^ 31) by (clear - Hbf Hix HN; unfold RGB_NMAX in HN; nia).
replace (beffmt * (ix + 1)) with (beffmt * ix + beffmt) by (clear; lia).
apply U_add_small_q; [apply (U_atom _ 719 (beffmt * ix)); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact (R717 Hb) | clear - Hpy; lia]
| apply (U_sext32_small _ 42 beffmt Rx42); clear - Hbf; lia
| clear - Hpy; lia | clear - Hbf; lia | clear - Hpy; lia]. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HarrD : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms) _ fq hh uu pp xx Ht HarrC L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
exact (UN1 (b + i) Hq1 Hq2). }
clear HarrC.
ga_join HS ss_SMH2 820%nat rga_deads_SMH2
ltac:(idtac; ga_join_val HS 820%nat 17%nat Q20 E837; ga_join_val HS 820%nat 18%nat Q23 E838; ga_join_val HS 820%nat 19%nat Q24 E839;
ga_join_val HS 820%nat 20%nat Q26 E840; ga_join_val HS 820%nat 21%nat QS E841).
m_join_win HS ss_SMH 700%nat rga_deads_SMH
ltac:(idtac; ga_join_val HS 700%nat 17%nat Q20 N717; ga_join_val HS 700%nat 18%nat Q23 N718; ga_join_val HS 700%nat 19%nat Q24 N719;
ga_join_val HS 700%nat 20%nat Q26 N720; ga_join_val HS 700%nat 21%nat QS N721).
m_hand_ih IH HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, (ix + 1), Ht, ent. m_inv_auto.
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x8379c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HarrD : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms) _ fq hh uu pp xx Ht HarrC L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
exact (UN1 (b + i) Hq1 Hq2). }
clear HarrC.
ga_join HS ss_SMT 850%nat rga_deads_SMT ltac:(idtac).
rga_hand RSMT HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, Ht, ent. m_inv_auto.
Qed.
End d.
End c.
