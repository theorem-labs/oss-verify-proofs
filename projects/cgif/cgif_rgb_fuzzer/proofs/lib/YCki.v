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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YI0d YI0h YChh YCia YCm1 YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCop.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCqg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0f YCd3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YCkr YCks YCkt YCku YCkv YCkw YCkx YClv.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gR4 : forall n : nat, rga_fromA B ss_R4 (fun _ => INV_R4 B (S n)) -> rga_from B ss_R3 (INV_R3 B (S n)).
Proof.
intros n RR4. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & p1 & ppc & npc & p2 & xxc & nxc & hn & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & Rpp & Rxx & Hppc_perm & Hxxc_perm & Rp1 & Hcase1 & Rp2 & Hcase2 & Rhn & Hhn01 & Hhn_gp & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt).
unfold g_perm in Hppc_perm, Hxxc_perm. rga_cbn_cx Hppc_perm. rga_cbn_cx Hxxc_perm. destruct Hppc_perm as [Tppc Appc]. destruct Hxxc_perm as [Txxc Axxc].
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_R3 in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hcnt0 & _) & _).
assert (HT24 : 524309 <= ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hcnt64 : 0 <= ht_cnt Ht < 2 ^ 64) by (clear - Hcnt0 HT24; lia).
assert (BT : 0 <= ht_T Ht < 2 ^ 64) by (clear - HT24; lia).
set (Tn := getNextPrimePower2 (ht_T Ht)) in *.
pose proof (ts_chain_next _ HTch HTlt) as HTnch. fold Tn in HTnch.
pose proof (ts_chain_next_gt _ HTch HTlt) as HTngt. fold Tn in HTngt.
assert (HTn24 : 1048583 <= Tn <= 16777216) by (clear - HTnch HTngt HT24; unfold ts_chain in HTnch; cbn [In] in HTnch; lia).
assert (BTn : 0 <= Tn < 2 ^ 64) by (clear - HTn24; lia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
pose proof (g_ts_rank_range (ht_T Ht)) as Hrk.
assert (Hrk4 : g_ts_rank (ht_T Ht) <= 4).
{ clear - HTch HTlt. unfold ts_chain in HTch. cbn [In] in HTch. unfold MAX_TABLE_SIZE in HTlt.
destruct HTch as [H|[H|[H|[H|[H|[H|[]]]]]]]; rewrite <- H in *; first [ vm_compute; discriminate | lia ]. }
assert (Hnpc : npc = 3 * ht_T Ht \/ npc = 3 * Tn) by (destruct Hcase1 as [(_ & _ & Hx) | (_ & _ & Hx)]; [left | right]; exact Hx).
assert (Hnpc0 : 1572927 <= npc <= 50331648) by (clear - Hnpc HT24 HTn24; lia).
assert (Hnxc : nxc = 4 * ht_T Ht \/ nxc = 4 * Tn) by (destruct Hcase2 as [(_ & _ & Hx) | (_ & _ & Hx)]; [left | right]; exact Hx).
assert (Hnxc0 : 2097236 <= nxc <= 67108864) by (clear - Hnxc HT24 HTn24; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (TBL := [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (ppc, npc); (xxc, nxc)] ++ optb hn (3 * Tn)).
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ TBL).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest TBL; YI0g.perm_tac).
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) TBL -> In (b, sz) lrest) by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Hcht_in3 : forall b sz, In (b, sz) TBL -> In (b, sz) (ablocks B ly3 S3)).
{ intros b sz Hb. eapply Permutation_in; [apply Permutation_sym; exact HPrt3|]. right. right. exact (Hcht_l b sz Hb). }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
idtac "OK-B".
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_fq].
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_hh].
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_uu].
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
assert (Hppc_in3 : In (ppc, npc) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hppc_l : In (ppc, npc) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ ppc _ HAR3 Hppc_in3 ltac:(clear - Hnpc0; lia)) as (Hppc4096 & Hppcceil & Hppc16 & Hppcpres).
pose proof (req_size_pos (npc) ltac:(clear - Hnpc0; lia)) as [_ Hrq_ppc].
assert (Bppc : 0 <= ppc < 2 ^ 64) by (clear - Hppc4096 Hppcceil Hnpc0 C1; lia).
assert (Hxxc_in3 : In (xxc, nxc) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hxxc_l : In (xxc, nxc) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ xxc _ HAR3 Hxxc_in3 ltac:(clear - Hnxc0; lia)) as (Hxxc4096 & Hxxcceil & Hxxc16 & Hxxcpres).
pose proof (req_size_pos (nxc) ltac:(clear - Hnxc0; lia)) as [_ Hrq_xxc].
assert (Bxxc : 0 <= xxc < 2 ^ 64) by (clear - Hxxc4096 Hxxcceil Hnxc0 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
idtac "OK-BLK".
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 340936.
idtac "OK-R0".
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-R1".
set (n4 := Tn).
assert (Hn4 : 64513 <= n4 < MALLOC_MAX) by (subst n4; unfold MALLOC_MAX; clear - HTn24; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) n4
ltac:(apply (U_atom _ 755 Tn R755 BTn)) Ha0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
idtac "OK-C0".
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_atD trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k n4 (-576) (Z_to_bv 64 0x82b0c) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ha0.
- unfold MALLOC_MAX in *. clear - Hn4. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPm3), !bsum_app, <- (blocks_bytes_bsum B ly S). subst TBL. rewrite !bsum_cons, !bsum_app, !bsum_cons. change (bsum []) with 0. cbn [snd].
assert (Hob : forall p z, 0 <= z -> 0 <= bsum (optb p z) <= z) by (intros p z Hz; unfold optb; destruct (p =? 0); cbn [bsum fold_right snd]; lia).
pose proof (Hob hn (3 * Tn) ltac:(clear - HTn24; lia)) as Hob_hn.
subst n4. clear - Hlive HfN HN1 HN HTn24 HT24 Hnpc0 Hnxc0 Hob_hn. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX in *. lia.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 Hrk Hrk4 HEVv HTlt; rga_lia).
- assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
idtac "OK-C1".
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & un & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hd7 & Hres7).
apply rga_d_malloc in Hd7; [|subst n4; clear - HTn24; lia].
clear Ha0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly3 S3 W3 _ W7 mem7 ly7 S7 _ _ un n4 Hres7) as (HK7 & HBin7 & HunIn).
pose proof (mres_range B LAWS ly7 S7 W7 mem7 md7 ly3 S3 un n4 _ _ (proj1 HJ7) Hres7) as Hrng7.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (apply HBin7; exact Hrin3).
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (apply HBin7; exact Htb_in3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
assert (HnF7 : forall a, F <= a < F + 8192 -> ~ (un <> 0 /\ un <= a < un + req_size n4)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ un n4 7 fpos HAR7 (HunIn Hnz) Hfin7) as Dd.
rewrite EFA7 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hin. lia. }
assert (HnC7 : forall a, cfp <= a < cfp + 24 -> ~ (un <> 0 /\ un <= a < un + req_size n4)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ un n4 cid pos HAR7 (HunIn Hnz) HfinS7) as Dd.
rewrite EFA7 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin Hflo Hfhi. lia. }
assert (HnO7 : forall b sz a, In (b, sz) (ablocks B ly3 S3) -> b <= a < b + req_size sz -> ~ (un <> 0 /\ un <= a < un + req_size n4)).
{ intros b sz a Hb Ha [Hnz Hin]. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (Hnz Hz)|].
pose proof (rg_sep_head_in B LAWS ly7 S7 _ _ _ (un, n4) (ablocks B ly3 S3) (b, sz) HAR7 ltac:(rewrite Ebl7; apply Permutation_sym; apply Permutation_cons_append) Hb) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin. lia. }
assert (HnR7 : forall a, r <= a < r + 64 -> ~ (un <> 0 /\ un <= a < un + req_size n4))
by (intros a Ha; apply (HnO7 r 64 a Hrin3); change (req_size 64) with 64; exact Ha).
assert (HnT7 : forall a, tb <= a < tb + 48 -> ~ (un <> 0 /\ un <= a < un + req_size n4))
by (intros a Ha; apply (HnO7 tb 48 a Htb_in3); change (req_size 48) with 48; exact Ha).
assert (HnS7 : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (un <> 0 /\ un <= a < un + req_size n4)).
{ intros a Ha [Hnz Hin]. destruct Hrng7 as [Hz | (Hb4096' & [_ Hbz] & _)]; [exact (Hnz Hz)|]. clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
idtac "OK-P0".
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK7 | exact (proj1 HJ7) | exact Htb_in7 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT7; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
idtac "OK-RS".
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Ha07 in Rres. symmetry in Rres. unfold w64 in Rres.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
idtac "OK-P2".
ga_join HS ss_R4 840%nat rga_deads_R4 ltac:(idtac).
idtac "OK-J".
assert (Hun01 : un = 0 \/ 4096 <= un) by (destruct Hrng7 as [Hz | (Hz & _)]; [left | right]; exact Hz).
assert (Hun_perm : un <> 0 -> aftok (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) (un, n4) /\
(forall blc lyq ownq i, In (un, n4) blc -> 0 <= i < req_size n4 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (un + i))).
{ intros Hnz. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (False_ind _ (Hnz Hz))|].
split; [exact (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ un n4 HJ3 HAR7 Ebl7 ltac:(clear - Hn4; lia))|].
intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ un n4 blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(clear - Hn4; lia) Hbl Hi). }
assert (HPm7 : Permutation (ablocks B ly7 S7)
(ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ (tb, 48) :: [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (ppc, npc); (xxc, nxc)] ++ optb hn (3 * Tn) ++ optb un n4)).
{ destruct Hres7 as [(Hz & Ebl7 & _) | (Hz & Ebl7 & _)].
- replace (optb un n4) with (@nil (Z * Z)) by (rewrite Hz; reflexivity). rewrite !app_nil_r, Ebl7. subst TBL. exact HPm3.
- replace (optb un n4) with [(un, n4)] by (unfold optb; replace (un =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hz; lia); reflexivity). rewrite Ebl7.
eapply Permutation_trans; [apply Permutation_app_tail; exact HPm3|]. subst TBL. YI0g.perm_tac. }
idtac "OK-PERM".
assert (Hn3T : 3 * ht_T Ht <= npc) by (clear - Hnpc HTngt; lia).
assert (Hn4T : 4 * ht_T Ht <= nxc) by (clear - Hnxc HTngt; lia).
assert (Harr0 : g_arrs (mrestrict (w_H W3) (ms_mem ms)) fq hh uu ppc xxc (ht_frequ Ht) (ht_keys Ht) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht)).
{ apply (g_arrs_kept (w_H W3) (ms_mem ms3) (ms_mem ms) fq hh uu ppc xxc (ht_T Ht) _ _ _ _ _ Harr (g_lens_of_inv Ht ent Hinv)).
intros a Ha. unfold g_in5 in Ha.
assert (Hq : 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (Hoff3 fq (4 * ht_T Ht) Hfq_l) | apply (Hoff3 hh (3 * ht_T Ht) Hhh_l) | apply (Hoff3 uu (ht_T Ht) Huu_l) | apply (Hoff3 ppc npc Hppc_l) | apply (Hoff3 xxc nxc Hxxc_l) ];
clear - Ha Hrq_fq Hrq_hh Hrq_uu Hrq_ppc Hrq_xxc Hn3T Hn4T; lia. }
exact (KP a (proj1 Hq) (proj2 Hq)). }
assert (KB7 : forall b sz, In (b, sz) (ablocks B ly3 S3) -> forall i, 0 <= i < sz -> aview trbsegs (w_H W7) mem7 (b + i) = aview trbsegs (w_H W3) (ms_mem ms) (b + i)).
{ intros b sz Hb i Hi. pose proof (req_size_pos sz ltac:(clear - Hi; lia)) as [_ Hrqb]. destruct HK7 as (_ & K2 & _).
apply (K2 b sz i Hb); [clear - Hi Hrqb; lia|]. apply (HnO7 b sz (b + i) Hb). clear - Hi Hrqb. lia. }
assert (Harr7 : g_arrs (mrestrict (w_H W7) mem7) fq hh uu ppc xxc (ht_frequ Ht) (ht_keys Ht) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht)).
{ apply (g_arrs_move (w_H W3) (w_H W7) (ms_mem ms) mem7 fq hh uu ppc xxc ppc xxc (ht_T Ht) _ _ _ _ _ Harr0 (g_lens_of_inv Ht ent Hinv)).
- intros i Hi. exact (KB7 fq _ Hfq_in3 i Hi).
- intros i Hi. exact (KB7 hh _ Hhh_in3 i Hi).
- intros i Hi. exact (KB7 uu _ Huu_in3 i Hi).
- intros i Hi. apply (KB7 ppc _ Hppc_in3 i). clear - Hi Hn3T. lia.
- intros i Hi. apply (KB7 xxc _ Hxxc_in3 i). clear - Hi Hn4T. lia. }
idtac "OK-ARR".
assert (Hk1 : k + 1 <= 8 + 12 * g_ts_rank (ht_T Ht) + 8) by (clear - Hk0; lia).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (Hgperm1 : g_perm B cxv ppc npc) by (unfold g_perm; rga_cbn_cx_goal; exact (conj Tppc Appc));
assert (Hgperm2 : g_perm B cxv xxc nxc) by (unfold g_perm; rga_cbn_cx_goal; exact (conj Txxc Axxc));
assert (Hgperm3 : un <> 0 -> g_perm B cxv un (Tn)) by (intros Hnz; unfold g_perm; rga_cbn_cx_goal; exact (Hun_perm Hnz)) end.
rga_hand RR4 HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. fold n4. m_inv_auto.
Qed.
End e.
End d.
