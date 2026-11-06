(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGc2.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 231fdaa2e59f) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 3 image addresses moved by code-verified function pairs (4 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 5 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGc2.v (donor image sha256 64b53ff86172), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* The can_fill = 0 arm of the frame-generic Allocate walk, k path (n <= 48).
   Ported from proofs/cgif/cgif_file_fuzzer/lib/AFhy.v..YFjg.v (cgif_file's released malloc walk, same image): the
   same scripts, with the caller's frame made abstract; the cf = 0 arm reuses the cf = 1 tail after 0x325d4.
   Each lemma starts where the cf = 1 proof splits on can_fill (AGj4.seg2c_even / AGj5.seg2c_odd start at
   at_S2 KS_Te / KS_To): the test at 0x3259c (cf = 0 takes it), then the cf = 1 tail from 0x325d4 (after the memset)
   to Allocate's ret. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1w AE3d AFhy AGhy AFi1 AGj6 AGhz AGi0 AGi2 AGc0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation R8v := (@AGj6.R8v n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation Uv := (@AGj6.Uv ly cl v).
Local Abbreviation SUv := (@AGj6.SUv ly cl v).
Local Abbreviation E0 := (@AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AGj6.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AGj6.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AGj6.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AGj6.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AGj6.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AGj6.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E1 := (@AGj6.E1 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AGj6.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AGj6.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AGj6.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPB := (@AGj6.EaPB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaNP := (@AGj6.EaNP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation WINT := (@AGj6.WINT ly cl).
Local Abbreviation PBW := (@AGj6.PBW ly n cl v).
Local Abbreviation WIN := (@AGj6.WIN ly regs0 n cl v).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
(* The allocator instance (atom aINST = register 11 of the virtual regs0) lies in the image, below the depot. *)
Hypothesis Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x17dec8.
Local Abbreviation DZONE := (@AGj6.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Local Abbreviation Kv_range := (@AGj6.Kv_range ly regs0 mem0 n tr cl v Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGj6.high_facts _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation blocks_facts := (@AGj6.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AGj6.off_T _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_C := (@AGj6.off_C _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_NB := (@AGj6.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGj6.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@AGj6.K0_facts n Nrange).
Local Abbreviation RZ_num := (@AGj6.RZ_num n Nrange).
#[local] Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AGj6.derived_ranges _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation WIN1 := (@AGj6.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@AGj6.WIN1_WIN ly regs0 mem0 n tr cl v Htrlen DPOST).
Local Abbreviation frame_WIN1 := (@AGj6.frame_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation stack_ivs := (@AGj6.stack_ivs _ ly regs0 mem0 n tr v Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation DZONE_disj := (@AGj6.DZONE_disj _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hso Hbp DPOST Nrange).
Local Abbreviation at_S2 := (@AGj6.at_S2 _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_RET0K := (@AGc0.at_RET0K _ W ly regs0 mem0 md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, AFSTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
(* The scratch window below Allocate's entry sp covers the whole stack part (regions 0 / 2, odd: 1 / 3). *)
Local Ltac stack_pres En HEn HS :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac);
destruct (Z_lt_le_dec a (sp0 - 128)) as [H1|H1];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 0 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 2 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ].
Local Ltac stack_pres_odd En HEn HS :=
intros a Ha; pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_); pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7');
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hlo_ Hhi_ T4' T7'; addr_tac);
destruct (Z_lt_le_dec a (sp0 - 128)) as [H1|H1];
[ eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| eapply (st_ok_window_apresent_off (w_H W) En _ _ 3 _ a HS); [reflexivity | clear - Ha Ra H1 Hlo_ Hhi_ T4' T7' HEn; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ] ].
(* can_fill (atom 15) is tested at 0x3259c; this is the cf = 0 arm (AGi2.kst_V0), which jumps to 0x325d4. *)
Lemma seg2cf0_even : getr regs0 15 = w64 0 -> NPv mod 8 = 0 -> forall z W0 c, at_S2 false KS_Te z W0 c -> SRr tfibsegs W0 c (at_RET0K false z).
Proof.
intros Hcf0 H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
assert (EUv : Uv = Kv + 16) by (clear - DR; zlia).
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 false (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
assert (ECF : U En (SOff 15 0) = 0) by (clear - HEn Hcf0; apply U_atom; [rewrite (HEn 15%nat (ltHAV 15 eq_refl)), (Er 15 15%bv eq_refl); exact Hcf0 | zlia]).
srr_run_to_sh tfibtbl_rtA_ok HS 0x337c0. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc ECF. rewrite branch_eq_U, ECF, (U_lit En 0) in Hc by zlia. first [discriminate Hc | apply Z.eqb_neq in Hc; zlia]. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
pose proof Kv_range as HKR. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
pose proof (DZONE_disj false) as DZD.
assert (PCH1 : forall a, ~ WIN1 false a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a N1' Ra Hp. apply (apresent_same (w_H W) mem1); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact N1' | exact Hp]. }
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R; rewrite R, (HEn 45%nat (ltHAV 45 eq_refl)), EaK. unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r. first [reflexivity | f_equal; clear - DR; zlia]. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn k (ltHAV k eq_refl)); symmetry; exact (Er k r eq_refl) | symmetry; exact Htp ] end. }
split. { exists mem2. split; [exact HDP|]. split; [exact PRD2|].
intros x Hx. destruct (DZD _ Hx) as (N0 & N2' & N3 & N4). rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply EQD, Hx. }
split. { intros x N0 ND N2' N3. rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply M0; assumption. }
split. { stack_pres En HEn HS. }
split. { intros a Ha.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR LF HKR; unfold WINT, PBW in Ha; numconst; destruct Ha as [Ha|[Ha|[_ Ha]]]; zlia).
destruct Ha as [Hw|[Hk|Hpb]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 41%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw H28 DR LF; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 52%nat (ltHAV 52 eq_refl)), EaSSLOT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; numconst; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
- destruct (Z_lt_le_dec a (Kv + 16)) as [H1|H1].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 48%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H1 DR LF HKR; numconst; zlia) ].
+
apply PCH1; [pose proof stack_ivs as SI; clear - Hk H1 DR LF HKR Hlo T7 PT SI EUv; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia | exact Ra |].
apply (apresent_same (w_H W) mem0); [apply M0; rewrite unsigned_lit_small by exact Ra | apply HKpres; clear - Hk H1 DR; numconst; zlia].
-- pose proof stack_ivs as SI; clear - Hk H1 DR LF HKR Hlo T7 PT SI EUv; unfold WIN, WINT, PBW; numconst; zlia.
-- pose proof blocks_facts as BF. clear - Hk H1 DR LF HKR Hlo T7 BF; unfold zdisjoint in BF; cbn [fst snd] in BF; unfold DZONE; numconst; zlia.
-- clear - Hk H1 DR; numconst; zlia.
- destruct Hpb as [Hpb _]. discriminate Hpb. }
cbv zeta.
assert (RK : 0 <= Kv /\ Kv + 2 ^ 16 < 2 ^ 64) by (clear - DR; numconst; zlia).
split. { memv HS 48%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | reflexivity | zlia]. }
split. { pose proof (hdr_byte1_ok jb Hjb) as [B1 B2].
memv HS 48%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 46%nat (ltHAV 46 eq_refl)), (eq_refl : ew E0 46 = w64 jb). unfold w64. rewrite unsigned_lit_small by zlia.
unfold hdr_byte1. reflexivity. }
split. { memv HS 48%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
split. { memv HS 48%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia
| cbn [sv_denot]; rewrite (HEn 62%nat (ltHAV 62 eq_refl)), EaNP; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; zlia | zlia]. }
split. { memv HS 45%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn 41%nat (ltHAV 41 eq_refl)), (eq_refl : ew E0 41 = w64 cnt); unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | zlia]. }
split. { memv HS 42%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T; numconst; zlia | reflexivity | zlia]. }
split. { intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 false (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply SRZ, Hx. }
split. { intros HH; discriminate HH. }
(* The block keeps its contents: it lies outside every write window of the run. *)
intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 false (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT EUv. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply M0.
- pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT EUv. unfold WIN, WINT, PBW. numconst. zlia.
- pose proof blocks_facts as BF. clear - Hx DR LF Hlo T7 BF HKR. unfold zdisjoint in BF. cbn [fst snd] in BF. unfold DZONE. numconst. zlia.
- clear - Hx DR. numconst. zlia.
Qed.
Lemma seg2cf0_odd : getr regs0 15 = w64 0 -> NPv mod 8 <> 0 -> forall z W0 c, at_S2 true KS_To z W0 c -> SRr tfibsegs W0 c (at_RET0K true z).
Proof.
intros Hcf0 H8 z W0 c (-> & ms & mat & En & mem2 & -> & HEn & HS & HDP & PRD2 & EQD & M0 & PRS & SRZ & PBV). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & NPR8 & _ & N8r & N8m & NPN8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
assert (Usp : 0 <= bv_unsigned (getr regs0 2) < 2 ^ 64) by apply u64_range.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
assert (EUv : Uv = Kv + 16) by (clear - DR; zlia).
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WIN1 true (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
assert (ECF : U En (SOff 15 0) = 0) by (clear - HEn Hcf0; apply U_atom; [rewrite (HEn 15%nat (ltHAV 15 eq_refl)), (Er 15 15%bv eq_refl); exact Hcf0 | zlia]).
srr_run_to_sh tfibtbl_rtA_ok HS 0x337c0. frame_acc HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc ECF. rewrite branch_eq_U, ECF, (U_lit En 0) in Hc by zlia. first [discriminate Hc | apply Z.eqb_neq in Hc; zlia]. }
clear Hc. srr_run_sh tfibtbl_rtA_ok HS. frame_acc HEn.
pose proof Kv_range as HKR. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PT). unfold zdisjoint in PT. cbn [fst snd] in PT.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx W En); [exact HS | reflexivity | vm_compute; reflexivity |].
intros matZ. match type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
rreg HS (1%bv : bv 5) RZ1. rewrite (HEn 1%nat (ltHAV 1 eq_refl)), E1 in RZ1. rewrite RZ1. unfold YK0s.ret_ok in Hra. rewrite Hra.
pose proof (DZONE_disj true) as DZD.
assert (PCH1 : forall a, ~ WIN1 true a -> 0 <= a < 2 ^ 64 -> apresent (w_H W) mem1 a -> apresent (w_H W) (ms_mem msZ) a).
{ intros a N1' Ra Hp. apply (apresent_same (w_H W) mem1); [apply MEQ; rewrite unsigned_lit_small by exact Ra; exact N1' | exact Hp]. }
split; [reflexivity|]. exists (ms_regs msZ), (ms_mem msZ), matZ. split; [reflexivity|].
split. { rreg HS (10%bv : bv 5) R; rewrite R, (HEn 45%nat (ltHAV 45 eq_refl)), EaK. unfold w64. rewrite ?Zbv_add_unsigned, ?Z.add_0_r. first [reflexivity | f_equal; clear - DR; zlia]. }
split. { intros r Hr. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
lazymatch goal with |- getr _ ?r = _ =>
let R := fresh "R" in rreg HS r R; rewrite R;
let k := eval cbv in (Z.to_nat (bv_unsigned r)) in
first [ rewrite (HEn k (ltHAV k eq_refl)); symmetry; exact (Er k r eq_refl) | symmetry; exact Htp ] end. }
split. { exists mem2. split; [exact HDP|]. split; [exact PRD2|].
intros x Hx. destruct (DZD _ Hx) as (N0 & N2' & N3 & N4). rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply EQD, Hx. }
split. { intros x N0 ND N2' N3. rewrite (MEQ x) by (intros H1; apply N0, WIN1_WIN, H1). apply M0; assumption. }
split. { stack_pres_odd En HEn HS. }
split. { intros a Ha.
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha DR LF HKR; unfold WINT, PBW in Ha; numconst; destruct Ha as [Ha|[Ha|[_ Ha]]]; zlia).
destruct Ha as [Hw|[Hk|Hpb]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 46%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
* eapply (st_ok_window_apresent_off (w_H W) En _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; zlia | off_by ltac:(clear - Hw H28 DR LF; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 52%nat (ltHAV 52 eq_refl)), EaSSLOT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T in *; numconst; zlia | off_by ltac:(clear - Hw DR LF; numconst; zlia) ].
- destruct (Z_lt_le_dec a (Kv + 16)) as [H1|H1].
+ eapply (st_ok_window_apresent_off (w_H W) En _ _ 49%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | off_by ltac:(clear - Hk H1 DR LF HKR; numconst; zlia) ].
+
apply PCH1; [pose proof stack_ivs as SI; clear - Hk H1 DR LF HKR Hlo T7 PT SI EUv; unfold WIN1, WINT, PBW, IFRAME; numconst; zlia | exact Ra |].
apply (apresent_same (w_H W) mem0); [apply M0; rewrite unsigned_lit_small by exact Ra | apply HKpres; clear - Hk H1 DR; numconst; zlia].
-- pose proof stack_ivs as SI; clear - Hk H1 DR LF HKR Hlo T7 PT SI EUv; unfold WIN, WINT, PBW; numconst; zlia.
-- pose proof blocks_facts as BF. clear - Hk H1 DR LF HKR Hlo T7 BF; unfold zdisjoint in BF; cbn [fst snd] in BF; unfold DZONE; numconst; zlia.
-- clear - Hk H1 DR; numconst; zlia.
- destruct Hpb as [_ Hpb]. eapply (st_ok_window_apresent_off (w_H W) En _ _ 0%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold aPB; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); zlia | off_by ltac:(clear - Hpb DR; numconst; zlia) ]. }
cbv zeta.
assert (RK : 0 <= Kv /\ Kv + 2 ^ 16 < 2 ^ 64) by (clear - DR; numconst; zlia).
split. { memv HS 49%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | reflexivity | zlia]. }
split. { pose proof (hdr_byte1_ok jb Hjb) as [B1 B2].
memv HS 49%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 46%nat (ltHAV 46 eq_refl)), (eq_refl : ew E0 46 = w64 jb). unfold w64. rewrite unsigned_lit_small by zlia.
unfold hdr_byte1. reflexivity. }
split. { memv HS 49%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.div_small by zlia. reflexivity. }
split. { memv HS 49%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 45%nat (ltHAV 45 eq_refl)), EaK; unfold w64; rewrite unsigned_lit_small by (clear - DR; numconst; zlia); clear - DR; zlia
| cbn [sv_denot]; rewrite (HEn 62%nat (ltHAV 62 eq_refl)), EaNP; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; f_equal; zlia | zlia]. }
split. { memv HS 46%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 40%nat (ltHAV 40 eq_refl)), EaP; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia
| cbn [sv_denot]; rewrite (HEn 41%nat (ltHAV 41 eq_refl)), (eq_refl : ew E0 41 = w64 cnt); unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | zlia]. }
split. { memv HS 43%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 32%nat (ltHAV 32 eq_refl)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); unfold T; numconst; zlia | reflexivity | zlia]. }
split. { intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 true (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply SRZ, Hx. }
split. { intros _.
pose proof (Z.mod_pos_bound NPv 8 ltac:(zlia)) as M8.
memv HS 0%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn 54%nat (ltHAV 54 eq_refl)), EaPB; unfold w64; rewrite unsigned_lit_small by (clear - DR LF; numconst; zlia); zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ =>
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 62%nat (ltHAV 62 eq_refl)), EaNP. unfold w64. rewrite unsigned_lit_small by zlia.
zcanon_simp. rewrite land_7_mod by zlia. zcanon_simp. rewrite Z.add_0_r. reflexivity. }
(* The block keeps its contents: it lies outside every write window of the run. *)
intros x Hx. pose proof (u64_range x) as Rx.
assert (N1' : ~ WIN1 true (bv_unsigned x)).
{ pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT EUv. unfold WIN1, WINT, PBW, IFRAME. numconst. zlia. }
rewrite (MEQ x N1'). apply M0.
- pose proof stack_ivs as SI. clear - Hx DR LF HKR Hlo T7 SI PT EUv. unfold WIN, WINT, PBW. numconst. zlia.
- pose proof blocks_facts as BF. clear - Hx DR LF Hlo T7 BF HKR. unfold zdisjoint in BF. cbn [fst snd] in BF. unfold DZONE. numconst. zlia.
- clear - Hx DR. numconst. zlia.
Qed.
End e.
End d.
