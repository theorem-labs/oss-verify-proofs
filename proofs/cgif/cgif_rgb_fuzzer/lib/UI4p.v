(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3l UO0e UI39
YI00 YI02 YI01 YI03
UI1e UI1i UI57 UI1h YI0x UI16 YI07 YP14 YI08 YI0c YI0g
UI3h UI3d UI4v UIZm YI0f UI4m UI4o.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Lemma ts_chain_bounds : forall T, In T ts_chain -> 524309 <= T <= 16777216.
Proof. intros T H. cbv [ts_chain In] in H. lia. Qed.
Lemma pixel_of_img : forall segs (m : word -> option byte) img imgl fmt N i,
arr8 segs m img imgl -> zlen imgl = fmt * N -> (fmt = 3 \/ fmt = 4) -> 0 <= i < N ->
exists c op, pixel_at segs m (img + fmt * i) fmt c op.
Proof.
intros segs m img imgl fmt N i Ha Hl Hf Hi.
assert (Hb : forall k, 0 <= k < fmt -> mbyte segs m (img + fmt * i + k) = Some (Z_to_bv 8 (getz imgl (fmt * i + k))) /\ 0 <= getz imgl (fmt * i + k) < 256).
{ intros k Hk. rewrite <- Z.add_assoc. apply (arr8_getz segs m img imgl); [exact Ha | nia]. }
exists (mkcol (getz imgl (fmt * i)) (getz imgl (fmt * i + 1)) (getz imgl (fmt * i + 2))).
destruct (Hb 0 ltac:(lia)) as [B0 R0]. destruct (Hb 1 ltac:(lia)) as [B1 R1]. destruct (Hb 2 ltac:(lia)) as [B2 R2].
replace (img + fmt * i + 0) with (img + fmt * i) in B0 by lia. replace (fmt * i + 0) with (fmt * i) in B0, R0 by lia.
destruct Hf as [-> | ->].
- exists true. split; [|left; split; reflexivity]. unfold col3, colour_ok, cR, cG, cB, mkcol. cbn [fst snd]. repeat split; assumption || lia.
- destruct (Hb 3 ltac:(lia)) as [B3 R3]. exists (128 <=? getz imgl (4 * i + 3)).
split; [unfold col3, colour_ok, cR, cG, cB, mkcol; cbn [fst snd]; repeat split; assumption || lia|].
right. split; [reflexivity|]. exists (getz imgl (4 * i + 3)). split; [exact B3|]. split; [exact R3 | reflexivity].
Qed.
Lemma rdn_of_bytes : forall segs (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte segs m (a + i) = Some b) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
intros segs m n. induction n as [|n IH]; intros a Hp Ha Han.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. unfold mbyte in Hb. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma reg_notin_clob : forall (l c : list reg) (rr : reg), forallb (fun r => negb (reg_in r c)) l = true -> In rr l -> reg_in rr c = false.
Proof.
intros l c rr Hf Hin. pose proof (proj1 (forallb_forall _ _) Hf rr Hin) as X. cbn beta in X.
destruct (reg_in rr c); [discriminate | reflexivity].
Qed.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis CH : col_hash_spec API.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation keep2 pnew fimg := (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]).
Local Notation JRN Lc Ac m mdc := (journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac m mdc).
Local Notation QQ := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Section j.
Variables (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model).
Variables (ha pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis HAT : at_SM (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C.
Let spv : Z := sp regs0.
Let cnt : Z := ht_cnt (ch_H C).
Let T : Z := ch_T C.
Let tmp : list (Z * Z) := cht_blks C.
Ltac open_HAT :=
pose proof HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hcnt & G15 & G14 & G11 & G27 & G26 & G18 & G20 & G8 & G21 &
Hsl & Hsh & Hfc & Hobj & Hcg & Him & Hcht & Harr & Hinv & HT & HTin & Hpnew & Hfimg & HB);
pose proof HINV as (HJ0 & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent);
destruct HREGS as (G2 & G3 & G4).
Definition kept (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (spv - COLHASH_STK <= a < spv) -> ~ (spv + 72 <= a < spv + 88) -> ~ (spv + 96 <= a < spv + 104) ->
~ (fimg <= a < fimg + N) -> mbyte ubs2segs m a = mbyte ubs2segs memc a.
Definition sm_mem (m : word -> option byte) : Prop :=
JRN Lc Ac m mdc /\ kept m /\ word_mem ubs2segs m (spv + 72) (2 ^ 64 - 1 - bef) /\ word_mem ubs2segs m (spv + 80) cnt /\
word_mem ubs2segs m (spv + 96) fmt.
Definition sl_regs (i : Z) (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 spv /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 20 = Z_to_bv 64 (ch_c C) /\ getr regs 8 = Z_to_bv 64 r /\ getr regs 21 = Z_to_bv 64 2 /\
getr regs 9 = Z_to_bv 64 (sm_cond ha bef) /\ getr regs 19 = Z_to_bv 64 1 /\ getr regs 26 = Z_to_bv 64 N /\
getr regs 27 = Z_to_bv 64 (2 ^ 64 - 1 - fimg) /\ getr regs 25 = Z_to_bv 64 i /\
getr regs 22 = Z_to_bv 64 (fmt * i) /\ getr regs 24 = Z_to_bv 64 (i * sx32v beffmt).
Definition at_SL (i : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
sl_regs i regs /\ getr regs 15 = Z_to_bv 64 img /\ getr regs 14 = Z_to_bv 64 fmt /\ sm_mem m /\ 0 <= i < N.
Definition at_CHs (i : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
sl_regs i regs /\ getr regs 1 = Z_to_bv 64 PC_C /\
getr regs 10 = Z_to_bv 64 (img + fmt * i) /\ getr regs 11 = Z_to_bv 64 (ch_h C) /\ getr regs 12 = Z_to_bv 64 (ch_u C) /\
getr regs 13 = Z_to_bv 64 T /\ getr regs 14 = Z_to_bv 64 fmt /\ sm_mem m /\ 0 <= i < N.
Definition at_SB (i : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
sl_regs i regs /\ getr regs 15 = Z_to_bv 64 img /\ getr regs 14 = Z_to_bv 64 fmt /\ sm_mem m /\ 0 <= i < N.
Definition at_EX (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
getr regs 2 = Z_to_bv 64 spv /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 20 = Z_to_bv 64 (ch_c C) /\ getr regs 8 = Z_to_bv 64 r /\ sm_mem m.
Lemma sm_nf :
RGBA_STK = 24576 /\ RGBA_FRAME = 5168 /\ CHT_SIZE = 48 /\ COLHASH_STK = 64 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\
spv = sp0 regs0 - 5168 /\ alloc_ceiling + 24576 <= sp0 regs0 /\ sp0 regs0 < 2 ^ 63 /\ spv mod 16 = 0 /\
3 <= fmt <= 4 /\ 1 <= N <= 10000 /\ 0 <= ha <= 1 /\ 0 <= cnt < 256 /\ 524309 <= T <= 16777216 /\
(bef <> 0 -> 3 <= beffmt <= 4) /\ 0 <= bef < 2 ^ 64 /\ 0 <= beffmt < 2 ^ 32 /\
4096 <= img /\ img + fmt * N <= alloc_ceiling /\ 4096 <= fimg /\ fimg + N <= alloc_ceiling /\
4096 <= ch_c C /\ ch_c C + 48 <= alloc_ceiling /\ ch_c C mod 16 = 0 /\
4096 <= ch_u C /\ ch_u C + T <= alloc_ceiling /\ 4096 <= ch_h C /\ ch_h C + 3 * T <= alloc_ceiling /\
4096 <= ch_p C /\ ch_p C + 3 * T <= alloc_ceiling /\ 4096 <= ch_x C /\ ch_x C + 4 * T <= alloc_ceiling /\ ch_x C mod 16 = 0 /\
(fimg + N <= img \/ img + fmt * N <= fimg) /\
(fimg + N <= ch_u C \/ ch_u C + T <= fimg) /\ (fimg + N <= ch_h C \/ ch_h C + 3 * T <= fimg) /\
(fimg + N <= ch_p C \/ ch_p C + 3 * T <= fimg) /\ (fimg + N <= ch_x C \/ ch_x C + 4 * T <= fimg) /\
(fimg + N <= ch_c C \/ ch_c C + 48 <= fimg) /\ (ch_c C + 48 <= ch_x C \/ ch_x C + 4 * T <= ch_c C) /\
(bef <> 0 -> 4096 <= bef /\ bef + beffmt * N <= alloc_ceiling /\ (fimg + N <= bef \/ bef + beffmt * N <= fimg) /\ In (bef, beffmt * N) (blocks Lc Ac)) /\
In (fimg, N) (blocks Lc Ac) /\ ~ In (fimg, N) (blocks L A) /\
(forall y, In y (BASE r g N img fmt rest s bef beffmt) -> fimg + N <= fst y \/ fst y + snd y <= fimg) /\
(forall y, In y (BASE r g N img fmt rest s bef beffmt) -> In y (blocks Lc Ac)) /\
4096 <= ch_f C /\ In (ch_f C, 4 * T) (blocks Lc Ac).
Proof.
open_HAT.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ0) as HHc.
pose proof HJ0 as (_ & _ & _ & _ & _ & (HalS & HSTK0 & Hceil & H63 & Hstw) & _).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HCSv : CHT_SIZE = 48) by reflexivity. assert (HCHv : COLHASH_STK = 64) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
pose proof (ts_chain_bounds _ HTin) as HTb.
destruct Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hc1 & _) & _).
assert (Hsp16 : spv mod 16 = 0).
{ subst spv. unfold sp, RGBA_FRAME. replace (sp0 regs0 - 5168) with (sp0 regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (Hib : img_block img fmt N = [(img, fmt * N)]) by (unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
assert (INb : forall x, In x (BASE r g N img fmt rest s bef beffmt) -> In x (blocks Lc Ac)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; left; exact Hx]. }
assert (INt : forall x, In x ([(pnew, fmt * N); (fimg, N)] ++ tmp) -> In x (blocks Lc Ac)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HB | apply in_app_iff; right; exact Hx]. }
assert (Himg : In (img, fmt * N) (BASE r g N img fmt rest s bef beffmt)).
{ unfold BASE. rewrite Hib. right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. left. reflexivity. }
assert (Hfim : In (fimg, N) ([(pnew, fmt * N); (fimg, N)] ++ tmp)) by (right; left; reflexivity).
assert (Hcin : In (ch_c C, CHT_SIZE) tmp) by (subst tmp; left; reflexivity).
assert (Huin : In (ch_u C, T) tmp) by (subst tmp T; right; right; right; left; reflexivity).
assert (Hhin : In (ch_h C, 3 * T) tmp) by (subst tmp T; right; right; left; reflexivity).
assert (Hpin : In (ch_p C, 3 * T) tmp) by (subst tmp T; right; right; right; right; left; reflexivity).
assert (Hxin : In (ch_x C, 4 * T) tmp) by (subst tmp T; right; right; right; right; right; left; reflexivity).
assert (Hfin' : In (ch_f C, 4 * T) tmp) by (subst tmp T; right; left; reflexivity).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_f C) (4 * T) HHc (INt _ ltac:(apply in_app_iff; right; exact Hfin')) ltac:(lia)) as (Rff0 & _ & _).
assert (INt' : forall x, In x tmp -> In x ([(pnew, fmt * N); (fimg, N)] ++ tmp)) by (intros x Hx; apply in_app_iff; right; exact Hx).
assert (HB1 : Permutation (blocks Lc Ac) (keep2 pnew fimg ++ tmp)) by (eapply Permutation_trans; [exact HB|]; rewrite <- app_assoc; apply Permutation_refl).
assert (SEPt : forall y, In y tmp -> fimg + N <= fst y \/ fst y + snd y <= fimg).
{ intros y Hy. pose proof (heap_sep_app' API Lc Ac memc mdc (keep2 pnew fimg) tmp (fimg, N) y HHc HB1 ltac:(apply in_app_iff; right; right; left; reflexivity) Hy) as X. cbn [fst snd] in X. exact X. }
assert (SEPb : forall y, In y (BASE r g N img fmt rest s bef beffmt) -> fimg + N <= fst y \/ fst y + snd y <= fimg).
{ intros y Hy. pose proof (heap_sep_app' API Lc Ac memc mdc (BASE r g N img fmt rest s bef beffmt) ([(pnew, fmt * N); (fimg, N)] ++ tmp) y (fimg, N) HHc HB Hy Hfim) as X. cbn [fst snd] in X. lia. }
assert (SEPcx : ch_c C + 48 <= ch_x C \/ ch_x C + 4 * T <= ch_c C).
{ pose proof (heap_sep_app' API Lc Ac memc mdc (keep2 pnew fimg ++ [(ch_c C, CHT_SIZE)]) (cht_blocks (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_T C)) (ch_c C, CHT_SIZE) (ch_x C, 4 * T) HHc
ltac:(eapply Permutation_trans; [exact HB1|]; subst tmp; unfold cht_blks; rewrite <- !app_assoc; cbn [app]; apply Permutation_refl)
ltac:(apply in_app_iff; right; left; reflexivity) ltac:(subst T; right; right; right; right; left; reflexivity)) as X.
cbn [fst snd] in X. rewrite HCSv in X. exact X. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img (fmt * N) HHc (INb _ Himg) ltac:(nia)) as (Ri0 & Ri1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc fimg N HHc (INt _ Hfim) ltac:(lia)) as (Rf0 & Rf1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc (INt _ (INt' _ Hcin)) ltac:(lia)) as (Rc0 & Rc1 & Rc16).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_u C) T HHc (INt _ (INt' _ Huin)) ltac:(lia)) as (Ru0 & Ru1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_h C) (3 * T) HHc (INt _ (INt' _ Hhin)) ltac:(lia)) as (Rh0 & Rh1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_p C) (3 * T) HHc (INt _ (INt' _ Hpin)) ltac:(lia)) as (Rp0 & Rp1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_x C) (4 * T) HHc (INt _ (INt' _ Hxin)) ltac:(lia)) as (Rx0 & Rx1 & Rx16).
pose proof (SEPb _ Himg) as Si. cbn [fst snd] in Si.
pose proof (SEPt _ Huin) as Su. pose proof (SEPt _ Hhin) as Sh. pose proof (SEPt _ Hpin) as Sp. pose proof (SEPt _ Hxin) as Sx. pose proof (SEPt _ Hcin) as Sc.
cbn [fst snd] in Su, Sh, Sp, Sx, Sc. rewrite HCSv in Sc.
assert (Hbefb : bef <> 0 -> 4096 <= bef /\ bef + beffmt * N <= alloc_ceiling /\ (fimg + N <= bef \/ bef + beffmt * N <= fimg) /\ In (bef, beffmt * N) (blocks Lc Ac)).
{ intros Hb0. assert (Hbin : In (bef, beffmt * N) (BASE r g N img fmt rest s bef beffmt)).
{ unfold BASE. right. apply in_app_iff; right. apply in_app_iff; left. unfold optb. rewrite (proj2 (Z.eqb_neq bef 0) Hb0). left. reflexivity. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc bef (beffmt * N) HHc (INb _ Hbin) ltac:(clear -Hbef Hb0 HN1; destruct Hbef as [|[-> | ->]]; lia)) as (Rb0 & Rb1 & _).
pose proof (SEPb _ Hbin) as Sb. cbn [fst snd] in Sb. split; [exact Rb0|]. split; [exact Rb1|]. split; [exact Sb | exact (INb _ Hbin)]. }
pose proof (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc (BASE r g N img fmt rest s bef beffmt) ([(pnew, fmt * N); (fimg, N)] ++ tmp) fimg N HHc HB HBent ltac:(intros x Hx; exact Hx) Hfim ltac:(lia)) as [Hf_in Hf_tmp].
assert (Hbef0 : 0 <= bef < 2 ^ 64).
{ destruct (obj_at_nth ubs2segs memc r LAY_Rgb _ 9 (48, 8%N) bef Hobj eq_refl eq_refl) as [_ Hr9]. clear -Hr9. cbn in Hr9. lia. }
assert (Hbf2 : 0 <= beffmt < 2 ^ 32).
{ destruct (obj_at_nth ubs2segs memc r LAY_Rgb _ 10 (56, 4%N) beffmt Hobj eq_refl eq_refl) as [_ Hr10]. clear -Hr10. cbn in Hr10. lia. }
assert (E1 : spv = sp0 regs0 - 5168) by (subst spv; unfold sp; rewrite HFv; reflexivity).
rewrite HRv in Hceil. rewrite HCSv in Rc1.
assert (F1 : 3 <= fmt <= 4) by (clear -Hfmt; lia).
assert (F2 : 1 <= N <= 10000) by (clear -HN1 HNmax HNMv; lia).
assert (F3 : 0 <= ha <= 1) by (clear -Hha; lia).
assert (F4 : 0 <= cnt < 256) by (subst cnt; clear -Hc1 Hcnt; lia).
assert (F5 : bef <> 0 -> 3 <= beffmt <= 4) by (clear -Hbef; intros Hb0; lia).
pose proof (INt _ ltac:(apply in_app_iff; right; exact Hfin')) as Hff_in.
subst cnt T.
repeat match goal with |- _ /\ _ => split end; try assumption; clear -F1 F2 F3 F4 HTb Hbf2 Hbef0 Hac; lia.
Qed.
Ltac open_NF :=
pose proof sm_nf as (HRv & HFv & HCSv & HCHv & Hac & Esp & Hceil & H63 & Hsp16 & Ffmt & FN & Fha & Fcnt & FT & Fbf & Fbef0 & Fbf2 &
Ri0 & Ri1 & Rf0 & Rf1 & Rc0 & Rc1 & Rc16 & Ru0 & Ru1 & Rh0 & Rh1 & Rp0 & Rp1 & Rx0 & Rx1 & Rx16 &
Si & Su & Sh & Sp & Sx & Sc & Scx & Hbefb & Hf_in & Hf_tmp & SEPB & INB & Rff0 & Hff_in).
Lemma wm_frameS : forall (m m' : word -> option byte) a v,
word_mem ubs2segs m a v -> (forall i, 0 <= i < 8 -> mbyte ubs2segs m' (a + i) = mbyte ubs2segs m (a + i)) -> word_mem ubs2segs m' a v.
Proof. intros m m' a v Hw Hf k Hk. rewrite Hf by lia. apply Hw. exact Hk. Qed.
Lemma sx32v_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= sx32v v < 2 ^ 64.
Proof. intros v Hv. unfold sx32v. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma kept_facts : forall m, kept m ->
word_mem ubs2segs m (spv + 88) bef /\ word_mem ubs2segs m (spv + 104) (sx32v beffmt) /\ word_mem ubs2segs m (spv + 64) (sm_notha ha) /\
word_mem ubs2segs m (spv + 24) pnew /\ word_mem ubs2segs m (spv + 48) fimg /\
word_mem ubs2segs m (spv + 112) img /\ word_mem ubs2segs m (spv + 120) fmt /\
arr8 ubs2segs m img imgl /\ arr8 ubs2segs m (ch_u C) (ht_used (ch_H C)) /\ arr8 ubs2segs m (ch_h C) (ht_keys (ch_H C)) /\
arr32 ubs2segs m (ch_x C) (ht_colidx (ch_H C)) /\ arr8 ubs2segs m (ch_p C) (ht_pal (ch_H C)) /\
word_mem ubs2segs m (ch_c C + 32) (ch_x C) /\ word_mem ubs2segs m (ch_c C + 24) (ch_p C) /\
word_mem ubs2segs m (ch_c C + 8) (ch_h C) /\ word_mem ubs2segs m (ch_c C + 16) (ch_u C) /\
val_mem ubs2segs m (ch_c C + 44) 4 T /\ val_mem ubs2segs m (ch_c C + 40) 4 cnt.
Proof.
intros m Hk. open_HAT. open_NF.
pose proof Hsl as (S8 & S16 & S24 & S48). pose proof Hsh as (S64 & S88 & S104 & S112 & S120).
unfold slot, SL_N, SL_cfp, SL_new, SL_fimg, SL_64, SL_88, SL_104, SL_112, SL_120 in *.
destruct Harr as (Af & Ah & Au & Ap & Ax). destruct Him as [Himg Hlen].
destruct Hinv as ((L1 & L2 & L3 & L4 & L5) & _). rewrite HT in *.
destruct (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 1 (8, 8%N) (ch_h C) Hcht eq_refl eq_refl) as [Vh _].
destruct (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 2 (16, 8%N) (ch_u C) Hcht eq_refl eq_refl) as [Vu _].
destruct (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 3 (24, 8%N) (ch_p C) Hcht eq_refl eq_refl) as [Vp _].
destruct (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 4 (32, 8%N) (ch_x C) Hcht eq_refl eq_refl) as [Vx _].
destruct (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 5 (40, 4%N) (ht_cnt (ch_H C)) Hcht eq_refl eq_refl) as [Vcnt _].
destruct (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 6 (44, 4%N) (ch_T C) Hcht eq_refl eq_refl) as [VT _].
cbn [fst snd N.to_nat] in Vh, Vu, Vp, Vx, Vcnt, VT. apply val_mem_word_mem in Vh. apply val_mem_word_mem in Vu. apply val_mem_word_mem in Vp. apply val_mem_word_mem in Vx.
assert (KS : forall off, 0 <= off -> off + 8 <= 5168 -> ~ (off < 88 /\ 72 < off + 8) -> ~ (off < 104 /\ 96 < off + 8) ->
forall i, 0 <= i < 8 -> mbyte ubs2segs m (spv + off + i) = mbyte ubs2segs memc (spv + off + i)).
{ intros off H0 H1 H2 H3 i Hi. apply Hk; clear -H0 H1 H2 H3 Hi Hac Esp Hceil H63 Rf1 HCHv; lia. }
assert (KH : forall b n, 4096 <= b -> b + n <= alloc_ceiling -> (fimg + N <= b \/ b + n <= fimg) -> forall a, b <= a < b + n -> mbyte ubs2segs m a = mbyte ubs2segs memc a).
{ intros b n Hb0 Hb Hs a Ha. apply Hk; clear -Hb0 Hb Hs Ha Hac Esp Hceil H63 Rf0 HCHv; lia. }
assert (KV4 : forall off v, 0 <= off -> off + 4 <= 48 -> val_mem ubs2segs memc (ch_c C + off) 4 v -> val_mem ubs2segs m (ch_c C + off) 4 v).
{ intros off v H0 H1 Hv k Hk'. rewrite (KH (ch_c C) 48 Rc0 Rc1 Sc) by lia. apply Hv. exact Hk'. }
split; [eapply wm_frameS; [exact S88 | apply KS; lia]|].
split; [eapply wm_frameS; [exact S104 | apply KS; lia]|].
split; [eapply wm_frameS; [exact S64 | apply KS; lia]|].
split; [eapply wm_frameS; [exact S24 | apply KS; lia]|].
split; [eapply wm_frameS; [exact S48 | apply KS; lia]|].
split; [eapply wm_frameS; [exact S112 | apply KS; lia]|].
split; [eapply wm_frameS; [exact S120 | apply KS; lia]|].
split; [eapply arr8_frame; [exact Himg | rewrite Hlen; apply (KH img (fmt * N)); [exact Ri0 | exact Ri1 | exact Si]] |].
split; [eapply arr8_frame; [exact Au | rewrite L1; apply (KH (ch_u C) T); [exact Ru0 | exact Ru1 | exact Su]] |].
split; [eapply arr8_frame; [exact Ah | rewrite L2; apply (KH (ch_h C) (3 * T)); [exact Rh0 | exact Rh1 | exact Sh]] |].
split; [eapply arr32_frame; [exact Ax | rewrite L4; apply (KH (ch_x C) (4 * T)); [exact Rx0 | exact Rx1 | exact Sx]] |].
split; [eapply arr8_frame; [exact Ap | rewrite L5; apply (KH (ch_p C) (3 * T)); [exact Rp0 | exact Rp1 | exact Sp]] |].
split; [eapply wm_frameS; [exact Vx | intros i Hi; apply (KH (ch_c C) 48 Rc0 Rc1 Sc); lia]|].
split; [eapply wm_frameS; [exact Vp | intros i Hi; apply (KH (ch_c C) 48 Rc0 Rc1 Sc); lia]|].
split; [eapply wm_frameS; [exact Vh | intros i Hi; apply (KH (ch_c C) 48 Rc0 Rc1 Sc); lia]|].
split; [eapply wm_frameS; [exact Vu | intros i Hi; apply (KH (ch_c C) 48 Rc0 Rc1 Sc); lia]|].
split; [apply (KV4 44 T); [lia | lia | exact VT] | apply (KV4 40 cnt); [lia | lia | exact Vcnt]].
Qed.
Lemma store_facts : forall i m, sm_mem m -> 0 <= i < N ->
wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) (fimg + i) /\ writable_at ubs2segs m (fimg + i).
Proof.
intros i m (HJ & _) Hi. open_NF. split.
- right. right. exists fimg, N. split; [exact Hf_in|]. split; [exact Hf_tmp | lia].
- apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac m mdc fimg N i (proj1 HJ) Hf_in ltac:(lia))).
Qed.
Lemma store_post : forall i regs m regs' m',
sl_regs i regs -> sm_mem m -> 0 <= i < N -> JRN Lc Ac m' mdc ->
(forall x, 0 <= x < 2 ^ 64 -> x <> fimg + i -> mbyte ubs2segs m' x = mbyte ubs2segs m x) ->
getr regs' 25 = Z_to_bv 64 (i + 1) -> getr regs' 22 = Z_to_bv 64 (fmt * i + fmt) ->
getr regs' 24 = Z_to_bv 64 (i * sx32v beffmt + sx32v beffmt) ->
getr regs' 15 = Z_to_bv 64 img -> getr regs' 14 = Z_to_bv 64 fmt ->
(forall rr : reg, In rr smj_A2Z_KEEP -> getr regs' rr = getr regs rr) ->
(i + 1 < N -> at_SL (i + 1) regs' m') /\ at_EX regs' m'.
Proof.
intros i regs m regs' m' HR (HJ & Hk & W72 & W80 & W96) Hi HJ' Hfr H25 H22 H24 H15 H14 HK'. open_NF.
pose proof HR as (R2 & R3 & R4 & R20 & R8 & R21 & R9 & R19 & R26 & R27 & R25 & R22 & R24).
assert (FR : forall off v, 0 <= off -> off + 8 <= 5168 -> word_mem ubs2segs m (spv + off) v -> word_mem ubs2segs m' (spv + off) v).
{ intros off v H0 H1 Hw. eapply wm_frameS; [exact Hw|]. intros k Hk'. apply Hfr; clear -H0 H1 Hk' Esp Hceil H63 Hac Rf1 Hi; lia. }
assert (SM' : sm_mem m').
{ split; [exact HJ'|]. split.
- intros a Ha W1 W2 W3 W4. rewrite (Hfr a Ha ltac:(clear -W4 Hi; lia)). apply Hk; assumption.
- split; [apply FR; [lia | lia | exact W72]|]. split; [apply FR; [lia | lia | exact W80] | apply FR; [lia | lia | exact W96]]. }
unfold at_SL, at_EX, sl_regs.
rewrite !(HK' 2%bv), !(HK' 3%bv), !(HK' 4%bv), !(HK' 20%bv), !(HK' 8%bv), !(HK' 21%bv), !(HK' 9%bv), !(HK' 19%bv), !(HK' 26%bv), !(HK' 27%bv)
by (apply in_bv5_sm; vm_compute; reflexivity).
rewrite H25, H22, H24.
split.
- intros Hlt. split; [| split; [exact H15 | split; [exact H14 | split; [exact SM' | lia]]]].
repeat match goal with |- _ /\ _ => split end; first [assumption | f_equal; ring].
- repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
Lemma SB_SR : forall i regs m,
at_SB i regs m ->
(forall regs' m', at_SL (i + 1) regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_SL) m' (seg_rom ubs2segs)) mdc) QQ) ->
(forall regs' m', at_EX regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_EX) m' (seg_rom ubs2segs)) mdc) QQ) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_SB) m (seg_rom ubs2segs)) mdc) QQ.
Proof.
intros i regs m (HR & Q15 & Q14 & SM & Hi) KSL KEX. pose proof SM as (HJ & Hk & _ & _ & W96). open_NF.
pose proof HR as (R2 & R3 & R4 & R20 & R8 & R21 & R9 & R19 & R26 & R27 & R25 & R22 & R24).
pose proof (kept_facts m Hk) as (_ & V104 & _ & _ & V48 & _).
destruct (store_facts i m SM Hi) as [Hwb Hwa].
assert (CONT : forall (last : bool), (if last then i + 1 = N else i + 1 <> N) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_SB) m (seg_rom ubs2segs)) mdc) QQ).
{ intros last Hlast.
eapply (SB_stretch API IMG last regs m RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac mdc spv fimg i N (fmt * i) (i * sx32v beffmt) fmt (sx32v beffmt));
[ exact HJ | exact Hwb | exact Hwa | exact R2 | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16
| exact V48 | exact Rf0 | exact Rf1 | exact R25 | exact Hi | exact R26 | exact R27 | exact Hlast
| exact W96 | exact V104 | clear -Ffmt; lia | exact (sx32v_range beffmt Fbf2) | exact R22 | exact R24 | ].
intros regs' m' HJ' Hfr H25 H22 H24 HK'.
destruct (store_post i regs m regs' m' HR SM Hi HJ' Hfr H25 H22 H24) as [PSL PEX];
[ rewrite (HK' 15%bv) by (apply in_bv5_sm; vm_compute; reflexivity); exact Q15
| rewrite (HK' 14%bv) by (apply in_bv5_sm; vm_compute; reflexivity); exact Q14
| intros rr Hrr; apply HK'; exact (in_subq smj_A2Z_KEEP SB_KEEP ltac:(vm_compute; reflexivity) rr Hrr) | ].
destruct last; [apply KEX; exact PEX | apply KSL; apply PSL; clear -Hlast Hi; lia]. }
destruct (Z.eq_dec (i + 1) N) as [Hl | Hl]; [exact (CONT true Hl) | exact (CONT false Hl)].
Qed.
Definition SLR : list reg := [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27]%bv.
Lemma sl_regs_transport : forall i (regs regs' : bvmap 5 word),
sl_regs i regs -> (forall rr : reg, In rr SLR -> getr regs' rr = getr regs rr) -> sl_regs i regs'.
Proof.
intros i regs regs' HR HK. unfold sl_regs in *.
rewrite !(HK 2%bv), !(HK 3%bv), !(HK 4%bv), !(HK 20%bv), !(HK 8%bv), !(HK 21%bv), !(HK 9%bv), !(HK 19%bv), !(HK 26%bv), !(HK 27%bv), !(HK 25%bv), !(HK 22%bv), !(HK 24%bv)
by (apply in_bv5_sm; vm_compute; reflexivity).
exact HR.
Qed.
Lemma CH_SR : forall i regs m,
at_CHs i regs m ->
(forall regs' m', at_SB i regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_SB) m' (seg_rom ubs2segs)) mdc) QQ) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_col_hash) m (seg_rom ubs2segs)) mdc) QQ.
Proof.
intros i regs m (HR & R1 & R10 & R11 & R12 & R13 & R14 & SM & Hi) KSB. pose proof SM as (HJ & Hk & W72 & W80 & W96). open_HAT. open_NF.
pose proof HR as (R2 & R3 & R4 & R20 & R8 & R21 & R9 & R19 & R26 & R27 & R25 & R22 & R24).
pose proof (kept_facts m Hk) as (V88 & V104 & V64 & V24 & V48 & V112 & V120 & Aimg & Au & Ah & Ax & Ap & Vx & Vp & Vh & Vu & VT & Vcnt).
destruct Him as [_ Hlen]. pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & _).
destruct (pixel_of_img ubs2segs m img imgl fmt N i Aimg Hlen Hfmt Hi) as (c & op & Hpix).
destruct (find_slot_exists (ch_H C) (ch_ent C) Hinv c) as (h & Hfs & Hh). rewrite HT in Hh.
assert (Hspz : spZ regs = spv) by (unfold spZ; rewrite R2; apply unsigned_lit_small; clear -Esp Hceil H63 Hac; lia).
assert (Hfi : fmt * i + fmt <= fmt * N) by (clear -Hi Ffmt; nia).
assert (Hfi0 : 0 <= fmt * i) by (clear -Hi Ffmt; nia).
eapply SR_bind.
{ eapply (CH RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac m mdc regs (img + fmt * i) (ch_h C) (ch_u C) T fmt
(ht_used (ch_H C)) (ht_keys (ch_H C)) c op h);
[ exact HJ | rewrite R1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspz; exact Hsp16
| rewrite Hspz; clear -Esp HRv HCHv; lia | rewrite Hspz; clear -Esp; lia
| exact R10 | exact R11 | exact R12 | exact R13 | exact R14 | exact Hpix | exact Au | exact Ah
| exact (eq_trans L1 HT) | rewrite L2, HT; reflexivity | clear -FT; lia
| clear -Ri0 Hfi0; lia | clear -Ri1 Hfi; lia | exact Ru0 | exact Ru1 | exact Rh0 | exact Rh1
| intros _; replace T with (ht_T (ch_H C)) by (exact HT); rewrite <- probe_of_htab; exact Hfs ]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Hres & Hfr2). rewrite R1.
rewrite Hspz in Hfr2.
assert (FR2 : forall off v, 0 <= off -> off + 8 <= 5168 -> word_mem ubs2segs m (spv + off) v -> word_mem ubs2segs mem2 (spv + off) v).
{ intros off v H0 H1 Hw. eapply wm_frameS; [exact Hw|]. intros k Hk'. apply Hfr2; clear -H0 H1 Hk' Esp Hceil H63 Hac HCHv; lia. }
assert (SM2 : sm_mem mem2).
{ split; [exact HJ2|]. split.
- intros a Ha W1 W2 W3 W4. rewrite (Hfr2 a Ha W1). apply Hk; assumption.
- split; [apply FR2; [lia | lia | exact W72]|]. split; [apply FR2; [lia | lia | exact W80] | apply FR2; [lia | lia | exact W96]]. }
assert (RK : forall rr : reg, In rr SLR -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. apply (regs_preserved_in _ _ rr HP2). exact (in_subq SLR CALLEE_SAVED ltac:(vm_compute; reflexivity) rr Hrr). }
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)) as (Hh2 & Hl2 & _).
pose proof (kept_facts mem2 (proj1 (proj2 SM2))) as (_ & _ & _ & _ & _ & V112' & V120' & _ & _ & _ & Ax' & _ & Vx' & _).
pose proof SM2 as (_ & _ & _ & W80' & _).
assert (R2' : getr regs2 2 = Z_to_bv 64 spv) by (rewrite (RK 2%bv ltac:(cbv; tauto)); exact R2).
destruct op.
-
destruct (arr32_getz ubs2segs mem2 (ch_x C) (ht_colidx (ch_H C)) h Ax' ltac:(rewrite L4, HT; exact Hh)) as [Vv Rv].
destruct (CI_stretch regs2 mem2 spv img fmt h (ch_c C) (ch_x C) (getz (ht_colidx (ch_H C)) h)) as (regs3 & Hms & Q15 & Q14 & HK3);
[ exact R2' | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact V112' | exact V120'
| clear -Ri0 Ri1 Hac Ffmt FN; nia | clear -Ffmt; lia
| exact Hres | clear -Hh FT; lia
| rewrite (RK 20%bv ltac:(cbv; tauto)); exact R20 | exact Rc0 | exact Rc1
| exact Vx' | exact Rx0 | clear -Rx1 Hh; lia | | exact Vv | exact Rv | clear -Scx Hh; lia | ].
+ clear -Rx16 Rx0. pose proof (Z.div_mod (ch_x C) 16 ltac:(lia)) as Hdm. rewrite Rx16 in Hdm. rewrite Hdm. replace (16 * (ch_x C / 16) + 0) with ((4 * (ch_x C / 16)) * 4) by lia. apply Z.mod_mul. lia.
+ eapply SR_msteps; [exact Hh2 | exact Hl2 | exact Hms |].
apply KSB. split; [| split; [exact Q15 | split; [exact Q14 | split; [exact SM2 | exact Hi]]]].
apply (sl_regs_transport i regs regs3); [exact HR|]. intros rr Hrr. rewrite (HK3 rr) by (exact (in_subq SLR KEEP2 ltac:(vm_compute; reflexivity) rr Hrr)). apply RK. exact Hrr.
-
destruct (CT_stretch regs2 mem2 spv img fmt cnt) as (regs3 & Hms & Q15 & Q14 & HK3);
[ exact R2' | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact Hres | exact W80' | exact V112' | exact V120'
| clear -Fcnt; lia | clear -Ri0 Ri1 Hac Ffmt FN; nia | clear -Ffmt; lia | ].
eapply SR_msteps; [exact Hh2 | exact Hl2 | exact Hms |].
apply KSB. split; [| split; [exact Q15 | split; [exact Q14 | split; [exact SM2 | exact Hi]]]].
apply (sl_regs_transport i regs regs3); [exact HR|]. intros rr Hrr. rewrite (HK3 rr) by (exact (in_subq SLR KEEP2 ltac:(vm_compute; reflexivity) rr Hrr)). apply RK. exact Hrr.
Qed.
Lemma SL_SR : forall i regs m,
at_SL i regs m ->
(forall regs' m', at_CHs i regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 ubs2_A_col_hash) m' (seg_rom ubs2segs)) mdc) QQ) ->
(forall regs' m', at_SL (i + 1) regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_SL) m' (seg_rom ubs2segs)) mdc) QQ) ->
(forall regs' m', at_EX regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_EX) m' (seg_rom ubs2segs)) mdc) QQ) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_SL) m (seg_rom ubs2segs)) mdc) QQ.
Proof.
intros i regs m (HR & Q15 & Q14 & SM & Hi) KCH KSL KEX. pose proof SM as (HJ & Hk & W72 & W80 & W96). open_NF.
pose proof HR as (R2 & R3 & R4 & R20 & R8 & R21 & R9 & R19 & R26 & R27 & R25 & R22 & R24).
pose proof (kept_facts m Hk) as (V88 & V104 & V64 & V24 & V48 & V112 & V120 & Aimg & Au & Ah & Ax & Ap & Vx & Vp & Vh & Vu & VT & Vcnt).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ fmt * N < 2 ^ 31) by (clear -Hi Ffmt FN; nia).
assert (TOCH : forall regs4,
getr regs4 1 = Z_to_bv 64 PC_C -> getr regs4 10 = Z_to_bv 64 (img + fmt * i) -> getr regs4 11 = Z_to_bv 64 (ch_h C) -> getr regs4 12 = Z_to_bv 64 (ch_u C) ->
getr regs4 13 = Z_to_bv 64 T -> getr regs4 14 = Z_to_bv 64 fmt ->
(forall rr : reg, In rr SLR -> getr regs4 rr = getr regs rr) ->
SR ubs2segs (mkCfg (mkst regs4 (Z_to_bv 64 ubs2_A_col_hash) m (seg_rom ubs2segs)) mdc) QQ).
{ intros regs4 T1 T10 T11 T12 T13 T14 TK. apply KCH.
split; [exact (sl_regs_transport i regs regs4 HR TK)|]. split; [exact T1|]. split; [exact T10|].
split; [exact T11|]. split; [exact T12|]. split; [exact T13|]. split; [exact T14|]. split; [exact SM | exact Hi]. }
unfold sm_cond in R9. destruct ((ha =? 0) && negb (bef =? 0)) eqn:Ec.
-
apply andb_prop in Ec as [E1 E2]. apply Z.eqb_eq in E1. apply negb_true_iff in E2. apply Z.eqb_neq in E2.
destruct (Hbefb E2) as (Rb0 & Rb1 & Sb & Hbin). pose proof (Fbf E2) as Fb.
assert (R24b : getr regs 24 = Z_to_bv 64 (i * beffmt)) by (rewrite R24, (sx32v_small beffmt) by (clear -Fb; lia); reflexivity).
assert (Hbi : 0 <= i * beffmt /\ i * beffmt + 3 <= beffmt * N /\ beffmt * N < 2 ^ 31) by (clear -Hi Fb FN; nia).
destruct (SLA1_stretch regs m spv (fmt * i) (i * beffmt) img bef) as (regs2 & Hms & Hra & Ha0 & Ha1 & Ha2 & Q23' & Q18' & HK2);
[ exact R2 | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact R9 | exact R19 | exact R22 | clear -Hfi Ffmt; lia
| exact R24b | clear -Hbi; lia | exact Q15 | exact Ri0 | clear -Ri1 Hac Hfi Ffmt; lia | exact W72 | exact V88 | clear -Rb0; lia
| clear -Rb0 Rb1 Hac Hbi; lia | ].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
destruct (rdn_of_bytes ubs2segs m 3 (img + fmt * i)) as (bs1 & Hbs1 & Hl1);
[ intros k Hk'; rewrite <- Z.add_assoc; destruct (arr8_getz ubs2segs m img imgl (fmt * i + k) Aimg) as [Bk _];
[open_HAT; destruct Him as [_ Hlen]; rewrite Hlen; clear -Hk' Hfi Ffmt; lia | rewrite Bk; eexists; reflexivity]
| clear -Ri0 Hfi; lia | clear -Ri1 Hfi Hac Ffmt; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | ].
destruct (rdn_of_bytes ubs2segs m 3 (bef + i * beffmt)) as (bs2 & Hbs2 & Hl2);
[ intros k Hk'; rewrite <- Z.add_assoc; apply (present_mbyte ubs2_msyms);
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac m mdc bef (beffmt * N) (i * beffmt + k) (proj1 HJ) Hbin ltac:(clear -Hk' Hbi; cbn in Hk'; lia)))
| clear -Rb0 Hbi; lia | clear -Rb1 Hbi Hac; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | ].
destruct (ubs2_bcmp bs1 bs2 (Z_to_bv 64 (img + fmt * i)) (Z_to_bv 64 (bef + i * beffmt)) (Z_to_bv 64 3) m (seg_rom ubs2segs) regs2 Ha0 Ha1 Ha2)
as (regs3 & Hms3 & Hres & Hfr3);
[ rewrite Hl1; reflexivity | rewrite Hl1, Hl2; reflexivity | rewrite Hl1; exact Hbs1 | rewrite Hl1; exact Hbs2
| rewrite Hl1, unsigned_lit_small; clear -Ri0 Ri1 Hfi Hac Ffmt; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| rewrite Hl1, unsigned_lit_small; clear -Rb0 Rb1 Hbi Hac; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | ].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms3 |].
replace (v_jalr (getr regs2 1) 0) with (Z_to_bv 64 PC_A2) by (rewrite Hra; symmetry; apply ret_ok_even; vm_compute; reflexivity).
assert (RK3 : forall rr : reg, In rr SLR -> getr regs3 rr = getr regs rr).
{ intros rr Hrr. rewrite (Hfr3 rr) by (intros ->; vm_compute in Hrr; clear -Hrr; intuition discriminate).
apply HK2. exact (in_subq SLR SL_KEEP ltac:(vm_compute; reflexivity) rr Hrr). }
assert (RK3_23 : getr regs3 23 = Z_to_bv 64 (img + fmt * i)) by (rewrite (Hfr3 23%bv) by (intros HH0; discriminate HH0); exact Q23').
assert (RK3_18 : getr regs3 18 = Z_to_bv 64 (fmt * i)) by (rewrite (Hfr3 18%bv) by (intros HH0; discriminate HH0); exact Q18').
assert (R2' : getr regs3 2 = Z_to_bv 64 spv) by (rewrite (RK3 2%bv ltac:(cbv; tauto)); exact R2).
destruct (Z.eq_dec (bv_unsigned (getr regs3 10)) 0) as [Hz | Hnz].
+
assert (Hr10 : getr regs3 10 = Z_to_bv 64 0) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs3 10)), Hz; reflexivity).
destruct (store_facts i m SM Hi) as [Hwb Hwa].
assert (CONT : forall (last : bool), (if last then i + 1 = N else i + 1 <> N) ->
SR ubs2segs (mkCfg (mkst regs3 (Z_to_bv 64 PC_A2) m (seg_rom ubs2segs)) mdc) QQ).
{ intros last Hlast.
eapply (A2z_stretch API IMG last regs3 m RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac mdc spv fimg i N
(fmt * i) (i * sx32v beffmt) fmt (sx32v beffmt) img fmt cnt);
[ exact HJ | exact Hwb | exact Hwa | exact R2' | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact Hr10
| exact V48 | exact Rf0 | exact Rf1 | rewrite (RK3 25%bv ltac:(cbv; tauto)); exact R25 | exact Hi
| rewrite (RK3 26%bv ltac:(cbv; tauto)); exact R26 | rewrite (RK3 27%bv ltac:(cbv; tauto)); exact R27 | exact Hlast
| exact W96 | exact V104 | clear -Ffmt; lia | exact (sx32v_range beffmt Fbf2)
| rewrite (RK3 22%bv ltac:(cbv; tauto)); exact R22 | rewrite (RK3 24%bv ltac:(cbv; tauto)); exact R24
| exact W80 | exact V112 | exact V120 | clear -Fcnt; lia | clear -Ri0 Ri1 Hac Ffmt FN; nia | clear -Ffmt; lia | ].
intros regs' m' HJ' Hfr H25 H22 H24 H15 H14 HK'.
destruct (store_post i regs3 m regs' m' (sl_regs_transport i regs regs3 HR RK3) SM Hi HJ' Hfr H25 H22 H24 H15 H14 HK') as [PSL PEX].
destruct last; [apply KEX; exact PEX | apply KSL; apply PSL; clear -Hlast Hi; lia]. }
destruct (Z.eq_dec (i + 1) N) as [Hl' | Hl']; [exact (CONT true Hl') | exact (CONT false Hl')].
+
destruct (A2nz_stretch regs3 m spv (fmt * i) img fmt (ch_c C) (ch_h C) (ch_u C) T) as (regs4 & Hms4 & T1 & T10 & T11 & T12 & T13 & T14 & HK4);
[ exact R2' | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact Hnz | exact V112 | exact V120 | clear -Ffmt; lia
| rewrite (RK3 19%bv ltac:(cbv; tauto)); exact R19 | exact RK3_18 | exact RK3_23 | clear -Hfi Ffmt; lia | exact Ri0 | clear -Ri1 Hac Hfi Ffmt; lia
| rewrite (RK3 20%bv ltac:(cbv; tauto)); exact R20 | exact Rc0 | exact Rc1
| exact Vh | clear -Rh0 Rh1 Hac FT; lia | exact Vu | clear -Ru0 Ru1 Hac FT; lia | exact VT | clear -FT; lia | ].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms4 |].
apply TOCH; [ exact T1 | exact T10 | exact T11 | exact T12 | exact T13 | exact T14 | ].
intros rr Hrr. rewrite (HK4 rr) by (exact (in_subq SLR KEEP2 ltac:(vm_compute; reflexivity) rr Hrr)). apply RK3. exact Hrr.
-
destruct (SLA0_stretch regs m spv (fmt * i) img fmt (ch_c C) (ch_h C) (ch_u C) T) as (regs4 & Hms4 & T1 & T10 & T11 & T12 & T13 & T14 & HK4);
[ exact R2 | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact R9 | exact R19 | exact R22 | clear -Hfi Ffmt; lia
| exact Q15 | exact Ri0 | clear -Ri1 Hac Hfi Ffmt; lia | exact Q14 | exact R20 | exact Rc0 | exact Rc1
| exact Vh | clear -Rh0 Rh1 Hac FT; lia | exact Vu | clear -Ru0 Ru1 Hac FT; lia | exact VT | clear -FT; lia | ].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms4 |].
apply TOCH; [ exact T1 | exact T10 | exact T11 | exact T12 | exact T13 | exact T14 | ].
intros rr Hrr. apply HK4. exact (in_subq SLR SL_KEEP ltac:(vm_compute; reflexivity) rr Hrr).
Qed.
Lemma loop_SR : forall (n : nat) i regs m,
N - i <= Z.of_nat n -> at_SL i regs m ->
(forall regs' m', at_EX regs' m' -> SR ubs2segs (mkCfg (mkst regs' (Z_to_bv 64 PC_EX) m' (seg_rom ubs2segs)) mdc) QQ) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_SL) m (seg_rom ubs2segs)) mdc) QQ.
Proof.
induction n as [|n IH]; intros i regs m Hn HSL KEX.
- exfalso. destruct HSL as (_ & _ & _ & _ & Hi). clear -Hn Hi. cbn in Hn. lia.
- apply (SL_SR i regs m HSL).
+ intros regs' m' HCH. apply (CH_SR i regs' m' HCH). intros regs'' m'' HSB.
apply (SB_SR i regs'' m'' HSB); [| exact KEX]. intros regs3 m3 HSL3. apply (IH (i + 1) regs3 m3); [clear -Hn; lia | exact HSL3 | exact KEX].
+ intros regs3 m3 HSL3. apply (IH (i + 1) regs3 m3); [clear -Hn; lia | exact HSL3 | exact KEX].
+ exact KEX.
Qed.
Definition ss_MC : sstate := mkSS ubs2_A_memcpy sr_atoms [] None (mkFacts [] [] []).
Definition ss_FC : sstate := mkSS ubs2_A_free_col_hash_table sr_atoms [] None (mkFacts [] [] []).
Lemma EX_SR : forall regs m,
K_FIN (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
at_EX regs m -> SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 PC_EX) m (seg_rom ubs2segs)) mdc) QQ.
Proof.
intros regs m KFIN (R2 & R3 & R4 & R20 & R8 & (HJ & Hk & W72 & W80 & W96)). open_HAT. open_NF.
pose proof (kept_facts m Hk) as (V88 & V104 & V64 & V24 & V48 & V112 & V120 & Aimg & Au & Ah & Ax & Ap & Vx & Vp & Vh & Vu & VT & Vcnt).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & _).
pose proof HJ as (HHm & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
destruct (heap_model _ _ LAWS _ _ _ _ HHm) as (Hh & Hl & _).
destruct (X1_stretch regs m spv (ch_c C) (ch_p C)) as (regs2 & Hms & Hra & Ha0 & Ha1 & Ha2 & HK2);
[ exact R2 | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16 | exact R20 | exact Rc0 | exact Rc1
| exact Vp | clear -Rp0 Rp1 Hac FT; lia | ].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
set (E := Ereg regs2 []).
assert (HS : st_ok ubs2segs E ss_MC (mkst regs2 (Z_to_bv 64 ubs2_A_memcpy) m (seg_rom ubs2segs))).
{ unfold ss_MC. subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | cbn [pairwise_disjoint all_disjoint]; exact I | cbn [atoms_ok]; exact I]. }
change m with (ms_mem (mkst regs2 (Z_to_bv 64 ubs2_A_memcpy) m (seg_rom ubs2segs))) in HJ.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs2_memcpy) with (d := spv + 166) (src := ch_p C) (n := 768);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ha0 | exact Ha1 | exact Ha2 | exact Hra
| apply ret_ok_even; vm_compute; reflexivity | lia | clear -Esp Hceil Hac; lia | clear -Rp0; lia
| clear -Esp H63; lia | clear -Rp1 FT Hac; lia | | | | ].
- intros i Hi. cbn [ms_mem mkst]. apply writable_off_img_present; [clear -Hi Esp Hceil H63 Hac; lia | unfold in_img1; clear -Hi Esp Hceil Hac; lia | apply Hstw; clear -Hi Esp HRv; lia].
- intros i Hi. cbn [ms_mem mkst]. destruct (arr8_getz ubs2segs m (ch_p C) (ht_pal (ch_H C)) i Ap ltac:(rewrite L5, HT; clear -Hi FT; lia)) as [Bi _]. rewrite Bi. eexists. reflexivity.
- right. clear -Rp1 Esp Hceil Hac FT. lia.
- intros a Ha. left. clear -Ha Esp HRv. lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & _ & Hfr3 & Hout3 & Hgr3 & _). clear HS HJ.
cbn [ms_regs ms_mem mkst] in Hfr3, Hout3, Hgr3, HJ3.
assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (spv + 166 <= x < spv + 934) -> mbyte ubs2segs mem3 x = mbyte ubs2segs m x).
{ intros x Hx Hn. unfold mbyte. rewrite (Hout3 (Z_to_bv 64 x)) by (rewrite unsigned_lit_small by exact Hx; clear -Hn; lia). reflexivity. }
assert (R3K : forall rr : reg, In rr [2; 3; 4; 8; 20]%bv -> getr regs3 rr = getr regs2 rr).
{ intros rr Hrr. apply Hfr3. exact (reg_notin_clob [2; 3; 4; 8; 20]%bv MEMCPY_CLOB rr ltac:(vm_compute; reflexivity) Hrr). }
assert (Vcnt3 : val_mem ubs2segs mem3 (ch_c C + 40) 4 cnt).
{ intros k Hk'. rewrite K3 by (clear -Hk' Rc0 Rc1 Hac Esp Hceil; cbn in Hk'; lia). apply Vcnt. exact Hk'. }
destruct (X2_stretch regs3 mem3 (ch_c C) cnt) as (regs4 & Hms4 & Hra4 & Ha4 & H9 & HK4);
[ rewrite (R3K 20%bv ltac:(cbv; tauto)), (HK2 20%bv ltac:(cbv; tauto)); exact R20 | exact Rc0 | exact Rc1 | exact Vcnt3 | clear -Fcnt; lia | ].
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)) as (Hh3 & Hl3 & _).
eapply SR_msteps; [exact Hh3 | exact Hl3 | exact Hms4 |].
set (E1 := Ereg regs4 []).
assert (HS : st_ok ubs2segs E1 ss_FC (mkst regs4 (Z_to_bv 64 ubs2_A_free_col_hash_table) mem3 (seg_rom ubs2segs))).
{ unfold ss_FC. subst E1. apply entry_st_ok; [vm_compute; reflexivity | constructor | cbn [pairwise_disjoint all_disjoint]; exact I | cbn [atoms_ok]; exact I]. }
set (ms := mkst regs4 (Z_to_bv 64 ubs2_A_free_col_hash_table) mem3 (seg_rom ubs2segs)) in *.
assert (Hmm : ms_mem ms = mem3) by reflexivity.
assert (Hr10 : getr (ms_regs ms) 10 = Z_to_bv 64 (ch_c C)).
{ cbn [ms ms_regs mkst]. rewrite Ha4, (R3K 20%bv ltac:(cbv; tauto)), (HK2 20%bv ltac:(cbv; tauto)). exact R20. }
assert (Hr2 : getr (ms_regs ms) 2 = Z_to_bv 64 spv).
{ cbn [ms ms_regs mkst]. rewrite (HK4 2%bv ltac:(cbv; tauto)), (R3K 2%bv ltac:(cbv; tauto)), (HK2 2%bv ltac:(cbv; tauto)). exact R2. }
assert (Hr4 : getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp ubs2_msyms)).
{ cbn [ms ms_regs mkst]. rewrite (HK4 4%bv ltac:(cbv; tauto)), (R3K 4%bv ltac:(cbv; tauto)), (HK2 4%bv ltac:(cbv; tauto)), R4. exact Htp0. }
assert (Hr1 : getr (ms_regs ms) 1 = Z_to_bv 64 PC_X3) by (cbn [ms ms_regs mkst]; exact Hra4).
assert (Hspms : spZ (ms_regs ms) = spv) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; clear -Esp Hceil H63 Hac; lia).
change mem3 with (ms_mem ms) in HJ3.
assert (Hcht3 : obj_at ubs2segs (ms_mem ms) (ch_c C) LAY_Cht [ch_f C; ch_h C; ch_u C; ch_p C; ch_x C; cnt; T]).
{ rewrite Hmm. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact Hcht | reflexivity |].
intros i Hi. rewrite K3 by (clear -Hi Rc0 Rc1 HCSv Hac Esp Hceil; lia). apply Hk; clear -Hi Rc0 Rc1 HCSv Hac Esp Hceil H63 HCHv Sc; lia. }
pose proof HB as HB0.
assert (Hf0 : ch_f C <> 0) by (clear -Rff0; lia). assert (Hh0 : ch_h C <> 0) by (clear -Rh0; lia). assert (Hu0 : ch_u C <> 0) by (clear -Ru0; lia).
assert (Hp0 : ch_p C <> 0) by (clear -Rp0; lia). assert (Hx0 : ch_x C <> 0) by (clear -Rx0; lia).
assert (HB6t : Permutation (blocks Lc Ac) (keep2 pnew fimg ++ tmp)) by (eapply Permutation_trans; [exact HB|]; rewrite <- app_assoc; apply Permutation_refl).
assert (HBc : Permutation (blocks Lc Ac) ((ch_c C, CHT_SIZE) :: optb (ch_f C) (4 * T) ++ optb (ch_h C) (3 * T) ++ optb (ch_u C) T ++ optb (ch_p C) (3 * T) ++ optb (ch_x C) (4 * T) ++ keep2 pnew fimg)).
{ rewrite (optb_nz _ _ Hf0), (optb_nz _ _ Hh0), (optb_nz _ _ Hu0), (optb_nz _ _ Hp0), (optb_nz _ _ Hx0).
eapply Permutation_trans; [exact HB6t|]. subst tmp T. unfold cht_blks, cht_blocks. apply Permutation_app_comm. }
assert (Hsub : forall x0, In x0 (BASE r g N img fmt rest s bef beffmt) -> In x0 (keep2 pnew fimg)) by (intros x0 Hx0'; apply in_app_iff; left; exact Hx0').
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (ch_c C, ch_c C + CHT_SIZE) :: optfp (ch_f C) (4 * T) ++ optfp (ch_h C) (3 * T) ++ optfp (ch_u C) T ++ optfp (ch_p C) (3 * T) ++ optfp (ch_x C) (4 * T))
(K := fun L7 A7 (regs7 : bvmap 5 word) (mem7 : word -> option byte) (md7 : Model) => Permutation (blocks L7 A7) (keep2 pnew fimg));
[ exact HS | reflexivity | exact HJ3 | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | apply Z.lt_le_incl; reflexivity
| rewrite Hspms; clear -Esp HRv; cbv [FREECHT_STK ALLOC_STACK Z.add Z.mul]; lia
| rewrite Hspms; clear -Esp; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (FCHT fx Lc Ac (ms_regs ms) (ms_mem ms) mdc (ch_c C) (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) cnt T
(4 * T) (3 * T) T (3 * T) (4 * T) (keep2 pnew fimg) HPRE1 Hr10 Hcht3 HBc). }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJc7 & HP7 & HB7).
exists L7, A7, regs7, mem7, md7. split; [rewrite Hr1; reflexivity|]. split; [exact HJc7|]. split; [exact HP7 | exact HB7].
- intros a Ha. right.
assert (Ha' : inFP (blocks_fp tmp) a).
{ subst tmp T. unfold cht_blks, cht_blocks. cbn [blocks_fp map fst snd].
unfold optfp in Ha. rewrite (proj2 (Z.eqb_neq _ 0) Hf0), (proj2 (Z.eqb_neq _ 0) Hh0), (proj2 (Z.eqb_neq _ 0) Hu0), (proj2 (Z.eqb_neq _ 0) Hp0), (proj2 (Z.eqb_neq _ 0) Hx0) in Ha.
cbn [app] in Ha. exact Ha. }
apply inFP_blocks_fp in Ha' as (b & n & Hbn & Hab). exists b, n.
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac (ms_mem ms) mdc (keep2 pnew fimg) tmp b n (proj1 HJ3) HB6t HBent Hsub Hbn ltac:(clear -Hab; lia)) as [H1 H2].
split; [exact H1|]. split; [exact H2 | clear -Hab; lia]. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & -> & HJ7 & HJc7 & HP7 & HB7).
cbn [ms_regs ms_mem mkst] in HJc7, HP7, HJ7.
pose proof HJc7 as (HH7 & _ & Hhi7 & _).
assert (KS7 : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + 72 <= x < spv + 88) -> ~ (spv + 96 <= x < spv + 104) ->
~ (spv + 166 <= x < spv + 934) -> mbyte ubs2segs mem7 x = mbyte ubs2segs memc x).
{ intros x Hx Hsx W1 W2 W3. etransitivity; [apply (proj1 (Hhi7 x Hx ltac:(rewrite Hspms; clear -Hsx; lia)))|]. change (mbyte (ms_segs ubs2_msyms)) with (mbyte ubs2segs). rewrite Hmm, (K3 x ltac:(clear -Hx Hac; lia) W3).
apply Hk; [clear -Hx Hac; lia | clear -Hsx HCHv; lia | exact W1 | exact W2 | clear -Hx Rf1; lia]. }
assert (HJc7' : journal ubs2_msyms MR FREECHT_STK (spZ (ms_regs ms)) (blocks_fp tmp) Lc Ac (ms_mem ms) mdc L7 A7 mem7 md7).
{ subst tmp T. unfold cht_blks, cht_blocks. cbn [blocks_fp map fst snd].
pose proof HJc7 as X. unfold optfp in X. rewrite (proj2 (Z.eqb_neq _ 0) Hf0), (proj2 (Z.eqb_neq _ 0) Hh0), (proj2 (Z.eqb_neq _ 0) Hu0), (proj2 (Z.eqb_neq _ 0) Hp0), (proj2 (Z.eqb_neq _ 0) Hx0) in X.
cbn [app] in X. exact X. }
assert (KB7 : forall b n i, In (b, n) (BASE r g N img fmt rest s bef beffmt) -> 0 <= i < n -> mbyte ubs2segs mem7 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b n i Hbn Hi. destruct (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n i (proj1 HJ0) (INB _ Hbn) Hi) as (_ & B0 & B1 & _).
pose proof (SEPB _ Hbn) as Sy. cbn [fst snd] in Sy.
rewrite (kept_across_call API FREECHT_STK (spZ (ms_regs ms)) Lc Ac (ms_mem ms) mdc L7 A7 mem7 md7 (keep2 pnew fimg) tmp (proj1 HJ3) HB6t HJc7' HB7 b n i ltac:(apply Hsub; exact Hbn) Hi).
rewrite Hmm, (K3 (b + i) ltac:(clear -Hi B0 B1 Hac; lia) ltac:(clear -Hi B1 Hac Esp Hceil; lia)).
apply Hk; [clear -Hi B0 B1 Hac; lia | clear -Hi B1 Hac Esp Hceil HCHv; lia | clear -Hi B1 Hac Esp Hceil; lia | clear -Hi B1 Hac Esp Hceil; lia | clear -Hi Sy; lia]. }
assert (R7 : forall rr : reg, In rr [2; 3; 4; 8; 9]%bv -> getr regs7 rr = getr regs4 rr).
{ intros rr Hrr. exact (regs_preserved_in _ _ rr HP7 (in_subq [2; 3; 4; 8; 9]%bv CALLEE_SAVED ltac:(vm_compute; reflexivity) rr Hrr)). }
assert (Hrin : In (r, RGB_SIZE) (BASE r g N img fmt rest s bef beffmt)) by (left; reflexivity).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE (proj1 HJ0) (INB _ Hrin) ltac:(cbv; reflexivity)) as (Rr0 & Rr1 & _).
assert (Hpin : In (pnew, fmt * N) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB0 | apply in_app_iff; right; left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pnew (fmt * N) (proj1 HJ0) Hpin ltac:(clear -Ffmt FN; nia)) as (Rn0 & Rn1 & _).
clear HS.
assert (G2_7 : getr regs7 2 = Z_to_bv 64 spv).
{ rewrite (R7 2%bv ltac:(cbv; tauto)), (HK4 2%bv ltac:(cbv; tauto)), (R3K 2%bv ltac:(cbv; tauto)), (HK2 2%bv ltac:(cbv; tauto)). exact R2. }
destruct (X3_stretch regs7 mem7 spv cnt pnew) as (regs8 & Hms8 & H18 & HK8);
[ exact G2_7 | clear -Esp Hceil; lia | clear -Esp H63; lia | exact Hsp16
| rewrite (R7 9%bv ltac:(cbv; tauto)); exact H9 | clear -Fcnt; lia
| eapply wm_frameS; [exact V24 | intros k Hk'; rewrite (KS7 (spv + 24 + k)) by (clear -Hk' Esp Hceil H63 Hac; lia); symmetry; apply Hk; clear -Hk' Esp Hceil H63 Hac HCHv Rf1; lia]
| clear -Rn0 Rn1 Hac Ffmt FN; nia | ].
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ7)) as (Hh7 & Hl7 & _).
eapply SR_msteps; [exact Hh7 | exact Hl7 | exact Hms8 |].
pose proof HJ7 as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw7) & _).
apply (KFIN fx regs8 L7 A7 mem7 md7 ha pnew fimg cnt Hfrm0).
unfold at_FIN.
split.
{ split; [exact HJ7|]. split; [exact (init_of_live_r API r g bef beffmt s N img fmt rest L7 A7 mem7 md7 _ (proj1 HJ7) HB7)|].
split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc mem7 (spv + 934)); [exact HRA | clear -Esp; lia | clear -Esp Hceil; lia | exact H63 |].
intros x Hx Hsx. apply KS7; [exact Hx | clear -Hsx; lia | clear -Hsx; lia | clear -Hsx; lia | clear -Hsx; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply KS7; clear -Hi Hclo Hchi Esp Hceil Hac; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (HK8 2%bv ltac:(cbv; tauto)); exact G2_7|].
split; [rewrite (HK8 3%bv ltac:(cbv; tauto)), (R7 3%bv ltac:(cbv; tauto)), (HK4 3%bv ltac:(cbv; tauto)), (R3K 3%bv ltac:(cbv; tauto)), (HK2 3%bv ltac:(cbv; tauto)); exact R3
| rewrite (HK8 4%bv ltac:(cbv; tauto)), (R7 4%bv ltac:(cbv; tauto)), (HK4 4%bv ltac:(cbv; tauto)), (R3K 4%bv ltac:(cbv; tauto)), (HK2 4%bv ltac:(cbv; tauto)); exact R4]. }
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [clear -Fcnt; lia|].
split; [rewrite (HK8 9%bv ltac:(cbv; tauto)), (R7 9%bv ltac:(cbv; tauto)); exact H9|].
split; [exact H18|].
split; [rewrite (HK8 8%bv ltac:(cbv; tauto)), (R7 8%bv ltac:(cbv; tauto)), (HK4 8%bv ltac:(cbv; tauto)), (R3K 8%bv ltac:(cbv; tauto)), (HK2 8%bv ltac:(cbv; tauto)); exact R8|].
split. { pose proof Hsl as (S1 & S2 & S3 & S4).
unfold slots_mid, slot, SL_N, SL_cfp, SL_new, SL_fimg in *.
repeat match goal with |- _ /\ _ => split end;
(eapply wm_frameS; [eassumption | intros k Hk'; apply KS7; clear -Hk' Esp Hceil H63 Hac; lia]). }
split. { pose proof Hsh as (S64 & _). unfold slot, SL_64 in *. eapply wm_frameS; [exact S64 | intros k Hk'; apply KS7; clear -Hk' Esp Hceil H63 Hac; lia]. }
split. { unfold fcfg_at, OFF_fcfg, OFF_apal in *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ 32); [exact Hfc | reflexivity |].
intros i Hi. apply KS7; clear -Hi Esp Hceil H63 Hac; lia. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros i Hi. apply (KB7 r RGB_SIZE i Hrin Hi). }
split. { eapply (cgif_at_kept _ _ g s N (BASE r g N img fmt rest s bef beffmt)); [| exact Hcg | exact KB7].
unfold BASE. apply Permutation_cons_app. apply Permutation_refl. }
split. { intros i Hi. unfold OFF_apal. apply (writable_present_high ubs2segs 140735332483072 mem7 _ ubs2_segs_below); [clear -Hi Esp Hceil H63 Hac; lia|].
apply Hstw7. clear -Hi Esp HRv. lia. }
split; [exact Hpnew|]. split; [exact Hfimg|]. exact HB7.
Qed.
End j.
Theorem ubs2_rgbadd_SM : seg_SM API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KFIN regs1 Lc Ac memc mdc ha pnew fimg imgl C HAT. unfold cfg_at.
pose proof HAT as (HINV & (G2 & G3 & G4) & Hfmt & HN1 & Hha & Hcnt & G15 & G14 & G11 & G27 & G26 & G18 & G20 & G8 & G21 & Hsl & Hsh & _).
pose proof HINV as (HJ0 & _).
pose proof (sm_nf regs1 Lc Ac memc mdc ha pnew fimg imgl C HAT) as (HRv & HFv & HCSv & HCHv & Hac & Esp & Hceil & H63 & Hsp16 & Ffmt & FN & Fha & Fcnt & FT & Fbf & Fbef0 & Fbf2 &
Ri0 & Ri1 & Rf0 & Rf1 & _).
pose proof Hsl as (S8 & S16 & S24 & S48). pose proof Hsh as (S64 & S88 & S104 & S112 & S120).
unfold slot, SL_fimg, SL_64, SL_88 in S48, S64, S88.
eapply (P_stretch API IMG regs1 memc RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac mdc (sp regs0) ha bef fmt img fimg N (ht_cnt (ch_H C)));
[ exact HJ0 | clear -Esp HRv; lia | clear -Esp; lia | exact Hsp16 | exact G2 | exact G11 | exact G14 | exact G15 | exact G27
| exact S48 | exact S64 | exact S88
| exact Fha | exact Fbef0 | exact Ffmt | clear -Ri0 Ri1 Hac Ffmt FN; nia | clear -Rf0 Rf1 Hac FN; lia | clear -FN; lia | exact Fcnt | ].
intros regs' mem' HJ' W72 W80 W96 Hfr Q25 Q22 Q24 Q9 Q19 Q26 Q27 Q15 Q14 HK.
apply (loop_SR regs1 Lc Ac memc mdc ha pnew fimg imgl C HAT (Z.to_nat N) 0 regs' mem').
- clear -FN. lia.
- split; [| split; [exact Q15 | split; [exact Q14 | split; [| clear -FN; lia]]]].
+ unfold sl_regs. rewrite (HK 2%bv ltac:(cbv; tauto)), (HK 3%bv ltac:(cbv; tauto)), (HK 4%bv ltac:(cbv; tauto)),
(HK 20%bv ltac:(cbv; tauto)), (HK 8%bv ltac:(cbv; tauto)), (HK 21%bv ltac:(cbv; tauto)).
rewrite Z.mul_0_r, Z.mul_0_l.
repeat match goal with |- _ /\ _ => split end; assumption.
+ split; [exact HJ'|]. split; [| split; [exact W72 | split; [exact W80 | exact W96]]].
intros a Ha _ W1 W2 _. apply Hfr; [exact Ha | exact W1 | exact W2].
- intros regs'' m'' HEX. exact (EX_SR regs1 Lc Ac memc mdc ha pnew fimg imgl C HAT regs'' m'' KFIN HEX).
Qed.
End f.
End e.
