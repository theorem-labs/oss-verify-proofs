(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UO3l YI00 YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Definition ct_sel (attr lct glob : Z) : Z := if Z.land attr 1 =? 0 then glob else lct.
Definition cmpPixel_fn (cattr ctidx cnlp battr btidx bnlp ngp : Z) (ctcur ctbef : list byte) (iCur iBef : Z) : Z :=
if negb (Z.land cattr 4 =? 0) && (iCur =? ctidx) then 0
else if negb (Z.land battr 4 =? 0) && (iBef =? btidx) then 1
else if (ct_sel battr bnlp ngp <=? iBef) || (ct_sel cattr cnlp ngp <=? iCur) then 1
else memcmp_spec (firstn 3 (skipn (Z.to_nat (3 * iBef)) ctbef)) (firstn 3 (skipn (Z.to_nat (3 * iCur)) ctcur)).
Definition ss_cmpPixel : sstate :=
mkSS ubs2_A_cmpPixel sr_atoms
[ YQ0b.mkRegion (Some 10%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 32 []);
YQ0b.mkRegion (Some 11%nat) 0 29 0 0 (obj_chunks_gen LAY_FrameConfig 49 []);
YQ0b.mkRegion (Some 12%nat) 0 29 0 0 (obj_chunks_gen LAY_FrameConfig 56 []) ]
None
(mkFacts [ (10%nat, mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4);
(11%nat, mkAF 4096 (2^63) 3); (12%nat, mkAF 4096 (2^63) 3);
(13%nat, mkAF 0 255 0); (14%nat, mkAF 0 255 0) ] [] []).
Lemma zv_add_nat : forall a k, (Z_to_bv 64 a + nat_to_word k)%bv = Z_to_bv 64 (a + Z.of_nat k).
Proof.
intros a k. unfold nat_to_word. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma ct_sub3 : forall mem (mem' : word -> option byte) base size ct i,
rdn ubs2segs mem (Z_to_bv 64 base) (Z.to_nat (3 * size)) = Some ct ->
(forall x, mem' x = mem x) ->
0 <= base -> base + 3 * size < 2 ^ 64 -> 0 <= i -> i < size ->
rdn ubs2segs mem' (Z_to_bv 64 (base + 3 * i)) 3 = Some (firstn 3 (skipn (Z.to_nat (3 * i)) ct)) /\
length (firstn 3 (skipn (Z.to_nat (3 * i)) ct)) = 3%nat.
Proof.
intros mem mem' base size ct i Hr Hm Hb Hnw Hi0 Hi.
pose proof (rdn_length _ _ _ _ _ Hr) as Hlen.
split.
- rewrite (rdn_ext ubs2segs 3 mem' mem).
+ replace (base + 3 * i) with (base + Z.of_nat (Z.to_nat (3 * i))) by lia. rewrite <- zv_add_nat.
apply (rdn_sub ubs2segs mem (Z_to_bv 64 base) (Z.to_nat (3 * size)) ct); [exact Hr | lia].
+ rewrite unsigned_lit_small by lia. cbn [Z.of_nat]. lia.
+ intros x _. apply Hm.
- rewrite length_firstn, length_skipn. lia.
Qed.
Lemma cmp_frame_in : forall r : reg,
r <> 5%bv -> r <> 6%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 0%bv ->
In r [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Proof.
intros r. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [intros; cbv; first [tauto | congruence] |]). destruct Hin.
Qed.
Ltac lia0 := repeat match goal with H : _ |- _ => clear H end; lia.
Ltac liaR :=
lazymatch goal with
| |- 0 <= ?v < _ => first [ match goal with R : 0 <= v < _ |- _ => clear - R; lia end | lia ]
| |- _ => lia
end.
Ltac Unorm H :=
lazymatch type of H with
| branch_taken BC_EQ _ _ = _ => rewrite branch_eq_U in H
| branch_taken BC_NE _ _ = _ => rewrite branch_ne_U in H
| branch_taken BC_GEU _ _ = _ => rewrite branch_geu_U in H
| branch_taken BC_LTU _ _ = _ => rewrite branch_ltu_U in H
end;
repeat first [ match type of H with context [U ?E (SAlu ALU_ADD (SMd M_MUL (SOff ?n 0) (SLit 3)) (SOff ?m 0))] =>
lazymatch goal with HEn : ew E n = Z_to_bv 64 ?i |- _ =>
lazymatch goal with HEm : ew E m = Z_to_bv 64 ?b |- _ =>
lazymatch goal with Ri : 0 <= i < 256 |- _ =>
rewrite (U_add_mul3 E n m i b HEn Ri HEm ltac:(lia) ltac:(lia)) in H
end end end end
| rewrite U_and_lit in H by lia0
| rewrite U_zext in H
| rewrite U_lit in H by lia0
| match type of H with context [U ?E (SOff ?n 0)] =>
match goal with HE : ew E n = Z_to_bv 64 ?v |- _ => rewrite (U_atom E n v HE) in H by liaR end end ];
try change (2 ^ Z.of_N 32) with 4294967296 in H;
try change (2 ^ Z.of_N 16) with 65536 in H;
try change (2 ^ Z.of_N 8) with 256 in H;
repeat (rewrite Z.mod_small in H by liaR);
try rewrite <- Z.leb_antisym in H;
lazymatch type of H with
| negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H
| negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H
| _ => idtac
end.
Ltac cmp_ret HS Hacc Hmem Hspec :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
let Hfin := fresh "Hfin" in
pose proof (pure_ret ubs2segs ubs2tbl ubs2tbl_ok E ss ms _ HS eq_refl ltac:(vm_compute; reflexivity) Hacc) as Hfin;
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok ubs2segs E ss ms _ _
[1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv
HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HK;
rewrite (HK 1%bv ltac:(cbv; tauto)) in Hfin;
exists (ms_regs ms), (ms_mem ms);
split; [exact Hfin|]; split; [exact Hmem|]; split;
[ let Ha := fresh "Ha" in jreg HS (10%bv:reg) as Ha; rewrite Ha, <- Hspec; reflexivity
| let r := fresh "r" in intros r; intros;
destruct (base.decide (r = 0%bv)) as [->|Hr0]; [rewrite !getr_zero; reflexivity|];
apply HK; apply cmp_frame_in; assumption ]
end.
Ltac cmp_memcmp HS Hacc Hmem Hspec :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok ubs2segs E ss ms _ _
[1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv
HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HK;
let Ha0 := fresh "Ha0" in let Ha1 := fresh "Ha1" in let Ha2 := fresh "Ha2" in
pose proof (st_ok_reg ubs2segs E ss ms (10%bv:reg) HS) as Ha0; eval_sr_get_in Ha0;
pose proof (st_ok_reg ubs2segs E ss ms (11%bv:reg) HS) as Ha1; eval_sr_get_in Ha1;
jreg HS (12%bv:reg) as Ha2;
repeat match goal with
| Hsel : (Z.land ?attr 1 =? 0) = _, R : context [ct_sel ?attr _ _] |- _ => unfold ct_sel in R; rewrite Hsel in R; cbv iota beta in R
end;
lazymatch type of Ha0 with
| _ = sv_denot _ (SAlu ALU_ADD (SMd M_MUL (SOff 14 0) (SLit 3)) (SOff ?pb 0)) =>
lazymatch type of Ha1 with
| _ = sv_denot _ (SAlu ALU_ADD (SMd M_MUL (SOff 13 0) (SLit 3)) (SOff ?pc 0)) =>
lazymatch goal with | HEb : ew E pb = Z_to_bv 64 ?bb |- _ =>
lazymatch goal with | HEc : ew E pc = Z_to_bv 64 ?bc |- _ =>
lazymatch type of Hspec with | _ = cmpPixel_fn _ _ _ _ _ _ _ ?ctc ?ctb ?iC ?iB =>
lazymatch goal with | Rbt : rdn _ _ (Z_to_bv 64 bb) (Z.to_nat (3 * ?szb)) = Some ctb |- _ =>
lazymatch goal with | Rct : rdn _ _ (Z_to_bv 64 bc) (Z.to_nat (3 * ?szc)) = Some ctc |- _ =>
lazymatch goal with | HE14 : ew E 14 = Z_to_bv 64 iB, HE13 : ew E 13 = Z_to_bv 64 iC |- _ =>
lazymatch goal with | RiB : 0 <= iB < 256, RiC : 0 <= iC < 256 |- _ =>
lazymatch goal with | Sb0 : 4096 <= bb, Sb1 : bb + 3 * szb <= 2 ^ 63 |- _ =>
lazymatch goal with | Sc0 : 4096 <= bc, Sc1 : bc + 3 * szc <= 2 ^ 63 |- _ =>
lazymatch goal with | Hac : _ <= alloc_ceiling <= _ |- _ =>
lazymatch goal with | Hcb : (szb <=? iB) = false, Hcc : (szc <=? iC) = false |- _ =>
let LTb := fresh "LTb" in let LTc := fresh "LTc" in
pose proof (proj1 (Z.leb_gt _ _) Hcb) as LTb; pose proof (proj1 (Z.leb_gt _ _) Hcc) as LTc;
rewrite (denot_add_mul3 E 14 pb iB bb HE14 RiB HEb ltac:(clear - Sb0; lia) ltac:(clear - Sb1 LTb RiB Hac; lia)) in Ha0;
rewrite (denot_add_mul3 E 13 pc iC bc HE13 RiC HEc ltac:(clear - Sc0; lia) ltac:(clear - Sc1 LTc RiC Hac; lia)) in Ha1;
let Sb := fresh "Sb" in let Sc := fresh "Sc" in let Lb := fresh "Lb" in let Lc := fresh "Lc" in
destruct (ct_sub3 _ (ms_mem ms) bb szb ctb iB Rbt Hmem ltac:(clear - Sb0; lia) ltac:(clear - Sb1 Hac; lia) ltac:(clear - RiB; lia) LTb) as [Sb Lb];
destruct (ct_sub3 _ (ms_mem ms) bc szc ctc iC Rct Hmem ltac:(clear - Sc0; lia) ltac:(clear - Sc1 Hac; lia) ltac:(clear - RiC; lia) LTc) as [Sc Lc];
let regs2 := fresh "regs2" in let Hms := fresh "Hms" in let Hres := fresh "Hres" in let Hfr := fresh "Hfr" in
edestruct (ubs2_memcmp (firstn 3 (skipn (Z.to_nat (3 * iB)) ctb)) (firstn 3 (skipn (Z.to_nat (3 * iC)) ctc))
_ _ _ (ms_mem ms) (seg_rom ubs2segs) (ms_regs ms) Ha0 Ha1 Ha2)
as (regs2 & Hms & Hres & Hfr);
[ rewrite Lb, unsigned_lit_small by lia0; reflexivity
| rewrite Lb, Lc; reflexivity | rewrite Lb; exact Sb | rewrite Lb; exact Sc
| rewrite Lb, unsigned_lit_small by (clear - Sb0 Sb1 LTb RiB Hac; lia); clear - Sb0 Sb1 LTb RiB Hac; lia
| rewrite Lb, unsigned_lit_small by (clear - Sc0 Sc1 LTc RiC Hac; lia); clear - Sc0 Sc1 LTc RiC Hac; lia |];
exists regs2, (ms_mem ms);
split; [ eapply msteps_trans; [exact Hacc|];
rewrite (st_ok_mkst _ _ _ _ HS eq_refl) at 1; cbn [ss_pc];
rewrite <- (HK 1%bv ltac:(cbv; tauto)); exact Hms |];
split; [exact Hmem|];
split; [rewrite Hres, <- Hspec; reflexivity|];
let r := fresh "r" in intros r; intros;
destruct (base.decide (r = 0%bv)) as [->|Hr0]; [rewrite !getr_zero; reflexivity|];
rewrite Hfr by assumption; apply HK; apply cmp_frame_in; assumption
| _ => fail "cmp_memcmp: bound conds" end
| _ => fail "cmp_memcmp: Hac" end
| _ => fail "cmp_memcmp: Sc" end
| _ => fail "cmp_memcmp: Sb" end
| _ => fail "cmp_memcmp: Ri" end
| _ => fail "cmp_memcmp: HE13/14" end
| _ => fail "cmp_memcmp: no table for" bc end
| _ => fail "cmp_memcmp: no table for" bb end
end
| _ => fail "cmp_memcmp: no value for atom" pc end
| _ => fail "cmp_memcmp: no value for atom" pb end
| ?t => fail "cmp_memcmp: a1 =" t end
| ?t => fail "cmp_memcmp: a0 =" t end
end.
Ltac add_sel_fact Hc HS :=
lazymatch type of Hc with
| (Z.land ?attr 1 =? 0) = _ =>
lazymatch goal with S0 : 4096 <= ct_sel attr ?l ?g, S1 : ct_sel attr ?l ?g + 3 * ?sz <= 2 ^ 63 |- _ =>
unfold ct_sel in S0, S1; rewrite Hc in S0, S1; cbv iota beta in S0; cbv iota beta in S1;
lazymatch type of S1 with ?b + 3 * ?szv <= _ =>
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch goal with HE : ew E ?n = Z_to_bv 64 b |- _ =>
lazymatch goal with HA : ew E ?na = Z_to_bv 64 attr |- _ =>
lazymatch goal with Hac : _ <= alloc_ceiling <= _ |- _ =>
lazymatch goal with Rsz : 0 <= szv < _ |- _ =>
let k := lazymatch na with 58%nat => constr:(14%nat) | 51%nat => constr:(13%nat) end in
lazymatch goal with HEk : ew E k = Z_to_bv 64 ?i |- _ =>
lazymatch goal with Ri : 0 <= i < 256 |- _ =>
let Hf := fresh "Hf" in
assert (Hf : afact_ok E n (mkAF 4096 (2 ^ 63) 0));
[ unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite HE, unsigned_lit_small by (clear - S0 S1 Hac Rsz; lia);
change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - S0 S1 Hac Rsz; lia
| apply (st_ok_add_fact segs E ss ms n _ HS) in Hf; clear HS;
let Hg := fresh "Hg" in
assert (Hg : branch_taken BC_GEU
(sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit 3)) (SOff n 0)))
(sv_denot E (SOff n 0)) = true);
[ rewrite branch_geu_U, (U_add_mul3 E k n i b HEk Ri HE) by (clear - S0 S1 Hac Rsz Ri; lia);
rewrite (U_atom E n b HE) by (clear - S0 S1 Hac Rsz; lia);
apply (proj2 (Bool.negb_true_iff _)); apply Z.ltb_ge; clear - Ri; lia
| lazymatch type of Hf with st_ok _ _ ?ss1 ?ms1 =>
apply (st_ok_add_cond segs E ss1 ms1 BC_GEU _ _ Hf) in Hg; clear Hf; rename Hg into HS;
lazymatch type of HS with st_ok _ _ ?ss2 _ => let ss3 := eval vm_compute in ss2 in change ss2 with ss3 in HS end
end ] ]
end end
end end end end end end
| |- _ => idtac
end
| _ => idtac
end.
Ltac cmp_go :=
lazymatch goal with
| HS : st_ok _ _ ?ss _, Hacc : msteps _ _ _, Hmem : (forall x, ms_mem _ x = _), Hspec : _ = cmpPixel_fn _ _ _ _ _ _ _ _ _ _ _ |- _ =>
prun_to ubs2tbl_ok HS Hacc Hmem ubs2_A_memcmp;
lazymatch goal with
| HS' : st_ok _ _ ?ss' _, Hacc' : msteps _ _ _, Hmem' : (forall x, ms_mem _ x = _) |- _ =>
let at_memcmp := eval vm_compute in (ss_pc ss' =? ubs2_A_memcmp) in
lazymatch at_memcmp with
| true => cmp_memcmp HS' Hacc' Hmem' Hspec
| false =>
let why := sym_why ubs2segs ubs2tbl ss' in
lazymatch why with
| SR_jalr _ => cmp_ret HS' Hacc' Hmem' Hspec
| SR_branch _ _ _ =>
pbranch ubs2tbl HS';
[ lazymatch goal with Hc : branch_taken _ _ _ = true, HS2 : st_ok _ _ _ _ |- _ =>
Unorm Hc; try (rewrite Hc in Hspec; cbn [negb andb orb] in Hspec); add_sel_fact Hc HS2; cmp_go end
| lazymatch goal with Hc : branch_taken _ _ _ = false, HS2 : st_ok _ _ _ _ |- _ =>
Unorm Hc; try (rewrite Hc in Hspec; cbn [negb andb orb] in Hspec); add_sel_fact Hc HS2; cmp_go end ]
| _ =>
exfalso; clear HS' Hacc' Hmem'; lia
end
end
end
end.
Theorem ubs2_cmpPixelG :
forall regs mem g gvals cur cvals bef bvals iCur iBef ctcur ctbef
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z),
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 cur -> getr regs 12 = Z_to_bv 64 bef ->
getr regs 13 = Z_to_bv 64 iCur -> getr regs 14 = Z_to_bv 64 iBef -> 0 <= iCur < 256 -> 0 <= iBef < 256 ->
obj_at ubs2segs mem g LAY_CGIF gvals ->
nth_error gvals CG_ngp = Some ngp -> nth_error gvals CG_pal = Some gpal ->
obj_at ubs2segs mem cur LAY_FrameConfig cvals ->
nth_error cvals FR_attr = Some cattr -> nth_error cvals FR_ctidx = Some ctidx ->
nth_error cvals FR_nlp = Some cnlp -> nth_error cvals FR_lpal = Some clpal ->
obj_at ubs2segs mem bef LAY_FrameConfig bvals ->
nth_error bvals FR_attr = Some battr -> nth_error bvals FR_ctidx = Some btidx ->
nth_error bvals FR_nlp = Some bnlp -> nth_error bvals FR_lpal = Some blpal ->
4096 <= g -> g + CGIF_SIZE <= alloc_ceiling -> g mod 16 = 0 ->
4096 <= cur -> cur + 32 <= 2 ^ 63 -> cur mod 8 = 0 ->
4096 <= bef -> bef + 32 <= 2 ^ 63 -> bef mod 8 = 0 ->
(g + CGIF_SIZE <= cur \/ cur + 29 <= g) -> (g + CGIF_SIZE <= bef \/ bef + 29 <= g) -> (cur + 29 <= bef \/ bef + 29 <= cur) ->
rdn ubs2segs mem (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur ->
rdn ubs2segs mem (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef ->
4096 <= ct_sel cattr clpal gpal -> ct_sel cattr clpal gpal + 3 * ct_sel cattr cnlp ngp <= 2 ^ 63 ->
4096 <= ct_sel battr blpal gpal -> ct_sel battr blpal gpal + 3 * ct_sel battr bnlp ngp <= 2 ^ 63 ->
exists regs' mem',
msteps ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_cmpPixel) mem (seg_rom ubs2segs))
(mkst regs' (v_jalr (getr regs 1) 0) mem' (seg_rom ubs2segs)) /\
(forall x, mem' x = mem x) /\
getr regs' 10 = Z_to_bv 64 (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef iCur iBef) /\
(forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs mem g gvals cur cvals bef bvals iCur iBef ctcur ctbef cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal
Hg Hcur Hbef HiC HiB RiC RiB Og Ongp Ogpal Oc Ocattr Octidx Ocnlp Oclpal Ob Obattr Obtidx Obnlp Oblpal
G0 G1 G16 C0 C1 C8 B0 B1 B8 Dgc Dgb Dcb Rct Rbt Sc0 Sc1 Sb0 Sb1.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (obj_at_nth ubs2segs mem g LAY_CGIF gvals 9 _ _ Og eq_refl Ongp) as [_ Rngp]. cbn [snd] in Rngp.
pose proof (obj_at_nth ubs2segs mem g LAY_CGIF gvals 3 _ _ Og eq_refl Ogpal) as [_ Rgpal]. cbn [snd] in Rgpal.
pose proof (obj_at_nth ubs2segs mem cur LAY_FrameConfig cvals 2 _ _ Oc eq_refl Ocattr) as [_ Rcattr]. cbn [snd] in Rcattr.
pose proof (obj_at_nth ubs2segs mem cur LAY_FrameConfig cvals 6 _ _ Oc eq_refl Octidx) as [_ Rctidx]. cbn [snd] in Rctidx.
pose proof (obj_at_nth ubs2segs mem cur LAY_FrameConfig cvals 5 _ _ Oc eq_refl Ocnlp) as [_ Rcnlp]. cbn [snd] in Rcnlp.
pose proof (obj_at_nth ubs2segs mem cur LAY_FrameConfig cvals 0 _ _ Oc eq_refl Oclpal) as [_ Rclpal]. cbn [snd] in Rclpal.
pose proof (obj_at_nth ubs2segs mem bef LAY_FrameConfig bvals 2 _ _ Ob eq_refl Obattr) as [_ Rbattr]. cbn [snd] in Rbattr.
pose proof (obj_at_nth ubs2segs mem bef LAY_FrameConfig bvals 6 _ _ Ob eq_refl Obtidx) as [_ Rbtidx]. cbn [snd] in Rbtidx.
pose proof (obj_at_nth ubs2segs mem bef LAY_FrameConfig bvals 5 _ _ Ob eq_refl Obnlp) as [_ Rbnlp]. cbn [snd] in Rbnlp.
pose proof (obj_at_nth ubs2segs mem bef LAY_FrameConfig bvals 0 _ _ Ob eq_refl Oblpal) as [_ Rblpal]. cbn [snd] in Rblpal.
pose proof (obj_at_length _ _ _ _ _ Og) as Lg. pose proof (obj_at_length _ _ _ _ _ Oc) as Lc. cbn in Lg, Lc.
assert (HS : st_ok ubs2segs (Ereg regs (map (Z_to_bv 64) gvals ++ map (Z_to_bv 64) (cvals ++ bvals))) ss_cmpPixel
(mkst regs (Z_to_bv 64 ubs2_A_cmpPixel) mem (seg_rom ubs2segs))).
{ apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ eapply (region_ok_obj_gen ubs2segs _ mem 10 g); [ | lia | lia | exact Og | reflexivity | | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity). rewrite Hg. apply unsigned_lit_small. lia.
* intros j v Hj. apply Ereg_vals. exact Hj.
+ eapply (region_ok_obj_gen ubs2segs _ mem 11 cur); [ | lia | lia | exact Oc | reflexivity | | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity). rewrite Hcur. apply unsigned_lit_small. lia.
* intros j v Hj. replace (49 + j)%nat with (32 + (length gvals + j))%nat by (rewrite Lg; reflexivity).
apply Ereg_more. rewrite nth_error_app1; [exact Hj|]. apply nth_error_Some. congruence.
+ eapply (region_ok_obj_gen ubs2segs _ mem 12 bef); [ | lia | lia | exact Ob | reflexivity | | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
* rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity). rewrite Hbef. apply unsigned_lit_small. lia.
* intros j v Hj. replace (56 + j)%nat with (32 + (length gvals + (length cvals + j)))%nat by (rewrite Lg, Lc; reflexivity).
apply Ereg_more. rewrite nth_error_app2 by lia. replace (length cvals + j - length cvals)%nat with j by lia. exact Hj.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity).
rewrite Hg, Hcur, Hbef, !unsigned_lit_small by lia. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs _ 10 10%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 11 11%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity).
rewrite (ew_Ereg_nat regs _ 14 14%bv) by (vm_compute; reflexivity).
rewrite Hg, Hcur, Hbef, HiC, HiB, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. repeat split; try lia.
all: rewrite Z.mod_1_r; reflexivity. }
pose proof (mst_refl ubs2segs (mkst regs (Z_to_bv 64 ubs2_A_cmpPixel) mem (seg_rom ubs2segs))) as Hacc.
assert (Hmem : forall x, ms_mem (mkst regs (Z_to_bv 64 ubs2_A_cmpPixel) mem (seg_rom ubs2segs)) x = mem x) by (intros x; reflexivity).
assert (HE13 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ map (Z_to_bv 64) (cvals ++ bvals))) 13 = Z_to_bv 64 iCur)
by (rewrite (ew_Ereg_nat regs _ 13 13%bv) by (vm_compute; reflexivity); exact HiC).
assert (HE14 : ew (Ereg regs (map (Z_to_bv 64) gvals ++ map (Z_to_bv 64) (cvals ++ bvals))) 14 = Z_to_bv 64 iBef)
by (rewrite (ew_Ereg_nat regs _ 14 14%bv) by (vm_compute; reflexivity); exact HiB).
assert (HEg : forall j v, nth_error gvals j = Some v ->
ew (Ereg regs (map (Z_to_bv 64) gvals ++ map (Z_to_bv 64) (cvals ++ bvals))) (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; apply Ereg_vals; exact Hj).
assert (HEc : forall j v, nth_error cvals j = Some v ->
ew (Ereg regs (map (Z_to_bv 64) gvals ++ map (Z_to_bv 64) (cvals ++ bvals))) (49 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (49 + j)%nat with (32 + (length gvals + j))%nat by (rewrite Lg; reflexivity).
apply Ereg_more. rewrite nth_error_app1; [exact Hj|]. apply nth_error_Some. congruence. }
assert (HEb : forall j v, nth_error bvals j = Some v ->
ew (Ereg regs (map (Z_to_bv 64) gvals ++ map (Z_to_bv 64) (cvals ++ bvals))) (56 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (56 + j)%nat with (32 + (length gvals + (length cvals + j)))%nat by (rewrite Lg, Lc; reflexivity).
apply Ereg_more. rewrite nth_error_app2 by lia. replace (length cvals + j - length cvals)%nat with j by lia. exact Hj. }
pose proof (HEg 3%nat _ Ogpal) as HE35. pose proof (HEg 9%nat _ Ongp) as HE41.
pose proof (HEc 0%nat _ Oclpal) as HE49. pose proof (HEc 2%nat _ Ocattr) as HE51.
pose proof (HEc 5%nat _ Ocnlp) as HE54. pose proof (HEc 6%nat _ Octidx) as HE55.
pose proof (HEb 0%nat _ Oblpal) as HE56. pose proof (HEb 2%nat _ Obattr) as HE58.
pose proof (HEb 5%nat _ Obnlp) as HE61. pose proof (HEb 6%nat _ Obtidx) as HE62.
cbn [Nat.add] in HE35, HE41, HE49, HE51, HE54, HE55, HE56, HE58, HE61, HE62. clear HEg HEc HEb.
cbn in Rngp, Rgpal, Rcattr, Rctidx, Rcnlp, Rclpal, Rbattr, Rbtidx, Rbnlp, Rblpal.
match goal with |- context [getr _ 10 = Z_to_bv 64 ?spec] =>
assert (Hspec : spec = spec) by reflexivity; unfold cmpPixel_fn in Hspec at 1; unfold ct_sel in Hspec at 1 2 end.
cmp_go.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
