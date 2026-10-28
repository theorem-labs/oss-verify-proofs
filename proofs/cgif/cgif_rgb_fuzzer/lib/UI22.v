(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1c UI39 UI1i UI59 UI56 YI0x UI57
UI1h UI16 UI1z UI1k.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FL_TOUT  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x954).
Definition FL_TIN   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x968).
Definition FL_TCMP  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x9b0).
Definition FL_TINX  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x9cc).
Definition FL_TOUTX : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x9e8).
Lemma rdn_agree : forall segs (m1 m2 : word -> option byte) n a,
(forall k, 0 <= k < Z.of_nat n -> mbyte segs m1 (a + k) = mbyte segs m2 (a + k)) ->
rdn segs m1 (Z_to_bv 64 a) n = rdn segs m2 (Z_to_bv 64 a) n.
Proof.
intros segs m1 m2 n. induction n as [|n IH]; intros a Heq; [reflexivity|].
cbn [rdn]. pose proof (Heq 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold mbyte in H0. rewrite H0.
assert (Ha1 : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)) by bv_solve.
rewrite Ha1, (IH (a + 1)); [reflexivity|]. intros k Hk. replace (a + 1 + k) with (a + (1 + k)) by lia. apply Heq. lia.
Qed.
Lemma ZZ_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.
Lemma wr_ok_cons_blk : forall E r rs STK sp0 FP bl0 blc n p b m,
r_base r = Some n -> bv_unsigned (ew E n) = p -> In (b, m) blc ->
(In (b, m) bl0 -> forall k, 0 <= k < m -> inFP FP (b + k)) ->
b <= p + r_wlo r -> p + r_whi r <= b + m ->
wr_ok E rs STK sp0 FP bl0 blc -> wr_ok E (r :: rs) STK sp0 FP bl0 blc.
Proof.
intros E r rs STK sp0 FP bl0 blc n p b m Hb Hn Hin Hfp Hlo Hhi H a (r' & [<-|Hin'] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha.
destruct (in_dec ZZ_eq_dec (b, m) bl0) as [Hi|Hni].
+ right. left. split; [replace a with (b + (a - b)) by lia; apply (Hfp Hi); lia|]. exists b, m. split; [exact Hin | lia].
+ right. right. exists b, m. split; [exact Hin | split; [exact Hni | lia]].
- apply H. exists r'. auto.
Qed.
Definition TIN_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 22; 24; 26; 27]%bv.
Definition tin_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 8 0) (SOff 19 0), SOff 34 0); (SAlu ALU_ADD (SOff 24 0) (SOff 25 0), SOff 35 0);
(SAlu ALU_XOR (SOff 26 0) (SLit 0), SOff 26 0) ].
Definition ss_tin : sstate :=
mkSS FL_TIN sr_atoms
[ YQ0b.mkRegion (Some 34%nat) 0 1 0 1 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ;
YQ0b.mkRegion (Some 2%nat) 112 128 112 112 [mkChunk 112 (CVal 8 (SOff 36 0)); mkChunk 120 (CVal 8 (SOff 37 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (34%nat, mkAF 4096 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0);
(19%nat, mkAF 0 (2^32 - 1) 0); (25%nat, mkAF 0 (2^32 - 1) 0); (24%nat, mkAF 4096 CEIL_MAX 0); (26%nat, mkAF 1 1 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ]
[ mkAC BC_GEU (SOff 34 0) (SOff 19 0); mkAC BC_GEU (SOff 35 0) (SOff 24 0) ] tin_alias).
Lemma U_add_small : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Hx Hy Rx Ry Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma U_mul_small' : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x * y < 2 ^ 64 ->
U E (SMd M_MUL a b) = x * y.
Proof. intros E a b x y Hx Hy Rx Ry Rp. rewrite U_SMd. cbn [zmd_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. nia. Qed.
Lemma denot_of_U' : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z <-. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Definition ss_tout (pc : Z) : sstate :=
mkSS pc (sr_set sr_atoms 26%bv (SLit 4294967295))
[ YQ0b.mkRegion (Some 2%nat) 80 120 80 80
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SOff 33 0)); mkChunk 96 (CVal 8 (SOff 34 0));
mkChunk 104 (CVal 8 (SOff 35 0)); mkChunk 112 (CVal 8 (SOff 36 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (33%nat, mkAF 1 (2^64 - 1) 0) ] [] []).
Definition TOUT_KEPT : list reg := [2; 3; 4; 8; 9; 18]%bv.
Definition hidePt (P : Prop) : Prop := P.
End c.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (hidePt (A \/ B)) in H end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section e.
Variables (mem0 : word -> option byte) (g cfp fhp bimg N pTmp Nt spv tv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis Og : obj_at ubs2segs mem0 g LAY_CGIF gvals.
Hypothesis Ongp : nth_error gvals CG_ngp = Some ngp.
Hypothesis Ogpal : nth_error gvals CG_pal = Some gpal.
Hypothesis Oc : obj_at ubs2segs mem0 cfp LAY_FrameConfig cvals.
Hypothesis Ocattr : nth_error cvals FR_attr = Some cattr.
Hypothesis Octidx : nth_error cvals FR_ctidx = Some ctidx.
Hypothesis Ocnlp : nth_error cvals FR_nlp = Some cnlp.
Hypothesis Oclpal : nth_error cvals FR_lpal = Some clpal.
Hypothesis Ob : obj_at ubs2segs mem0 fhp LAY_FrameConfig bvals.
Hypothesis Obattr : nth_error bvals FR_attr = Some battr.
Hypothesis Obtidx : nth_error bvals FR_ctidx = Some btidx.
Hypothesis Obnlp : nth_error bvals FR_nlp = Some bnlp.
Hypothesis Oblpal : nth_error bvals FR_lpal = Some blpal.
Hypothesis G0 : 4096 <= g. Hypothesis G1 : g + CGIF_SIZE <= alloc_ceiling. Hypothesis G16 : g mod 16 = 0.
Hypothesis C0 : 4096 <= cfp. Hypothesis C1 : cfp + 32 <= 2 ^ 63. Hypothesis C8 : cfp mod 8 = 0.
Hypothesis B0 : 4096 <= fhp. Hypothesis B1 : fhp + 32 <= 2 ^ 63. Hypothesis B8 : fhp mod 8 = 0.
Hypothesis Dgc : g + CGIF_SIZE <= cfp \/ cfp + 29 <= g.
Hypothesis Dgb : g + CGIF_SIZE <= fhp \/ fhp + 29 <= g.
Hypothesis Dcb : cfp + 29 <= fhp \/ fhp + 29 <= cfp.
Hypothesis Rct : rdn ubs2segs mem0 (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur.
Hypothesis Rbt : rdn ubs2segs mem0 (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef.
Hypothesis Sc0 : 4096 <= ct_sel cattr clpal gpal. Hypothesis Sc1 : ct_sel cattr clpal gpal + 3 * ct_sel cattr cnlp ngp <= alloc_ceiling.
Hypothesis Sb0 : 4096 <= ct_sel battr blpal gpal. Hypothesis Sb1 : ct_sel battr blpal gpal + 3 * ct_sel battr bnlp ngp <= alloc_ceiling.
Hypothesis Hcnn : 0 <= 3 * ct_sel cattr cnlp ngp. Hypothesis Hbnn : 0 <= 3 * ct_sel battr bnlp ngp.
Hypothesis Hbimg0 : 4096 <= bimg. Hypothesis Hbimg1 : bimg + N <= alloc_ceiling.
Hypothesis HN : N < 2 ^ 32.
Hypothesis Ht0 : 4096 <= pTmp. Hypothesis Ht1 : pTmp + Nt <= alloc_ceiling.
Hypothesis Xg : g + CGIF_SIZE <= pTmp \/ pTmp + Nt <= g.
Hypothesis Xc : cfp + 32 <= pTmp \/ pTmp + Nt <= cfp.
Hypothesis Xb : fhp + 32 <= pTmp \/ pTmp + Nt <= fhp.
Hypothesis Xct : ct_sel cattr clpal gpal + 3 * ct_sel cattr cnlp ngp <= pTmp \/ pTmp + Nt <= ct_sel cattr clpal gpal.
Hypothesis Xbt : ct_sel battr blpal gpal + 3 * ct_sel battr bnlp ngp <= pTmp \/ pTmp + Nt <= ct_sel battr blpal gpal.
Hypothesis Xbimg : bimg + N <= pTmp \/ pTmp + Nt <= bimg.
Hypothesis Hsp0 : alloc_ceiling <= spv. Hypothesis Hsp1 : spv + 272 <= 2 ^ 63. Hypothesis Hsp16 : spv mod 16 = 0.
Hypothesis Wg : word_mem ubs2segs mem0 (spv + 112) g. Hypothesis Wc : word_mem ubs2segs mem0 (spv + 120) cfp. Hypothesis Rtv : 0 <= tv < 2 ^ 64.
Definition KT (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (pTmp <= a < pTmp + Nt) -> mbyte ubs2segs m a = mbyte ubs2segs mem0 a.
Lemma KT_trans : forall m1 m2, KT m1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (pTmp <= a < pTmp + Nt) -> mbyte ubs2segs m2 a = mbyte ubs2segs m1 a) -> KT m2.
Proof. intros m1 m2 K1 K2 a Ha Hna. rewrite (K2 a Ha Hna). apply K1; assumption. Qed.
Lemma cmp_objs : forall m, KT m ->
obj_at ubs2segs m g LAY_CGIF gvals /\ obj_at ubs2segs m cfp LAY_FrameConfig cvals /\ obj_at ubs2segs m fhp LAY_FrameConfig bvals /\
rdn ubs2segs m (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur /\
rdn ubs2segs m (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef /\
word_mem ubs2segs m (spv + 112) g /\ word_mem ubs2segs m (spv + 120) cfp.
Proof.
intros m K. pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
split; [| split; [| split; [| split; [| split; [| split]]]]].
- eapply obj_at_transport_range; [exact Og | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply K; clear - Hi Xg G0 G1 Ht0 Ht1 Hac HGSv; unfold hidePt in *; lia].
- eapply obj_at_transport_range; [exact Oc | exact lay_inside_FrameConfig | intros i Hi; apply K; clear - Hi Xc C0 C1 Ht0 Ht1 Hac; unfold hidePt in *; lia].
- eapply obj_at_transport_range; [exact Ob | exact lay_inside_FrameConfig | intros i Hi; apply K; clear - Hi Xb B0 B1 Ht0 Ht1 Hac; unfold hidePt in *; lia].
- rewrite <- Rct. apply rdn_agree. intros k Hk. apply K; clear - Hk Xct Sc0 Sc1 Hcnn Ht0 Ht1 Hac; unfold hidePt in *; lia.
- rewrite <- Rbt. apply rdn_agree. intros k Hk. apply K; clear - Hk Xbt Sb0 Sb1 Hbnn Ht0 Ht1 Hac; unfold hidePt in *; lia.
- intros k Hk. rewrite <- (Wg k Hk). apply K; clear - Hk Hsp0 Hsp1 Ht0 Ht1 Hac; lia.
- intros k Hk. rewrite <- (Wc k Hk). apply K; clear - Hk Hsp0 Hsp1 Ht0 Ht1 Hac; lia.
Qed.
Definition tin_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_TINX) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KT mem' /\
(forall r : reg, In r TIN_KEPT -> getr regs' r = getr regs r).
Lemma fl_tin : forall (n : nat) (p boff : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc pend,
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KT memc ->
In (pTmp, Nt) (blocks Lc Ac) -> (In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
In (bimg, N) (blocks Lc Ac) ->
pTmp <= p -> p + Z.of_nat n = pend -> (1 <= n)%nat -> pend <= pTmp + Nt -> pend <= pTmp + N ->
0 <= boff -> boff + Z.of_nat n <= N ->
sp0 - STK <= spv -> spv = sp0 - 272 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 pTmp -> getr regs 9 = Z_to_bv 64 tv -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 25 = Z_to_bv 64 boff -> getr regs 19 = Z_to_bv 64 (p - pTmp) -> getr regs 23 = Z_to_bv 64 (pend - p) ->
getr regs 24 = Z_to_bv 64 bimg -> getr regs 26 = Z_to_bv 64 1 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_TIN) memc (seg_rom ubs2segs)) mdc) (tin_post STK sp0 FP L A mem md Lc Ac mdc regs).
Proof.
intros n. induction n as [|n IH]; intros p boff STK sp0 FP L A mem md Lc Ac mdc regs memc pend HJ K0 Htin Htfp Hbin Hp HpN Hn Hpe HpeN Hb0 HbN Hstk Hspv
G2 G8 G9 G18 G25 G19 G23 G24 G26; [lia|].
hide_disj.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
destruct (cmp_objs memc K0) as (Og' & Oc' & Ob' & Rct' & Rbt' & Wg' & Wc').
set (bc := byte_at memc p). set (bb := byte_at memc (bimg + boff)).
pose proof (byte_at_range memc p) as Rbc. pose proof (byte_at_range memc (bimg + boff)) as Rbb. fold bc in Rbc. fold bb in Rbb.
assert (HoffR : 0 <= p - pTmp < 2 ^ 32) by (clear - Hp HpN HpeN HN; lia).
assert (HbofR : 0 <= boff < 2 ^ 32) by (clear - Hb0 HbN HN; lia).
set (E := Ereg regs (map (Z_to_bv 64) [bc; bb; p; bimg + boff; g; cfp] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [bc; bb; p; bimg + boff; g; cfp] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [bc; bb; p; bimg + boff; g; cfp] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 p) by (subst E; apply (Ereg_vals regs [bc; bb; p; bimg + boff; g; cfp] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 (bimg + boff)) by (subst E; apply (Ereg_vals regs [bc; bb; p; bimg + boff; g; cfp] [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 g) by (subst E; apply (Ereg_vals regs [bc; bb; p; bimg + boff; g; cfp] [] 4%nat); reflexivity).
assert (HE37 : ew E 37 = Z_to_bv 64 cfp) by (subst E; apply (Ereg_vals regs [bc; bb; p; bimg + boff; g; cfp] [] 5%nat); reflexivity).
assert (HE8 : ew E 8 = Z_to_bv 64 pTmp) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE19 : ew E 19 = Z_to_bv 64 (p - pTmp)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE24 : ew E 24 = Z_to_bv 64 bimg) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE25 : ew E 25 = Z_to_bv 64 boff) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (HE23 : ew E 23 = Z_to_bv 64 (pend - p)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE26 : ew E 26 = Z_to_bv 64 1) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (HU34 : bv_unsigned (ew E 34) = p) by (rewrite HE34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = bimg + boff) by (rewrite HE35; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 34%nat) 0 1 0 1 [mkChunk 0 (CVal 1 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). replace (p + o) with (pTmp + (p - pTmp + o)) by lia. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pTmp Nt (p - pTmp + o) HHc Htin ltac:(clear - Hp HpN Hn Hpe Ho; lia))). }
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. replace p with (pTmp + (p - pTmp)) by lia. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pTmp Nt (p - pTmp) HHc Htin ltac:(clear - Hp HpN Hn Hpe; lia))). }
assert (HR1 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N boff HHc Hbin ltac:(clear - Hb0 HbN Hn; lia))). }
assert (HR2 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 112 128 112 112 [mkChunk 112 (CVal 8 (SOff 36 0)); mkChunk 120 (CVal 8 (SOff 37 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ g); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wg'].
- eapply (chunk_ok_val _ _ _ _ _ _ _ cfp); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wc']. }
assert (HPD : pairwise_disjoint E (ss_mem ss_tin)).
{ cbn [ss_mem ss_tin pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU34, HU35, HU2.
clear - Hp HpN Hn Hpe Hb0 HbN Xbimg Hsp0 Ht1 Hbimg1; unfold hidePt in *. repeat split; lia. }
assert (HFA : facts_ok E (ss_facts ss_tin)).
{ split; [| split].
- cbn [ss_facts ss_tin f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU34, HU35, HE19, HE25, HE24, HE26, HE32, HE33, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
clear - Hp HpN Hn Hpe Hb0 HbN Ht0 Ht1 Hbimg0 Hbimg1 HN Hsp0 Hsp1 Hsp16 Rbc Rbb Hac HoffR HbofR. repeat split; try lia.
- cbn [conds_ok f_conds ss_facts ss_tin]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 34 _ HE34), (U_atom _ 19 _ HE19), (U_atom _ 35 _ HE35), (U_atom _ 24 _ HE24) by lia.
repeat split; try exact I; apply Bool.negb_true_iff, Z.ltb_ge; lia.
- cbn [alias_ok f_alias ss_facts ss_tin tin_alias]. split; [|split; [|split; [|exact I]]]; apply U_inj.
-- rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 8 _ HE8), (U_atom _ 19 _ HE19), (U_atom _ 34 _ HE34) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
-- rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 24 _ HE24), (U_atom _ 25 _ HE25), (U_atom _ 35 _ HE35) by lia. apply zcanon_id. unfold M64. lia.
-- rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 26 _ HE26), YI00.U_lit by lia. rewrite Z.lxor_0_r. apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok ubs2segs E ss_tin (mkst regs (Z_to_bv 64 FL_TIN) memc (seg_rom ubs2segs))).
{ unfold ss_tin. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | exact HPD | exact HFA].
constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_TIN) memc (seg_rom ubs2segs))) in HJ.
assert (WR : forall E0 rs cs0, bv_unsigned (ew E0 34) = p -> Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E0 (YQ0b.mkRegion (Some 34%nat) 0 1 0 1 cs0 :: rs) STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 rs cs0 H34 Hrs. eapply (wr_ok_cons_blk E0 (YQ0b.mkRegion (Some 34%nat) 0 1 0 1 cs0) rs STK sp0 FP (blocks L A) (blocks Lc Ac) 34 p pTmp Nt eq_refl H34 Htin Htfp); [cbn; lia | cbn; lia |].
induction Hrs as [|r rs' Hr Hrs' IHrs]; [apply wr_ok_nil | apply wr_ok_cons_ro; [exact Hr | exact IHrs]]. }
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cmpPixel. { apply WR; [exact HU34 | repeat constructor; cbn; lia]. }
jreg HS (10%bv:reg) as Ha0. rewrite HE36 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE37 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE32 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE33 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (KSTEP : forall (E' : env) (m m' : word -> option byte) cs0,
bv_unsigned (ew E' 34) = p -> KT m ->
frame_of E' [YQ0b.mkRegion (Some 34%nat) 0 1 0 1 cs0; YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))];
YQ0b.mkRegion (Some 2%nat) 112 128 112 112 [mkChunk 112 (CVal 8 (SOff 36 0)); mkChunk 120 (CVal 8 (SOff 37 0))]] m m' ->
KT m').
{ intros E' m m' cs0 H34 Km HFx. apply (KT_trans m m' Km). intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HFx Ha).
intros r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?H34; clear - Hna Hp HpN Hn Hpe; lia |]). destruct Hr. }
pose proof (KSTEP E _ _ _ HU34 K0 HF) as K1. clear HF HG.
destruct (cmp_objs (ms_mem ms) K1) as (Og1 & Oc1 & Ob1 & Rct1 & Rbt1 & Wg1 & Wc1).
destruct (ubs2_cmpPixel (ms_regs ms) (ms_mem ms) g gvals cfp cvals fhp bvals bc bb ctcur ctbef cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal
Ha0 Ha1 Ha2 Ha3 Ha4 Rbc Rbb Og1 Ongp Ogpal Oc1 Ocattr Octidx Ocnlp Oclpal Ob1 Obattr Obtidx Obnlp Oblpal
G0 G1 G16 C0 C1 C8 B0 B1 B8 Dgc Dgb Dcb Rct1 Rbt1 Sc0 Sc1 Sb0 Sb1) as (regs2 & mem2 & Hms & Hmem2 & Hres & Hfr2).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc ss_tin].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms) 1) 0) with (Z_to_bv 64 FL_TCMP).
2:{ rewrite Hra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
assert (HJ2 : journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc).
{ eapply (journal_exec _ _ LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2 | intros a []]. }
clear HJ.
assert (K2 : KT mem2) by (apply (KT_trans _ _ K1); intros a _ _; apply mbyte_of_eq; exact Hmem2).
jafter_stretch_keep HS 38%nat regs2 mem2 CMP_CLOB FL_TCMP [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. destruct (cmp_clob_out rr Hrr) as (?&?&?&?&?&?&?&?&?&?). apply Hfr2; assumption. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_out ubs2segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU34, ?HU35, ?HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU34, ?HU35, ?HU2; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_TCMP) mem2 (seg_rom ubs2segs))) in HJ2.
set (E2 := havoc E 38 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (HU34' : bv_unsigned (ew E2 34) = p) by (subst E2; ew_havocA; exact HU34).
assert (EXIT : forall ss ms', st_ok ubs2segs E2 ss ms' -> ss_pc ss = FL_TINX -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KT (ms_mem ms') ->
tin_post STK sp0 FP L A mem md Lc Ac mdc regs (mkCfg ms' mdc)).
{ intros ss ms' HS' Hpc Hrv Hkl HJ' K'. exists (ms_regs ms'), (ms_mem ms').
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|].
intros rr Hrr. subst E E2. exact (regs_kept_of_st_ok ubs2segs _ ss ms' regs _ TIN_KEPT HS' EA1 Hkl rr Hrr). }
assert (NEXT : forall ss ms', st_ok ubs2segs E2 ss ms' -> ss_pc ss = FL_TIN -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
sr_get (ss_regs ss) 19%bv = SOff 19 1 -> sr_get (ss_regs ss) 25%bv = SOff 25 1 -> sr_get (ss_regs ss) 23%bv = SOff 23 (-1) ->
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KT (ms_mem ms') -> p + 1 <> pend ->
SR ubs2segs (mkCfg ms' mdc) (tin_post STK sp0 FP L A mem md Lc Ac mdc regs)).
{ intros ss ms' HS' Hpc Hrv Hkl Q19 Q25 Q23 HJ' K' Hne.
pose proof (regs_kept_of_st_ok ubs2segs _ ss ms' regs _ TIN_KEPT HS' ltac:(subst E E2; exact EA1) Hkl) as HKR.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
eapply SR_mono.
{ eapply (IH (p + 1) (boff + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ pend HJ' K' Htin Htfp Hbin ltac:(lia) ltac:(lia) ltac:(lia) Hpe HpeN ltac:(lia) ltac:(lia) Hstk Hspv).
- rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 50)). exact G18.
- rewrite (st_ok_reg ubs2segs _ ss ms' 25%bv HS'), Q25. cbn [sv_denot]. subst E2. ew_havocA. rewrite HE25, unsigned_lit_small by lia. reflexivity.
- rewrite (st_ok_reg ubs2segs _ ss ms' 19%bv HS'), Q19. cbn [sv_denot]. subst E2. ew_havocA. rewrite HE19, unsigned_lit_small by lia. f_equal. lia.
- rewrite (st_ok_reg ubs2segs _ ss ms' 23%bv HS'), Q23. cbn [sv_denot]. subst E2. ew_havocA. rewrite HE23, unsigned_lit_small by lia. f_equal. lia.
- rewrite (HKR 24%bv ltac:(cbv; auto 50)). exact G24.
- rewrite (HKR 26%bv ltac:(cbv; auto 50)). exact G26. }
cbv beta. intros c' (regs' & mem' & -> & HJ'' & K'' & HK''). exists regs', mem'.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|].
intros rr Hrr. rewrite (HK'' rr Hrr). apply (HKR rr Hrr). }
assert (WR2 : forall rs cs0, Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E2 (YQ0b.mkRegion (Some 34%nat) 0 1 0 1 cs0 :: rs) STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros rs cs0 Hrs. apply WR; [exact HU34' | exact Hrs]. }
assert (LOOPC : forall b, branch_taken BC_NE (sv_denot E2 (SOff 23 (-1))) (sv_denot E2 (SLit 0)) = b -> (b = true <-> p + 1 <> pend)).
{ intros b Hc. rewrite branch_ne_U, (U_atom_off _ 23 (pend - p) (-1)), YI00.U_lit in Hc by first [subst E2; ew_havocA; exact HE23 | lia].
subst b. destruct (Z.eqb_spec (pend - p + -1) 0) as [Hq|Hq]; cbn; split; intros X; first [discriminate X | lia | reflexivity]. }
jbranch ubs2tbl HS; clear Hc.
- jrun_to LAWS ubs2tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (KSTEP E2 _ _ _ HU34' K2 HF) as K3. clear HF HG.
jbranch ubs2tbl HS.
+ assert (Hne : p + 1 <> pend) by exact (proj1 (LOOPC true Hc) eq_refl). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (KSTEP E2 _ _ _ HU34' K3 HF) as K4. clear HF HG.
apply (NEXT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl HJ2 K4 Hne).
+ clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ2 FL_TINX. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (KSTEP E2 _ _ _ HU34' K3 HF) as K4. clear HF HG.
apply SR_ret. apply (EXIT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ2 K4).
- jrun_to LAWS ubs2tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (KSTEP E2 _ _ _ HU34' K2 HF) as K3. clear HF HG.
jbranch ubs2tbl HS.
+ assert (Hne : p + 1 <> pend) by exact (proj1 (LOOPC true Hc) eq_refl). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (KSTEP E2 _ _ _ HU34' K3 HF) as K4. clear HF HG.
apply (NEXT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl HJ2 K4 Hne).
+ clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ2 FL_TINX. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (KSTEP E2 _ _ _ HU34' K3 HF) as K4. clear HF HG.
apply SR_ret. apply (EXIT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ2 K4).
Qed.
Definition tout_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_TOUTX) mem' (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KT mem' /\
(forall r : reg, In r TOUT_KEPT -> getr regs' r = getr regs r).
Variables (w h top left Wd Hd wsh : Z).
Hypothesis Hw : 1 <= w. Hypothesis Hlw : left + w <= Wd. Hypothesis Hl0 : 0 <= left.
Hypothesis Hh : 1 <= h. Hypothesis Hth : top + h <= Hd. Hypothesis Ht0' : 0 <= top.
Hypothesis HNd : N = Wd * Hd. Hypothesis Hwh : w * h <= Nt.
Hypothesis Wsh : word_mem ubs2segs mem0 (spv + 72) wsh. Hypothesis Rsh : 1 <= wsh < 2 ^ 64.
Hypothesis Whh : word_mem ubs2segs mem0 (spv + 80) h.
Hypothesis Ww : word_mem ubs2segs mem0 (spv + 88) w.
Hypothesis WW : word_mem ubs2segs mem0 (spv + 104) Wd.
Hypothesis Hh31 : h < 2 ^ 31.
Lemma stk_objs : forall m, KT m ->
word_mem ubs2segs m (spv + 72) wsh /\ word_mem ubs2segs m (spv + 80) h /\ word_mem ubs2segs m (spv + 88) w /\
word_mem ubs2segs m (spv + 104) Wd /\ word_mem ubs2segs m (spv + 112) g /\ word_mem ubs2segs m (spv + 120) cfp.
Proof.
intros m K. pose proof (proj1 alloc_ceiling_val) as Hac.
repeat split; intros k Hk; [rewrite <- (Wsh k Hk) | rewrite <- (Whh k Hk) | rewrite <- (Ww k Hk) | rewrite <- (WW k Hk) | rewrite <- (Wg k Hk) | rewrite <- (Wc k Hk)];
(apply K; clear - Hk Hsp0 Hsp1 Ht0 Ht1 Hac; lia).
Qed.
Definition ss_toutV (pc : Z) : sstate :=
mkSS pc sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 72 112 72 72
[mkChunk 72 (CVal 8 (SOff 32 0)); mkChunk 80 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0)); mkChunk 104 (CVal 8 (SOff 35 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (32%nat, mkAF 1 (2^64 - 1) 0); (22%nat, mkAF 0 (2^31 - 2) 0) ] [] []).
Lemma fl_tout : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KT memc ->
In (pTmp, Nt) (blocks Lc Ac) -> (In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
In (bimg, N) (blocks Lc Ac) ->
0 <= i -> i + Z.of_nat n = h -> (1 <= n)%nat ->
sp0 - STK <= spv -> spv = sp0 - 272 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 pTmp -> getr regs 9 = Z_to_bv 64 tv -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 22 = Z_to_bv 64 i -> getr regs 21 = Z_to_bv 64 (i * w) -> getr regs 27 = Z_to_bv 64 ((top + i) * Wd + left) ->
getr regs 24 = Z_to_bv 64 bimg -> getr regs 26 = Z_to_bv 64 1 ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 FL_TOUT) memc (seg_rom ubs2segs)) mdc) (tout_post STK sp0 FP L A mem md Lc Ac mdc regs).
Proof using B0 B1 B8 C0 C1 C8 Dcb Dgb Dgc G0 G1 G16 HN HNd Hbimg0 Hbimg1 Hbnn Hcnn Hh Hh31 Hl0 Hlw Hsp0 Hsp1 Hsp16 Ht0 Ht0' Ht1 Hth Hw Hwh IMG Ob Obattr Oblpal Obnlp Obtidx Oc Ocattr Oclpal Ocnlp Octidx Og Ogpal Ongp Rbt Rct Rsh Rtv Sb0 Sb1 Sc0 Sc1 WW Wc Wg Whh Wsh Ww Xb Xbimg Xbt Xc Xct Xg.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc HJ K0 Htin Htfp Hbin Hi Hin Hn Hstk Hspv
G2 G8 G9 G18 G22 G21 G27 G24 G26; [lia|].
hide_disj.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNt1 : 1 <= Nt) by (clear - Hw Hh Hwh; nia).
assert (HN1 : (top + i) * Wd + left + w <= N) by (clear - Hw Hlw Hl0 Hh Hth Ht0' HNd Hi Hin Hn; nia).
assert (Hrow0 : 0 <= i * w) by (clear - Hi Hw; nia).
assert (Hrow1 : i * w + w <= Nt) by (clear - Hi Hin Hn Hw Hwh; nia).
assert (Hb00 : 0 <= (top + i) * Wd + left) by (clear - Hi Ht0' Hl0 Hlw Hw; nia).
assert (Hiw : i * w <= (top + i) * Wd) by (clear - Hi Ht0' Hl0 Hlw Hw; nia).
assert (HNr : i * w + w <= N) by (clear - HN1 Hiw Hl0; lia).
assert (Hi31 : i <= 2 ^ 31 - 2) by (clear - Hin Hn Hh31; lia).
assert (HWd : 0 <= Wd /\ Wd < 2 ^ 32) by (clear - Hlw Hl0 Hw HNd HN Hh Hth Ht0'; nia).
destruct (stk_objs memc K0) as (Wsh0 & Wh0 & Ww0 & WW0 & _).
set (E := Ereg regs (map (Z_to_bv 64) [wsh; h; w; Wd] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 wsh) by (subst E; apply (Ereg_vals regs [wsh; h; w; Wd] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 h) by (subst E; apply (Ereg_vals regs [wsh; h; w; Wd] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 w) by (subst E; apply (Ereg_vals regs [wsh; h; w; Wd] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 Wd) by (subst E; apply (Ereg_vals regs [wsh; h; w; Wd] [] 3%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR0 : region_ok ubs2segs E memc (YQ0b.mkRegion (Some 2%nat) 72 112 72 72
[mkChunk 72 (CVal 8 (SOff 32 0)); mkChunk 80 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0)); mkChunk 104 (CVal 8 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?HE32, ?HE33, ?HE34, ?HE35, Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; assumption]).
all: clear - Rsh Hh Hh31 Hw Hlw Hl0 HWd; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (32%nat, mkAF 1 (2^64 - 1) 0); (22%nat, mkAF 0 (2^31 - 2) 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE32, (HE 22%nat 22%bv eq_refl), G22, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hac Hsp0 Hsp1 Hsp16 Rsh Hi Hi31. repeat split; lia. }
assert (HS : st_ok ubs2segs E (ss_toutV FL_TOUT) (mkst regs (Z_to_bv 64 FL_TOUT) memc (seg_rom ubs2segs))).
{ unfold ss_toutV. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_TOUT) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ FL_TIN. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : KT (ms_mem ms)).
{ apply (KT_trans _ _ K0). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs _ [2; 3; 4; 8; 9; 18; 21; 22; 24; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
jreg HS (19%bv:reg) as G19. rewrite (HE 21%nat 21%bv eq_refl), G21 in G19.
jreg HS (25%bv:reg) as G25. rewrite (HE 27%nat 27%bv eq_refl), G27 in G25.
jreg HS (23%bv:reg) as G23. rewrite HE34 in G23.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_tin (Z.to_nat w) (pTmp + i * w) ((top + i) * Wd + left) STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) (pTmp + (i * w + w)) HJ K1 Htin Htfp Hbin);
[ clear - Hrow0; lia | clear - Hw; lia | clear - Hw; lia | clear - Hrow1; lia | clear - HNr; lia | exact Hb00 | clear - HN1 Hw; lia | exact Hstk | exact Hspv
| rewrite (HKR 2%bv ltac:(cbv; auto 50)); exact G2 | rewrite (HKR 8%bv ltac:(cbv; auto 50)); exact G8
| rewrite (HKR 9%bv ltac:(cbv; auto 50)); exact G9 | rewrite (HKR 18%bv ltac:(cbv; auto 50)); exact G18
| exact G25 | rewrite G19; f_equal; clear; lia | rewrite G23; f_equal; clear; lia
| rewrite (HKR 24%bv ltac:(cbv; auto 50)); exact G24 | rewrite (HKR 26%bv ltac:(cbv; auto 50)); exact G26 ]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & K3 & HK3). clear HS HJ.
assert (R3 : forall r : reg, In r TIN_KEPT -> getr regs3 r = getr regs r) by (intros rr H1; rewrite (HK3 rr H1); exact (HKR rr H1)).
destruct (stk_objs mem3 K3) as (Wsh3 & Wh3 & Ww3 & WW3 & _).
set (E3 := Ereg regs3 (map (Z_to_bv 64) [wsh; h; w; Wd] ++ [])).
assert (HE3 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E3 m = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (HE3_32 : ew E3 32 = Z_to_bv 64 wsh) by (subst E3; apply (Ereg_vals regs3 [wsh; h; w; Wd] [] 0%nat); reflexivity).
assert (HE3_33 : ew E3 33 = Z_to_bv 64 h) by (subst E3; apply (Ereg_vals regs3 [wsh; h; w; Wd] [] 1%nat); reflexivity).
assert (HE3_34 : ew E3 34 = Z_to_bv 64 w) by (subst E3; apply (Ereg_vals regs3 [wsh; h; w; Wd] [] 2%nat); reflexivity).
assert (HE3_35 : ew E3 35 = Z_to_bv 64 Wd) by (subst E3; apply (Ereg_vals regs3 [wsh; h; w; Wd] [] 3%nat); reflexivity).
assert (G3_2 : getr regs3 2 = Z_to_bv 64 spv) by (rewrite (R3 2%bv ltac:(cbv; auto 50)); exact G2).
assert (G3_22 : getr regs3 22 = Z_to_bv 64 i) by (rewrite (R3 22%bv ltac:(cbv; auto 50)); exact G22).
assert (HU3_2 : bv_unsigned (ew E3 2) = spv) by (rewrite (HE3 2%nat 2%bv eq_refl), G3_2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR0 : region_ok ubs2segs E3 mem3 (YQ0b.mkRegion (Some 2%nat) 72 112 72 72
[mkChunk 72 (CVal 8 (SOff 32 0)); mkChunk 80 (CVal 8 (SOff 33 0)); mkChunk 88 (CVal 8 (SOff 34 0)); mkChunk 104 (CVal 8 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU3_2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?HE3_32, ?HE3_33, ?HE3_34, ?HE3_35, Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; assumption]).
all: clear - Rsh Hh Hh31 Hw Hlw Hl0 HWd; lia. }
assert (HFA : atoms_ok E3 [ (2%nat, mkAF CEIL_MIN (2^63) 4); (32%nat, mkAF 1 (2^64 - 1) 0); (22%nat, mkAF 0 (2^31 - 2) 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU3_2, HE3_32, (HE3 22%nat 22%bv eq_refl), G3_22, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. clear - Hac Hsp0 Hsp1 Hsp16 Rsh Hi Hi31. repeat split; lia. }
assert (HS : st_ok ubs2segs E3 (ss_toutV FL_TINX) (mkst regs3 (Z_to_bv 64 FL_TINX) mem3 (seg_rom ubs2segs))).
{ unfold ss_toutV. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]]. }
clear HR0 HFA.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 FL_TINX) mem3 (seg_rom ubs2segs))) in HJ3.
jrun LAWS ubs2tbl_ok HS HJ3. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (K4 : KT (ms_mem msx)) end.
{ apply (KT_trans _ _ K3). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (HU3_33 : U E3 (SOff 33 0) = h) by (apply (U_atom _ 33 h HE3_33); clear - Hh Hh31; lia).
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, (U_atom_off _ 22 i 1), HU3_33 in Hc by first [rewrite (HE3 22%nat 22%bv eq_refl); exact G3_22 | clear - Hi Hi31; lia].
assert (Hne : i + 1 <> h) by (destruct (Z.eqb_spec (i + 1) h); [discriminate Hc | assumption]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ3 FL_TOUT. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (K5 : KT (ms_mem msx)) end.
{ apply (KT_trans _ _ K4). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs3 _ [2; 3; 4; 8; 9; 18; 24; 26]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR4 end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ3 K5 Htin Htfp Hbin ltac:(clear - Hi; lia) ltac:(clear - Hin; lia) ltac:(clear - Hin Hne Hn; lia) Hstk Hspv).
- rewrite (HKR4 2%bv ltac:(cbv; auto 50)). exact G3_2.
- rewrite (HKR4 8%bv ltac:(cbv; auto 50)), (R3 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR4 9%bv ltac:(cbv; auto 50)), (R3 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR4 18%bv ltac:(cbv; auto 50)), (R3 18%bv ltac:(cbv; auto 50)). exact G18.
- reg_nowF HS ltac:(rewrite (HE3 22%nat 22%bv eq_refl), G3_22, unsigned_lit_small by (clear - Hi Hi31; lia); reflexivity).
- lazymatch type of HS with st_ok _ _ ?ssx ?msx => rewrite (st_ok_reg ubs2segs E3 ssx msx 21%bv HS) end. eval_sr_get. apply denot_of_U'.
replace ((i + 1) * w) with (i * w + w) by ring.
rewrite (U_add_small E3 _ _ (i * w) w); [reflexivity | | | exact Hrow0 | clear - Hw; lia | clear - Hrow1 Ht0 Ht1 Hac; lia].
+ apply U_atom; [| clear - Hrow0 Hrow1 Ht0 Ht1 Hac HNt1 Hw; lia]. rewrite (HE3 21%nat 21%bv eq_refl), (R3 21%bv ltac:(cbv; auto 50)). exact G21.
+ apply (U_atom _ 34 w HE3_34). clear - Hw Hlw Hl0 HWd; lia.
- lazymatch type of HS with st_ok _ _ ?ssx ?msx => rewrite (st_ok_reg ubs2segs E3 ssx msx 27%bv HS) end. eval_sr_get. apply denot_of_U'.
replace ((top + (i + 1)) * Wd + left) with ((top + i) * Wd + left + Wd) by ring.
rewrite (U_add_small E3 _ _ ((top + i) * Wd + left) Wd); [reflexivity | | | exact Hb00 | clear - HWd; lia | clear - HN1 Hw HN HWd; lia].
+ apply U_atom; [| clear - Hb00 HN1 Hw HN; lia]. rewrite (HE3 27%nat 27%bv eq_refl), (R3 27%bv ltac:(cbv; auto 50)). exact G27.
+ apply (U_atom _ 35 Wd HE3_35). clear - HWd; lia.
- rewrite (HKR4 24%bv ltac:(cbv; auto 50)), (R3 24%bv ltac:(cbv; auto 50)). exact G24.
- rewrite (HKR4 26%bv ltac:(cbv; auto 50)), (R3 26%bv ltac:(cbv; auto 50)). exact G26. }
cbv beta. intros c' (regs' & mem' & -> & HJ' & K' & HK'). exists regs', mem'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact K'|].
intros rr Hrr. rewrite (HK' rr Hrr). cbv in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [match goal with |- getr _ ?r = _ => rewrite (HKR4 r ltac:(cbv; auto 50)); apply (R3 r); solve [cbv; auto 50] end |]). destruct Hrr.
-
clear Hc. jrun_to LAWS ubs2tbl_ok HS HJ3 FL_TOUTX. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (K5 : KT (ms_mem msx)) end.
{ apply (KT_trans _ _ K4). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs Ef ssf msf regs3 _ [2; 3; 4; 8; 9; 18; 24; 26]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR4 end.
apply SR_ret. lazymatch goal with |- _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx) end.
split; [rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ3|]. split; [exact K5|].
intros rr Hrr. cbv in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [match goal with |- getr _ ?r = _ => rewrite (HKR4 r ltac:(cbv; auto 50)); apply (R3 r); solve [cbv; auto 50] end |]). destruct Hrr.
Qed.
End e.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
