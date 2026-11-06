(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3a YI06 YI5b YI09 YI08 YI0r YI1w YI1v YI4l YI21 YI5o YI5l YI6b YI5n YI20 YI1d YI2l.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI6c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FL_TOUT  : Z := Eval vm_compute in (src0_A_flushFrame + 0x5c0).
Definition FL_TIN   : Z := Eval vm_compute in (src0_A_flushFrame + 0x5e0).
Definition FL_TCMP  : Z := Eval vm_compute in (src0_A_flushFrame + 0x600).
Definition FL_TINX  : Z := Eval vm_compute in (src0_A_flushFrame + 0x618).
Definition FL_TOUTX : Z := Eval vm_compute in (src0_A_flushFrame + 0x630).
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
Lemma wrap64_nzT : forall v, -256 < v < 256 -> v <> 0 -> zcanon (bv_wrap 64 v + 0) <> 0.
Proof. intros v Hv Hnz. unfold zcanon, bv_wrap, M64. cbn [bv_modulus]. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
intros Hm. apply (Z.mod_divide v (2 ^ 64)) in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0 \/ q <= -1 \/ q >= 1) by lia. nia. Qed.
Lemma cmpPixel_fn_rangeT : forall cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b,
-256 < cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef a b < 256.
Proof. intros. unfold cmpPixel_fn. repeat (destruct (_ : bool); try lia). apply memcmp_spec_range. Qed.
Definition TIN_KEPT : list reg := [2; 3; 4; 8; 9; 18; 21; 27; 24; 23; 25; 22]%bv.
Definition tin_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_AND (SOff 19 0) (SLit 4294967295)), SOff 34 0) ].
Definition ss_tin : sstate :=
mkSS FL_TIN (sr_set sr_atoms 26%bv (SLit 4294967295))
[ YP09.mkRegion (Some 20%nat) 0 1 0 1 [mkChunk 0 (CVal 1 (SOff 32 0))] ;
YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))] ;
YP09.mkRegion (Some 2%nat) 112 120 112 112 [mkChunk 112 (CVal 8 (SOff 35 0))] ]
None (mkFacts [ (20%nat, mkAF 4096 (CEIL_MAX - 1) 0); (34%nat, mkAF 4096 (CEIL_MAX - 1) 0);
(2%nat, mkAF CEIL_MIN (2^63) 4); (19%nat, mkAF 0 4294967295 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0) ] [] tin_alias).
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
[ YP09.mkRegion (Some 2%nat) 80 120 80 80
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SOff 33 0)); mkChunk 96 (CVal 8 (SOff 34 0));
mkChunk 104 (CVal 8 (SOff 35 0)); mkChunk 112 (CVal 8 (SOff 36 0))] ]
None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (33%nat, mkAF 1 (2^64 - 1) 0) ] [] []).
Definition TOUT_KEPT : list reg := [2; 3; 4; 8; 9; 18]%bv.
Definition hidePt (P : Prop) : Prop := P.
End d.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (hidePt (A \/ B)) in H end.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Section j.
Variables (mem0 : word -> option byte) (g cfp fhp bimg N pTmp Nt spv tv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis Og : obj_at src0segs mem0 g LAY_CGIF gvals.
Hypothesis Ongp : nth_error gvals CG_ngp = Some ngp.
Hypothesis Ogpal : nth_error gvals CG_pal = Some gpal.
Hypothesis Oc : obj_at src0segs mem0 cfp LAY_FrameConfig cvals.
Hypothesis Ocattr : nth_error cvals FR_attr = Some cattr.
Hypothesis Octidx : nth_error cvals FR_ctidx = Some ctidx.
Hypothesis Ocnlp : nth_error cvals FR_nlp = Some cnlp.
Hypothesis Oclpal : nth_error cvals FR_lpal = Some clpal.
Hypothesis Ob : obj_at src0segs mem0 fhp LAY_FrameConfig bvals.
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
Hypothesis Rct : rdn src0segs mem0 (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur.
Hypothesis Rbt : rdn src0segs mem0 (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef.
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
Hypothesis Wtv : word_mem src0segs mem0 (spv + 112) tv. Hypothesis Rtv : 0 <= tv < 2 ^ 64.
Definition KT (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (pTmp <= a < pTmp + Nt) -> mbyte src0segs m a = mbyte src0segs mem0 a.
Lemma KT_trans : forall m1 m2, KT m1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (pTmp <= a < pTmp + Nt) -> mbyte src0segs m2 a = mbyte src0segs m1 a) -> KT m2.
Proof. intros m1 m2 K1 K2 a Ha Hna. rewrite (K2 a Ha Hna). apply K1; assumption. Qed.
Lemma cmp_objs : forall m, KT m ->
obj_at src0segs m g LAY_CGIF gvals /\ obj_at src0segs m cfp LAY_FrameConfig cvals /\ obj_at src0segs m fhp LAY_FrameConfig bvals /\
rdn src0segs m (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur /\
rdn src0segs m (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef /\
word_mem src0segs m (spv + 112) tv.
Proof.
intros m K. pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
split; [| split; [| split; [| split; [| split]]]].
- eapply obj_at_transport_range; [exact Og | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply K; clear - Hi Xg G0 G1 Ht0 Ht1 Hac HGSv; unfold hidePt in *; lia].
- eapply obj_at_transport_range; [exact Oc | exact lay_inside_FrameConfig | intros i Hi; apply K; clear - Hi Xc C0 C1 Ht0 Ht1 Hac; unfold hidePt in *; lia].
- eapply obj_at_transport_range; [exact Ob | exact lay_inside_FrameConfig | intros i Hi; apply K; clear - Hi Xb B0 B1 Ht0 Ht1 Hac; unfold hidePt in *; lia].
- rewrite <- Rct. apply rdn_agree. intros k Hk. apply K; clear - Hk Xct Sc0 Sc1 Hcnn Ht0 Ht1 Hac; unfold hidePt in *; lia.
- rewrite <- Rbt. apply rdn_agree. intros k Hk. apply K; clear - Hk Xbt Sb0 Sb1 Hbnn Ht0 Ht1 Hac; unfold hidePt in *; lia.
- intros k Hk. rewrite <- (Wtv k Hk). apply K; clear - Hk Hsp0 Hsp1 Ht0 Ht1 Hac; lia.
Qed.
Definition TRF (m : word -> option byte) (a bo : Z) : Z :=
if cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at m a) (byte_at mem0 (bimg + bo)) =? 0 then tv mod 256 else byte_at m a.
Lemma byte_at_of_val1 : forall m a v, val_mem src0segs m a 1 v -> 0 <= v < 256 -> byte_at m a = v.
Proof.
intros m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. unfold byte_at. rewrite Hv.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Definition tin_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (p boff pend : Z) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_TINX) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KT mem' /\
getr regs' 26 = Z_to_bv 64 4294967295 /\
(forall r : reg, In r TIN_KEPT -> getr regs' r = getr regs r) /\
(forall a, pTmp <= a < pTmp + Nt -> byte_at mem' a = if (p <=? a) && (a <? pend) then TRF memc a (boff + (a - p)) else byte_at memc a).
Lemma fl_tinV : forall (n : nat) (p boff : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc pend,
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KT memc ->
In (pTmp, Nt) (blocks Lc Ac) -> (In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
In (bimg, N) (blocks Lc Ac) ->
pTmp <= p -> p + Z.of_nat n = pend -> (1 <= n)%nat -> pend <= pTmp + Nt ->
0 <= boff -> boff + Z.of_nat n <= N ->
sp0 - STK <= spv -> spv = sp0 - 272 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 19 = Z_to_bv 64 boff -> getr regs 20 = Z_to_bv 64 p -> getr regs 25 = Z_to_bv 64 pend ->
getr regs 22 = Z_to_bv 64 bimg -> getr regs 26 = Z_to_bv 64 4294967295 ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_TIN) memc (seg_rom src0segs)) mdc) (tin_postV STK sp0 FP L A mem md Lc Ac mdc regs memc p boff pend).
Proof.
intros n. induction n as [|n IH]; intros p boff STK sp0 FP L A mem md Lc Ac mdc regs memc pend HJ K0 Htin Htfp Hbin Hp HpN Hn Hpe Hb0 HbN Hstk Hspv
G2 G8 G9 G18 G19 G20 G25 G22 G26; [lia|].
hide_disj.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
destruct (cmp_objs memc K0) as (Og' & Oc' & Ob' & Rct' & Rbt' & Wtv').
set (bc := byte_at memc p). set (bb := byte_at memc (bimg + boff)).
pose proof (byte_at_range memc p) as Rbc. pose proof (byte_at_range memc (bimg + boff)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [bc; bb; bimg + boff; tv] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 bc) by (subst E; apply (Ereg_vals regs [bc; bb; bimg + boff; tv] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 bb) by (subst E; apply (Ereg_vals regs [bc; bb; bimg + boff; tv] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (bimg + boff)) by (subst E; apply (Ereg_vals regs [bc; bb; bimg + boff; tv] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 tv) by (subst E; apply (Ereg_vals regs [bc; bb; bimg + boff; tv] [] 3%nat); reflexivity).
assert (HU20 : bv_unsigned (ew E 20) = p) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = bimg + boff) by (rewrite HE34; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU19 : bv_unsigned (ew E 19) = boff) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 22) = bimg) by (rewrite (HE 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; lia).
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 20%nat) 0 1 0 1 [mkChunk 0 (CVal 1 (SOff 32 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable src0_msyms). replace (p + o) with (pTmp + (p - pTmp + o)) by lia. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pTmp Nt (p - pTmp + o) HHc Htin ltac:(clear - Hp HpN Hn Hpe Ho; lia))). }
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. replace p with (pTmp + (p - pTmp)) by lia. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pTmp Nt (p - pTmp) HHc Htin ltac:(clear - Hp HpN Hn Hpe; lia))). }
assert (HR1 : region_ok src0segs E memc (YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn. rewrite Z.add_0_r. apply byte_at_val. apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc bimg N boff HHc Hbin ltac:(clear - Hb0 HbN Hn; lia))). }
assert (HR2 : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 112 120 112 112 [mkChunk 112 (CVal 8 (SOff 35 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ tv); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wtv']. }
assert (HPD : pairwise_disjoint E (ss_mem ss_tin)).
{ cbn [ss_mem ss_tin pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU20, HU34, HU2.
clear - Hp HpN Hn Hpe Hb0 HbN Xbimg Hsp0 Ht1 Hbimg1; unfold hidePt in *. repeat split; lia. }
assert (HFA : facts_ok E (ss_facts ss_tin)).
{ split; [| split; [exact I|]].
- cbn [ss_facts ss_tin f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU20, HU34, HU2, HU19, HE32, HE33, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
clear - Hp HpN Hn Hpe Hb0 HbN Ht0 Ht1 Hbimg0 Hbimg1 HN Hsp0 Hsp1 Hsp16 Rbc Rbb Hac. repeat split; try lia.
- cbn [ss_facts ss_tin f_alias tin_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit, (U_atom _ 22 bimg ltac:(rewrite (HE 22%nat 22%bv eq_refl); exact G22)), (U_atom _ 19 boff ltac:(rewrite (HE 19%nat 19%bv eq_refl); exact G19)), (U_atom _ 34 (bimg + boff) HE34) by lia.
change 4294967295 with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok src0segs E ss_tin (mkst regs (Z_to_bv 64 FL_TIN) memc (seg_rom src0segs))).
{ unfold ss_tin. apply entry_st_ok_full; [| vm_compute; reflexivity | | exact HPD | exact HFA].
- apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G26. reflexivity.
- constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor. }
clear HR0 HR1 HR2 HPD HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_TIN) memc (seg_rom src0segs))) in HJ.
assert (WR : forall E0 rs cs0, bv_unsigned (ew E0 20) = p -> Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E0 (YP09.mkRegion (Some 20%nat) 0 1 0 1 cs0 :: rs) STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros E0 rs cs0 H20 Hrs. eapply (wr_ok_cons_blk E0 (YP09.mkRegion (Some 20%nat) 0 1 0 1 cs0) rs STK sp0 FP (blocks L A) (blocks Lc Ac) 20 p pTmp Nt eq_refl H20 Htin Htfp); [cbn; lia | cbn; lia |].
induction Hrs as [|r rs' Hr Hrs' IHrs]; [apply wr_ok_nil | apply wr_ok_cons_ro; [exact Hr | exact IHrs]]. }
jrun_to LAWS src0tbl_ok HS HJ src0_A_cmpPixel. { apply WR; [exact HU20 | repeat constructor; cbn; lia]. }
jreg HS (10%bv:reg) as Ha0. rewrite (HE 8%nat 8%bv eq_refl), G8 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite (HE 9%nat 9%bv eq_refl), G9 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE32 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE33 in Ha4.
jreg HS (1%bv:reg) as Hra.
cbn [ms_mem mkst] in HF.
assert (KSTEP : forall (E' : env) (m m' : word -> option byte) cs0,
bv_unsigned (ew E' 20) = p -> KT m ->
frame_of E' [YP09.mkRegion (Some 20%nat) 0 1 0 1 cs0; YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))];
YP09.mkRegion (Some 2%nat) 112 120 112 112 [mkChunk 112 (CVal 8 (SOff 35 0))]] m m' ->
KT m').
{ intros E' m m' cs0 H20 Km HFx. apply (KT_trans m m' Km). intros a Ha Hna. apply (mbyte_of_frame _ _ _ _ a HFx Ha).
intros r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?H20; clear - Hna Hp HpN Hn Hpe; lia |]). destruct Hr. }
assert (BSTEP : forall (E' : env) (m m' : word -> option byte) cs0,
bv_unsigned (ew E' 20) = p ->
frame_of E' [YP09.mkRegion (Some 20%nat) 0 1 0 1 cs0; YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 33 0))];
YP09.mkRegion (Some 2%nat) 112 120 112 112 [mkChunk 112 (CVal 8 (SOff 35 0))]] m m' ->
forall a, 0 <= a < 2 ^ 64 -> a <> p -> byte_at m' a = byte_at m a).
{ intros E' m m' cs0 H20 HFx a Ha Hna. unfold byte_at. rewrite (mbyte_of_frame _ _ _ _ a HFx Ha); [reflexivity|].
intros r Hr. cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; rewrite ?H20; clear - Hna; lia |]). destruct Hr. }
pose proof (BSTEP E _ _ _ HU20 HF) as BS1.
pose proof (KSTEP E _ _ _ HU20 K0 HF) as K1. clear HF HG.
destruct (cmp_objs (ms_mem ms) K1) as (Og1 & Oc1 & Ob1 & Rct1 & Rbt1 & Wtv1).
destruct (src0_cmpPixel (ms_regs ms) (ms_mem ms) g gvals cfp cvals fhp bvals bc bb ctcur ctbef cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal
Ha0 Ha1 Ha2 Ha3 Ha4 Rbc Rbb Og1 Ongp Ogpal Oc1 Ocattr Octidx Ocnlp Oclpal Ob1 Obattr Obtidx Obnlp Oblpal
G0 G1 G16 C0 C1 C8 B0 B1 B8 Dgc Dgb Dcb Rct1 Rbt1 Sc0 Sc1 Sb0 Sb1) as (regs2 & mem2 & Hms & Hmem2 & Hres & Hfr2).
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc ss_tin].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs ms) 1) 0) with (Z_to_bv 64 FL_TCMP).
2:{ rewrite Hra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
assert (HJ2 : journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc).
{ eapply (journal_exec _ _ LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2 | intros a []]. }
clear HJ.
assert (K2 : KT mem2) by (apply (KT_trans _ _ K1); intros a _ _; apply mbyte_of_eq; exact Hmem2).
jafter_stretch_keep HS 36%nat regs2 mem2 CMP_CLOB FL_TCMP [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. destruct (cmp_clob_out rr Hrr) as (?&?&?&?&?&?&?&?&?&?). apply Hfr2; assumption. }
{ constructor; [|constructor; [|constructor; [|constructor]]];
(eapply (region_kept_out src0segs _ _ _ _ 0 0); [intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2
| cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU20, ?HU34, ?HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU20, ?HU34, ?HU2; lia
| intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 FL_TCMP) mem2 (seg_rom src0segs))) in HJ2.
set (E2 := havoc E 36 (map (getr regs2) CMP_CLOB)) in HS.
assert (EA1 : env_agree 32 E E2) by (apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (HU20' : bv_unsigned (ew E2 20) = p) by (subst E2; ew_havocA; exact HU20).
assert (EXIT : forall ss ms', st_ok src0segs E2 ss ms' -> ss_pc ss = FL_TINX -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
sr_get (ss_regs ss) 26%bv = SLit 4294967295 ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KT (ms_mem ms') ->
(forall a, 0 <= a < 2 ^ 64 -> a <> p -> byte_at (ms_mem ms') a = byte_at memc a) -> byte_at (ms_mem ms') p = TRF memc p boff -> p + 1 = pend ->
tin_postV STK sp0 FP L A mem md Lc Ac mdc regs memc p boff pend (mkCfg ms' mdc)).
{ intros ss ms' HS' Hpc Hrv Hkl Q26 HJ' K' F1 F2 Hpe1. exists (ms_regs ms'), (ms_mem ms').
split; [rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact HJ'|]. split; [exact K'|].
split; [rewrite (st_ok_reg src0segs _ ss ms' 26%bv HS'), Q26; reflexivity|].
split; [intros rr Hrr; subst E E2; exact (regs_kept_of_st_ok src0segs _ ss ms' regs _ TIN_KEPT HS' EA1 Hkl rr Hrr)|].
intros a Ha. destruct (Z.eq_dec a p) as [-> | Hap].
- replace ((p <=? p) && (p <? pend)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hpe1; lia).
rewrite F2. f_equal. clear; lia.
- replace ((p <=? a) && (a <? pend)) with false by (symmetry; apply andb_false_iff; destruct (Z.lt_ge_cases a p); [left; apply Z.leb_gt | right; apply Z.ltb_ge]; clear - Hap Hpe1 H; lia).
apply F1; [clear - Ha Ht0 Ht1 Hac; lia | exact Hap]. }
assert (NEXT : forall ss ms', st_ok src0segs E2 ss ms' -> ss_pc ss = FL_TIN -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
sr_get (ss_regs ss) 20%bv = SOff 20 1 -> sr_get (ss_regs ss) 19%bv = SOff 19 1 -> sr_get (ss_regs ss) 26%bv = SLit 4294967295 ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> KT (ms_mem ms') -> p + 1 <> pend ->
(forall a, 0 <= a < 2 ^ 64 -> a <> p -> byte_at (ms_mem ms') a = byte_at memc a) -> byte_at (ms_mem ms') p = TRF memc p boff ->
SR src0segs (mkCfg ms' mdc) (tin_postV STK sp0 FP L A mem md Lc Ac mdc regs memc p boff pend)).
{ intros ss ms' HS' Hpc Hrv Hkl Q20 Q19 Q26 HJ' K' Hne F1 F2.
pose proof (regs_kept_of_st_ok src0segs _ ss ms' regs _ TIN_KEPT HS' ltac:(subst E E2; exact EA1) Hkl) as HKR.
rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc.
eapply SR_mono.
{ eapply (IH (p + 1) (boff + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ pend HJ' K' Htin Htfp Hbin ltac:(lia) ltac:(lia) ltac:(lia) Hpe ltac:(lia) ltac:(lia) Hstk Hspv).
- rewrite (HKR 2%bv ltac:(cbv; auto 50)). exact G2.
- rewrite (HKR 8%bv ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR 18%bv ltac:(cbv; auto 50)). exact G18.
- rewrite (st_ok_reg src0segs _ ss ms' 19%bv HS'), Q19. cbn [sv_denot]. subst E2. ew_havocA. rewrite HU19. reflexivity.
- rewrite (st_ok_reg src0segs _ ss ms' 20%bv HS'), Q20. cbn [sv_denot]. subst E2. ew_havocA. rewrite HU20. reflexivity.
- rewrite (HKR 25%bv ltac:(cbv; auto 50)). exact G25.
- rewrite (HKR 22%bv ltac:(cbv; auto 50)). exact G22.
- rewrite (st_ok_reg src0segs _ ss ms' 26%bv HS'), Q26. reflexivity. }
cbv beta. intros c' (regs' & mem' & -> & HJ'' & K'' & R26 & HK'' & HV''). exists regs', mem'.
split; [reflexivity|]. split; [exact HJ''|]. split; [exact K''|]. split; [exact R26|].
split; [intros rr Hrr; rewrite (HK'' rr Hrr); apply (HKR rr Hrr)|].
intros a Ha. rewrite (HV'' a Ha). destruct (Z.eq_dec a p) as [-> | Hap].
- replace ((p + 1 <=? p) && (p <? pend)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; clear; lia).
replace ((p <=? p) && (p <? pend)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - HpN; lia).
rewrite F2. f_equal. clear; lia.
- replace (p + 1 <=? a) with (p <=? a) by (destruct (Z.leb_spec p a), (Z.leb_spec (p + 1) a); try reflexivity; exfalso; clear - Hap H H0; lia).
assert (Fa : byte_at (ms_mem ms') a = byte_at memc a) by (apply F1; [clear - Ha Ht0 Ht1 Hac; lia | exact Hap]).
unfold TRF. rewrite Fa. replace (boff + 1 + (a - (p + 1))) with (boff + (a - p)) by (clear; lia). reflexivity. }
assert (WR2 : forall rs cs0, Forall (fun r => r_whi r <= r_wlo r) rs ->
wr_ok E2 (YP09.mkRegion (Some 20%nat) 0 1 0 1 cs0 :: rs) STK sp0 FP (blocks L A) (blocks Lc Ac)).
{ intros rs cs0 Hrs. apply WR; [exact HU20' | exact Hrs]. }
assert (B2 : forall a, 0 <= a < 2 ^ 64 -> a <> p -> byte_at mem2 a = byte_at memc a)
by (intros a Ha Hap; rewrite <- (BS1 a Ha Hap); unfold byte_at; rewrite (mbyte_of_eq _ _ _ _ Hmem2); reflexivity).
assert (PVAL : forall ss ms' e v, st_ok src0segs E2 ss ms' ->
(exists rg0, nth_error (ss_mem ss) 0 = Some rg0 /\ r_base rg0 = Some 20%nat /\ In (mkChunk 0 (CVal 1 e)) (r_chunks rg0)) ->
bv_unsigned (sv_denot E2 e) mod 2 ^ 8 = v -> byte_at (ms_mem ms') p = v).
{ intros ss ms' e v HS' (rg0 & Hrg0 & Hbs0 & Hin0) He. apply byte_at_of_val1; [| rewrite <- He; apply Z.mod_pos_bound; clear; lia].
replace p with (p + 0) by (clear; lia).
eapply (vval_mem_of_chunk_mod src0segs E2 (ms_mem ms') rg0 20%nat p 0 1%N e v); [exact (vst_ok_region_nth src0segs E2 ss ms' 0%nat rg0 HS' Hrg0) | exact Hbs0 | exact Hin0 | exact HU20' | exact He | cbn; clear; lia]. }
assert (HTRF : TRF memc p boff = if cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb =? 0 then tv mod 256 else bc).
{ unfold TRF. fold bc. replace (byte_at mem0 (bimg + boff)) with bb; [reflexivity|]. subst bb. unfold byte_at. rewrite (K0 (bimg + boff)); [reflexivity | clear - Hb0 HbN Hbimg0 Hbimg1 Hac; lia |].
clear - Xbimg Hb0 HbN Hn. unfold hidePt in *. lia. }
jbranch src0tbl HS.
-
assert (HCZ : cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb <> 0).
{ intros Hz. rewrite branch_ne_U, U_lit, (U_atom E2 38 0) in Hc; [discriminate Hc | | clear; lia | clear; lia].
subst E2. change 38%nat with (36 + 2)%nat. rewrite (ew_havoc_new E 36 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) by (cbn; lia).
cbn [nth map CMP_CLOB]. rewrite Hres, Hz. reflexivity. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (BSTEP E2 _ _ _ HU20' HF) as BS3. pose proof (KSTEP E2 _ _ _ HU20' K2 HF) as K3. clear HF HG.
jbranch src0tbl HS.
+ rewrite branch_ne_U, (U_atom_off _ 20 p 1), (U_atom _ 25 pend) in Hc by first [subst E2; ew_havocA; first [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | rewrite (HE 25%nat 25%bv eq_refl); exact G25] | lia].
assert (Hne : p + 1 <> pend) by (destruct (Z.eqb_spec (p + 1) pend); [discriminate Hc | assumption]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (BSTEP E2 _ _ _ HU20' HF) as BS4. pose proof (KSTEP E2 _ _ _ HU20' K3 HF) as K4. clear HF HG.
apply (NEXT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl HJ2 K4 Hne (fun a Ha Hap => eq_trans (BS4 a Ha Hap) (eq_trans (BS3 a Ha Hap) (B2 a Ha Hap)))).
apply (PVAL _ _ (SOff 32 0) _ HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto|]. rewrite HTRF. destruct (Z.eqb_spec (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb) 0) as [Hq|_]; [exfalso; exact (HCZ Hq)|]. cbn [sv_denot]. rewrite Z.add_0_r. subst E2. ew_havocA. rewrite Z_to_bv_bv_unsigned, HE32, unsigned_lit_small by (clear - Rbc; lia). apply Z.mod_small. clear - Rbc. lia.
+ rewrite branch_ne_U, (U_atom_off _ 20 p 1), (U_atom _ 25 pend) in Hc by first [subst E2; ew_havocA; first [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | rewrite (HE 25%nat 25%bv eq_refl); exact G25] | lia].
assert (Hpe1 : p + 1 = pend) by (destruct (Z.eqb_spec (p + 1) pend); [assumption | discriminate Hc]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_TINX. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (BSTEP E2 _ _ _ HU20' HF) as BS4. pose proof (KSTEP E2 _ _ _ HU20' K3 HF) as K4. clear HF HG.
apply SR_ret. apply (EXIT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl HJ2 K4 (fun a Ha Hap => eq_trans (BS4 a Ha Hap) (eq_trans (BS3 a Ha Hap) (B2 a Ha Hap)))); [| exact Hpe1].
apply (PVAL _ _ (SOff 32 0) _ HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto|]. rewrite HTRF. destruct (Z.eqb_spec (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb) 0) as [Hq|_]; [exfalso; exact (HCZ Hq)|]. cbn [sv_denot]. rewrite Z.add_0_r. subst E2. ew_havocA. rewrite Z_to_bv_bv_unsigned, HE32, unsigned_lit_small by (clear - Rbc; lia). apply Z.mod_small. clear - Rbc. lia.
-
assert (HCZ : cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb = 0).
{ destruct (Z.eq_dec (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb) 0) as [Hz|Hnz]; [exact Hz | exfalso].
rewrite branch_ne_U, U_lit, U_SOff in Hc by (clear; lia). subst E2. change 38%nat with (36 + 2)%nat in Hc.
rewrite (ew_havoc_new E 36 (map (getr regs2) CMP_CLOB) 2 (Z_to_bv 64 0)) in Hc by (cbn; lia). cbn [nth map CMP_CLOB] in Hc. rewrite Hres, Z_to_bv_unsigned in Hc.
pose proof (cmpPixel_fn_rangeT cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb) as Rr.
pose proof (wrap64_nzT _ Rr Hnz) as X. destruct (Z.eqb_spec (zcanon (bv_wrap 64 (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef bc bb) + 0)) 0) as [Hq|Hq]; [exact (X Hq) | discriminate Hc]. }
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (BSTEP E2 _ _ _ HU20' HF) as BS3. pose proof (KSTEP E2 _ _ _ HU20' K2 HF) as K3. clear HF HG.
jbranch src0tbl HS.
+ rewrite branch_ne_U, (U_atom_off _ 20 p 1), (U_atom _ 25 pend) in Hc by first [subst E2; ew_havocA; first [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | rewrite (HE 25%nat 25%bv eq_refl); exact G25] | lia].
assert (Hne : p + 1 <> pend) by (destruct (Z.eqb_spec (p + 1) pend); [discriminate Hc | assumption]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_TIN. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (BSTEP E2 _ _ _ HU20' HF) as BS4. pose proof (KSTEP E2 _ _ _ HU20' K3 HF) as K4. clear HF HG.
apply (NEXT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl HJ2 K4 Hne (fun a Ha Hap => eq_trans (BS4 a Ha Hap) (eq_trans (BS3 a Ha Hap) (B2 a Ha Hap)))).
apply (PVAL _ _ (SOff 35 0) _ HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto|]. rewrite HTRF. rewrite HCZ. cbn [Z.eqb sv_denot]. rewrite Z.add_0_r. subst E2. ew_havocA. rewrite Z_to_bv_bv_unsigned, HE35, unsigned_lit_small by exact Rtv. reflexivity.
+ rewrite branch_ne_U, (U_atom_off _ 20 p 1), (U_atom _ 25 pend) in Hc by first [subst E2; ew_havocA; first [rewrite (HE 20%nat 20%bv eq_refl); exact G20 | rewrite (HE 25%nat 25%bv eq_refl); exact G25] | lia].
assert (Hpe1 : p + 1 = pend) by (destruct (Z.eqb_spec (p + 1) pend); [assumption | discriminate Hc]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ2 FL_TINX. { apply WR2. repeat constructor; cbn; lia. }
cbn [ms_mem mkst] in HF. pose proof (BSTEP E2 _ _ _ HU20' HF) as BS4. pose proof (KSTEP E2 _ _ _ HU20' K3 HF) as K4. clear HF HG.
apply SR_ret. apply (EXIT _ _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl HJ2 K4 (fun a Ha Hap => eq_trans (BS4 a Ha Hap) (eq_trans (BS3 a Ha Hap) (B2 a Ha Hap)))); [| exact Hpe1].
apply (PVAL _ _ (SOff 35 0) _ HS); [eexists; split; [reflexivity|]; split; [reflexivity|]; cbn [r_chunks In]; tauto|]. rewrite HTRF. rewrite HCZ. cbn [Z.eqb sv_denot]. rewrite Z.add_0_r. subst E2. ew_havocA. rewrite Z_to_bv_bv_unsigned, HE35, unsigned_lit_small by exact Rtv. reflexivity.
Qed.
Definition tout_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_TOUTX) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KT mem' /\
(forall r : reg, In r TOUT_KEPT -> getr regs' r = getr regs r).
Variables (w h top left Wd Hd wsh : Z).
Hypothesis Hw : 1 <= w. Hypothesis Hlw : left + w <= Wd. Hypothesis Hl0 : 0 <= left.
Hypothesis Hh : 1 <= h. Hypothesis Hth : top + h <= Hd. Hypothesis Ht0' : 0 <= top.
Hypothesis HNd : N = Wd * Hd. Hypothesis Hwh : w * h <= Nt.
Hypothesis Wp : word_mem src0segs mem0 (spv + 80) pTmp.
Hypothesis Wsh : word_mem src0segs mem0 (spv + 88) wsh. Hypothesis Rsh : 1 <= wsh < 2 ^ 64.
Hypothesis Whh : word_mem src0segs mem0 (spv + 96) h.
Hypothesis WW : word_mem src0segs mem0 (spv + 104) Wd.
Lemma stk_objs : forall m, KT m ->
word_mem src0segs m (spv + 80) pTmp /\ word_mem src0segs m (spv + 88) wsh /\ word_mem src0segs m (spv + 96) h /\
word_mem src0segs m (spv + 104) Wd /\ word_mem src0segs m (spv + 112) tv.
Proof.
intros m K. pose proof (proj1 alloc_ceiling_val) as Hac.
repeat split; intros k Hk; [rewrite <- (Wp k Hk) | rewrite <- (Wsh k Hk) | rewrite <- (Whh k Hk) | rewrite <- (WW k Hk) | rewrite <- (Wtv k Hk)];
(apply K; clear - Hk Hsp0 Hsp1 Ht0 Ht1 Hac; lia).
Qed.
Definition BOF (k : Z) : Z := (top + k / w) * Wd + left + k mod w.
Lemma BOF_row : forall i c, 0 <= c < w -> BOF (i * w + c) = (top + i) * Wd + left + c.
Proof.
intros i c Hc. unfold BOF. rewrite (Z.add_comm (i * w) c), Z.div_add, Z.mod_add, (Z.div_small c w), (Z.mod_small c w) by (clear - Hc Hw; lia). f_equal; clear; lia.
Qed.
Lemma byte_at_eqm : forall (m1 m2 : word -> option byte) a, (forall x, m2 x = m1 x) -> byte_at m2 a = byte_at m1 a.
Proof. intros m1 m2 a Hm. unfold byte_at. rewrite (mbyte_of_eq _ _ _ _ Hm). reflexivity. Qed.
Definition TOUTV (memc mem' : word -> option byte) (i : Z) : Prop :=
forall a, pTmp <= a < pTmp + Nt -> byte_at mem' a = if (pTmp + i * w <=? a) && (a <? pTmp + h * w) then TRF memc a (BOF (a - pTmp)) else byte_at memc a.
Lemma tout_row_combine : forall (memc m1 mem3 : word -> option byte) i, i + 1 = h ->
(forall x, m1 x = memc x) ->
(forall a, pTmp <= a < pTmp + Nt -> byte_at mem3 a = if (pTmp + i * w <=? a) && (a <? pTmp + (i * w + w)) then TRF m1 a ((top + i) * Wd + left + (a - (pTmp + i * w))) else byte_at m1 a) ->
TOUTV memc mem3 i.
Proof.
intros memc m1 mem3 i Hih M1 HV a Ha. rewrite (HV a Ha). replace (pTmp + h * w) with (pTmp + (i * w + w)) by (rewrite <- Hih; clear; lia).
destruct ((pTmp + i * w <=? a) && (a <? pTmp + (i * w + w))) eqn:Ec; [| apply byte_at_eqm; exact M1].
apply andb_true_iff in Ec. destruct Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
unfold TRF. rewrite (byte_at_eqm memc m1 a M1). replace (a - pTmp) with (i * w + (a - (pTmp + i * w))) by (clear; lia). rewrite BOF_row by (clear - E1 E2; lia). reflexivity.
Qed.
Lemma tout_step_combine : forall (memc m1 mem3 m5 mem' : word -> option byte) i, 0 <= i -> i + 1 <= h ->
(forall x, m1 x = memc x) ->
(forall a, pTmp <= a < pTmp + Nt -> byte_at mem3 a = if (pTmp + i * w <=? a) && (a <? pTmp + (i * w + w)) then TRF m1 a ((top + i) * Wd + left + (a - (pTmp + i * w))) else byte_at m1 a) ->
(forall x, m5 x = mem3 x) -> TOUTV m5 mem' (i + 1) -> TOUTV memc mem' i.
Proof.
intros memc m1 mem3 m5 mem' i Hi0 Hih M1 HV M5 HIH a Ha. rewrite (HIH a Ha).
assert (Hm5 : byte_at m5 a = byte_at mem3 a) by (apply byte_at_eqm; exact M5). specialize (HV a Ha).
assert (Hrw : (i + 1) * w <= h * w) by (clear - Hih Hw; nia).
destruct (Z.lt_ge_cases a (pTmp + i * w)) as [Hlo | Hlo].
- replace (pTmp + (i + 1) * w <=? a) with false by (symmetry; apply Z.leb_gt; clear - Hlo Hw; nia).
replace (pTmp + i * w <=? a) with false by (symmetry; apply Z.leb_gt; exact Hlo). cbn [andb].
replace (pTmp + i * w <=? a) with false in HV by (symmetry; apply Z.leb_gt; exact Hlo). cbn [andb] in HV.
rewrite Hm5, HV. apply byte_at_eqm. exact M1.
- replace (pTmp + i * w <=? a) with true by (symmetry; apply Z.leb_le; exact Hlo).
replace (pTmp + i * w <=? a) with true in HV by (symmetry; apply Z.leb_le; exact Hlo). cbn [andb] in HV |- *.
destruct (Z.lt_ge_cases a (pTmp + (i * w + w))) as [Hrow | Hrow].
+ replace (pTmp + (i + 1) * w <=? a) with false by (symmetry; apply Z.leb_gt; clear - Hrow; lia). cbn [andb].
replace (a <? pTmp + (i * w + w)) with true in HV by (symmetry; apply Z.ltb_lt; exact Hrow).
replace (a <? pTmp + h * w) with true by (symmetry; apply Z.ltb_lt; clear - Hrow Hrw; lia).
rewrite Hm5, HV. unfold TRF. rewrite (byte_at_eqm memc m1 a M1). replace (a - pTmp) with (i * w + (a - (pTmp + i * w))) by (clear; lia). rewrite BOF_row by (clear - Hlo Hrow; lia). reflexivity.
+ replace (pTmp + (i + 1) * w <=? a) with true by (symmetry; apply Z.leb_le; clear - Hrow; lia). cbn [andb].
replace (a <? pTmp + (i * w + w)) with false in HV by (symmetry; apply Z.ltb_ge; exact Hrow).
assert (Hm1 : byte_at m5 a = byte_at memc a) by (rewrite Hm5, HV; apply byte_at_eqm; exact M1).
unfold TRF. rewrite Hm1. reflexivity.
Qed.
Definition tout_postV STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (memc : word -> option byte) (i : Z) (c' : config) : Prop :=
exists regs' mem',
c' = mkCfg (mkst regs' (Z_to_bv 64 FL_TOUTX) mem' (seg_rom src0segs)) mdc /\
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ KT mem' /\
(forall r : reg, In r TOUT_KEPT -> getr regs' r = getr regs r) /\
TOUTV memc mem' i.
Lemma fl_toutV : forall (n : nat) (i : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> KT memc ->
In (pTmp, Nt) (blocks Lc Ac) -> (In (pTmp, Nt) (blocks L A) -> forall k, 0 <= k < Nt -> inFP FP (pTmp + k)) ->
In (bimg, N) (blocks Lc Ac) ->
0 <= i -> i + Z.of_nat n = h -> (1 <= n)%nat ->
sp0 - STK <= spv -> spv = sp0 - 272 ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 fhp ->
getr regs 21 = Z_to_bv 64 i -> getr regs 27 = Z_to_bv 64 (pTmp + i * w) -> getr regs 24 = Z_to_bv 64 ((top + i) * Wd + left) ->
getr regs 23 = Z_to_bv 64 w -> getr regs 22 = Z_to_bv 64 bimg -> getr regs 26 = Z_to_bv 64 4294967295 ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 FL_TOUT) memc (seg_rom src0segs)) mdc) (tout_postV STK sp0 FP L A mem md Lc Ac mdc regs memc i).
Proof.
intros n. induction n as [|n IH]; intros i STK sp0 FP L A mem md Lc Ac mdc regs memc HJ K0 Htin Htfp Hbin Hi Hin Hn Hstk Hspv
G2 G8 G9 G18 G21 G27 G24 G23 G22 G26; [lia|].
hide_disj.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HNt1 : 1 <= Nt) by (clear - Hw Hh Hwh; nia).
assert (HN1 : (top + i) * Wd + left + w <= N) by (clear - Hw Hlw Hl0 Hh Hth Ht0' HNd Hi Hin Hn; nia).
assert (Hrow0 : 0 <= i * w) by (clear - Hi Hw; nia).
assert (Hrow1 : i * w + w <= Nt) by (clear - Hi Hin Hn Hw Hwh; nia).
assert (Hb00 : 0 <= (top + i) * Wd + left) by (clear - Hi Ht0' Hl0 Hlw Hw; nia).
destruct (stk_objs memc K0) as (Wp0 & Wsh0 & Wh0 & WW0 & Wtv0).
set (E := Ereg regs (map (Z_to_bv 64) [pTmp; wsh; h; Wd; tv] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 pTmp) by (subst E; apply (Ereg_vals regs [pTmp; wsh; h; Wd; tv] [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 wsh) by (subst E; apply (Ereg_vals regs [pTmp; wsh; h; Wd; tv] [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 h) by (subst E; apply (Ereg_vals regs [pTmp; wsh; h; Wd; tv] [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 Wd) by (subst E; apply (Ereg_vals regs [pTmp; wsh; h; Wd; tv] [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 tv) by (subst E; apply (Ereg_vals regs [pTmp; wsh; h; Wd; tv] [] 4%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (Hh64 : h < 2 ^ 62) by (clear - Hh Hw Hwh Ht0 Ht1 Hac; nia).
assert (HWd : 0 <= Wd /\ Wd < 2 ^ 32) by (clear - Hlw Hl0 Hw HNd HN Hh Hth Ht0'; nia).
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 80 120 80 80
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SOff 33 0)); mkChunk 96 (CVal 8 (SOff 34 0));
mkChunk 104 (CVal 8 (SOff 35 0)); mkChunk 112 (CVal 8 (SOff 36 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?HE32, ?HE33, ?HE34, ?HE35, ?HE36, Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; assumption]).
all: clear - Ht0 Ht1 HNt1 Rsh Hh Hh64 HWd Rtv Hac; lia. }
assert (HFA : atoms_ok E [ (2%nat, mkAF CEIL_MIN (2^63) 4); (33%nat, mkAF 1 (2^64 - 1) 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE33, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hsp0 Hsp1 Hsp16 Rsh. repeat split; lia. }
assert (HS : st_ok src0segs E (ss_tout FL_TOUT) (mkst regs (Z_to_bv 64 FL_TOUT) memc (seg_rom src0segs))).
{ unfold ss_tout. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]].
apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite G26. reflexivity. }
clear HR0 HFA.
change memc with (ms_mem (mkst regs (Z_to_bv 64 FL_TOUT) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ FL_TIN. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : KT (ms_mem ms)).
{ apply (KT_trans _ _ K0). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
assert (M1 : forall x, ms_mem ms x = memc x) by (intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end; reflexivity).
clear HF HG.
assert (HU21 : U E (SOff 21 0) = i) by (apply (U_atom _ 21 i); [rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hi Hin Hh64; lia]).
assert (HU23 : U E (SOff 23 0) = w) by (apply (U_atom _ 23 w); [rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hw Hrow1 Hrow0 Ht0 Ht1 Hac Hi; nia]).
assert (HU32 : U E (SOff 32 0) = pTmp) by (apply (U_atom _ 32 pTmp HE32); clear - Ht0 Ht1 HNt1 Hac; lia).
jreg HS (25%bv:reg) as G25'.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
assert (G25 : getr (ms_regs msx) 25 = Z_to_bv 64 (pTmp + (i * w + w)));
[ rewrite (st_ok_reg src0segs E ssx msx 25%bv HS); eval_sr_get; apply denot_of_U';
rewrite (U_add_small E _ _ pTmp (w + w * i) HU32); [clear - Hi Hw; nia | | clear - Ht0; lia | clear - Hi Hw; nia | clear - Hrow1 Ht0 Ht1 Hac Hi Hw; nia];
rewrite (U_add_small E _ _ w (w * i) HU23); [reflexivity | | clear - Hw; lia | clear - Hi Hw; nia | clear - Hrow1 Ht0 Ht1 Hac Hi Hw HNt1; nia];
apply (U_mul_small' E _ _ w i HU23 HU21); clear - Hw Hi Hrow1 Ht0 Ht1 Hac HNt1; nia
| clear G25' ] end.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs _ [2; 3; 4; 8; 9; 18; 21; 27; 24; 23; 22]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
jreg HS (19%bv:reg) as G19. rewrite (HE 24%nat 24%bv eq_refl), G24 in G19.
jreg HS (20%bv:reg) as G20. rewrite (HE 27%nat 27%bv eq_refl), G27 in G20.
jreg HS (26%bv:reg) as G26'.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (fl_tinV (Z.to_nat w) (pTmp + i * w) ((top + i) * Wd + left) STK sp0 FP L A mem md Lc Ac mdc (ms_regs ms) (ms_mem ms) (pTmp + (i * w + w)) HJ K1 Htin Htfp Hbin);
[ clear - Hrow0; lia | clear - Hw; lia | clear - Hw; lia | clear - Hrow1; lia | exact Hb00 | clear - HN1 Hw; lia | exact Hstk | exact Hspv
| rewrite (HKR 2%bv ltac:(cbv; auto 50)); exact G2 | rewrite (HKR 8%bv ltac:(cbv; auto 50)); exact G8
| rewrite (HKR 9%bv ltac:(cbv; auto 50)); exact G9 | rewrite (HKR 18%bv ltac:(cbv; auto 50)); exact G18
| exact G19 | exact G20 | exact G25 | rewrite (HKR 22%bv ltac:(cbv; auto 50)); exact G22 | exact G26' ]. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & K3 & R26 & HK3 & HV3). clear HS HJ.
assert (R3 : forall r : reg, In r TIN_KEPT -> In r [2; 3; 4; 8; 9; 18; 21; 27; 24; 23; 22]%bv -> getr regs3 r = getr regs r).
{ intros rr H1 H2. rewrite (HK3 rr H1). apply (HKR rr H2). }
destruct (stk_objs mem3 K3) as (Wp3 & Wsh3 & Wh3 & WW3 & Wtv3).
set (E3 := Ereg regs3 (map (Z_to_bv 64) [pTmp; wsh; h; Wd; tv] ++ [])).
assert (HE3 : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E3 m = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (HE3_32 : ew E3 32 = Z_to_bv 64 pTmp) by (subst E3; apply (Ereg_vals regs3 [pTmp; wsh; h; Wd; tv] [] 0%nat); reflexivity).
assert (HE3_33 : ew E3 33 = Z_to_bv 64 wsh) by (subst E3; apply (Ereg_vals regs3 [pTmp; wsh; h; Wd; tv] [] 1%nat); reflexivity).
assert (HE3_34 : ew E3 34 = Z_to_bv 64 h) by (subst E3; apply (Ereg_vals regs3 [pTmp; wsh; h; Wd; tv] [] 2%nat); reflexivity).
assert (HE3_35 : ew E3 35 = Z_to_bv 64 Wd) by (subst E3; apply (Ereg_vals regs3 [pTmp; wsh; h; Wd; tv] [] 3%nat); reflexivity).
assert (HE3_36 : ew E3 36 = Z_to_bv 64 tv) by (subst E3; apply (Ereg_vals regs3 [pTmp; wsh; h; Wd; tv] [] 4%nat); reflexivity).
assert (G3_2 : getr regs3 2 = Z_to_bv 64 spv) by (rewrite (R3 2%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)); exact G2).
assert (HU3_2 : bv_unsigned (ew E3 2) = spv) by (rewrite (HE3 2%nat 2%bv eq_refl), G3_2; apply unsigned_lit_small; clear - Hsp0 Hsp1 Hac; lia).
assert (HR0 : region_ok src0segs E3 mem3 (YP09.mkRegion (Some 2%nat) 80 120 80 80
[mkChunk 80 (CVal 8 (SOff 32 0)); mkChunk 88 (CVal 8 (SOff 33 0)); mkChunk 96 (CVal 8 (SOff 34 0));
mkChunk 104 (CVal 8 (SOff 35 0)); mkChunk 112 (CVal 8 (SOff 36 0))])).
{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU3_2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat (apply Forall_cons); [..|apply Forall_nil];
(eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, ?HE3_32, ?HE3_33, ?HE3_34, ?HE3_35, ?HE3_36, Z_to_bv_bv_unsigned; reflexivity | cbn | cbn; lia | apply val_mem_word_mem; assumption]).
all: clear - Ht0 Ht1 HNt1 Rsh Hh Hh64 HWd Rtv Hac; lia. }
assert (HFA : atoms_ok E3 [ (2%nat, mkAF CEIL_MIN (2^63) 4); (33%nat, mkAF 1 (2^64 - 1) 0) ]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU3_2, HE3_33, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite Z.mod_1_r. try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hsp0 Hsp1 Hsp16 Rsh. repeat split; lia. }
assert (HS : st_ok src0segs E3 (ss_tout FL_TINX) (mkst regs3 (Z_to_bv 64 FL_TINX) mem3 (seg_rom src0segs))).
{ unfold ss_tout. apply entry_st_ok_full; [| vm_compute; reflexivity | constructor; [exact HR0 | constructor] | cbn [pairwise_disjoint all_disjoint]; split; exact I | split; [exact HFA | split; exact I]].
apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx |]. rewrite R26. reflexivity. }
clear HR0 HFA.
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 FL_TINX) mem3 (seg_rom src0segs))) in HJ3.
jrun LAWS src0tbl_ok HS HJ3. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (M4 : forall x, ms_mem msx x = mem3 x) end.
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (K4 : KT (ms_mem msx)) end.
{ apply (KT_trans _ _ K3). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
assert (HU3_21 : U E3 (SOff 21 0) = i).
{ apply (U_atom _ 21 i); [| clear - Hi Hin Hh64; lia]. rewrite (HE3 21%nat 21%bv eq_refl), (R3 21%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G21. }
assert (HU3_34 : U E3 (SOff 34 0) = h) by (apply (U_atom _ 34 h HE3_34); clear - Hh Hh64; lia).
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs3 _ [2; 3; 4; 8; 9; 18; 23; 22]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR3 end.
jbranch src0tbl HS.
-
rewrite branch_ne_U, (U_atom_off _ 21 i 1), HU3_34 in Hc by first [rewrite (HE3 21%nat 21%bv eq_refl), (R3 21%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)); exact G21 | clear - Hi Hin Hh64; lia].
assert (Hne : i + 1 <> h) by (destruct (Z.eqb_spec (i + 1) h); [discriminate Hc | assumption]). clear Hc.
jrun_to LAWS src0tbl_ok HS HJ3 FL_TOUT. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (M5 : forall x, ms_mem msx x = mem3 x) end.
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply M4. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (K5 : KT (ms_mem msx)) end.
{ apply (KT_trans _ _ K4). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs3 _ [2; 3; 4; 8; 9; 18; 23; 22]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR4 end.
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (i + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ3 K5 Htin Htfp Hbin ltac:(clear - Hi; lia) ltac:(clear - Hin; lia) ltac:(clear - Hin Hne Hn; lia) Hstk Hspv).
- rewrite (HKR4 2%bv ltac:(cbv; auto 50)). exact G3_2.
- rewrite (HKR4 8%bv ltac:(cbv; auto 50)), (R3 8%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G8.
- rewrite (HKR4 9%bv ltac:(cbv; auto 50)), (R3 9%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G9.
- rewrite (HKR4 18%bv ltac:(cbv; auto 50)), (R3 18%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G18.
- reg_nowF HS ltac:(rewrite (HE3 21%nat 21%bv eq_refl), (R3 21%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)), G21, unsigned_lit_small by (clear - Hi Hin Hh64; lia); reflexivity).
- lazymatch type of HS with st_ok _ _ ?ssx ?msx => rewrite (st_ok_reg src0segs E3 ssx msx 27%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite (U_add_small E3 _ _ w (pTmp + i * w)); [clear - Hi; lia | | | clear - Hw; lia | clear - Ht0 Hrow0; lia | clear - Hrow1 Ht0 Ht1 Hac Hi Hw HNt1; nia].
+ apply U_atom; [| clear - Hw Hrow0 Hrow1 Ht0 Ht1 Hac HNt1; lia]. rewrite (HE3 23%nat 23%bv eq_refl), (R3 23%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G23.
+ apply U_atom; [| clear - Ht0 Ht1 Hrow0 Hrow1 Hac HNt1 Hw; lia]. rewrite (HE3 27%nat 27%bv eq_refl), (R3 27%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G27.
- lazymatch type of HS with st_ok _ _ ?ssx ?msx => rewrite (st_ok_reg src0segs E3 ssx msx 24%bv HS) end. eval_sr_get. apply denot_of_U'.
rewrite (U_add_small E3 _ _ ((top + i) * Wd + left) Wd); [clear - Hi; lia | | | exact Hb00 | clear - HWd; lia | clear - HN1 Hw HN HWd; lia].
+ apply U_atom; [| clear - Hb00 HN1 Hw HN; lia]. rewrite (HE3 24%nat 24%bv eq_refl), (R3 24%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G24.
+ apply (U_atom _ 35 Wd HE3_35). clear - HWd; lia.
- rewrite (HKR4 23%bv ltac:(cbv; auto 50)), (R3 23%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G23.
- rewrite (HKR4 22%bv ltac:(cbv; auto 50)), (R3 22%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)). exact G22.
- reg_nowF HS ltac:(reflexivity). }
cbv beta. intros c' (regs' & mem' & -> & HJ' & K' & HK' & HV'). exists regs', mem'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact K'|].
split; [| exact (tout_step_combine memc (ms_mem ms) mem3 _ mem' i Hi ltac:(clear - Hin Hn; lia) M1 HV3 M5 HV')].
intros rr Hrr. rewrite (HK' rr Hrr). cbv in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [match goal with |- getr _ ?r = _ => rewrite (HKR4 r ltac:(cbv; auto 50)); apply (R3 r); solve [cbv; auto 50] end |]). destruct Hrr.
-
rewrite branch_ne_U, (U_atom_off _ 21 i 1), HU3_34 in Hc by first [rewrite (HE3 21%nat 21%bv eq_refl), (R3 21%bv ltac:(cbv; auto 50) ltac:(cbv; auto 50)); exact G21 | clear - Hi Hin Hh64; lia].
assert (Heq : i + 1 = h) by (destruct (Z.eqb_spec (i + 1) h); [assumption | discriminate Hc]).
clear Hc. jrun_to LAWS src0tbl_ok HS HJ3 FL_TOUTX. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (M5 : forall x, ms_mem msx x = mem3 x) end.
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply M4. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => assert (K5 : KT (ms_mem msx)) end.
{ apply (KT_trans _ _ K4). intros a _ _. unfold mbyte. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF HG.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src0segs Ef ssf msf regs3 _ [2; 3; 4; 8; 9; 18; 23; 22]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR4 end.
apply SR_ret. lazymatch goal with |- _ (mkCfg ?msx _) => exists (ms_regs msx), (ms_mem msx) end.
split; [rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl); reflexivity|]. split; [exact HJ3|]. split; [exact K5|].
split; [| intros a Ha; rewrite (byte_at_eqm _ _ a M5); exact (tout_row_combine memc (ms_mem ms) mem3 i Heq M1 HV3 a Ha)].
intros rr Hrr. cbv in Hrr.
repeat (destruct Hrr as [<- | Hrr]; [match goal with |- getr _ ?r = _ => rewrite (HKR4 r ltac:(cbv; auto 50)); apply (R3 r); solve [cbv; auto 50] end |]). destruct Hrr.
Qed.
End j.
End S.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
