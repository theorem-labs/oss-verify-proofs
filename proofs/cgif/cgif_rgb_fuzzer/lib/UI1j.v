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
UI1h UI16 UI1z UI1k UI22.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FL_SLOW : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x164).
Definition FL_S1O  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x198).
Definition FL_S1I  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x1e0).
Definition FL_S1R  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x238).
Definition FL_S1X  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x248).
Definition FL_S1F  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x280).
Definition FL_IDENT: Z := Eval vm_compute in (ubs2_A_flushFrame + 0x26c).
Definition FL_S2   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x2c4).
Definition FL_S2O  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x2f8).
Definition FL_S2I  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x324).
Definition FL_S2R  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x350).
Definition FL_S2X  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x360).
Definition FL_S2F  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x3fc).
Definition FL_S3   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x408).
Definition FL_S3L  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x43c).
Definition FL_S3R  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x460).
Definition FL_S4L  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x4d4).
Definition FL_S4R  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x4f8).
Definition FL_S4F  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x540).
Definition FL_FAST : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x384).
Definition FL_F1L  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x3a4).
Definition FL_F1R  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x3dc).
Definition FL_F2   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x564).
Definition FL_F2L  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x5b4).
Definition FL_F2R  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x5ec).
Definition FL_F3   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x604).
Definition FL_F3L  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x65c).
Definition FL_F4   : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x6c8).
Definition FL_F4L  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x6f8).
Definition FL_F4F  : Z := Eval vm_compute in (ubs2_A_flushFrame + 0x754).
Definition dctx (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte) : Prop :=
obj_at ubs2segs mem0 g LAY_CGIF gvals /\ nth_error gvals CG_ngp = Some ngp /\ nth_error gvals CG_pal = Some gpal /\
obj_at ubs2segs mem0 cfp LAY_FrameConfig cvals /\ nth_error cvals FR_attr = Some cattr /\ nth_error cvals FR_ctidx = Some ctidx /\
nth_error cvals FR_nlp = Some cnlp /\ nth_error cvals FR_lpal = Some clpal /\
obj_at ubs2segs mem0 fhp LAY_FrameConfig bvals /\ nth_error bvals FR_attr = Some battr /\ nth_error bvals FR_ctidx = Some btidx /\
nth_error bvals FR_nlp = Some bnlp /\ nth_error bvals FR_lpal = Some blpal /\
4096 <= g /\ g + CGIF_SIZE <= alloc_ceiling /\ g mod 16 = 0 /\
4096 <= cfp /\ cfp + 40 <= alloc_ceiling /\ cfp mod 8 = 0 /\
4096 <= fhp /\ fhp + 40 <= alloc_ceiling /\ fhp mod 8 = 0 /\
(g + CGIF_SIZE <= cfp \/ cfp + 29 <= g) /\ (g + CGIF_SIZE <= fhp \/ fhp + 29 <= g) /\ (cfp + 29 <= fhp \/ fhp + 29 <= cfp) /\
rdn ubs2segs mem0 (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur /\
rdn ubs2segs mem0 (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef /\
4096 <= ct_sel cattr clpal gpal /\ ct_sel cattr clpal gpal + 3 * ct_sel cattr cnlp ngp <= alloc_ceiling /\
4096 <= ct_sel battr blpal gpal /\ ct_sel battr blpal gpal + 3 * ct_sel battr bnlp ngp <= alloc_ceiling /\
0 <= 3 * ct_sel cattr cnlp ngp /\ 0 <= 3 * ct_sel battr bnlp ngp /\
4096 <= fimg /\ fimg + N <= alloc_ceiling /\ 4096 <= bimg /\ bimg + N <= alloc_ceiling /\ (fimg + N <= bimg \/ bimg + N <= fimg) /\
1 <= W <= 65535 /\ 1 <= H <= 65535 /\ N = W * H /\ N <= 100000000 /\
alloc_ceiling + 8192 <= spv /\ spv + 272 <= 2 ^ 63 /\ spv mod 16 = 0 /\
word_mem ubs2segs mem0 (spv + 80) H /\ word_mem ubs2segs mem0 (spv + 104) W /\
word_mem ubs2segs mem0 (spv + 112) g /\ word_mem ubs2segs mem0 (spv + 120) cfp.
Definition KD (mem0 : word -> option byte) (spv : Z) (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 8 <= a < spv + 16) -> ~ (spv + 40 <= a < spv + 56) -> ~ (spv + 64 <= a < spv + 72) -> ~ (spv + 88 <= a < spv + 104) -> mbyte ubs2segs m a = mbyte ubs2segs mem0 a.
Definition CMPp (mem0 : word -> option byte) (fimg bimg : Z) (cattr ctidx cnlp battr btidx bnlp ngp : Z) (ctcur ctbef : list byte) (p : Z) : Z :=
cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef (byte_at mem0 (fimg + p)) (byte_at mem0 (bimg + p)).
End b.
Ltac dctx_open HC :=
pose proof HC as (Og & Ongp & Ogpal & Oc & Ocattr & Octidx & Ocnlp & Oclpal & Ob & Obattr & Obtidx & Obnlp & Oblpal
& G0 & G1 & G16 & C0 & C1 & C8 & B0 & B1 & B8 & Dgc & Dgb & Dcb & Rct & Rbt & Sc0 & Sc1 & Sb0 & Sb1 & Hcnn & Hbnn
& Hfimg0 & Hfimg1 & Hbimg0 & Hbimg1 & Dfb & HW & HH & HN & HNle & Hsp0 & Hsp1 & Hsp16 & WH0 & WW0 & WG0 & WC0).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma KD_refl : forall mem0 spv, KD mem0 spv mem0.
Proof. intros mem0 spv a _ _ _ _ _. reflexivity. Qed.
Lemma KD_eq : forall mem0 spv m1 m2, KD mem0 spv m1 -> (forall x, m2 x = m1 x) -> KD mem0 spv m2.
Proof. intros mem0 spv m1 m2 K Heq a Ha Hn1 Hn2 Hn3 Hn4. rewrite (mbyte_of_eq _ _ _ _ Heq). apply K; assumption. Qed.
Lemma KD_frame : forall mem0 spv m1 m2, KD mem0 spv m1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spv + 8 <= a < spv + 16) -> ~ (spv + 40 <= a < spv + 56) -> ~ (spv + 64 <= a < spv + 72) -> ~ (spv + 88 <= a < spv + 104) -> mbyte ubs2segs m2 a = mbyte ubs2segs m1 a) -> KD mem0 spv m2.
Proof. intros mem0 spv m1 m2 K H a Ha Hn1 Hn2 Hn3 Hn4. rewrite (H a Ha Hn1 Hn2 Hn3 Hn4). apply K; assumption. Qed.
Lemma byte_at_KD : forall mem0 spv m a, KD mem0 spv m -> 0 <= a < 2 ^ 64 -> a + 1 <= spv \/ spv + 112 <= a -> byte_at m a = byte_at mem0 a.
Proof. intros mem0 spv m a K Ha Hna. unfold byte_at. rewrite (K a Ha) by lia. reflexivity. Qed.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Section d.
Variables (mem0 : word -> option byte) (g cfp fhp fimg bimg W H N spv : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis HC : dctx mem0 g cfp fhp fimg bimg W H N spv gvals cvals bvals cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal ctcur ctbef.
Lemma dctx_objs : forall m, KD mem0 spv m ->
obj_at ubs2segs m g LAY_CGIF gvals /\ obj_at ubs2segs m cfp LAY_FrameConfig cvals /\ obj_at ubs2segs m fhp LAY_FrameConfig bvals /\
rdn ubs2segs m (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur /\
rdn ubs2segs m (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef /\
word_mem ubs2segs m (spv + 80) H /\ word_mem ubs2segs m (spv + 104) W /\ word_mem ubs2segs m (spv + 112) g /\ word_mem ubs2segs m (spv + 120) cfp.
Proof.
intros m K. dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
- eapply obj_at_transport_range; [exact Og | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply K; clear - Hi G0 G1 Hsp0 Hac HGSv; lia].
- eapply obj_at_transport_range; [exact Oc | exact lay_inside_FrameConfig | intros i Hi; apply K; clear - Hi C0 C1 Hsp0 Hac; lia].
- eapply obj_at_transport_range; [exact Ob | exact lay_inside_FrameConfig | intros i Hi; apply K; clear - Hi B0 B1 Hsp0 Hac; lia].
- rewrite <- Rct. apply rdn_agree. intros k Hk. apply K; clear - Hk Sc0 Sc1 Hcnn Hsp0 Hac; lia.
- rewrite <- Rbt. apply rdn_agree. intros k Hk. apply K; clear - Hk Sb0 Sb1 Hbnn Hsp0 Hac; lia.
- intros k Hk. rewrite <- (WH0 k Hk). apply K; clear - Hk Hsp0 Hsp1 Hac; lia.
- intros k Hk. rewrite <- (WW0 k Hk). apply K; clear - Hk Hsp0 Hsp1 Hac; lia.
- intros k Hk. rewrite <- (WG0 k Hk). apply K; clear - Hk Hsp0 Hsp1 Hac; lia.
- intros k Hk. rewrite <- (WC0 k Hk). apply K; clear - Hk Hsp0 Hsp1 Hac; lia.
Qed.
Lemma cmp_callD : forall STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (m : word -> option byte) (p retpc : Z),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac m mdc -> KD mem0 spv m ->
0 <= p < N ->
getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 cfp -> getr regs 12 = Z_to_bv 64 fhp ->
getr regs 13 = Z_to_bv 64 (byte_at m (fimg + p)) -> getr regs 14 = Z_to_bv 64 (byte_at m (bimg + p)) ->
v_jalr (getr regs 1) 0 = Z_to_bv 64 retpc ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cmpPixel) m (seg_rom ubs2segs)) mdc)
(fun c' => exists regs2 mem2, c' = mkCfg (mkst regs2 (Z_to_bv 64 retpc) mem2 (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\ (forall x, mem2 x = m x) /\
getr regs2 10 = Z_to_bv 64 (CMPp mem0 fimg bimg cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef p) /\
(forall r : reg, reg_in r CMP_CLOB = false -> getr regs2 r = getr regs r)).
Proof.
intros STK sp0 FP L A mem md Lc Ac mdc regs m p retpc HJ K Hp G10 G11 G12 G13 G14 Hret.
dctx_open HC. pose proof (proj1 alloc_ceiling_val) as Hac.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
destruct (dctx_objs m K) as (Og' & Oc' & Ob' & Rct' & Rbt' & _).
destruct (ubs2_cmpPixel regs m g gvals cfp cvals fhp bvals (byte_at m (fimg + p)) (byte_at m (bimg + p)) ctcur ctbef cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal
G10 G11 G12 G13 G14 (byte_at_range _ _) (byte_at_range _ _) Og' Ongp Ogpal Oc' Ocattr Octidx Ocnlp Oclpal Ob' Obattr Obtidx Obnlp Oblpal
G0 G1 G16 C0 ltac:(clear - C1 Hac; lia) C8 B0 ltac:(clear - B1 Hac; lia) B8 Dgc Dgb Dcb Rct' Rbt' Sc0 Sc1 Sb0 Sb1) as (regs2 & mem2 & Hms & Hmem2 & Hres & Hfr2).
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |]. rewrite Hret.
apply SR_ret. exists regs2, mem2. split; [reflexivity|]. split; [| split; [exact Hmem2 | split]].
- eapply (journal_exec _ _ LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2 | intros a []].
- rewrite Hres. unfold CMPp. rewrite (byte_at_KD mem0 spv m (fimg + p) K) by (clear - Hp Hfimg0 Hfimg1 Hsp0 Hac; lia).
rewrite (byte_at_KD mem0 spv m (bimg + p) K) by (clear - Hp Hbimg0 Hbimg1 Hsp0 Hac; lia). reflexivity.
- intros r Hr. destruct (cmp_clob_out r Hr) as (?&?&?&?&?&?&?&?&?&?). apply Hfr2; assumption.
Qed.
End d.
End S.
End c.
