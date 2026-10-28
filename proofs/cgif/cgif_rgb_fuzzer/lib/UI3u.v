(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
UI3h UI4v UIZm UI4w UI3s UI3t YP12 UIZ8.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Ltac2 sat_vars () := [@API; @L; @A; @regs0; @mem0; @md0; @r; @cfp; @g; @wfn; @ctx; @path; @attr; @gen; @loops; @W; @H; @bef; @beffmt; @cur; @s; @N; @img; @fmt; @fattr; @fgen; @delay; @rest; @Lq; @Aq; @mdq; @memD; @flt; @fimg; @t; @cc].
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac inK := repeat (first [left; apply bv_eq; reflexivity | right]).
Ltac in_sub Hrr := cbn [In] in Hrr; repeat (destruct Hrr as [<- | Hrr]; [inK|]); destruct Hrr.
Lemma U_mul_off : forall E a b x y k,
ew E a = Z_to_bv 64 x -> bv_unsigned (ew E b) = y -> 0 <= x < 2 ^ 16 -> 0 <= y < 2 ^ 32 -> 0 <= y + k < 2 ^ 32 ->
sv_denot E (SMd M_MUL (SOff a 0) (SOff b k)) = Z_to_bv 64 (x * (y + k)).
Proof.
intros E a b x y k Ha Hb Hx Hy Hyk. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E a x Ha) by lia. rewrite U_SOff, Hb.
rewrite (zcanon_id (y + k)) by (unfold M64; lia). apply zcanon_id. unfold M64; nia.
Qed.
Lemma U_subw_zext : forall E a b x y,
bv_unsigned (ew E a) = x -> bv_unsigned (ew E b) = y -> 0 <= y <= x -> x < 2 ^ 31 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff a 0) (SLit 32)) (SMd M_MUL (SOff b 0) (SLit 79228162514264337589248983040))) (SLit 32))
= Z_to_bv 64 (x - y).
Proof.
intros E a b x y Ha Hb Hyx Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, !U_SLit, Ha, Hb, !Z.add_0_r. rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia).
change (Z.land (zcanon 32) 63) with 32.
replace (zcanon 79228162514264337589248983040) with (2 ^ 64 - 2 ^ 32) by reflexivity.
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; nia).
unfold zcanon, M64.
rewrite Zdiv.Zplus_mod_idemp_r.
replace (x * 2 ^ 32 + y * (2 ^ 64 - 2 ^ 32)) with ((x - y) * 2 ^ 32 + y * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small ((x - y) * 2 ^ 32)) by nia.
rewrite Z.div_mul by lia. apply Z.mod_small. lia.
Qed.
Lemma U_subw_zext' : forall E a b x y,
bv_unsigned (ew E a) = x -> bv_unsigned (ew E b) = y -> 0 <= y <= x -> x < 2 ^ 31 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff b 0) (SLit 79228162514264337589248983040)) (SAlu ALU_SLL (SOff a 0) (SLit 32))) (SLit 32))
= Z_to_bv 64 (x - y).
Proof.
intros E a b x y Ha Hb Hyx Hx. rewrite <- (U_subw_zext E a b x y Ha Hb Hyx Hx).
apply U_inj. rewrite (U_SAlu E ALU_SRL), (U_SAlu E ALU_SRL).
assert (Hc : U E (SAlu ALU_ADD (SMd M_MUL (SOff b 0) (SLit 79228162514264337589248983040)) (SAlu ALU_SLL (SOff a 0) (SLit 32)))
= U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff a 0) (SLit 32)) (SMd M_MUL (SOff b 0) (SLit 79228162514264337589248983040))))
by (rewrite !(U_SAlu E ALU_ADD); cbn [zalu_raw]; rewrite Z.add_comm; reflexivity).
rewrite Hc. reflexivity.
Qed.
Lemma mod4_of16 : forall a k, a mod 16 = 0 -> (a + 4 * k) mod 4 = 0.
Proof.
intros a k Ha. apply (proj1 (Z.mod_divide a 16 ltac:(lia))) in Ha. destruct Ha as [q ->].
replace (q * 16 + 4 * k) with ((4 * q + k) * 4) by ring. apply Z.mod_mul. lia.
Qed.
Lemma leaf_in_nodes : forall u n, In n (tree_leaves u) -> In n (tree_nodes u).
Proof.
intros u. induction u as [|n0|n0 l IHl rr IHr]; intros n Hin; cbn [tree_leaves tree_nodes] in *.
- destruct Hin.
- destruct Hin as [<- | []]. left. reflexivity.
- right. apply in_app_iff. apply in_app_iff in Hin as [Hin|Hin]; [left; exact (IHl n Hin) | right; exact (IHr n Hin)].
Qed.
Lemma fregs3_kept : forall (f f' : bvmap 5 word) (K : list reg), (forall rr, In rr K -> reg_get f' rr = reg_get f rr) ->
In 8%bv K -> In 9%bv K -> In 18%bv K -> fregs3 f -> fregs3 f'.
Proof.
intros f f' K HK H8 H9 H18 (F8 & F9 & F18). unfold fregs3. rewrite (HK _ H8), (HK _ H9), (HK _ H18).
split; [exact F8 | split; [exact F9 | exact F18]].
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis GLNI : forall fx', glni_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section e.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree) (cc : Z).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis HW1 : 1 <= W. Hypothesis HWN : exists h, 1 <= h /\ N = W * h.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hdisj : flt + 4 * M <= fimg \/ fimg + N <= flt.
Hypothesis Hfro : flt + 4 * M <= SRC2_RO_LO \/ SRC2_RO_HI <= flt.
Hypothesis Hgro : fimg + N <= SRC2_RO_LO \/ SRC2_RO_HI <= fimg.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbf : forall i, 0 <= i < 4 * M -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (flt + i).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis HtreeD : tree_at ubs2segs memD t. Hypothesis Hfull : tree_full t. Hypothesis Hwft : tree_forall tnode_wf t.
Hypothesis Hnodes : forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Hypothesis Hntb : forall b, In b (tree_blocks t) -> In b (blocks Lq Aq).
Hypothesis Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n.
Hypothesis Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * M <= tn_addr n.
Hypothesis Hs48 : slot regs0 memD 48 fimg. Hypothesis Hs80 : slot regs0 memD 80 (troot t).
Hypothesis Hs104 : slot regs0 memD 104 N. Hypothesis Hs112 : slot regs0 memD 112 (2 ^ 64 - 1 - fimg).
Hypothesis Hs120 : slot regs0 memD 120 fmt.
Hypothesis Hro0 : ubs2_rgb_rodata_ok mem0.
Hypothesis Htroot : 4096 <= troot t /\ troot t + NODE_SIZE <= alloc_ceiling /\ troot t mod 16 = 0.
Local Notation memIv := (memI N fmt memD flt fimg).
Lemma lregs_keptK : forall regs regs' i (K : list reg), (forall rr, In rr K -> getr regs' rr = getr regs rr) ->
(forall rr : reg, In rr LKEEP -> In rr K) -> lregs regs0 W N fmt flt regs i -> lregs regs0 W N fmt flt regs' i.
Proof. intros regs regs' i K HK HS HL. apply (lregs_kept regs0 W N fmt flt regs regs' i); [intros rr Hrr; exact (HK rr (HS rr Hrr)) | exact HL]. Qed.
Lemma di_consts' : RGBA_STK = 24576 /\ RGBA_FRAME = 5168 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX).
Proof. repeat match goal with H : _ |- _ => clear H end. pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma tree_now : forall m, memIv m -> tree_at ubs2segs m t.
Proof.
intros m HMI. pose proof di_consts' as (_ & _ & HNSv & Hac). eapply tree_at_frame; [exact HtreeD|].
intros n a Hn Ha. destruct (Hnodes n Hn) as (X1 & X2 & X3). pose proof (Hsep_tf n Hn). pose proof (Hsep_tl n Hn).
apply HMI; unfold M in *; lia.
Qed.
Definition dregs_b (regs : bvmap 5 word) : Prop :=
getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\ getr regs 8 = Z_to_bv 64 r /\ getr regs 20 = Z_to_bv 64 cc.
Lemma dregs_b_kept : forall regs regs' (K : list reg), (forall rr, In rr K -> getr regs' rr = getr regs rr) ->
In 3%bv K -> In 4%bv K -> In 8%bv K -> In 20%bv K -> dregs_b regs -> dregs_b regs'.
Proof.
intros regs regs' K HK H3 H4 H8 H20 (G3 & G4 & G8 & G20). unfold dregs_b.
rewrite (HK _ H3), (HK _ H4), (HK _ H8), (HK _ H20). repeat split; assumption.
Qed.
Definition dregs (regs : bvmap 5 word) (i : Z) : Prop :=
lregs regs0 W N fmt flt regs i /\ getr regs 7 = Z_to_bv 64 fmt /\ dregs_b regs.
Lemma lregs_next : forall regs regs' i, lregs regs0 W N fmt flt regs i -> (forall rr, In rr IN_KEEP -> getr regs' rr = getr regs rr) ->
getr regs' 23 = Z_to_bv 64 (i + 1) -> getr regs' 9 = Z_to_bv 64 (fmt * (i + 1)) -> lregs regs0 W N fmt flt regs' (i + 1).
Proof.
intros regs regs' i (G2 & G23 & G9 & G19 & G21 & G22 & G25 & G26 & G27 & G24 & G18) HK R23 R9.
unfold lregs. rewrite (HK 2%bv), (HK 19%bv), (HK 21%bv), (HK 22%bv), (HK 25%bv), (HK 26%bv), (HK 27%bv), (HK 24%bv), (HK 18%bv) by inK.
repeat split; assumption.
Qed.
Ltac lk_sub := intros rr Hrr; unfold LKEEP in Hrr; in_sub Hrr.
Lemma LK_H : forall rr : reg, In rr LKEEP -> In rr H_KEEP. Proof. lk_sub. Qed.
Lemma LK_CL : forall rr : reg, In rr LKEEP -> In rr CL_KEEP. Proof. lk_sub. Qed.
Lemma LK_GA : forall rr : reg, In rr LKEEP -> In rr GA_KEEP. Proof. lk_sub. Qed.
Lemma LK_CS : forall rr : reg, In rr LKEEP -> In rr CALLEE_SAVED. Proof. lk_sub. Qed.
Lemma LK_GK : forall rr : reg, In rr LKEEP -> In rr GK_KEEP. Proof. lk_sub. Qed.
Definition dpost (i pc : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\ fregs3 (@fp_regs fy') /\
memIv mem' /\ dregs regs' i.
Lemma PIX_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> fregs3 (@fp_regs fy) -> memIv mem -> dregs regs i ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom ubs2segs)) mdq) (dpost (i + 1) (if i + 1 <? N then PC_DIH else PC_DIX)).
Proof.
intros fy regs mem i Hi HJ Hfrm HF3 HMI (HL & G7 & HB).
pose proof di_consts' as (HRv & HFv & HNSv & Hac).
assert (HFi : fmt * i + 3 <= fmt * N) by (destruct Hfmt as [-> | ->]; lia).
eapply SR_bind.
{ ltac2:(satvl H_run using (sat_vars ()) as LEM); exact (LEM fy regs mem i Hi HJ Hfrm HMI HL G7). }
cbv beta. intros c1 (fy1 & regs1 & mem1 & skip & -> & HJ1 & Hfrm1 & Hk1 & Q7 & Hfk1 & Hm1 & Hns & Hsk). clear HJ.
assert (HMI1 : memIv mem1).
{ eapply memI_trans; [exact HMI|]. intros a Ha H1 H2. apply Hm1; [exact Ha | lia]. }
pose proof (lregs_keptK regs regs1 i H_KEEP Hk1 LK_H HL) as HL1.
pose proof (dregs_b_kept regs regs1 H_KEEP Hk1 ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB) as HB1.
pose proof (fregs3_kept _ _ H_FKEEP Hfk1 ltac:(inK) ltac:(inK) ltac:(inK) HF3) as HF31.
pose proof HL1 as (L2 & L23 & L9 & L19 & L21 & L22 & L25 & L26 & L27 & L24 & L18).
destruct skip.
- eapply SR_mono.
  { ltac2:(satvl IN_run using (sat_vars ()) as LEM); exact (LEM fy1 regs1 mem1 i Hi HJ1 HMI1 L2 Q7 (Hsk eq_refl) L9). }
  cbv beta. intros c2 (regs2 & -> & R23 & R9 & Hk2).
  exists fy1, regs2, mem1. split; [reflexivity|]. split; [exact HJ1|]. split; [exact Hfrm1|]. split; [exact HF31|]. split; [exact HMI1|].
  split; [exact (lregs_next regs1 regs2 i HL1 Hk2 R23 R9)|].
  split; [rewrite (Hk2 7%bv) by inK; exact Q7|].
  exact (dregs_b_kept regs1 regs2 IN_KEEP Hk2 ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB1).
- destruct (Hns eq_refl) as (Q10 & Q11 & Q12).
  eapply SR_bind.
  { ltac2:(satvl CL3_run using (sat_vars ()) as LEM); exact (LEM fy1 regs1 mem1 i Hi HJ1 Hfrm1 HF31 Q12 Q11 L24 L19). }
  cbv beta. intros c2 (fy2 & regs2 & mem2 & v0 & v1 & v2 & -> & HJ2 & Hfrm2 & Hk2 & Hfk2 & Hm2 & Hcells). clear HJ1.
  assert (HMI2 : memIv mem2).
  { eapply memI_trans; [exact HMI1|]. intros a Ha H1 H2. apply Hm2; [exact Ha | unfold M in *; lia]. }
  pose proof (lregs_keptK regs1 regs2 i CL_KEEP Hk2 LK_CL HL1) as HL2.
  pose proof (dregs_b_kept regs1 regs2 CL_KEEP Hk2 ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB1) as HB2.
  pose proof (fregs3_kept _ _ CL_FKEEP Hfk2 ltac:(inK) ltac:(inK) ltac:(inK) HF31) as HF32.
  assert (Q10' : getr regs2 10 = Z_to_bv 64 (fmt * i)) by (rewrite (Hk2 10%bv) by inK; exact Q10).
  pose proof HL2 as (M2 & M23 & M9 & M19 & M21 & M22 & M25 & M26 & M27 & M24 & M18).
  eapply SR_bind.
  { ltac2:(satvl GA_run using (sat_vars ()) as LEM); exact (LEM fy2 regs2 mem2 i Hi HJ2 HMI2 M2 Q10' M24 M19). }
  cbv beta. intros c3 (regs3 & -> & S1 & S10 & S11 & Hk3).
  pose proof (lregs_keptK regs2 regs3 i GA_KEEP Hk3 LK_GA HL2) as HL3.
  pose proof (dregs_b_kept regs2 regs3 GA_KEEP Hk3 ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB2) as HB3.
  eapply SR_bind.
  { apply (GLNI fy2 RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem2 mdq regs3 t (flt + 4 * (fmt * i)) HJ2).
    - rewrite S1. apply ret_ok_even. vm_compute. reflexivity.
    - exact Hfrm2.
    - exact S10.
    - exact S11.
    - exact (tree_now mem2 HMI2).
    - exact Hfull.
    - intros m Hm. destruct (Hnodes m Hm) as (X1 & X2 & X3). pose proof (Hsep_tl m Hm) as X4.
      split; [unfold tree_forall in Hwft; exact (proj1 (Forall_forall _ _) Hwft m Hm)|].
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. unfold M in *. lia.
    - lia.
    - unfold M in *. lia.
    - exact (mod4_of16 flt (fmt * i) Hflt16).
    - intros j Hj. replace (flt + 4 * (fmt * i) + j) with (flt + (4 * (fmt * i) + j)) by lia.
      ltac2:(satvl flt_present using (sat_vars ()) as LEM); apply (LEM mem2 HJ2). unfold M in *. lia. }
  cbv beta. intros c4 (fy4 & regs4 & m & -> & Hfrm4 & Hfp4 & HP4 & Hlm & Q10c).
  rewrite S1.
  pose proof (leaf_in_nodes t m Hlm) as Hmn.
  assert (Hcidx : 0 <= tn_cidx m < 256).
  { unfold tree_forall in Hwft. destruct (proj1 (Forall_forall _ _) Hwft m Hmn) as (_ & Hc & _). exact Hc. }
  pose proof (lregs_keptK regs3 regs4 i CALLEE_SAVED (fun rr Hr => regs_preserved_in regs3 regs4 rr HP4 Hr) LK_CS HL3) as HL4.
  pose proof (dregs_b_kept regs3 regs4 CALLEE_SAVED (fun rr Hr => regs_preserved_in regs3 regs4 rr HP4 Hr) ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB3) as HB4.
  pose proof (fregs3_kept _ _ FCALLEE_SAVED Hfp4 ltac:(inK) ltac:(inK) ltac:(inK) HF32) as HF34.
  eapply SR_bind.
  { ltac2:(satvl GK_run using (sat_vars ()) as LEM); exact (LEM fy4 regs4 mem2 i (tn_cidx m) v0 v1 v2 Hi Hcidx HJ2 Hfrm4 HMI2 HL4 Q10c HF34 Hcells). }
  cbv beta. intros c5 (fy5 & regs5 & mem5 & -> & HJ5 & Hfrm5 & Hk5 & Hfk5 & R11 & R7 & Hm5). clear HJ2.
  assert (HMI5 : memIv mem5).
  { eapply memI_trans; [exact HMI2|]. intros a Ha H1 H2. apply Hm5; [exact Ha | exact H1 | lia]. }
  pose proof (lregs_keptK regs4 regs5 i GK_KEEP Hk5 LK_GK HL4) as HL5.
  pose proof (dregs_b_kept regs4 regs5 GK_KEEP Hk5 ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB4) as HB5.
  pose proof (fregs3_kept _ _ GK_FKEEP Hfk5 ltac:(inK) ltac:(inK) ltac:(inK) HF34) as HF35.
  pose proof HL5 as (N2 & _ & N9 & _).
  eapply SR_mono.
  { ltac2:(satvl IN_run using (sat_vars ()) as LEM); exact (LEM fy5 regs5 mem5 i Hi HJ5 HMI5 N2 R7 R11 N9). }
  cbv beta. intros c6 (regs6 & -> & R23 & R9 & Hk6).
  exists fy5, regs6, mem5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact Hfrm5|]. split; [exact HF35|]. split; [exact HMI5|].
  split; [exact (lregs_next regs5 regs6 i HL5 Hk6 R23 R9)|].
  split; [rewrite (Hk6 7%bv) by inK; exact R7|].
  exact (dregs_b_kept regs5 regs6 IN_KEEP Hk6 ltac:(inK) ltac:(inK) ltac:(inK) ltac:(inK) HB5).
Qed.
Lemma LOOP_run : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> Z.of_nat k = N - 1 - i ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> fregs3 (@fp_regs fy) -> memIv mem -> dregs regs i ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom ubs2segs)) mdq) (dpost N PC_DIX).
Proof.
induction k as [|k IH]; intros fy regs mem i Hi Hk HJ Hfrm HF3 HMI HD.
- assert (Hlast : i + 1 = N) by lia.
  eapply SR_mono; [exact (PIX_run fy regs mem i Hi HJ Hfrm HF3 HMI HD)|].
  cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & HF3' & HMI' & HD').
  replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Hlast in HD'.
  exists fy', regs', mem'. repeat (split; [first [reflexivity | assumption]|]). exact HD'.
- eapply SR_bind; [exact (PIX_run fy regs mem i Hi HJ Hfrm HF3 HMI HD)|].
  cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & HF3' & HMI' & HD').
  replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
  exact (IH fy' regs' mem' (i + 1) ltac:(lia) ltac:(lia) HJ' Hfrm' HF3' HMI' HD').
Qed.
End e.
Section f.
Context {fxi : YK11.FPState}.
Definition ss_PREx : sstate :=
mkSS PC_DI sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 160 104 120 [mkChunk 48 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (18%nat, mkAF 1 RGB_NMAX 0); (25%nat, mkAF 1 RGB_NMAX 0); (7%nat, mkAF 3 4 0);
(24%nat, mkAF 4096 CEIL_MAX 4); (32%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition ss_PRE : sstate := mkSST PC_DI (ss_regs ss_PREx) (sfr_atoms 64) (ss_mem ss_PREx) None (ss_facts ss_PREx).
Definition ss_DIXx : sstate := mkSS PC_DIX sr_atoms [] None (mkFacts [] [] []).
Lemma DI_at : forall regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
K_QE (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_DI (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_DI) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hdi & HQR & G18 & Hsl & Hsq & S80 & Hfc & Hobj & Hcg & Himg & Hchq & Htok & Hpnew & Hfimg & Hfnz & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
destruct HQR as (G24 & G25 & G7 & G20 & G8 & G21).
pose proof Hsl as (S8 & S16 & S24 & S48).
pose proof Hsq as ((S64 & S88 & S104 & S112 & S120) & S32 & S40).
pose proof Htok as (Htree & Hfull & Hth & Hwft & Hmok & Hnodes).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (Hsp16 : spv mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
pose proof Hwf as (_ & HW1' & HH1' & HNWH & _). rewrite HW in HW1'. rewrite HH in HH1'. rewrite HW, HH in HNWH.
assert (HW1 : 1 <= W) by lia. assert (HWN : exists h, 1 <= h /\ N = W * h) by (exists H; lia). assert (HWN' : W <= N) by nia.
set (keep := BASEv ++ cht_blks C ++ tree_blocks t).
assert (HBk : Permutation (blocks Lc Ac) (keep ++ [(pnew, fmt * N); (fimg, N); (flt, 4 * (fmt * N))])).
{ eapply Permutation_trans; [exact HB|]. subst keep. perm_tac. }
assert (Hsub : forall x0, In x0 BASEv -> In x0 keep) by (intros x0 Hx0; subst keep; apply in_app_iff; left; exact Hx0).
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ flt (4 * (fmt * N)) HHc HBk HBent Hsub ltac:(right; right; left; reflexivity) ltac:(lia)) as [Hfin Hfnot].
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ fimg N HHc HBk HBent Hsub ltac:(right; left; reflexivity) ltac:(lia)) as [Hgin Hgnot].
destruct (heap_blocks_range _ _ LAWS _ _ _ _ flt (4 * (fmt * N)) HHc Hfin ltac:(lia)) as (Hflt0 & Hflt1 & Hflt16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc Hgin ltac:(lia)) as (Hfimg0 & Hfimg1 & _).
assert (HBf : Permutation (blocks Lc Ac) ((flt, 4 * (fmt * N)) :: (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t))).
{ eapply Permutation_trans; [exact HB|]. perm_tac. }
assert (HBg : Permutation (blocks Lc Ac) ((fimg, N) :: (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]))).
{ eapply Permutation_trans; [exact HB|]. perm_tac. }
assert (Hdisj : flt + 4 * (fmt * N) <= fimg \/ fimg + N <= flt).
{ pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (fimg, N) HHc HBf ltac:(apply in_app_iff; right; apply in_app_iff; left; right; left; reflexivity)) as X. cbn [fst snd] in X. lia. }
pose proof (block_off_rod API IMG Lc Ac memc mdc flt (4 * (fmt * N)) HHc Hfin ltac:(lia)) as Hfro.
pose proof (block_off_rod API IMG Lc Ac memc mdc fimg N HHc Hgin ltac:(lia)) as Hgro.
assert (Hwbf : forall i, 0 <= i < 4 * (fmt * N) -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lc Ac) (flt + i)).
{ intros i Hi. right. right. exists flt, (4 * (fmt * N)). split; [exact Hfin|]. split; [exact Hfnot | lia]. }
assert (Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lc Ac) (fimg + i)).
{ intros i Hi. right. right. exists fimg, N. split; [exact Hgin|]. split; [exact Hgnot | lia]. }
assert (Hntb : forall b, In b (tree_blocks t) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply blocks_perm_in; [exact HBf|]. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
assert (Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n).
{ intros n Hn. pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (tn_addr n, NODE_SIZE) HHc HBg
ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; apply tree_blocks_in_nodes; exists n; auto)) as X. cbn [fst snd] in X. lia. }
assert (Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * (fmt * N) <= tn_addr n).
{ intros n Hn. pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (tn_addr n, NODE_SIZE) HHc HBf
ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply tree_blocks_in_nodes; exists n; auto)) as X. cbn [fst snd] in X. lia. }
assert (Htroot : 4096 <= troot t /\ troot t + NODE_SIZE <= alloc_ceiling /\ troot t mod 16 = 0).
{ destruct (troot_in_nodes t Hfull) as (m0 & Hm0 & Hr0). rewrite Hr0. exact (Hnodes m0 Hm0). }
unfold RGB_NMAX in HNmax.
set (E0 := Ereg regs1 (map (Z_to_bv 64) [fimg] ++ [])).
set (E := ew_fregs E0 64 (@fp_regs fxi)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs1 rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [fimg] jj = Some v -> ew E0 (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E0; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E0 32 = Z_to_bv 64 fimg) by exact (HV 0%nat _ eq_refl).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs1 rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (U2 : bv_unsigned (ew E0 2) = spv) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U18 : bv_unsigned (ew E0 18) = W) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E0 25) = N) by (rewrite (HE0 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; lia).
assert (U7 : bv_unsigned (ew E0 7) = fmt) by (rewrite (HE0 7%nat 7%bv eq_refl), G7; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E0 24) = flt) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E0 32) = fimg) by (rewrite HE32; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok ubs2segs fxi E0 ss_PREx (@mkst fxi regs1 (Z_to_bv 64 PC_DI) memc (seg_rom ubs2segs))).
{ unfold ss_PREx. subst E0. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
  split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|].
  split; [intros o Ho; apply Hstw; unfold sp, sp0 in *; lia|].
  apply Forall_cons; [|apply Forall_nil].
  eapply (chunk_ok_val _ _ _ _ _ _ _ fimg); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S48.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U18, U25, U7, U24, U32.
  change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold RGB_NMAX. unfold sp, sp0 in *. repeat split; lia. }
pose proof (st_ok_enterF ubs2segs fxi 64 E0 ss_PREx _ HS0 ltac:(vm_compute; reflexivity) HFRM) as HS.
change (ew_fregs E0 64 (@fp_regs fxi)) with E in HS.
change (mkSST (ss_pc ss_PREx) (ss_regs ss_PREx) (sfr_atoms 64) (ss_mem ss_PREx) (ss_resv ss_PREx) (ss_facts ss_PREx)) with ss_PRE in HS.
clear HS0. rewrite <- !HEE in U2, U18, U25, U7, U24, U32 by lia.
change memc with (ms_mem (@mkst fxi regs1 (Z_to_bv 64 PC_DI) memc (seg_rom ubs2segs))) in HJ.
jrunF_to LAWS ubs2tbl_ok HS HJ PC_DIH.
{ wr_ok_eval. eapply YI0f.wr_ok_cons_win; [reflexivity | exact U2 | cbn [r_wlo]; unfold sp, sp0 in *; lia | cbn [r_whi]; unfold sp, sp0 in *; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
set (memD := ms_mem ms) in *.
assert (KW : forall x, 0 <= x < 2 ^ 64 -> ~ (spv + 104 <= x < spv + 120) -> mbyte ubs2segs memD x = mbyte ubs2segs memc x).
{ intros x Hx Hnx. apply (mbyte_of_frame_g ubs2segs E _ memc memD x HF Hx). intros rg Hrg. cbv [In] in Hrg.
  destruct Hrg as [<- | []]. cbn [r_base r_wlo r_whi base_val]. rewrite U2. exact Hnx. }
pose proof (fun rr => st_okF_reg ubs2segs E _ _ rr HS) as RG.
pose proof (st_okF_regs_kept ubs2segs E _ _ regs1 [2; 3; 4; 7; 8; 18; 20; 24]%bv HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as Hk0.
assert (E7 : ew E 7 = Z_to_bv 64 fmt) by (rewrite (HE 7%nat 7%bv eq_refl); exact G7).
assert (E24 : ew E 24 = Z_to_bv 64 flt) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HL0 : lregs regs0 W N fmt flt (ms_regs ms) 0).
{ unfold lregs.
  split; [rewrite (Hk0 2%bv) by inK; exact G2|].
  split; [rewrite (RG 23%bv); eval_sr_get; reflexivity|].
  split; [rewrite (RG 9%bv); eval_sr_get; rewrite Z.mul_0_r; reflexivity|].
  split; [rewrite (RG 19%bv); eval_sr_get; rewrite denot_lit_U, (U_not E 24 flt E24) by lia; reflexivity|].
  split; [rewrite (RG 21%bv); eval_sr_get; cbn [sv_denot]; rewrite U18; f_equal; lia|].
  split; [rewrite (RG 22%bv); eval_sr_get; rewrite (U_mul_off E 7 18 fmt W (-1) E7 U18) by lia; f_equal; lia|].
  split; [rewrite (RG 25%bv); eval_sr_get; rewrite (U_mul_off E 7 18 fmt W 0 E7 U18) by lia; f_equal; lia|].
  split; [rewrite (RG 26%bv); eval_sr_get; rewrite (U_mul_off E 7 18 fmt W 1 E7 U18) by lia; f_equal; lia|].
  split; [rewrite (RG 27%bv); eval_sr_get; rewrite (U_subw_zext' E 25 18 N W U25 U18) by lia; reflexivity|].
  split; [rewrite (Hk0 24%bv) by inK; exact G24|].
  rewrite (Hk0 18%bv) by inK; exact G18. }
assert (HD0 : dregs flt (ch_c C) (ms_regs ms) 0).
{ split; [exact HL0|]. split; [rewrite (Hk0 7%bv) by inK; exact G7|].
  unfold dregs_b. rewrite (Hk0 3%bv), (Hk0 4%bv), (Hk0 8%bv), (Hk0 20%bv) by inK.
  split; [exact G3|]. split; [exact G4|]. split; [exact G8 | exact G20]. }
assert (HF30 : fregs3 (ms_fregs ms)).
{ unfold fregs3. rewrite !(st_okF_freg ubs2segs E _ _ _ HS).
  repeat match goal with |- context [sfr_get ?l ?rr] => let v := eval vm_compute in (sfr_get l rr) in change (sfr_get l rr) with v end.
  cbn [sv_denot]. split; [vm_compute; reflexivity | split; vm_compute; reflexivity]. }
pose proof (st_okF_frm ubs2segs E _ _ HS) as Hfrm1.
assert (HSl : @st_ok ubs2segs (fp_of ms) E _ ms) by exact (st_okF_to_legacy ubs2segs E _ ms HS).
assert (Hs48 : slot regs0 memD 48 fimg).
{ intros k Hk. rewrite KW; [apply S48; exact Hk | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia]. }
assert (Hs80 : slot regs0 memD 80 (troot t)).
{ intros k Hk. rewrite KW; [apply S80; exact Hk | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia]. }
assert (Hs120 : slot regs0 memD 120 fmt).
{ intros k Hk. rewrite KW; [apply S120; exact Hk | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia]. }
assert (Hs104 : slot regs0 memD 104 N).
{ unfold slot. apply val_mem_word_mem.
  eapply (st_chunk_val ubs2segs E _ ms 0%nat _ 2%nat 104 8%N (SOff 25 0) spv N HSl); [reflexivity | reflexivity | cbv; auto 20 | exact U2 | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite U25, Z.add_0_r. reflexivity. }
assert (Hs112 : slot regs0 memD 112 (2 ^ 64 - 1 - fimg)).
{ unfold slot. apply val_mem_word_mem.
  eapply (st_chunk_val ubs2segs E _ ms 0%nat _ 2%nat 112 8%N (SAlu ALU_XOR (SOff 32 0) (SLit (-1))) spv (2 ^ 64 - 1 - fimg) HSl);
  [reflexivity | reflexivity | cbv; auto 20 | exact U2 | | cbn; lia | cbn; lia].
  rewrite denot_lit_U, (U_not E 32 fimg) by first [rewrite HEE by lia; exact HE32 | lia]. reflexivity. }
assert (HtreeD : tree_at ubs2segs memD t).
{ eapply tree_at_frame; [exact Htree|]. intros n a Hn Ha. destruct (Hnodes n Hn) as (X1 & X2 & X3).
  apply KW; unfold sp, sp0 in *; lia. }
rewrite (st_okF_mkst ubs2segs E _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (@mkst _ _ (Z_to_bv 64 ?p) _ _) _) _ => change p with PC_DIH end.
clear HS HSl HF RG.
eapply SR_bind.
{ pose (Lq := Lc). pose (Aq := Ac). pose (mdq := mdc). pose (cc := ch_c C).
  ltac2:(satvl LOOP_run using (sat_vars ()) as LEM10); exact (LEM10 (Z.to_nat (N - 1)) (fp_of ms) (ms_regs ms) memD 0 ltac:(lia) ltac:(lia) HJ Hfrm1 HF30 ltac:(intros a0 _ _ _; reflexivity) HD0). }
cbv beta. intros cE (fyE & regsE & memE & -> & HJE & HfrmE & HF3E & HMIE & HDE). clear HJ.
destruct HDE as ((F2 & F23 & F9 & F19 & F21 & F22 & F25 & F26 & F27 & F24 & F18) & F7 & (F3 & F4 & F8 & F20)).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJE)) as (Hh & Hlz & _).
set (E2 := Ereg regsE []).
assert (HS : @st_ok ubs2segs fyE E2 ss_DIXx (@mkst fyE regsE (Z_to_bv 64 PC_DIX) memE (seg_rom ubs2segs))).
{ unfold ss_DIXx. subst E2. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
pure_to ubs2tbl_ok HS PC_QE. eapply (SR_msteps ubs2segs _ _ mdc _ Hh Hlz Hms).
lazymatch goal with |- SR _ (mkCfg (@mkst _ ?rg _ _ _) _) _ => rename rg into regsF end.
pose proof (regs_kept_of_st_ok _ _ _ _ regsE _ [2; 3; 4; 8; 20; 24]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HkF. cbn [ms_regs mkst] in HkF. clear HS.
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> ~ (spv + SL_104 <= x < spv + SL_120) ->
mbyte ubs2segs memE x = mbyte ubs2segs memc x).
{ intros x Hx Hs Hna Hnb. unfold SL_104, SL_120 in Hnb. rewrite <- (KW x ltac:(lia) Hnb). apply HMIE; lia. }
assert (KB : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte ubs2segs memE (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi.
  assert (Hbf : In (b, m) (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t)).
  { apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; exact Hbm]. }
  assert (Hbg : In (b, m) (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))])).
  { apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; rewrite app_assoc; apply in_app_iff; left; exact Hbm]. }
  pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (b, m) HHc HBf Hbf) as X1. cbn [fst snd] in X1.
  pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (b, m) HHc HBg Hbg) as X2. cbn [fst snd] in X2.
  destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc ltac:(eapply blocks_perm_in; [exact HBf | right; exact Hbf]) ltac:(lia)) as (Y1 & Y2 & _).
  rewrite <- (KW (b + i) ltac:(lia) ltac:(unfold sp, sp0 in *; lia)). apply HMIE; lia. }
ltac2:(satvl qfacts_kept_di using (sat_vars ()) as QKD).
destruct (QKD memc memE pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH KB) as (TR & TS & TQ & TF & TO & TC & TI & TH & TT).
apply (KQE fyE regsF Lc Ac memE mdc ha pnew fimg imgl C cnt pal t flt HfrmE).
split.
{ split; [exact HJE|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
  split; [exact (TR HRA)|]. split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
  split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
    intros i Hi. unfold RGBFC_SIZE in *. apply KH; unfold sp, sp0, RGBA_FRAME, OFF_apal, SL_104, SL_120 in *; lia. }
  split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [unfold RGB_NMAX; exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [rewrite (HkF 2%bv) by inK; exact F2 | split; [rewrite (HkF 3%bv) by inK; exact F3 | rewrite (HkF 4%bv) by inK; exact F4]]|].
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|].
split; [rewrite (HkF 24%bv) by inK; exact F24|].
split; [rewrite (HkF 20%bv) by inK; exact F20|].
split; [rewrite (HkF 8%bv) by inK; exact F8|].
split; [exact (TS Hsl)|].
split; [exact (TQ SL_80 (troot t) ltac:(unfold SL_80; lia) ltac:(unfold SL_80, SL_104; lia) S80)|].
split; [exact (TQ SL_64 (nha ha) ltac:(unfold SL_64; lia) ltac:(unfold SL_64, SL_104; lia) S64)|].
split; [exact (TF Hfc)|]. split; [exact (TO Hobj)|]. split; [exact (TC Hcg)|].
split; [exact (TI Himg)|]. split; [exact (TH Hchq)|]. split; [exact (TT Htok)|].
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfnz|]. exact HB.
Qed.
End f.
Lemma ubs2_rgbadd_DI : seg_DI (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KQE fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt HFRM HAT. exact (DI_at regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT). Qed.
End d.
End c.
