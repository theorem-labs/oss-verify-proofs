(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03 YI07
YI1e YI1i YI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d YI0e
YI3h YI4v YI4r YI4s YI4w YI3s YI3t YP12.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN07.
Ltac2 sat_vars () := [@API; @L; @A; @regs0; @mem0; @md0; @r; @cfp; @g; @wfn; @ctx; @path; @attr; @gen; @loops; @W; @H; @bef; @beffmt; @cur; @s; @N; @img; @fmt; @fattr; @fgen; @delay; @rest; @Lq; @Aq; @mdq; @memD; @flt; @fimg; @t; @pnew; @cc].
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
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Section e.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree) (pnew cc : Z).
Let M : Z := fmt * N.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN1 : 1 <= N. Hypothesis HNmax : N <= RGB_NMAX.
Hypothesis HW1 : 1 <= W. Hypothesis HWN : exists h, 1 <= h /\ N = W * h.
Hypothesis Hceil : alloc_ceiling + RGBA_STK <= sp0v. Hypothesis H63 : sp0v < 2 ^ 63. Hypothesis Hal0 : sp0v mod 16 = 0.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt16 : flt mod 16 = 0.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis Hdisj : flt + 4 * M <= fimg \/ fimg + N <= flt.
Hypothesis Hfro : flt + 4 * M <= SRC2_RO9 \/ SRC2_RO9 + 8 <= flt.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq). Hypothesis Hgin : In (fimg, N) (blocks Lq Aq).
Hypothesis Hwbf : forall i, 0 <= i < 4 * M -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (flt + i).
Hypothesis Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (fimg + i).
Hypothesis HtreeD : tree_at src2segs memD t. Hypothesis Hfull : tree_full t. Hypothesis Hwft : tree_forall tnode_wf t.
Hypothesis Hnodes : forall n, In n (tree_nodes t) -> 4096 <= tn_addr n /\ tn_addr n + NODE_SIZE <= alloc_ceiling /\ tn_addr n mod 16 = 0.
Hypothesis Hntb : forall b, In b (tree_blocks t) -> In b (blocks Lq Aq).
Hypothesis Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n.
Hypothesis Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * M <= tn_addr n.
Hypothesis HslotW : slot regs0 memD SL_64 W.
Hypothesis Hro0 : src2_rgb_rodata_ok mem0.
Local Notation memIv := (memI N fmt memD flt fimg).
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5136 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 158.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte src2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.

Lemma tree_now : forall m, memIv m -> tree_at src2segs m t.
Proof.
intros m HMI. pose proof di_consts as (HRv & HFv & _ & HNSv & Hac & _). eapply tree_at_frame; [exact HtreeD|].
intros n a Hn Ha. destruct (Hnodes n Hn) as (X1 & X2 & X3). pose proof (Hsep_tf n Hn). pose proof (Hsep_tl n Hn).
apply HMI; lia.
Qed.
Lemma leaf_facts : forall m u n, tree_at src2segs m u -> In n (tree_leaves u) ->
In n (tree_nodes u) /\ length (tn_mean n) = 3%nat /\ exists c0 c1, obj_at src2segs m (tn_addr n) LAY_Node (node_vals c0 c1 n 1).
Proof.
intros m u. induction u as [|n0|n0 l IHl rr IHr]; intros n Ht Hin; cbn [tree_leaves tree_at tree_nodes] in *.
- destruct Hin.
- destruct Hin as [<- | []]. destruct Ht as (_ & Hlen & c0 & c1 & Hobj). split; [left; reflexivity|]. split; [exact Hlen|]. exists c0, c1. exact Hobj.
- fold (tree_at src2segs) in Ht. destruct Ht as (_ & _ & _ & Hl & Hr). apply in_app_iff in Hin as [Hin|Hin].
+ destruct (IHl n Hl Hin) as (A1 & A2 & A3). split; [right; apply in_app_iff; left; exact A1|]. auto.
+ destruct (IHr n Hr Hin) as (A1 & A2 & A3). split; [right; apply in_app_iff; right; exact A1|]. auto.
Qed.
Lemma root_cases : forall m u, tree_at src2segs m u -> tree_full u ->
exists n lf c0 c1, troot u = tn_addr n /\ In n (tree_nodes u) /\ (lf = 0 \/ lf = 1) /\ length (tn_mean n) = 3%nat /\
obj_at src2segs m (tn_addr n) LAY_Node (node_vals c0 c1 n lf) /\
(lf = 1 -> u = TLeaf n) /\ (lf = 0 -> exists l rr, u = TNode n l rr).
Proof.
intros m [|n|n l rr] Ht Hf; [destruct Hf| |]; cbn [tree_at] in Ht.
- destruct Ht as (_ & Hlen & c0 & c1 & Hobj). exists n, 1, c0, c1.
split; [reflexivity|]. split; [left; reflexivity|]. split; [right; reflexivity|]. split; [exact Hlen|]. split; [exact Hobj|].
split; [intros _; reflexivity | intros HH0; discriminate HH0].
- fold (tree_at src2segs) in Ht. destruct Ht as (_ & Hlen & Hobj & _ & _). exists n, 0, (troot l), (troot rr).
split; [reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|]. split; [exact Hlen|]. split; [exact Hobj|].
split; [intros HH0; discriminate HH0 | intros _; exists l, rr; reflexivity].
Qed.
Definition DC_REGS : list reg := [2; 3; 4; 10; 27; 25; 14; 11; 12; 7; 13; 6; 5; 17; 1; 20; 8; 24]%bv.
Definition dregs_c (regs : bvmap 5 word) (i : Z) : Prop :=
getr regs 2 = Z_to_bv 64 spv /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 10 = Z_to_bv 64 flt /\ getr regs 27 = Z_to_bv 64 (troot t) /\ getr regs 25 = Z_to_bv 64 fimg /\
getr regs 14 = Z_to_bv 64 i /\ getr regs 11 = Z_to_bv 64 (fmt * i) /\
getr regs 12 = Z_to_bv 64 (W - 1) /\ getr regs 7 = Z_to_bv 64 (N - W) /\
getr regs 13 = Z_to_bv 64 (fmt * W) /\ getr regs 6 = Z_to_bv 64 (fmt * (W - 1)) /\ getr regs 5 = Z_to_bv 64 (fmt * (W + 1)) /\
getr regs 17 = Z_to_bv 64 N /\ getr regs 1 = Z_to_bv 64 W /\
getr regs 20 = Z_to_bv 64 cc /\ getr regs 8 = Z_to_bv 64 r /\ getr regs 24 = Z_to_bv 64 pnew.
Definition dregs (regs : bvmap 5 word) (i : Z) : Prop :=
dregs_c regs i /\ getr regs 26 = Z_to_bv 64 fmt /\ getr regs 16 = Z_to_bv 64 4 /\ getr regs 15 = Z_to_bv 64 (spv + OFF_apal + 3).
Lemma dregs_c_kept : forall regs regs' i, (forall rr : reg, In rr DC_REGS -> getr regs' rr = getr regs rr) -> dregs_c regs i -> dregs_c regs' i.
Proof.
intros regs regs' i HK (G2 & G3 & G4 & G10 & G27 & G25 & G14 & G11 & G12 & G7 & G13 & G6 & G5 & G17 & G1 & G20 & G8 & G24).
unfold dregs_c. rewrite (HK 2%bv), (HK 3%bv), (HK 4%bv), (HK 10%bv), (HK 27%bv), (HK 25%bv), (HK 14%bv), (HK 11%bv), (HK 12%bv), (HK 7%bv), (HK 13%bv), (HK 6%bv),
(HK 5%bv), (HK 17%bv), (HK 1%bv), (HK 20%bv), (HK 8%bv), (HK 24%bv) by inK. repeat (split; [assumption|]). assumption.
Qed.
Ltac dc_sub := intros rr Hrr; unfold DC_REGS in Hrr; in_sub Hrr.
Lemma DC_sub_H : forall rr : reg, In rr DC_REGS -> In rr H_KEEP. Proof. dc_sub. Qed.
Lemma DC_sub_CL : forall rr : reg, In rr DC_REGS -> In rr CL_KEEP. Proof. dc_sub. Qed.
Lemma DC_sub_D0 : forall rr : reg, In rr DC_REGS -> In rr D0_KEEP. Proof. dc_sub. Qed.
Lemma DC_sub_DL : forall rr : reg, In rr DC_REGS -> In rr DL_KEEP. Proof. dc_sub. Qed.
Lemma DC_sub_LF : forall rr : reg, In rr DC_REGS -> In rr LF_KEEP. Proof. dc_sub. Qed.
Lemma DC_sub_KL : forall rr : reg, In rr DC_REGS -> In rr KL_KEEP. Proof. dc_sub. Qed.
Definition dpost (i pc : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\ memIv mem' /\ dregs regs' i.
Lemma TAIL_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z) (m : tnode) (c0 c1 : Z),
0 <= i < N -> In m (tree_leaves t) ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem ->
obj_at src2segs mem (tn_addr m) LAY_Node (node_vals c0 c1 m 1) ->
dregs_c regs i -> getr regs 9 = Z_to_bv 64 (tn_addr m) -> getr regs 30 = Z_to_bv 64 (fimg + i) -> getr regs 29 = Z_to_bv 64 (i + 1) ->
getr regs 26 = Z_to_bv 64 fmt -> getr regs 16 = Z_to_bv 64 4 -> getr regs 15 = Z_to_bv 64 (spv + OFF_apal + 3) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_LF) mem (seg_rom src2segs)) mdq) (dpost (i + 1) (if i + 1 <? N then PC_DIH else PC_DIX)).
Proof.
intros fy regs mem i m c0 c1 Hi Hlm HJ Hfrm HMI Hobj HDC G9 G30 G29 G26 G16 G15.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HDC as (G2 & G3 & G4 & G10 & G27 & G25 & G14 & G11 & G12 & G7 & G13 & G6 & G5 & G17 & G1 & G20 & G8 & G24).
destruct (leaf_facts memD t m HtreeD Hlm) as (Hmn & Hmlen & _).
assert (Hwfm : tnode_wf m) by (unfold tree_forall in Hwft; exact (proj1 (Forall_forall _ _) Hwft m Hmn)). destruct Hwfm as (_ & Hcidx & _).
eapply SR_bind.
{ ltac2:(satvl LF_run using (sat_vars ()) as LEM1); exact (LEM1 fy regs mem i m c0 c1 Hi Hlm HJ HMI G2 G9 G30 G14 G1 Hobj). }
cbv beta. intros c2 (regs2 & mem2 & -> & HJ2 & HMI2 & P9 & P19 & P31 & Pib & Hk2). clear HJ.
pose proof (dregs_c_kept regs regs2 i (fun rr Hrr => Hk2 rr (DC_sub_LF rr Hrr)) HDC) as HDC2.
pose proof HDC2 as (_ & _ & _ & Q10 & _ & _ & Q14 & _ & Q12 & Q7 & Q13 & Q6 & Q5 & _).
eapply SR_bind.
{ ltac2:(satvl KL_run using (sat_vars ()) as LEM2);
exact (LEM2 fy regs2 mem2 i (tn_cidx m) Hi Hcidx HJ2 Hfrm P9 ltac:(rewrite (Hk2 15%bv ltac:(inK)); exact G15) ltac:(rewrite (Hk2 30%bv ltac:(inK)); exact G30) Pib Q10
ltac:(rewrite P19; exact G11) ltac:(rewrite (Hk2 26%bv ltac:(inK)); exact G26) Q13 Q6 Q5 P31 Q12 Q14 Q7). }
cbv beta. intros c3 (fy3 & regs3 & mem3 & -> & HJ3 & Hfrm3 & Hk3 & K15 & Hm3). clear HJ2.
assert (HMI3 : memIv mem3).
{ eapply memI_trans; [exact HMI2|]. intros a Ha H1 H2. apply Hm3; [exact Ha | subst M; exact H1]. }
pose proof (dregs_c_kept regs2 regs3 i (fun rr Hrr => Hk3 rr (DC_sub_KL rr Hrr)) HDC2) as HDC3.
pose proof HDC3 as (R2 & R3 & R4 & R10 & R27 & R25 & _ & R11 & R12 & R7 & R13 & R6 & R5 & R17 & R1 & R20 & R8 & R24).
assert (T26 : getr regs3 26 = Z_to_bv 64 fmt) by (rewrite (Hk3 26%bv ltac:(inK)), (Hk2 26%bv ltac:(inK)); exact G26).
assert (T16 : getr regs3 16 = Z_to_bv 64 4) by (rewrite (Hk3 16%bv ltac:(inK)), (Hk2 16%bv ltac:(inK)); exact G16).
assert (T29 : getr regs3 29 = Z_to_bv 64 (i + 1)) by (rewrite (Hk3 29%bv ltac:(inK)), (Hk2 29%bv ltac:(inK)); exact G29).
assert (T15 : getr regs3 15 = Z_to_bv 64 (spv + OFF_apal + 3)) by (rewrite K15, (Hk2 15%bv ltac:(inK)); exact G15).
eapply SR_mono.
{ ltac2:(satvl IN_run using (sat_vars ()) as LEM4); exact (LEM4 fy3 regs3 mem3 i Hi HJ3 T26 R17 T29 R11). }
cbv beta. intros c5 (regs5 & -> & S14 & S11 & Hk5).
exists fy3, regs5, mem3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrm3|]. split; [exact HMI3|].
split.
{ unfold dregs_c. rewrite (Hk5 2%bv), (Hk5 3%bv), (Hk5 4%bv), (Hk5 10%bv), (Hk5 27%bv), (Hk5 25%bv), (Hk5 12%bv), (Hk5 7%bv), (Hk5 13%bv), (Hk5 6%bv), (Hk5 5%bv),
(Hk5 17%bv), (Hk5 1%bv), (Hk5 20%bv), (Hk5 8%bv), (Hk5 24%bv) by inK.
repeat (split; [assumption|]). assumption. }
rewrite (Hk5 26%bv), (Hk5 16%bv), (Hk5 15%bv) by inK. repeat (split; [assumption|]). assumption.
Qed.
Lemma PIX_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> dregs regs i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom src2segs)) mdq) (dpost (i + 1) (if i + 1 <? N then PC_DIH else PC_DIX)).
Proof.
intros fy regs mem i Hi HJ Hfrm HMI (HDC & G26 & G16 & G15).
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap).
pose proof HDC as (G2 & G3 & G4 & G10 & G27 & G25 & G14 & G11 & G12 & G7 & G13 & G6 & G5 & G17 & G1 & G20 & G8 & G24).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
eapply SR_bind.
{ ltac2:(satvl H_run using (sat_vars ()) as LEM5); exact (LEM5 fy regs mem i Hi HJ Hfrm G14 G25 G26 G16 G11 G10). }
cbv beta. intros c1 (fy1 & regs1 & mem1 & skip & -> & HJ1 & Hfrm1 & Q30 & Q29 & Q26 & Q16 & Hk1 & Hm1 & Hns & Hsk). clear HJ.
assert (HMI1 : memIv mem1).
{ eapply memI_trans; [exact HMI|]. intros a Ha H1 H2. apply Hm1; [exact Ha | lia]. }
pose proof (dregs_c_kept regs regs1 i (fun rr Hrr => Hk1 rr (DC_sub_H rr Hrr)) HDC) as HDC1.
assert (Q15 : getr regs1 15 = Z_to_bv 64 (spv + OFF_apal + 3)) by (rewrite (Hk1 15%bv ltac:(inK)); exact G15).
destruct skip.
-
pose proof HDC1 as (_ & _ & _ & _ & _ & _ & _ & P11 & _ & _ & _ & _ & _ & P17 & _).
eapply SR_mono.
{ ltac2:(satvl IN_run using (sat_vars ()) as LEM6); exact (LEM6 fy1 regs1 mem1 i Hi HJ1 Q26 P17 Q29 P11). }
cbv beta. intros c2 (regs2 & -> & R14 & R11 & Hk2).
exists fy1, regs2, mem1. split; [reflexivity|]. split; [exact HJ1|]. split; [exact Hfrm1|]. split; [exact HMI1|].
pose proof HDC1 as (P2 & P3 & P4 & P10 & P27 & P25 & _ & _ & P12 & P7 & P13 & P6 & P5 & _ & P1 & P20 & P8 & P24).
split.
{ unfold dregs_c. rewrite (Hk2 2%bv), (Hk2 3%bv), (Hk2 4%bv), (Hk2 10%bv), (Hk2 27%bv), (Hk2 25%bv), (Hk2 12%bv), (Hk2 7%bv), (Hk2 13%bv), (Hk2 6%bv), (Hk2 5%bv),
(Hk2 17%bv), (Hk2 1%bv), (Hk2 20%bv), (Hk2 8%bv), (Hk2 24%bv) by inK.
repeat (split; [assumption|]). assumption. }
rewrite (Hk2 26%bv), (Hk2 16%bv), (Hk2 15%bv) by inK. repeat (split; [assumption|]). assumption.
-
destruct (Hns eq_refl) as (Q9 & Q31 & Q18).
pose proof HDC1 as (_ & _ & _ & P10 & _).
eapply SR_bind.
{ ltac2:(satvl CL3_run using (sat_vars ()) as LEM7); exact (LEM7 fy1 regs1 mem1 i Hi HJ1 Hfrm1 Q18 Q9 P10). }
cbv beta. intros c2 (fy2 & regs2 & mem2 & -> & HJ2 & Hfrm2 & Hk2 & Hm2). clear HJ1.
assert (HMI2 : memIv mem2).
{ eapply memI_trans; [exact HMI1|]. intros a Ha H1 H2. apply Hm2; [exact Ha | subst M; nia]. }
pose proof (dregs_c_kept regs1 regs2 i (fun rr Hrr => Hk2 rr (DC_sub_CL rr Hrr)) HDC1) as HDC2.
pose proof (tree_now mem2 HMI2) as Htree2.
destruct (root_cases mem2 t Htree2 Hfull) as (n & lf & c0 & c1 & Hroot & Hnin & Hlf & Hlen & Hobj & HifL & HifN).
destruct (Hnodes n Hnin) as (Hn0 & Hn1 & Hn16).
pose proof HDC2 as (_ & _ & _ & R10 & R27 & _).
eapply SR_bind.
{ ltac2:(satvl D0_run using (sat_vars ()) as LEM8); exact (LEM8 fy2 regs2 mem2 i n c0 c1 lf Hi Hlf HJ2 ltac:(rewrite R27, Hroot; reflexivity) ltac:(rewrite (Hk2 31%bv ltac:(inK)); exact Q31) R10 Hobj Hlen Hn0 Hn1 Hn16). }
cbv beta. intros c3 (regs3 & -> & S9 & S31 & Hk3).
pose proof (dregs_c_kept regs2 regs3 i (fun rr Hrr => Hk3 rr (DC_sub_D0 rr Hrr)) HDC2) as HDC3.
assert (T30 : getr regs3 30 = Z_to_bv 64 (fimg + i)) by (rewrite (Hk3 30%bv), (Hk2 30%bv) by inK; exact Q30).
assert (T29 : getr regs3 29 = Z_to_bv 64 (i + 1)) by (rewrite (Hk3 29%bv), (Hk2 29%bv) by inK; exact Q29).
assert (T26 : getr regs3 26 = Z_to_bv 64 fmt) by (rewrite (Hk3 26%bv), (Hk2 26%bv) by inK; exact Q26).
assert (T16 : getr regs3 16 = Z_to_bv 64 4) by (rewrite (Hk3 16%bv), (Hk2 16%bv) by inK; exact Q16).
assert (T15 : getr regs3 15 = Z_to_bv 64 (spv + OFF_apal + 3)) by (rewrite (Hk3 15%bv), (Hk2 15%bv) by inK; exact Q15).
destruct Hlf as [-> | ->].
+
change (if 0 =? 0 then PC_DL else PC_LF) with PC_DL.
destruct (HifN eq_refl) as (tl & tr & Ht).
assert (HpM : 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia). assert (Hfi : 0 <= fmt * i) by nia.
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
eapply SR_bind.
{ ltac2:(satvl DG_run using (sat_vars ()) as LEM9); apply (LEM9 t n tl tr fy2 regs3 mem2 (flt + 4 * (fmt * i)) Ht Hh Hlz Hfrm2 S9 (S31 eq_refl) Htree2 Hfull).
- intros m Hm. split; [unfold tree_forall in Hwft; exact (proj1 (Forall_forall _ _) Hwft m Hm)|].
destruct (Hnodes m Hm) as (X1 & X2 & X3). pose proof (Hsep_tl m Hm). repeat split; lia.
- lia. - lia.
- replace (flt + 4 * (fmt * i)) with (flt + (fmt * i) * 4) by lia. rewrite Z.mod_add by lia. exact Hf4.
- intros j Hj. rewrite <- Z.add_assoc. apply (flt_present mem2 HJ2). lia. }
cbv beta. intros c4 (fy4 & regs4 & m & -> & Hfrm4 & Hlm & S9m & Hk4).
pose proof (dregs_c_kept regs3 regs4 i (fun rr Hrr => Hk4 rr (DC_sub_DL rr Hrr)) HDC3) as HDC4.
destruct (leaf_facts mem2 t m Htree2 Hlm) as (_ & _ & d0 & d1 & Hobjm).
apply (TAIL_run fy4 regs4 mem2 i m d0 d1 Hi Hlm HJ2 Hfrm4 HMI2 Hobjm HDC4 S9m).
* rewrite (Hk4 30%bv) by inK. exact T30.
* rewrite (Hk4 29%bv) by inK. exact T29.
* rewrite (Hk4 26%bv) by inK. exact T26.
* rewrite (Hk4 16%bv) by inK. exact T16.
* rewrite (Hk4 15%bv) by inK. exact T15.
+
change (if 1 =? 0 then PC_DL else PC_LF) with PC_LF.
pose proof (HifL eq_refl) as Ht.
assert (Hlm : In n (tree_leaves t)) by (rewrite Ht; left; reflexivity).
apply (TAIL_run fy2 regs3 mem2 i n c0 c1 Hi Hlm HJ2 Hfrm2 HMI2 Hobj HDC3 S9 T30 T29 T26 T16 T15).
Qed.
Lemma LOOP_run : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N -> Z.of_nat k = N - 1 - i ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memIv mem -> dregs regs i ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_DIH) mem (seg_rom src2segs)) mdq) (dpost N PC_DIX).
Proof.
induction k as [|k IH]; intros fy regs mem i Hi Hk HJ Hfrm HMI HD.
- assert (Hlast : i + 1 = N) by lia.
eapply SR_mono; [exact (PIX_run fy regs mem i Hi HJ Hfrm HMI HD)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & HMI' & HD').
replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Hlast in HD'.
exists fy', regs', mem'. repeat (split; [first [reflexivity | assumption]|]). exact HD'.
- eapply SR_bind; [exact (PIX_run fy regs mem i Hi HJ Hfrm HMI HD)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & HMI' & HD').
replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia).
exact (IH fy' regs' mem' (i + 1) ltac:(lia) ltac:(lia) HJ' Hfrm' HMI' HD').
Qed.
End e.
Section f.
Context {fxi : YK11.FPState}.
Definition ss_PREx : sstate :=
mkSS PC_DI sr_atoms [] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (1%nat, mkAF 1 RGB_NMAX 0); (22%nat, mkAF 1 RGB_NMAX 0); (26%nat, mkAF 3 4 0) ] [] []).
Definition ss_PRE : sstate := mkSST PC_DI (ss_regs ss_PREx) (sfr_atoms 64) (ss_mem ss_PREx) None (ss_facts ss_PREx).
Definition ss_DIXx : sstate := mkSS PC_DIX sr_atoms [] None (mkFacts [] [] []).
Lemma DI_at : forall regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt,
K_QE (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_DI (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt ->
SR src2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_DI) memc (seg_rom src2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hdi & HQR & Hsl & Hsq & Hfc & Hobj & Hcg & Himg & Hchq & Htok & Hpnew & Hfimg & Hfnz & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
destruct HQR as (G10 & G11 & G17 & G1 & G27 & G24 & G26 & G22 & G25 & G20 & G8).
pose proof Htok as (Htree & Hfull & Hth & Hwft & Hnodes).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HNSv : NODE_SIZE = 56) by reflexivity.
assert (Hsp16 : spv mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
pose proof Hwf as (_ & HW1' & HH1' & HNWH & _). rewrite HW in HW1'. rewrite HH in HH1'. rewrite HW, HH in HNWH.
assert (HW1 : 1 <= W) by lia. assert (HWN : exists h, 1 <= h /\ N = W * h) by (exists H; lia). assert (HWN' : W <= N) by nia.
set (keep := BASEv ++ cht_blks C ++ tree_blocks t).
assert (HBk : Permutation (blocks Lc Ac) (keep ++ [(pnew, fmt * N); (fimg, N); (flt, 4 * (fmt * N))])).
{ eapply Permutation_trans; [exact HB|]. subst keep. perm_tac. }
assert (Hsub : forall x0, In x0 BASEv -> In x0 keep) by (intros x0 Hx0; subst keep; apply in_app_iff; left; exact Hx0).
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ flt (4 * (fmt * N)) HHc HBk HBent Hsub ltac:(right; right; left; reflexivity) ltac:(lia)) as [Hfin Hfnot].
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ fimg N HHc HBk HBent Hsub ltac:(right; left; reflexivity) ltac:(lia)) as [Hgin Hgnot].
destruct (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep _ pnew (fmt * N) HHc HBk HBent Hsub ltac:(left; reflexivity) ltac:(lia)) as [Hpin _].
destruct (heap_blocks_range _ _ LAWS _ _ _ _ flt (4 * (fmt * N)) HHc Hfin ltac:(lia)) as (Hflt0 & Hflt1 & Hflt16).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HHc Hgin ltac:(lia)) as (Hfimg0 & Hfimg1 & _).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ pnew (fmt * N) HHc Hpin ltac:(lia)) as (Hpnew0 & Hpnew1 & _).
assert (HBf : Permutation (blocks Lc Ac) ((flt, 4 * (fmt * N)) :: (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t))).
{ eapply Permutation_trans; [exact HB|]. perm_tac. }
assert (HBg : Permutation (blocks Lc Ac) ((fimg, N) :: (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))]))).
{ eapply Permutation_trans; [exact HB|]. perm_tac. }
assert (Hdisj : flt + 4 * (fmt * N) <= fimg \/ fimg + N <= flt).
{ pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (fimg, N) HHc HBf ltac:(apply in_app_iff; right; apply in_app_iff; left; right; left; reflexivity)) as X. cbn [fst snd] in X. lia. }
pose proof (block_off_ro9 API IMG Lc Ac memc mdc flt (4 * (fmt * N)) HHc Hfin ltac:(lia)) as Hfro.
assert (Hwbf : forall i, 0 <= i < 4 * (fmt * N) -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lc Ac) (flt + i)).
{ intros i Hi. right. right. exists flt, (4 * (fmt * N)). split; [exact Hfin|]. split; [exact Hfnot | lia]. }
assert (Hwbg : forall i, 0 <= i < N -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lc Ac) (fimg + i)).
{ intros i Hi. right. right. exists fimg, N. split; [exact Hgin|]. split; [exact Hgnot | lia]. }
assert (Htb : forall b, In b (tree_blocks t) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply blocks_perm_in; [exact HBf|]. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
assert (Hsep_tf : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= fimg \/ fimg + N <= tn_addr n).
{ intros n Hn. pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (tn_addr n, NODE_SIZE) HHc HBg
ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; apply tree_blocks_in_nodes; exists n; auto)) as X. cbn [fst snd] in X. lia. }
assert (Hsep_tl : forall n, In n (tree_nodes t) -> tn_addr n + NODE_SIZE <= flt \/ flt + 4 * (fmt * N) <= tn_addr n).
{ intros n Hn. pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (tn_addr n, NODE_SIZE) HHc HBf
ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; apply tree_blocks_in_nodes; exists n; auto)) as X. cbn [fst snd] in X. lia. }
assert (Rcfp : 0 <= cfp < 2 ^ 64) by (clear - Hclo Hchi Hceil Hac HRv; unfold sp0, RGBFC_SIZE in *; lia).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HBf|]; right; apply in_app_iff; left; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ r RGB_SIZE HHc Hrin ltac:(lia)) as (Hr0 & Hr1 & _).
set (E0 := Ereg regs1 []).
set (E := ew_fregs E0 64 (@fp_regs fxi)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs1 rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs1 rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (U2 : bv_unsigned (ew E0 2) = spv) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U22 : bv_unsigned (ew E0 22) = N) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E0 26) = fmt) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U1 : bv_unsigned (ew E0 1) = W) by (rewrite (HE0 1%nat 1%bv eq_refl), G1; apply unsigned_lit_small; lia).
assert (HS0 : @st_ok src2segs fxi E0 ss_PREx (@mkst fxi regs1 (Z_to_bv 64 PC_DI) memc (seg_rom src2segs))).
{ unfold ss_PREx. subst E0. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U1, U22, U26.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold sp, sp0 in *. repeat split; lia. }
pose proof (st_ok_enterF src2segs fxi 64 E0 ss_PREx _ HS0 ltac:(vm_compute; reflexivity) HFRM) as HS.
change (ew_fregs E0 64 (@fp_regs fxi)) with E in HS.
change (mkSST (ss_pc ss_PREx) (ss_regs ss_PREx) (sfr_atoms 64) (ss_mem ss_PREx) (ss_resv ss_PREx) (ss_facts ss_PREx)) with ss_PRE in HS.
clear HS0. rewrite <- !HEE in U2, U22, U26, U1 by lia.
change memc with (ms_mem (@mkst fxi regs1 (Z_to_bv 64 PC_DI) memc (seg_rom src2segs))) in HJ.
jrunF_to LAWS src2tbl_ok HS HJ PC_DIH. { wr_ok_eval. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
assert (Hmm : ms_mem ms = memc).
{ apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
rewrite Hmm in HJ. rewrite (st_okF_mkst src2segs E _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm.
assert (RG : forall rr : reg, getr (ms_regs ms) rr = sv_denot E (sr_get (ss_regs (fst (sym_run_toFN src2segs src2tbl FUEL PC_DIH ss_PRE))) rr)) by (intros rr; exact (st_okF_reg src2segs E _ _ rr HS)).
match type of RG with context [ss_regs (fst ?x)] => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in RG end.
pose proof (st_okF_regs_kept src2segs E _ _ regs1 [1; 2; 3; 4; 8; 10; 20; 24; 25; 26; 27]%bv HS ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(vm_compute; reflexivity)) as Hk0.
assert (HD0 : dregs flt fimg t pnew (ch_c C) (ms_regs ms) 0).
{ split.
- unfold dregs_c. rewrite (Hk0 2%bv), (Hk0 3%bv), (Hk0 4%bv), (Hk0 10%bv), (Hk0 27%bv), (Hk0 25%bv), (Hk0 1%bv), (Hk0 20%bv), (Hk0 8%bv), (Hk0 24%bv) by inK.
split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G10|]. split; [exact G27|]. split; [exact G25|].
split; [rewrite (RG 14%bv); eval_sr_get; cbn [sv_denot]; reflexivity|].
split; [rewrite (RG 11%bv); eval_sr_get; cbn [sv_denot]; f_equal; lia|].
split; [rewrite (RG 12%bv); eval_sr_get; cbn [sv_denot]; rewrite U1; reflexivity|].
split; [rewrite (RG 7%bv); eval_sr_get; first [rewrite (U_subw_zext E 22 1 N W U22 U1) by lia | rewrite (U_subw_zext' E 22 1 N W U22 U1) by lia]; reflexivity|].
split; [rewrite (RG 13%bv); eval_sr_get; rewrite (U_mul_off E 26 1 fmt W 0) by first [rewrite <- U26; symmetry; apply Z_to_bv_bv_unsigned | exact U1 | lia]; f_equal; lia|].
split; [rewrite (RG 6%bv); eval_sr_get; rewrite (U_mul_off E 26 1 fmt W (-1)) by first [rewrite <- U26; symmetry; apply Z_to_bv_bv_unsigned | exact U1 | lia]; f_equal; lia|].
split; [rewrite (RG 5%bv); eval_sr_get; rewrite (U_mul_off E 26 1 fmt W 1) by first [rewrite <- U26; symmetry; apply Z_to_bv_bv_unsigned | exact U1 | lia]; f_equal; lia|].
split; [rewrite (RG 17%bv); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, U22; reflexivity|].
split; [exact G1|]. split; [exact G20|]. split; [exact G8|]. exact G24.
- rewrite (Hk0 26%bv) by inK.
split; [exact G26|].
split; [rewrite (RG 16%bv); eval_sr_get; cbn [sv_denot]; reflexivity|].
rewrite (RG 15%bv); eval_sr_get; cbn [sv_denot]; rewrite U2; f_equal; unfold OFF_apal; lia. }
pose proof (st_okF_frm src2segs E _ _ HS) as Hfrm1. clear HS HF RG.
eapply SR_bind.
{ pose (Lq := Lc). pose (Aq := Ac). pose (mdq := mdc). pose (memD := memc). pose (cc := ch_c C).
ltac2:(satvl LOOP_run using (sat_vars ()) as LEM10); exact (LEM10 (Z.to_nat (N - 1)) (fp_of ms) (ms_regs ms) memc 0 ltac:(lia) ltac:(lia) HJ Hfrm1 ltac:(intros a0 _ _ _; reflexivity) HD0). }
cbv beta. intros cE (fyE & regsE & memE & -> & HJE & HfrmE & HMIE & HDE). clear HJ.
destruct HDE as ((F2 & F3 & F4 & F10 & F27 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F20 & F8 & F24) & _).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJE)) as (Hh & Hlz & _).
set (E2 := Ereg regsE []).
assert (HS : @st_ok src2segs fyE E2 ss_DIXx (@mkst fyE regsE (Z_to_bv 64 PC_DIX) memE (seg_rom src2segs))).
{ unfold ss_DIXx. subst E2. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
pure_to src2tbl_ok HS PC_QE. eapply (SR_msteps src2segs _ _ mdc _ Hh Hlz Hms).
lazymatch goal with |- SR _ (mkCfg (@mkst _ ?rg _ _ _) _) _ => rename rg into regsF end.
pose proof (regs_kept_of_st_ok _ _ _ _ regsE _ [2; 3; 4; 8; 10; 20; 24; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HkF. cbn [ms_regs mkst] in HkF. clear HS.
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte src2segs memE x = mbyte src2segs memc x).
{ intros x Hx Hs Hna. apply HMIE; lia. }
assert (KB : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte src2segs memE (b + i) = mbyte src2segs memc (b + i)).
{ intros b m i Hbm Hi.
assert (Hbf : In (b, m) (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t)).
{ apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; exact Hbm]. }
assert (Hbg : In (b, m) (BASEv ++ [(pnew, fmt * N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))])).
{ apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; exact Hbm | apply in_app_iff; right; apply in_app_iff; right; rewrite app_assoc; apply in_app_iff; left; exact Hbm]. }
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (b, m) HHc HBf Hbf) as X1. cbn [fst snd] in X1.
pose proof (heap_sep_perm _ _ LAWS _ _ _ _ _ _ (b, m) HHc HBg Hbg) as X2. cbn [fst snd] in X2.
destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc ltac:(eapply blocks_perm_in; [exact HBf | right; exact Hbf]) ltac:(lia)) as (Y1 & Y2 & _).
apply HMIE; lia. }
destruct (qfacts_kept regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest memc memE ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH KB)
as (TR & TS & TQ & TF & TO & TC & TI & TH & TT).
apply (KQE fyE regsF Lc Ac memE mdc ha pnew fimg imgl C cnt pal t flt HfrmE).
split.
{ split; [exact HJE|]. split; [exact Hinit|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split; [exact (TR HRA)|]. split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range src2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply KH; unfold sp, sp0, RGBA_FRAME, OFF_apal in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [rewrite (HkF 2%bv) by inK; exact F2 | split; [rewrite (HkF 3%bv) by inK; exact F3 | rewrite (HkF 4%bv) by inK; exact F4]]|].
split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|].
split; [rewrite (HkF 10%bv) by inK; exact F10|]. split; [rewrite (HkF 27%bv) by inK; exact F27|]. split; [rewrite (HkF 20%bv) by inK; exact F20|].
split; [rewrite (HkF 8%bv) by inK; exact F8|]. split; [rewrite (HkF 24%bv) by inK; exact F24|].
split; [exact (TS Hsl)|]. split; [exact (TQ Hsq)|]. split; [exact (TF Hfc)|]. split; [exact (TO Hobj)|]. split; [exact (TC Hcg)|].
split; [exact (TI Himg)|]. split; [exact (TH Hchq)|]. split; [exact (TT Htok)|].
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfnz|]. exact HB.
Qed.
End f.
Lemma src2_rgbadd_DI : seg_DI (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KQE fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt HFRM HAT. exact (DI_at regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt pal t flt KQE HFRM HAT). Qed.
End d.
End c.
