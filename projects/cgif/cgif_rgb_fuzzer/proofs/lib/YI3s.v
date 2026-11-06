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
YI3h YI4v YI4r YI4s YI4w YP12.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_DIH : Z := 0x14050.
Definition PC_C0  : Z := 0x1407c.
Definition PC_CL  : Z := 0x14088.
Definition PC_D0  : Z := 0x140cc.
Definition PC_DL  : Z := 0x140e8.
Definition PC_DC  : Z := 0x1410c.
Definition PC_LF  : Z := 0x14124.
Definition PC_KL  : Z := 0x14138.
Definition PC_IN  : Z := 0x14258.
Definition PC_DIX : Z := 0x14264.
Definition SRC2_RO9 : Z := 0x103d8.
Lemma val_mem_byte1 : forall segs m a v, mbyte segs m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem segs m a 1 v.
Proof.
intros segs m a v H Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
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
Lemma src2_ro9_in_img : forall a, SRC2_RO9 <= a < SRC2_RO9 + 8 -> in_img src2_msyms a.
Proof.
intros a Ha. unfold in_img. split; [vm_compute; discriminate|].
eexists. split; [left; reflexivity|].
lazymatch goal with |- bv_unsigned ?x <= _ < bv_unsigned ?x' + bv_unsigned ?y =>
let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v;
let w := eval vm_compute in (bv_unsigned y) in change (bv_unsigned y) with w end.
unfold SRC2_RO9 in Ha. lia.
Qed.
Lemma block_off_ro9 : forall Lc Ac memc mdc b sz,
heap_ok MR Lc Ac memc mdc -> In (b, sz) (blocks Lc Ac) -> 0 < sz -> b + sz <= SRC2_RO9 \/ SRC2_RO9 + 8 <= b.
Proof.
intros Lc Ac memc mdc b sz HH Hin Hsz.
destruct (Z_lt_le_dec SRC2_RO9 (b + sz)) as [H1|H1]; [|left; lia].
destruct (Z_lt_le_dec b (SRC2_RO9 + 8)) as [H2|H2]; [|right; lia].
exfalso. apply blocks_In in Hin as (p & Hp & Hpin).
pose proof (eq_refl : SRC2_RO9 = 0x103d8).
apply (il_blocks IMG Lc Ac memc mdc p sz (Z.max b SRC2_RO9 - b) (proj1 HH) Hpin ltac:(lia)).
rewrite Hp. apply src2_ro9_in_img. lia.
Qed.
Section f.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (memD : word -> option byte).
Variables (flt fimg : Z) (t : tree).
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
Definition memI (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> ~ (fimg <= a < fimg + N) -> mbyte src2segs m a = mbyte src2segs memD a.
Lemma memI_trans : forall m m', memI m ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> ~ (fimg <= a < fimg + N) -> mbyte src2segs m' a = mbyte src2segs m a) -> memI m'.
Proof. intros m m' Hm Hk a Ha H1 H2. rewrite (Hk a Ha H1 H2). apply Hm; assumption. Qed.
Lemma di_consts : RGBA_STK = 24576 /\ RGBA_FRAME = 5136 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\ (CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ OFF_apal = 158.
Proof. repeat match goal with H : _ |- _ => clear H end.   pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | lia]. Qed.
Lemma flt_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte src2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma flt_writable : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, flt <= a < flt + 4 * M -> writable_at src2segs m a.
Proof.
intros m HJ a Ha. replace a with (flt + (a - flt)) by lia. apply (present_writable src2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) (a - flt) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin ltac:(lia))).
Qed.
Lemma fimg_writable : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, fimg <= a < fimg + N -> writable_at src2segs m a.
Proof.
intros m HJ a Ha. replace a with (fimg + (a - fimg)) by lia. apply (present_writable src2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq fimg N (a - fimg) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia))).
Qed.
Lemma apal_present : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 768 -> exists b, mbyte src2segs m (spv + OFF_apal + i) = Some b.
Proof.
intros m HJ i Hi. pose proof di_consts as (HRv & HFv & _ & _ & Hac & Hap).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
apply mbyte_of_present. apply src2_writable_high_present; [unfold sp, sp0 in *; lia|].
apply Hstw. unfold sp, sp0 in *. lia.
Qed.
Lemma src2_ro9_bytes : forall a, SRC2_RO9 <= a < SRC2_RO9 + 8 -> exists b, seg_rom src2segs (Z_to_bv 64 a) = Some b.
Proof.
intros a Ha. unfold SRC2_RO9 in Ha.
assert (X : a = 0x103d8 \/ a = 0x103d9 \/ a = 0x103da \/ a = 0x103db \/ a = 0x103dc \/ a = 0x103dd \/ a = 0x103de \/ a = 0x103df) by lia.
repeat (destruct X as [-> | X]; [eexists; vm_compute; reflexivity|]). subst a. eexists; vm_compute; reflexivity.
Qed.
Lemma rodata_now : forall m, journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq -> src2_rgb_rodata_ok m.
Proof. intros m HJ. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & Hik). exact (src2_rgb_rodata_kept mem0 m Hik Hro0). Qed.
Definition klw (a d : nat) : YQ0b.region := YQ0b.mkRegion (Some a) 0 12 0 12 [mkChunk 0 (CData d 0 12)].
Definition kl_mem (c1 c2 c3 : bool) : smem :=
[ YQ0b.mkRegion (Some 30%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 37 0))];
YQ0b.mkRegion (Some 38%nat) 0 3 0 0 [mkChunk 0 (CData 5 0 3)]; klw 32 0 ]
++ (if c1 then [klw 33 1] else []) ++ (if c2 then [klw 34 2] else [])
++ (if c2 && c3 then [klw 35 3] else []) ++ (if c2 && c1 then [klw 36 4] else [])
++ [ YQ0b.mkRegion None SRC2_RO9 (SRC2_RO9 + 8) 0 0 [mkChunk SRC2_RO9 (CImg 8)] ].
Definition kl_facts (c1 c2 c3 : bool) : list (nat * afact) :=
[ (9%nat, mkAF CEIL_MIN (2^63) 0); (10%nat, mkAF 4096 CEIL_MAX 2);
(19%nat, mkAF 0 (2^20) 0); (26%nat, mkAF 3 4 0); (13%nat, mkAF 0 (2^20) 0); (6%nat, mkAF 0 (2^20) 0); (5%nat, mkAF 0 (2^20) 0);
(31%nat, mkAF 0 (2^16) 0); (12%nat, mkAF 0 (2^16) 0); (14%nat, mkAF 0 (2^14) 0); (7%nat, mkAF 0 (2^32 - 1) 0);
(30%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF CEIL_MIN (2^63) 0);
(32%nat, mkAF 4096 CEIL_MAX 2) ]
++ (if c1 then [(33%nat, mkAF 4096 CEIL_MAX 2)] else []) ++ (if c2 then [(34%nat, mkAF 4096 CEIL_MAX 2)] else [])
++ (if c2 && c3 then [(35%nat, mkAF 4096 CEIL_MAX 2)] else []) ++ (if c2 && c1 then [(36%nat, mkAF 4096 CEIL_MAX 2)] else []).
Definition kl_conds (c1 c2 c3 : bool) : list acond :=
[ mkAC (if c1 then BC_LTU else BC_GEU) (SOff 31%nat 0) (SOff 12%nat 0);
mkAC (if c2 then BC_LTU else BC_GEU) (SOff 14%nat 0) (SOff 7%nat 0);
mkAC (if c3 then BC_NE else BC_EQ) (SOff 31%nat 0) (SLit 0) ].
Definition kl_cell (x : sv) : sv := SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL x (SLit 2)).
Definition kl_alias : list (sv * sv) :=
[ (kl_cell (SOff 19 0), SOff 32%nat 0);
(kl_cell (SAlu ALU_ADD (SOff 26 0) (SOff 19 0)), SOff 33%nat 0);
(kl_cell (SAlu ALU_ADD (SOff 13 0) (SOff 19 0)), SOff 34%nat 0);
(kl_cell (SAlu ALU_ADD (SOff 6 0) (SOff 19 0)), SOff 35%nat 0);
(kl_cell (SAlu ALU_ADD (SOff 5 0) (SOff 19 0)), SOff 36%nat 0);
(SAlu ALU_ADD (SOff 9 0) (SMd M_MUL (SOff 37 0) (SLit 3)), SOff 38%nat 0) ].
Definition ss_KLx (c1 c2 c3 : bool) : sstate :=
mkSS PC_KL (sr_set sr_atoms 15%bv (SOff 9%nat 3)) (kl_mem c1 c2 c3) None (mkFacts (kl_facts c1 c2 c3) (kl_conds c1 c2 c3) kl_alias).
Definition ss_KL (c1 c2 c3 : bool) : sstate :=
mkSST PC_KL (ss_regs (ss_KLx c1 c2 c3)) (sfr_atoms 96) (kl_mem c1 c2 c3) None (ss_facts (ss_KLx c1 c2 c3)).
Definition KL_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 16; 17; 20; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KL_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_IN) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
(forall rr : reg, In rr KL_KEEP -> getr regs' rr = getr regs rr) /\ getr regs' 15 = getr regs 15 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> mbyte src2segs mem' a = mbyte src2segs mem a).
Lemma N_ge_W' : W <= N. Proof. destruct HWN as (h & Hh & HN). subst N. nia. Qed.
Lemma KL_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i idx : Z),
0 <= i < N -> 0 <= idx < 256 ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 9 = Z_to_bv 64 (spv + OFF_apal) -> getr regs 15 = Z_to_bv 64 (spv + OFF_apal + 3) ->
getr regs 30 = Z_to_bv 64 (fimg + i) -> val_mem src2segs mem (fimg + i) 1 idx ->
getr regs 10 = Z_to_bv 64 flt ->
getr regs 19 = Z_to_bv 64 (fmt * i) -> getr regs 26 = Z_to_bv 64 fmt -> getr regs 13 = Z_to_bv 64 (fmt * W) ->
getr regs 6 = Z_to_bv 64 (fmt * (W - 1)) -> getr regs 5 = Z_to_bv 64 (fmt * (W + 1)) ->
getr regs 31 = Z_to_bv 64 (i mod W) -> getr regs 12 = Z_to_bv 64 (W - 1) -> getr regs 14 = Z_to_bv 64 i -> getr regs 7 = Z_to_bv 64 (N - W) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_KL) mem (seg_rom src2segs)) mdq) (KL_post fy regs mem).
Proof.
intros fy regs mem i idx Hi Hidx HJ Hfrm G9 G15 G30 Hib G10 G19 G26 G13 G6 G5 G31 G12 G14 G7.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap). pose proof N_ge_W' as HWN'.
destruct HWN as (hh & Hh1 & HNW).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
assert (Hmod : 0 <= i mod W < W) by (apply Z.mod_pos_bound; lia).
pose proof (block_off_ro9 Lq Aq mem mdq fimg N (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia)) as Hgro.
set (c1 := i mod W <? W - 1). set (c2 := i <? N - W). set (c3 := negb (i mod W =? 0)).
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 12 <= 4 * M) by (subst M; nia).
assert (Hcr : c1 = true -> 0 <= 4 * (fmt * (i + 1)) /\ 4 * (fmt * (i + 1)) + 12 <= 4 * M).
{ intros Hc. subst c1. apply Z.ltb_lt in Hc. pose proof (fs_right W hh N HW1 HNW i Hi Hc). subst M; nia. }
assert (Hcd : c2 = true -> 0 <= 4 * (fmt * (i + W)) /\ 4 * (fmt * (i + W)) + 12 <= 4 * M).
{ intros Hc. subst c2. apply Z.ltb_lt in Hc. subst M; nia. }
assert (Hcdl : c2 = true -> c3 = true -> 0 <= 4 * (fmt * (i + W - 1)) /\ 4 * (fmt * (i + W - 1)) + 12 <= 4 * M).
{ intros Hc Hc'. subst c2 c3. apply Z.ltb_lt in Hc. apply Bool.negb_true_iff in Hc'. apply Z.eqb_neq in Hc'. subst M; nia. }
assert (Hcdr : c2 = true -> c1 = true -> 0 <= 4 * (fmt * (i + W + 1)) /\ 4 * (fmt * (i + W + 1)) + 12 <= 4 * M).
{ intros Hc Hc'. subst c2 c1. apply Z.ltb_lt in Hc. apply Z.ltb_lt in Hc'. pose proof (fs_down_right W hh N HW1 HNW i Hi Hc Hc'). subst M; nia. }
destruct (bytes_of_present src2segs mem (spv + OFF_apal + 3 * idx) 3 ltac:(intros j Hj; replace (spv + OFF_apal + 3 * idx + j) with (spv + OFF_apal + (3 * idx + j)) by lia; apply (apal_present mem HJ); lia)) as (bp & Lbp & Hbp).
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * i)) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); lia)) as (b0 & Lb0 & Hb0).
assert (Xr : exists b1, length b1 = 12%nat /\ (c1 = true -> forall j, (j < 12)%nat -> mbyte src2segs mem (flt + 4 * (fmt * (i + 1)) + Z.of_nat j) = nth_error b1 j)).
{ destruct c1; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * (i + 1))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcr eq_refl); lia)) as (b & Lb & Hb).
exists b. auto. }
destruct Xr as (b1 & Lb1 & Hb1).
assert (Xd : exists b2, length b2 = 12%nat /\ (c2 = true -> forall j, (j < 12)%nat -> mbyte src2segs mem (flt + 4 * (fmt * (i + W)) + Z.of_nat j) = nth_error b2 j)).
{ destruct c2; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * (i + W))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcd eq_refl); lia)) as (b & Lb & Hb).
exists b. auto. }
destruct Xd as (b2 & Lb2 & Hb2).
assert (Xdl : exists b3, length b3 = 12%nat /\ (c2 = true -> c3 = true -> forall j, (j < 12)%nat -> mbyte src2segs mem (flt + 4 * (fmt * (i + W - 1)) + Z.of_nat j) = nth_error b3 j)).
{ destruct c2; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
destruct c3; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros _ HH0; discriminate HH0]].
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * (i + W - 1))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcdl eq_refl eq_refl); lia)) as (b & Lb & Hb).
exists b. auto. }
destruct Xdl as (b3 & Lb3 & Hb3).
assert (Xdr : exists b4, length b4 = 12%nat /\ (c2 = true -> c1 = true -> forall j, (j < 12)%nat -> mbyte src2segs mem (flt + 4 * (fmt * (i + W + 1)) + Z.of_nat j) = nth_error b4 j)).
{ destruct c2; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
destruct c1; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros _ HH0; discriminate HH0]].
destruct (bytes_of_present src2segs mem (flt + 4 * (fmt * (i + W + 1))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcdr eq_refl eq_refl); lia)) as (b & Lb & Hb).
exists b. auto. }
destruct Xdr as (b4 & Lb4 & Hb4).
set (vals := [flt + 4 * (fmt * i); flt + 4 * (fmt * (i + 1)); flt + 4 * (fmt * (i + W)); flt + 4 * (fmt * (i + W - 1)); flt + 4 * (fmt * (i + W + 1)); idx; spv + OFF_apal + 3 * idx]).
set (E0 := EregB regs (map (Z_to_bv 64) vals) [b0; b1; b2; b3; b4; bp]).
set (E := ew_fregs E0 96 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 96)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply EregB_vals; exact Hj).
assert (HD : forall d, ed E d = nth d [b0; b1; b2; b3; b4; bp] []) by (intros d; subst E E0; reflexivity).
pose proof (HV 0%nat _ eq_refl) as A32. pose proof (HV 1%nat _ eq_refl) as A33. pose proof (HV 2%nat _ eq_refl) as A34.
pose proof (HV 3%nat _ eq_refl) as A35. pose proof (HV 4%nat _ eq_refl) as A36. pose proof (HV 5%nat _ eq_refl) as A37. pose proof (HV 6%nat _ eq_refl) as A38.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38.
assert (U9 : bv_unsigned (ew E0 9) = spv + OFF_apal) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U10 : bv_unsigned (ew E0 10) = flt) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = fmt * i) by (rewrite (HE0 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; nia).
assert (U26 : bv_unsigned (ew E0 26) = fmt) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E0 13) = fmt * W) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; nia).
assert (U6 : bv_unsigned (ew E0 6) = fmt * (W - 1)) by (rewrite (HE0 6%nat 6%bv eq_refl), G6; apply unsigned_lit_small; nia).
assert (U5 : bv_unsigned (ew E0 5) = fmt * (W + 1)) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; nia).
assert (U31 : bv_unsigned (ew E0 31) = i mod W) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E0 12) = W - 1) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E0 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (U7 : bv_unsigned (ew E0 7) = N - W) by (rewrite (HE0 7%nat 7%bv eq_refl), G7; apply unsigned_lit_small; lia).
assert (U30 : bv_unsigned (ew E0 30) = fimg + i) by (rewrite (HE0 30%nat 30%bv eq_refl), G30; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E0 37) = idx) by (rewrite A37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E0 38) = spv + OFF_apal + 3 * idx) by (rewrite A38; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U32 : bv_unsigned (ew E0 32) = flt + 4 * (fmt * i)) by (rewrite A32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = flt + 4 * (fmt * (i + 1))) by (rewrite A33; apply unsigned_lit_small; nia).
assert (U34 : bv_unsigned (ew E0 34) = flt + 4 * (fmt * (i + W))) by (rewrite A34; apply unsigned_lit_small; nia).
assert (U35 : bv_unsigned (ew E0 35) = flt + 4 * (fmt * (i + W - 1))) by (rewrite A35; apply unsigned_lit_small; nia).
assert (U36 : bv_unsigned (ew E0 36) = flt + 4 * (fmt * (i + W + 1))) by (rewrite A36; apply unsigned_lit_small; nia).
assert (RW : forall (a : nat) (d : nat) base bs, bv_unsigned (ew E0 a) = base -> ed E0 d = bs -> length bs = 12%nat ->
4096 <= base -> base + 12 <= alloc_ceiling ->
(forall j, (j < 12)%nat -> mbyte src2segs mem (base + Z.of_nat j) = nth_error bs j) ->
(forall a', base <= a' < base + 12 -> writable_at src2segs mem a') ->
@region_ok src2segs E0 mem (klw a d)).
{ intros a d base bs Ha Hd Hl R0 R1 Hbs Hw. unfold klw, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite Ha.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length bs)) by (rewrite Hl; reflexivity).
apply (chunk_ok_data src2segs E0 mem base 0 d bs Hd). intros j Hj. rewrite Z.add_0_r. apply Hbs. rewrite <- Hl. exact Hj. }
assert (HS0 : @st_ok src2segs fy E0 (ss_KLx c1 c2 c3) (@mkst fy regs (Z_to_bv 64 PC_KL) mem (seg_rom src2segs))).
{ unfold ss_KLx. apply entry_st_ok_env.
- apply regs_ok_pin; [subst E0; apply regs_ok_EregB | intros HH0; discriminate HH0 |].
cbn [sv_denot]. rewrite U9, G15. reflexivity.
- subst c1 c2 c3. destruct (i mod W <? W - 1), (i <? N - W), (negb (i mod W =? 0)); vm_compute; reflexivity.
- unfold kl_mem. apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]].
+ constructor; [|constructor; [|constructor; [|constructor]]].
* unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U30.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, U37; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Hib.
* unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U38.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. replace 3 with (Z.of_nat (length bp)) at 2 by (rewrite Lbp; reflexivity).
apply (chunk_ok_data src2segs E0 mem _ 0 5 bp ltac:(subst E0; reflexivity)). intros j Hj. rewrite Z.add_0_r. apply Hbp. rewrite <- Lbp. exact Hj.
* apply (RW 32%nat 0%nat _ b0 U32 ltac:(subst E0; reflexivity) Lb0); [lia | lia | exact Hb0 | intros a' Ha'; apply (flt_writable mem HJ); lia].
+ destruct c1 eqn:Ec1; [|constructor]. constructor; [|constructor].
specialize (Hcr eq_refl). apply (RW 33%nat 1%nat _ b1 U33 ltac:(subst E0; reflexivity) Lb1); [lia | lia | exact (Hb1 eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
+ destruct c2 eqn:Ec2; [|constructor]. constructor; [|constructor].
specialize (Hcd eq_refl). apply (RW 34%nat 2%nat _ b2 U34 ltac:(subst E0; reflexivity) Lb2); [lia | lia | exact (Hb2 eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
+ destruct c2 eqn:Ec2; [|constructor]. destruct c3 eqn:Ec3; [|constructor]. constructor; [|constructor].
specialize (Hcdl eq_refl eq_refl). apply (RW 35%nat 3%nat _ b3 U35 ltac:(subst E0; reflexivity) Lb3); [lia | lia | exact (Hb3 eq_refl eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
+ destruct c2 eqn:Ec2; [|constructor]. destruct c1 eqn:Ec1; [|constructor]. constructor; [|constructor].
specialize (Hcdr eq_refl eq_refl). apply (RW 36%nat 4%nat _ b4 U36 ltac:(subst E0; reflexivity) Lb4); [lia | lia | exact (Hb4 eq_refl eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
+ constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [unfold SRC2_RO9; lia|]. split; [unfold SRC2_RO9; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [c_off c_val c_len cv_len cbyte] in Hj |- *.
destruct (src2_ro9_bytes (SRC2_RO9 + j) ltac:(lia)) as [b Hb]. exists b. unfold img_byte. rewrite Z.add_0_l.
split; [exact Hb|]. rewrite (rodata_now mem HJ (SRC2_RO9 + j)); [exact Hb|]. unfold SRC2_RO_LO, SRC2_RO_HI, SRC2_RO9 in *. lia.
-
unfold kl_mem, klw. subst c1 c2 c3.
assert (Q1 : fmt <= fmt * W) by nia. assert (Q2 : 2 <= W -> 2 * fmt <= fmt * W) by nia. assert (Q3 : 3 <= W -> 3 * fmt <= fmt * W) by nia.
assert (P0 : 0 <= fmt * i) by nia.
assert (R1 : fmt * (i + 1) = fmt * i + fmt) by ring. assert (R2 : fmt * (i + W) = fmt * i + fmt * W) by ring.
assert (R3 : fmt * (i + W - 1) = fmt * i + fmt * W - fmt) by ring. assert (R4 : fmt * (i + W + 1) = fmt * i + fmt * W + fmt) by ring.
rewrite R1 in U33, Hcr. rewrite R2 in U34, Hcd. rewrite R3 in U35, Hcdl. rewrite R4 in U36, Hcdr.
assert (Hsplo : alloc_ceiling <= spv) by (unfold sp, sp0 in *; lia).
set (pI := fmt * i) in *. set (qW := fmt * W) in *.
destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3;
cbn [andb app pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
rewrite ?U30, ?U38, ?U32, ?U33, ?U34, ?U35, ?U36;
first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
first [apply Bool.negb_true_iff in E3; apply Z.eqb_neq in E3 | apply Bool.negb_false_iff in E3; apply Z.eqb_eq in E3];
clearbody pI qW; clear - P0 Q1 Q2 Q3 Hmod E1 E2 E3 Hflt0 Hflt1 Hfro Hsplo Hfmt Hac HW1 Hci Hcr Hcd Hcdl Hcdr Hidx Hap Hi HWN' Hfimg0 Hfimg1 Hdisj HFv Hgro;
unfold SRC2_RO9 in *; repeat split; lia.
- split; [|split].
+ unfold kl_facts. subst c1 c2 c3.
assert (P0 : 0 <= fmt * i) by nia. assert (P1 : fmt * (i + W + 1) <= 2 ^ 19) by nia. assert (Q1 : fmt <= fmt * W) by nia.
assert (R1 : fmt * (i + 1) = fmt * i + fmt) by ring. assert (R2 : fmt * (i + W) = fmt * i + fmt * W) by ring.
assert (R3 : fmt * (i + W - 1) = fmt * i + fmt * W - fmt) by ring. assert (R4 : fmt * (i + W + 1) = fmt * i + fmt * W + fmt) by ring.
rewrite R1 in U33, Hcr. rewrite R2 in U34, Hcd. rewrite R3 in U35, Hcdl. rewrite R4 in U36, Hcdr, P1.
assert (Q6 : 0 <= fmt * (W - 1) <= 2 ^ 19) by nia. assert (Q5 : 0 <= fmt * (W + 1) <= 2 ^ 19) by nia. assert (Q13 : 0 <= fmt * W <= 2 ^ 19) by nia.
rewrite <- R2 in U34. rewrite R2 in U34.
assert (Hspr : alloc_ceiling <= spv /\ spv + RGBA_FRAME <= 2 ^ 63) by (unfold sp, sp0 in *; lia).
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (MD4 : forall x, (flt + 4 * x) mod 4 = 0) by (intros x; replace (flt + 4 * x) with (flt + x * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
pose proof (MD4 (fmt * i)) as M0. pose proof (MD4 (fmt * i + fmt)) as M1. pose proof (MD4 (fmt * i + fmt * W)) as M2.
pose proof (MD4 (fmt * i + fmt * W - fmt)) as M3. pose proof (MD4 (fmt * i + fmt * W + fmt)) as M4.
set (pI := fmt * i) in *. set (qW := fmt * W) in *.
destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3;
cbn [andb app f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite ?U9, ?U10, ?U19, ?U26, ?U13, ?U6, ?U5, ?U31, ?U12, ?U14, ?U7, ?U30, ?U37, ?U38, ?U32, ?U33, ?U34, ?U35, ?U36;
change (2 ^ 2) with 4; change (2 ^ 0) with 1; rewrite !Z.mod_1_r;
first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
first [apply Bool.negb_true_iff in E3; apply Z.eqb_neq in E3 | apply Bool.negb_false_iff in E3; apply Z.eqb_eq in E3];
set (q6 := fmt * (W - 1)) in *; set (q5 := fmt * (W + 1)) in *;
clearbody pI qW q6 q5; clear - P0 P1 Q1 Q6 Q5 Q13 Hmod E1 E2 E3 Hflt0 Hflt1 Hspr Hfmt Hac HFv HW1 Hci Hcr Hcd Hcdl Hcdr Hidx Hap Hi HWN' HNmax HNMv Hf4 M0 M1 M2 M3 M4 Hfimg0 Hfimg1;
repeat split; lia.
+ unfold kl_conds. cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. subst c1 c2 c3.
split; [|split; [|split; [|exact I]]].
* destruct (i mod W <? W - 1) eqn:E1; [rewrite branch_ltu_U | rewrite branch_geu_U]; rewrite !U_SOff, U31, U12, !Z.add_0_r, !zcanon_id by (unfold M64; lia); rewrite E1; reflexivity.
* destruct (i <? N - W) eqn:E2; [rewrite branch_ltu_U | rewrite branch_geu_U]; rewrite !U_SOff, U14, U7, !Z.add_0_r, !zcanon_id by (unfold M64; lia); rewrite E2; reflexivity.
* destruct (negb (i mod W =? 0)) eqn:E3; [rewrite branch_ne_U | rewrite branch_eq_U]; rewrite U_SOff, U_SLit, U31, Z.add_0_r, !zcanon_id by (unfold M64; lia);
[exact E3 | apply Bool.negb_false_iff in E3; exact E3].
+ unfold kl_alias, kl_cell. cbn [f_alias alias_ok].
assert (P0 : 0 <= fmt * i) by nia. assert (P1 : fmt * (i + W + 1) <= 2 ^ 19) by nia.
assert (AL0 : forall (m : nat) b, bv_unsigned (ew E0 m) = b -> b = flt + 4 * (fmt * i) ->
sv_denot E0 (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SOff 19 0) (SLit 2))) = sv_denot E0 (SOff m 0)).
{ intros m b Hm ->. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U10, U19, Hm, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id (fmt * i)) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id (fmt * i * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
assert (AL : forall (n m : nat) x b, bv_unsigned (ew E0 n) = x -> bv_unsigned (ew E0 m) = b -> 0 <= x <= 2 ^ 19 -> b = flt + 4 * (x + fmt * i) ->
sv_denot E0 (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLL (SAlu ALU_ADD (SOff n 0) (SOff 19 0)) (SLit 2))) = sv_denot E0 (SOff m 0)).
{ intros n m x b Hn Hm Hx ->. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit, U10, U19, Hn, Hm, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id (fmt * i)), (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (x + fmt * i)) by (unfold M64; lia).
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. rewrite (zcanon_id ((x + fmt * i) * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
split; [apply (AL0 32%nat _ U32); reflexivity|].
split; [apply (AL 26%nat 33%nat fmt _ U26 U33); [lia | ring]|].
split; [apply (AL 13%nat 34%nat (fmt * W) _ U13 U34); [nia | ring]|].
split; [apply (AL 6%nat 35%nat (fmt * (W - 1)) _ U6 U35); [nia | ring]|].
split; [apply (AL 5%nat 36%nat (fmt * (W + 1)) _ U5 U36); [nia | ring]|].
split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, U_SLit, U9, U37, U38, !Z.add_0_r.
assert (Hspr : alloc_ceiling <= spv /\ spv + RGBA_FRAME <= 2 ^ 63) by (unfold sp, sp0 in *; lia).
rewrite (zcanon_id (spv + OFF_apal)), (zcanon_id idx), (zcanon_id 3) by (unfold M64; lia). rewrite (zcanon_id (idx * 3)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia. }
pose proof (st_ok_enterF src2segs fy 96 E0 (ss_KLx c1 c2 c3) _ HS0 ltac:(subst c1 c2 c3; destruct (i mod W <? W - 1), (i <? N - W), (negb (i mod W =? 0)); vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 96 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc (ss_KLx c1 c2 c3)) (ss_regs (ss_KLx c1 c2 c3)) (sfr_atoms 96) (ss_mem (ss_KLx c1 c2 c3)) (ss_resv (ss_KLx c1 c2 c3)) (ss_facts (ss_KLx c1 c2 c3))) with (ss_KL c1 c2 c3) in HS.
clear HS0 RW.
rewrite <- !HEE in U9, U10, U19, U26, U13, U6, U5, U31, U12, U14, U7, U30, U37, U38, U32, U33, U34, U35, U36 by lia.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_KL) mem (seg_rom src2segs))) in HJ.
assert (WRw : forall (a : nat) (d : nat) base rs, bv_unsigned (ew E a) = base -> flt <= base -> base + 12 <= flt + 4 * M ->
wr_ok E rs RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) -> wr_ok E (klw a d :: rs) RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros a d base rs Ha Hlo Hhi Hrs. eapply wr_ok_cons_gen; [reflexivity | exact Ha | | exact Hrs].
cbn [klw r_wlo r_whi]. intros x Hx. replace x with (flt + (x - flt)) by lia. apply Hwbf. lia. }
assert (Hwr : wr_ok E (kl_mem c1 c2 c3) RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ unfold kl_mem. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. cbn [app].
apply (WRw 32%nat 0%nat _ _ U32); [lia | lia |].
assert (Wtail : wr_ok E [YQ0b.mkRegion None SRC2_RO9 (SRC2_RO9 + 8) 0 0 [mkChunk SRC2_RO9 (CImg 8)]] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
subst c1 c2 c3. destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3; cbn [andb app];
repeat (first [ apply (WRw 33%nat 1%nat _ _ U33); [specialize (Hcr eq_refl); lia | specialize (Hcr eq_refl); lia |]
| apply (WRw 34%nat 2%nat _ _ U34); [specialize (Hcd eq_refl); lia | specialize (Hcd eq_refl); lia |]
| apply (WRw 35%nat 3%nat _ _ U35); [specialize (Hcdl eq_refl eq_refl); lia | specialize (Hcdl eq_refl eq_refl); lia |]
| apply (WRw 36%nat 4%nat _ _ U36); [specialize (Hcdr eq_refl eq_refl); lia | specialize (Hcdr eq_refl eq_refl); lia |] ]);
exact Wtail. }
assert (POST : forall (ssx : sstate) (msx : machine_state), st_okF src2segs E ssx msx -> ss_resv ssx = None -> ss_pc ssx = PC_IN ->
sr_get (ss_regs ssx) 15%bv = SOff 9%nat 3 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) KL_KEEP = true ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem msx) mdq ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> mbyte src2segs (ms_mem msx) a = mbyte src2segs mem a) ->
KL_post fy regs mem (mkCfg msx mdq)).
{ intros ssx msx HSx Hrv Hpc H15 Hkb HJx Hmb. exists (fp_of msx), (ms_regs msx), (ms_mem msx).
split; [rewrite (st_okF_mkst src2segs E ssx msx HSx Hrv), Hpc; reflexivity|]. split; [exact HJx|]. split; [exact (st_okF_frm src2segs E _ _ HSx)|].
split; [exact (st_okF_regs_kept src2segs E ssx msx _ KL_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb) |].
split; [| exact Hmb]. rewrite (st_okF_reg src2segs E ssx msx 15%bv HSx), H15. cbn [sv_denot]. rewrite U9, G15. reflexivity. }
subst c1 c2 c3.
destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3;
(jrunF_to LAWS src2tbl_ok HS HJ PC_IN; [wr_ok_eval; exact Hwr|]);
cbn [ms_mem mkst] in HF, HJ; apply SR_ret;
(eapply (POST _ _ HS); [reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ |]);
intros a Ha Hna; mb_frames ltac:(exact Ha) ltac:(rewrite ?U32, ?U33, ?U34, ?U35, ?U36; first [lia | specialize (Hcr eq_refl); lia | specialize (Hcd eq_refl); lia | specialize (Hcdl eq_refl eq_refl); lia | specialize (Hcdr eq_refl eq_refl); lia]); reflexivity.
Qed.
Definition lf_lits : list (option Z) := [None; None; None; None; None; None; None; None; None; Some 1].
Definition ss_LF : sstate :=
mkSS PC_LF sr_atoms
[ YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 32 lf_lits);
YQ0b.mkRegion (Some 30%nat) 0 1 0 1 [] ] None
(mkFacts [ (9%nat, mkAF 4096 (CEIL_MAX - NODE_SIZE) 4); (2%nat, mkAF CEIL_MIN (2^63) 4); (30%nat, mkAF 4096 CEIL_MAX 0);
(40%nat, mkAF 0 255 0); (1%nat, mkAF 1 RGB_NMAX 0); (14%nat, mkAF 0 RGB_NMAX 0) ] [] []).
Definition LF_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30]%bv.
Lemma LF_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z) (n : tnode) c0 c1,
0 <= i < N -> In n (tree_leaves t) ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> memI mem ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 9 = Z_to_bv 64 (tn_addr n) -> getr regs 30 = Z_to_bv 64 (fimg + i) ->
getr regs 14 = Z_to_bv 64 i -> getr regs 1 = Z_to_bv 64 W ->
obj_at src2segs mem (tn_addr n) LAY_Node (node_vals c0 c1 n 1) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_LF) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs' mem',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 PC_KL) mem' (seg_rom src2segs)) mdq /\
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ memI mem' /\
getr regs' 9 = Z_to_bv 64 (spv + OFF_apal) /\ getr regs' 19 = getr regs 11 /\ getr regs' 31 = Z_to_bv 64 (i mod W) /\
val_mem src2segs mem' (fimg + i) 1 (tn_cidx n) /\
(forall rr : reg, In rr LF_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i n c0 c1 Hi Hleaf HJ HMI G2 G9 G30 G14 G1 Hobj.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap). pose proof N_ge_W' as HWN'.
assert (Hn_in : In n (tree_nodes t)) by (clear - Hleaf; induction t as [|m|m l IHl rr IHr]; cbn in *; [exact Hleaf | exact Hleaf | right; apply in_app_iff; apply in_app_iff in Hleaf; tauto]).
destruct (Hnodes n Hn_in) as (Hn0 & Hn1 & Hn16). pose proof (Hsep_tf n Hn_in) as Hstf.
assert (Hwfn : tnode_wf n) by (unfold tree_forall in Hwft; exact (proj1 (Forall_forall _ _) Hwft n Hn_in)).
destruct Hwfn as (Hcut & Hcidx & _ & _ & Hlen & _).
set (E := Ereg regs (map (Z_to_bv 64) (node_vals c0 c1 n 1) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (node_vals c0 c1 n 1) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
rewrite (node_vals_expand c0 c1 n 1 Hlen) in Hobj, HV.
assert (A40 : ew E 40 = Z_to_bv 64 (tn_cidx n)) by (apply (HV 8%nat); reflexivity).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (U9 : bv_unsigned (ew E 9) = tn_addr n) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U30 : bv_unsigned (ew E 30) = fimg + i) by (rewrite (HE 30%nat 30%bv eq_refl), G30; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E 14) = i) by (rewrite (HE 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (U1 : bv_unsigned (ew E 1) = W) by (rewrite (HE 1%nat 1%bv eq_refl), G1; apply unsigned_lit_small; lia).
assert (HS : @st_ok src2segs fy E ss_LF (@mkst fy regs (Z_to_bv 64 PC_LF) mem (seg_rom src2segs))).
{ unfold ss_LF. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply (region_ok_obj_gen src2segs _ mem 9 (tn_addr n)); [exact U9 | lia | lia | exact Hobj | reflexivity | exact HV | | intros k Hk; lia].
intros j z Hj. do 9 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|]. destruct j; discriminate Hj.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U30.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (fimg_writable mem HJ); lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U30.
repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U30, U14, U1, A40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold sp, sp0 in *.
assert ((spZ regs0 - RGBA_FRAME) mod 16 = 0) by (rewrite HFv; replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia; rewrite Z.mod_add by lia; exact Hal0).
repeat split; lia. }
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_LF) mem (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ PC_KL.
{ wr_ok_eval. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact U30 | cbn [r_wlo r_whi]; intros a Ha; replace a with (fimg + (a - fimg)) by lia; apply Hwbg; lia | apply wr_ok_nil]. }
cbn [ms_mem mkst] in HF, HJ.
rewrite (st_ok_mkst src2segs E _ _ HS eq_refl). cbn [ss_pc]. apply SR_ret.
lazymatch goal with |- context [mkst (ms_regs ?m) _ (ms_mem _) _] => exists (ms_regs m), (ms_mem m) end.
split; [reflexivity|]. split; [exact HJ|].
split. { eapply memI_trans; [exact HMI|]. intros a Ha H1 H2. mb_frames ltac:(exact Ha) ltac:(rewrite ?U30; lia). reflexivity. }
jreg HS (9%bv:reg) as Q9. jreg HS (19%bv:reg) as Q19. cbn [ms_regs mkst] in Q9, Q19.
split; [rewrite Q9, U2; reflexivity|].
split; [rewrite Q19, (HE 11%nat 11%bv eq_refl); reflexivity|].
split.
{ pose proof (st_ok_reg src2segs E _ _ 31%bv HS) as Q31. eval_sr_get_in Q31. cbn [ms_regs mkst] in Q31. rewrite Q31, denot_lit_U. f_equal.
apply (U_remuw_small E (SOff 14 0) (SOff 1 0) i W); [apply (U_atom E 14 i); [rewrite <- U14; symmetry; apply Z_to_bv_bv_unsigned | lia] | apply (U_atom E 1 W); [rewrite <- U1; symmetry; apply Z_to_bv_bv_unsigned | lia] | lia | lia]. }
split.
{ lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
rewrite <- (Z.add_0_r (fimg + i));
apply (st_chunk_val src2segs E ssf msf 1%nat _ 30%nat 0 1%N (SOff 40 0) (fimg + i) (tn_cidx n) HS eq_refl eq_refl ltac:(cbn; tauto) U30
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A40, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) end. }
exact (regs_kept_of_st_ok _ _ _ _ regs _ LF_KEEP HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)).
Qed.
Definition ss_IN : sstate := mkSS PC_IN sr_atoms [] None
(mkFacts [ (26%nat, mkAF 3 4 0); (11%nat, mkAF 0 (2^20) 0); (29%nat, mkAF 0 (2^20) 0); (17%nat, mkAF 0 (2^20) 0) ] [] []).
Definition IN_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma IN_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal src2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq ->
getr regs 26 = Z_to_bv 64 fmt -> getr regs 17 = Z_to_bv 64 N -> getr regs 29 = Z_to_bv 64 (i + 1) ->
getr regs 11 = Z_to_bv 64 (fmt * i) ->
SR src2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_IN) mem (seg_rom src2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if i + 1 <? N then PC_DIH else PC_DIX)) mem (seg_rom src2segs)) mdq /\
getr regs' 14 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 (fmt * (i + 1)) /\
(forall rr : reg, In rr IN_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i Hi HJ G26 G17 G29 G11.
pose proof di_consts as (HRv & HFv & HNMv & HNSv & Hac & Hap). pose proof N_ge_W' as HWN'.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
set (E := Ereg regs []).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U26 : bv_unsigned (ew E 26) = fmt) by (rewrite (HE 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (U17 : bv_unsigned (ew E 17) = N) by (rewrite (HE 17%nat 17%bv eq_refl), G17; apply unsigned_lit_small; lia).
assert (U29 : bv_unsigned (ew E 29) = i + 1) by (rewrite (HE 29%nat 29%bv eq_refl), G29; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = fmt * i) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; nia).
assert (HS : @st_ok src2segs fy E ss_IN (@mkst fy regs (Z_to_bv 64 PC_IN) mem (seg_rom src2segs))).
{ unfold ss_IN. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U26, U11, U29, U17. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; nia. }
assert (ADD : forall (a : nat) x, bv_unsigned (ew E a) = x -> 0 <= x -> x + fmt < 2 ^ 62 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff 26 0)) = Z_to_bv 64 (x + fmt)).
{ intros a x Ha Hx0 Hx1. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Ha, U26, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id fmt) by (unfold M64; lia). apply zcanon_id. unfold M64; lia. }
assert (ADD' : forall (a : nat) x, bv_unsigned (ew E a) = x -> 0 <= x -> x + fmt < 2 ^ 62 -> sv_denot E (SAlu ALU_ADD (SOff 26 0) (SOff a 0)) = Z_to_bv 64 (x + fmt)).
{ intros a x Ha Hx0 Hx1. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Ha, U26, !Z.add_0_r.
rewrite (zcanon_id x), (zcanon_id fmt) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
pure_to src2tbl_ok HS PC_DIX.
eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms).
assert (POST : forall ss1 regsx pc, @st_ok src2segs fy E ss1 (@mkst fy regsx (Z_to_bv 64 pc) mem (seg_rom src2segs)) ->
ss_regs ss1 = ss_regs (fst (sym_run_toN src2segs src2tbl FUEL PC_DIX ss_IN)) ->
getr regsx 14 = Z_to_bv 64 (i + 1) /\ getr regsx 11 = Z_to_bv 64 (fmt * (i + 1)) /\
(forall rr : reg, In rr IN_KEEP -> getr regsx rr = getr regs rr)).
{ intros ss1 regsx pc HS1 Hr1.
match type of Hr1 with _ = ss_regs (fst ?x) => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in Hr1 end.
assert (RG : forall rr : reg, getr regsx rr = sv_denot E (sr_get (ss_regs ss1) rr)) by (intros rr; exact (st_ok_reg src2segs E ss1 _ rr HS1)).
rewrite Hr1 in RG.
split; [rewrite (RG 14%bv); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, (HE 29%nat 29%bv eq_refl), Z_to_bv_bv_unsigned; exact G29|].
split; [rewrite (RG 11%bv); eval_sr_get; first [rewrite (ADD 11%nat (fmt * i) U11) by nia | rewrite (ADD' 11%nat (fmt * i) U11) by nia]; f_equal; nia|].
exact (regs_kept_of_st_ok _ _ _ _ regs _ IN_KEEP HS1 (env_agree_refl _ _) ltac:(rewrite Hr1; vm_compute; reflexivity)). }
pbranch src2tbl HS.
- rewrite branch_ne_U, !U_SOff, U29, U17, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
destruct (Z_lt_ge_dec (i + 1) N) as [Hlt|Hge]; [| exfalso; destruct (Z.eqb_spec (i + 1) N); [discriminate Hc | lia]].
pure_to src2tbl_ok HS PC_DIH. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
exists regs2. replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia). split; [reflexivity|].
apply (POST _ _ PC_DIH HS). reflexivity.
- rewrite branch_ne_U, !U_SOff, U29, U17, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
destruct (Z_lt_ge_dec (i + 1) N) as [Hlt|Hge]; [exfalso; destruct (Z.eqb_spec (i + 1) N); [lia | discriminate Hc] |].
pure_to src2tbl_ok HS PC_DIX. eapply (SR_msteps src2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
exists regs2. replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia). split; [reflexivity|].
apply (POST _ _ PC_DIX HS). reflexivity.
Qed.
End f.
End e.
End c.
