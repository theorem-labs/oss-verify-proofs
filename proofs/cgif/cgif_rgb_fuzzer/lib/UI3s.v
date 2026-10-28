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
UI3h UI4v UIZm UI4w YP12.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06 YM02 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_DIH : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x10c4).
Definition PC_CL  : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1120).
Definition PC_GA  : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1174).
Definition PC_GR  : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1194).
Definition PC_IN  : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1350).
Definition PC_DIX : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1360).
Lemma val_mem_byte1 : forall segs m a v, mbyte segs m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem segs m a 1 v.
Proof.
intros segs m a v H Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ubs2_rod_bytes : forall a, SRC2_RO_LO <= a < SRC2_RO_HI -> exists b, seg_rom ubs2segs (Z_to_bv 64 a) = Some b.
Proof.
intros a Ha.
assert (HB : forallb (fun j => match seg_rom ubs2segs (Z_to_bv 64 (SRC2_RO_LO + Z.of_nat j)) with Some _ => true | None => false end)
  (seq 0 (Z.to_nat (SRC2_RO_HI - SRC2_RO_LO))) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in HB. specialize (HB (Z.to_nat (a - SRC2_RO_LO))).
rewrite Z2Nat.id in HB by lia. replace (SRC2_RO_LO + (a - SRC2_RO_LO)) with a in HB by lia.
destruct (seg_rom ubs2segs (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
exfalso. assert (X : false = true); [apply HB; apply in_seq; unfold SRC2_RO_LO, SRC2_RO_HI in *; lia | discriminate X].
Qed.
Lemma fregs_kept_of : forall (f f' : bvmap 5 word) (K : list reg), (forall r, In r K -> reg_get f' r = reg_get f r) ->
  forall r, In r K -> reg_get f' r = reg_get f r.
Proof. intros f f' K H. exact H. Qed.
Ltac inK := repeat (first [left; apply bv_eq; reflexivity | right]).
Ltac zc := repeat match goal with |- context [zcanon ?x] =>
  lazymatch x with context [zcanon _] => fail | _ => rewrite (zcanon_id x) by (unfold M64; lia) end end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Lemma ubs2_rod_in_img : forall a, SRC2_RO_LO <= a < SRC2_RO_HI -> in_img ubs2_msyms a.
Proof.
intros a Ha. unfold in_img. split; [vm_compute; discriminate|].
eexists. split; [left; reflexivity|].
lazymatch goal with |- bv_unsigned ?x <= _ < bv_unsigned ?x' + bv_unsigned ?y =>
let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v;
let w := eval vm_compute in (bv_unsigned y) in change (bv_unsigned y) with w end.
unfold SRC2_RO_LO, SRC2_RO_HI in Ha. lia.
Qed.
Lemma block_off_rod : forall Lc Ac memc mdc b sz,
heap_ok MR Lc Ac memc mdc -> In (b, sz) (blocks Lc Ac) -> 0 < sz -> b + sz <= SRC2_RO_LO \/ SRC2_RO_HI <= b.
Proof.
intros Lc Ac memc mdc b sz HH Hin Hsz.
destruct (Z_lt_le_dec SRC2_RO_LO (b + sz)) as [H1|H1]; [|left; lia].
destruct (Z_lt_le_dec b SRC2_RO_HI) as [H2|H2]; [|right; lia].
exfalso. apply blocks_In in Hin as (p & Hp & Hpin).
apply (il_blocks IMG Lc Ac memc mdc p sz (Z.max b SRC2_RO_LO - b) (proj1 HH) Hpin ltac:(lia)).
rewrite Hp. apply ubs2_rod_in_img. unfold SRC2_RO_LO, SRC2_RO_HI in *. lia.
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
Definition memI (m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> ~ (fimg <= a < fimg + N) -> mbyte ubs2segs m a = mbyte ubs2segs memD a.
Lemma memI_trans : forall m m', memI m ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> ~ (fimg <= a < fimg + N) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) -> memI m'.
Proof. intros m m' Hm Hk a Ha H1 H2. rewrite (Hk a Ha H1 H2). apply Hm; assumption. Qed.
Lemma di_consts : RGBA_STK = 24576 /\ 934 <= RGBA_FRAME <= 8192 /\ RGBA_FRAME mod 16 = 0 /\ RGB_NMAX = 10000 /\ NODE_SIZE = 56 /\
  (CEIL_MIN <= alloc_ceiling <= CEIL_MAX).
Proof. repeat match goal with H : _ |- _ => clear H end. pose proof (proj1 alloc_ceiling_val). repeat split; first [reflexivity | unfold RGBA_FRAME; lia | lia]. Qed.
Lemma sp_facts : alloc_ceiling + 16384 <= spv /\ spv + 934 <= 2 ^ 63 /\ spv mod 16 = 0.
Proof.
pose proof di_consts as (HRv & HF1 & HF16 & _ & _ & Hac). unfold sp, sp0 in *.
split; [lia|]. split; [lia|]. rewrite Zminus_mod, Hal0, HF16. reflexivity.
Qed.
Lemma slot_now : forall m off v, memI m -> 0 <= off -> off + 8 <= 160 -> slot regs0 memD off v -> slot regs0 m off v.
Proof.
intros m off v HMI Ho1 Ho2 Hs k Hk. pose proof sp_facts as (S1 & S2 & _). pose proof di_consts as (_ & _ & _ & _ & _ & Hac).
unfold slot, word_mem in Hs |- *. rewrite HMI; [apply Hs; exact Hk | lia | lia | lia].
Qed.
Lemma flt_present : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 4 * M -> exists b, mbyte ubs2segs m (flt + i) = Some b.
Proof.
intros m HJ i Hi. apply mbyte_of_present.
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin Hi)).
Qed.
Lemma flt_writable : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, flt <= a < flt + 4 * M -> writable_at ubs2segs m a.
Proof.
intros m HJ a Ha. replace a with (flt + (a - flt)) by lia. apply (present_writable ubs2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq flt (4 * M) (a - flt) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin ltac:(lia))).
Qed.
Lemma fimg_writable : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall a, fimg <= a < fimg + N -> writable_at ubs2segs m a.
Proof.
intros m HJ a Ha. replace a with (fimg + (a - fimg)) by lia. apply (present_writable ubs2_msyms).
exact (proj1 (heap_blocks _ _ LAWS Lq Aq m mdq fimg N (a - fimg) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hgin ltac:(lia))).
Qed.
Lemma frame_present : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq ->
forall i, 0 <= i < 934 -> exists b, mbyte ubs2segs m (spv + i) = Some b.
Proof.
intros m HJ i Hi. pose proof di_consts as (HRv & HF1 & _ & _ & _ & Hac).
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstw) & _).
apply mbyte_of_present. apply ubs2_writable_high_present; [unfold sp, sp0 in *; lia|].
apply Hstw. unfold sp, sp0 in *. lia.
Qed.
Lemma rodata_now : forall m, journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq m mdq -> ubs2_rgb_rodata_ok m.
Proof.
intros m HJ. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & Hik). exact (ubs2_rgb_rodata_kept mem0 m Hik Hro0).
Qed.
Definition fregs3 (fr : bvmap 5 word) : Prop :=
reg_get fr 8%bv = nan_box (Z_to_bv 32 0) /\ reg_get fr 9%bv = nan_box (Z_to_bv 32 S255) /\ reg_get fr 18%bv = nan_box (Z_to_bv 32 Shi).
Definition lregs (regs : bvmap 5 word) (i : Z) : Prop :=
getr regs 2 = Z_to_bv 64 spv /\ getr regs 23 = Z_to_bv 64 i /\ getr regs 9 = Z_to_bv 64 (fmt * i) /\
getr regs 19 = Z_to_bv 64 (2 ^ 64 - 1 - flt) /\ getr regs 21 = Z_to_bv 64 (W - 1) /\
getr regs 22 = Z_to_bv 64 (fmt * (W - 1)) /\ getr regs 25 = Z_to_bv 64 (fmt * W) /\
getr regs 26 = Z_to_bv 64 (fmt * (W + 1)) /\ getr regs 27 = Z_to_bv 64 (N - W) /\
getr regs 24 = Z_to_bv 64 flt /\ getr regs 18 = Z_to_bv 64 W.
Definition LKEEP : list reg := [2; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma lregs_kept : forall regs regs' i, (forall rr : reg, In rr LKEEP -> getr regs' rr = getr regs rr) -> lregs regs i -> lregs regs' i.
Proof.
intros regs regs' i HK (G2 & G23 & G9 & G19 & G21 & G22 & G25 & G26 & G27 & G24 & G18).
unfold lregs. rewrite !HK by inK. repeat split; assumption.
Qed.
Definition cells_at (m : word -> option byte) (i c0 c1 c2 : Z) : Prop :=
val_mem ubs2segs m (flt + 4 * (fmt * i)) 4 c0 /\ val_mem ubs2segs m (flt + 4 * (fmt * i) + 4) 4 c1 /\
val_mem ubs2segs m (flt + 4 * (fmt * i) + 8) 4 c2 /\
0 <= c0 < 2 ^ 32 /\ 0 <= c1 < 2 ^ 32 /\ 0 <= c2 < 2 ^ 32 /\ s_in c0 0 255 /\ s_in c1 0 255 /\ s_in c2 0 255.
Lemma N_ge_W' : W <= N. Proof. destruct HWN as (h & Hh & HN). subst N. nia. Qed.
Definition gkw (a d : nat) : YQ0b.region := YQ0b.mkRegion (Some a) 0 12 0 12 [mkChunk 0 (CData d 0 12)].
Definition gk_frame : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 160 0 0 [mkChunk 48 (CVal 8 (SOff 34 0)); mkChunk 112 (CVal 8 (SOff 33 0)); mkChunk 120 (CVal 8 (SOff 32 0))].
Definition gk_rod : YQ0b.region := YQ0b.mkRegion None SRC2_RO_LO SRC2_RO_HI 0 0 [mkChunk SRC2_RO_LO (CImg (SRC2_RO_HI - SRC2_RO_LO))].
Definition gk_mem (c1 c2 c3 : bool) : smem :=
[ gk_frame; YQ0b.mkRegion (Some 35%nat) 0 1 0 1 [];
  YQ0b.mkRegion (Some 36%nat) 0 12 0 0 [mkChunk 0 (CVal 4 (SOff 37 0)); mkChunk 4 (CVal 4 (SOff 38 0)); mkChunk 8 (CVal 4 (SOff 39 0))];
  YQ0b.mkRegion (Some 40%nat) 0 3 0 0 [mkChunk 0 (CVal 1 (SOff 41 0)); mkChunk 1 (CVal 1 (SOff 42 0)); mkChunk 2 (CVal 1 (SOff 43 0))] ]
++ (if c1 then [gkw 44 0] else []) ++ (if c2 then [gkw 45 1] else [])
++ (if c2 && c3 then [gkw 46 2] else []) ++ (if c2 && c1 then [gkw 47 3] else []) ++ [gk_rod].
Definition gk_facts (c1 c2 c3 : bool) : list (nat * afact) :=
[ (10%nat, mkAF 0 255 0); (23%nat, mkAF 0 RGB_NMAX 0); (9%nat, mkAF 0 (2 ^ 20) 0); (19%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0);
  (21%nat, mkAF 0 (2 ^ 16) 0); (22%nat, mkAF 0 (2 ^ 20) 0); (25%nat, mkAF 0 (2 ^ 20) 0); (26%nat, mkAF 0 (2 ^ 20) 0);
  (27%nat, mkAF 0 (2 ^ 32 - 1) 0); (24%nat, mkAF 4096 CEIL_MAX 4); (18%nat, mkAF 1 (2 ^ 16) 0); (2%nat, mkAF CEIL_MIN (2 ^ 63) 4);
  (32%nat, mkAF 3 4 0); (33%nat, mkAF (2 ^ 64 - 1 - CEIL_MAX) (2 ^ 64 - 1 - 4096) 0); (34%nat, mkAF 4096 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0);
  (36%nat, mkAF 4096 CEIL_MAX 2); (37%nat, mkAF 0 (2 ^ 32 - 1) 0); (38%nat, mkAF 0 (2 ^ 32 - 1) 0); (39%nat, mkAF 0 (2 ^ 32 - 1) 0);
  (40%nat, mkAF CEIL_MIN (2 ^ 63) 0); (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0) ]
++ (if c1 then [(44%nat, mkAF 4096 CEIL_MAX 2)] else []) ++ (if c2 then [(45%nat, mkAF 4096 CEIL_MAX 2)] else [])
++ (if c2 && c3 then [(46%nat, mkAF 4096 CEIL_MAX 2)] else []) ++ (if c2 && c1 then [(47%nat, mkAF 4096 CEIL_MAX 2)] else []).
Definition GK_REMU : sv := SMdw M_REMU (SOff 23 0) (SOff 18 0).
Definition gk_conds (c1 c2 c3 : bool) : list acond :=
[ mkAC (if c1 then BC_LTU else BC_GEU) GK_REMU (SOff 21 0); mkAC (if c2 then BC_LTU else BC_GEU) (SOff 23 0) (SOff 27 0);
  mkAC (if c3 then BC_NE else BC_EQ) GK_REMU (SLit 0) ].
Definition gk_cell (x : sv) : sv := SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL x (SLit 2)).
Definition gk_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 34 0) (SOff 23 0), SOff 35 0); (gk_cell (SOff 9 0), SOff 36 0);
  (SAlu ALU_ADD (SAlu ALU_ADD (SOff 2 166) (SOff 10 0)) (SAlu ALU_SLL (SOff 10 0) (SLit 1)), SOff 40 0);
  (gk_cell (SAlu ALU_ADD (SOff 32 0) (SOff 9 0)), SOff 44 0); (gk_cell (SAlu ALU_ADD (SOff 25 0) (SOff 9 0)), SOff 45 0);
  (gk_cell (SAlu ALU_ADD (SOff 22 0) (SOff 9 0)), SOff 46 0); (gk_cell (SAlu ALU_ADD (SOff 26 0) (SOff 9 0)), SOff 47 0) ].
Definition ss_GKx (c1 c2 c3 : bool) : sstate := mkSS PC_GR sr_atoms (gk_mem c1 c2 c3) None (mkFacts (gk_facts c1 c2 c3) (gk_conds c1 c2 c3) gk_alias).
Definition GK_KD (k : nat) : sv := KDIFF (37 + k) (41 + k).
Definition GK_KE (k : nat) : sv := KERR (37 + k) (41 + k).
Definition gk_fconds (c1 c2 : bool) (k : nat) : list acond :=
[ mkAC BC_NE (SF2 (FP2_cmp F_LT FMT_S) (SLit SloB) (GK_KD k)) (SLit 0); mkAC BC_NE (SF2 (FP2_cmp F_LT FMT_S) (GK_KD k) (SOff 82 0)) (SLit 0) ] ++
(if c1 then [mkAC BC_EQ (SAluw ALU_SUB (SAlu ALU_SLL (GK_KE k) (SLit 3)) (GK_KE k)) (SAlu ALU_SUB (SAlu ALU_SLL (GK_KE k) (SLit 3)) (GK_KE k))] else []) ++
(if c2 then [mkAC BC_EQ (SAluw ALU_ADD (SAlu ALU_SLL (GK_KE k) (SLit 2)) (GK_KE k)) (SAlu ALU_ADD (SAlu ALU_SLL (GK_KE k) (SLit 2)) (GK_KE k))] else []).
Fixpoint add_conds (ss : sstate) (cs : list acond) : sstate :=
match cs with [] => ss | c :: cs' => add_conds (add_cond ss c) cs' end.
Lemma st_okF_add_conds : forall E ss ms cs, st_okF ubs2segs E ss ms ->
Forall (fun c => branch_taken (ac_c c) (sv_denot E (ac_a c)) (sv_denot E (ac_b c)) = true) cs ->
st_okF ubs2segs E (add_conds ss cs) ms.
Proof.
intros E ss ms cs. revert ss. induction cs as [|[c a b] cs IH]; intros ss HS HF; cbn [add_conds]; [exact HS|].
apply Forall_cons_iff in HF as (Hc & HF'). cbn [ac_c ac_a ac_b] in Hc. apply IH; [apply st_okF_add_cond; [exact HS | exact Hc] | exact HF'].
Qed.
Definition GK_KEEP : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition GK_FKEEP : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition GK_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (i : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 PC_IN) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
(forall rr : reg, In rr GK_KEEP -> getr regs' rr = getr regs rr) /\
(forall rr : reg, In rr GK_FKEEP -> reg_get (@fp_regs fy') rr = reg_get (@fp_regs fy) rr) /\
getr regs' 11 = Z_to_bv 64 (i + 1) /\ getr regs' 7 = Z_to_bv 64 fmt /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> a <> fimg + i -> mbyte ubs2segs mem' a = mbyte ubs2segs mem a).
Lemma GK_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i cidx v0 v1 v2 : Z),
0 <= i < N -> 0 <= cidx < 256 ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) -> memI mem ->
lregs regs i -> getr regs 10 = Z_to_bv 64 cidx -> fregs3 (@fp_regs fy) -> cells_at mem i v0 v1 v2 ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_GR) mem (seg_rom ubs2segs)) mdq) (GK_post fy regs mem i).
Proof.
intros fy regs mem i cidx v0 v1 v2 Hi Hcidx HJ Hfrm HMI HL G10 HF3 HC.
pose proof di_consts as (HRv & HF1 & HF16 & HNMv & HNSv & Hac). pose proof sp_facts as (S1 & S2 & S3). pose proof N_ge_W' as HWN'.
destruct HWN as (hh & Hh1 & HNW).
destruct HL as (G2 & G23 & G9 & G19 & G21 & G22 & G25 & G26 & G27 & G24 & G18).
destruct HF3 as (F8 & F9 & F18).
destruct HC as (V0 & V1 & V2 & R0 & R1 & R2 & I0 & I1 & I2).
assert (Hmod : 0 <= i mod W < W) by (apply Z.mod_pos_bound; lia).
assert (Hs48' := slot_now mem 48 _ HMI ltac:(lia) ltac:(lia) Hs48).
assert (Hs112' := slot_now mem 112 _ HMI ltac:(lia) ltac:(lia) Hs112).
assert (Hs120' := slot_now mem 120 _ HMI ltac:(lia) ltac:(lia) Hs120).
set (c1 := i mod W <? W - 1). set (c2 := i <? N - W). set (c3 := negb (i mod W =? 0)).
assert (Hci : 0 <= 4 * (fmt * i) /\ 4 * (fmt * i) + 12 <= 4 * M) by (unfold M; nia).
assert (Hcr : c1 = true -> 0 <= 4 * (fmt * (i + 1)) /\ 4 * (fmt * (i + 1)) + 12 <= 4 * M).
{ intros Hc. subst c1. apply Z.ltb_lt in Hc. pose proof (fs_right W hh N HW1 HNW i Hi Hc). unfold M; nia. }
assert (Hcd : c2 = true -> 0 <= 4 * (fmt * (i + W)) /\ 4 * (fmt * (i + W)) + 12 <= 4 * M).
{ intros Hc. subst c2. apply Z.ltb_lt in Hc. unfold M; nia. }
assert (Hcdl : c2 = true -> c3 = true -> 0 <= 4 * (fmt * (i + W - 1)) /\ 4 * (fmt * (i + W - 1)) + 12 <= 4 * M).
{ intros Hc Hc'. subst c2 c3. apply Z.ltb_lt in Hc. apply Bool.negb_true_iff in Hc'. apply Z.eqb_neq in Hc'. unfold M; nia. }
assert (Hcdr : c2 = true -> c1 = true -> 0 <= 4 * (fmt * (i + W + 1)) /\ 4 * (fmt * (i + W + 1)) + 12 <= 4 * M).
{ intros Hc Hc'. subst c2 c1. apply Z.ltb_lt in Hc. apply Z.ltb_lt in Hc'. pose proof (fs_down_right W hh N HW1 HNW i Hi Hc Hc'). unfold M; nia. }
assert (PB : forall j, 0 <= j < 3 -> exists p, 0 <= p < 256 /\ val_mem ubs2segs mem (spv + 166 + 3 * cidx + j) 1 p).
{ intros j Hj. destruct (frame_present mem HJ (166 + 3 * cidx + j) ltac:(lia)) as (b & Hb).
  pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
  exists (bv_unsigned b). split; [exact Rb|]. apply val_mem_byte1; [|exact Rb].
  replace (spv + 166 + 3 * cidx + j) with (spv + (166 + 3 * cidx + j)) by lia. rewrite Hb, Z_to_bv_bv_unsigned. reflexivity. }
destruct (PB 0 ltac:(lia)) as (p0 & Rp0 & P0). destruct (PB 1 ltac:(lia)) as (p1 & Rp1 & P1). destruct (PB 2 ltac:(lia)) as (p2 & Rp2 & P2). clear PB.
assert (Xr : exists b1, length b1 = 12%nat /\ (c1 = true -> forall j, (j < 12)%nat -> mbyte ubs2segs mem (flt + 4 * (fmt * (i + 1)) + Z.of_nat j) = nth_error b1 j)).
{ destruct c1; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
  destruct (bytes_of_present ubs2segs mem (flt + 4 * (fmt * (i + 1))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcr eq_refl); lia)) as (b & Lb & Hb).
  exists b. auto. }
destruct Xr as (b1 & Lb1 & Hb1).
assert (Xd : exists b2, length b2 = 12%nat /\ (c2 = true -> forall j, (j < 12)%nat -> mbyte ubs2segs mem (flt + 4 * (fmt * (i + W)) + Z.of_nat j) = nth_error b2 j)).
{ destruct c2; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
  destruct (bytes_of_present ubs2segs mem (flt + 4 * (fmt * (i + W))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcd eq_refl); lia)) as (b & Lb & Hb).
  exists b. auto. }
destruct Xd as (b2 & Lb2 & Hb2).
assert (Xdl : exists b3, length b3 = 12%nat /\ (c2 = true -> c3 = true -> forall j, (j < 12)%nat -> mbyte ubs2segs mem (flt + 4 * (fmt * (i + W - 1)) + Z.of_nat j) = nth_error b3 j)).
{ destruct c2; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
  destruct c3; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros _ HH0; discriminate HH0]].
  destruct (bytes_of_present ubs2segs mem (flt + 4 * (fmt * (i + W - 1))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcdl eq_refl eq_refl); lia)) as (b & Lb & Hb).
  exists b. auto. }
destruct Xdl as (b3 & Lb3 & Hb3).
assert (Xdr : exists b4, length b4 = 12%nat /\ (c2 = true -> c1 = true -> forall j, (j < 12)%nat -> mbyte ubs2segs mem (flt + 4 * (fmt * (i + W + 1)) + Z.of_nat j) = nth_error b4 j)).
{ destruct c2; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros HH0; discriminate HH0]].
  destruct c1; [| exists (repeat (Z_to_bv 8 0) 12); split; [reflexivity | intros _ HH0; discriminate HH0]].
  destruct (bytes_of_present ubs2segs mem (flt + 4 * (fmt * (i + W + 1))) 12 ltac:(intros j Hj; rewrite <- Z.add_assoc; apply (flt_present mem HJ); specialize (Hcdr eq_refl eq_refl); lia)) as (b & Lb & Hb).
  exists b. auto. }
destruct Xdr as (b4 & Lb4 & Hb4).
set (vals := [fmt; 2 ^ 64 - 1 - fimg; fimg; fimg + i; flt + 4 * (fmt * i); v0; v1; v2; spv + 166 + 3 * cidx; p0; p1; p2;
  flt + 4 * (fmt * (i + 1)); flt + 4 * (fmt * (i + W)); flt + 4 * (fmt * (i + W - 1)); flt + 4 * (fmt * (i + W + 1))]).
set (E0 := EregB regs (map (Z_to_bv 64) vals) [b1; b2; b3; b4]).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_EregB_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply EregB_vals; exact Hj).
pose proof (HV 0%nat _ eq_refl) as A32. pose proof (HV 1%nat _ eq_refl) as A33. pose proof (HV 2%nat _ eq_refl) as A34.
pose proof (HV 3%nat _ eq_refl) as A35. pose proof (HV 4%nat _ eq_refl) as A36. pose proof (HV 5%nat _ eq_refl) as A37.
pose proof (HV 6%nat _ eq_refl) as A38. pose proof (HV 7%nat _ eq_refl) as A39. pose proof (HV 8%nat _ eq_refl) as A40.
pose proof (HV 9%nat _ eq_refl) as A41. pose proof (HV 10%nat _ eq_refl) as A42. pose proof (HV 11%nat _ eq_refl) as A43.
pose proof (HV 12%nat _ eq_refl) as A44. pose proof (HV 13%nat _ eq_refl) as A45. pose proof (HV 14%nat _ eq_refl) as A46.
pose proof (HV 15%nat _ eq_refl) as A47.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47.
assert (Hf4 : flt mod 4 = 0) by (pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd; rewrite Hflt16, Z.add_0_r in Hd; rewrite Hd;
  replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia; apply Z_mod_mult).
assert (MD4 : forall x, (flt + 4 * x) mod 4 = 0) by (intros x; replace (flt + 4 * x) with (flt + x * 4) by lia; rewrite Z.mod_add by lia; exact Hf4).
assert (UR : forall (k : nat) (rr : reg) v, Z.of_nat k = bv_unsigned rr -> getr regs rr = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 k) = v).
{ intros k rr v Hk Hr Hv. rewrite (HE0 k rr Hk), Hr. apply unsigned_lit_small. exact Hv. }
assert (UA : forall (k : nat) v, ew E0 k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 k) = v).
{ intros k v Hk Hv. rewrite Hk. apply unsigned_lit_small. exact Hv. }
pose proof (UR 2%nat 2%bv _ eq_refl G2 ltac:(lia)) as U2. pose proof (UR 23%nat 23%bv _ eq_refl G23 ltac:(lia)) as U23.
pose proof (UR 9%nat 9%bv _ eq_refl G9 ltac:(nia)) as U9. pose proof (UR 19%nat 19%bv _ eq_refl G19 ltac:(lia)) as U19.
pose proof (UR 21%nat 21%bv _ eq_refl G21 ltac:(lia)) as U21. pose proof (UR 22%nat 22%bv _ eq_refl G22 ltac:(nia)) as U22.
pose proof (UR 25%nat 25%bv _ eq_refl G25 ltac:(nia)) as U25. pose proof (UR 26%nat 26%bv _ eq_refl G26 ltac:(nia)) as U26.
pose proof (UR 27%nat 27%bv _ eq_refl G27 ltac:(lia)) as U27. pose proof (UR 24%nat 24%bv _ eq_refl G24 ltac:(lia)) as U24.
pose proof (UR 18%nat 18%bv _ eq_refl G18 ltac:(lia)) as U18. pose proof (UR 10%nat 10%bv _ eq_refl G10 ltac:(lia)) as U10.
pose proof (UA 32%nat _ A32 ltac:(lia)) as U32. pose proof (UA 33%nat _ A33 ltac:(lia)) as U33. pose proof (UA 34%nat _ A34 ltac:(lia)) as U34.
pose proof (UA 35%nat _ A35 ltac:(lia)) as U35. pose proof (UA 36%nat _ A36 ltac:(lia)) as U36. pose proof (UA 37%nat _ A37 ltac:(lia)) as U37.
pose proof (UA 38%nat _ A38 ltac:(lia)) as U38. pose proof (UA 39%nat _ A39 ltac:(lia)) as U39. pose proof (UA 40%nat _ A40 ltac:(lia)) as U40.
pose proof (UA 41%nat _ A41 ltac:(lia)) as U41. pose proof (UA 42%nat _ A42 ltac:(lia)) as U42. pose proof (UA 43%nat _ A43 ltac:(lia)) as U43.
pose proof (UA 44%nat _ A44 ltac:(nia)) as U44. pose proof (UA 45%nat _ A45 ltac:(nia)) as U45.
pose proof (UA 46%nat _ A46 ltac:(nia)) as U46. pose proof (UA 47%nat _ A47 ltac:(nia)) as U47.
clear UR UA.
assert (RW : forall (a : nat) (d : nat) base bs, bv_unsigned (ew E0 a) = base -> ed E0 d = bs -> length bs = 12%nat ->
  4096 <= base -> base + 12 <= alloc_ceiling ->
  (forall j, (j < 12)%nat -> mbyte ubs2segs mem (base + Z.of_nat j) = nth_error bs j) ->
  (forall a', base <= a' < base + 12 -> writable_at ubs2segs mem a') ->
  @region_ok ubs2segs E0 mem (gkw a d)).
{ intros a d base bs Ha Hd Hl R0' R1' Hbs Hw. unfold gkw, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite Ha.
  split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
  apply Forall_cons; [|apply Forall_nil]. replace 12 with (Z.of_nat (length bs)) by (rewrite Hl; reflexivity).
  apply (chunk_ok_data ubs2segs E0 mem base 0 d bs Hd). intros j Hj. rewrite Z.add_0_r. apply Hbs. rewrite <- Hl. exact Hj. }
assert (HS0 : @st_ok ubs2segs fy E0 (ss_GKx c1 c2 c3) (@mkst fy regs (Z_to_bv 64 PC_GR) mem (seg_rom ubs2segs))).
{ unfold ss_GKx. apply entry_st_ok_env.
  - subst E0; apply regs_ok_EregB.
  - subst c1 c2 c3. destruct (i mod W <? W - 1), (i <? N - W), (negb (i mod W =? 0)); vm_compute; reflexivity.
  - unfold gk_mem. apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]].
    + constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * unfold gk_frame, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs48'].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs112'].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs120'].
      * unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U35.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply (fimg_writable mem HJ); lia | constructor].
      * unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U36.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V0].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V1].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V2].
      * unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U40.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor; [|constructor]]].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A41, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; replace (spv + 166 + 3 * cidx) with (spv + 166 + 3 * cidx + 0) by lia; exact P0].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A42, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact P1].
        -- eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A43, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact P2].
    + destruct c1 eqn:Ec1; [|constructor]. constructor; [|constructor].
      specialize (Hcr eq_refl). apply (RW 44%nat 0%nat _ b1 U44 ltac:(subst E0; reflexivity) Lb1); [lia | lia | exact (Hb1 eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
    + destruct c2 eqn:Ec2; [|constructor]. constructor; [|constructor].
      specialize (Hcd eq_refl). apply (RW 45%nat 1%nat _ b2 U45 ltac:(subst E0; reflexivity) Lb2); [lia | lia | exact (Hb2 eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
    + destruct c2 eqn:Ec2; [|constructor]. destruct c3 eqn:Ec3; [|constructor]. constructor; [|constructor].
      specialize (Hcdl eq_refl eq_refl). apply (RW 46%nat 2%nat _ b3 U46 ltac:(subst E0; reflexivity) Lb3); [lia | lia | exact (Hb3 eq_refl eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
    + destruct c2 eqn:Ec2; [|constructor]. destruct c1 eqn:Ec1; [|constructor]. constructor; [|constructor].
      specialize (Hcdr eq_refl eq_refl). apply (RW 47%nat 3%nat _ b4 U47 ltac:(subst E0; reflexivity) Lb4); [lia | lia | exact (Hb4 eq_refl eq_refl) | intros a' Ha'; apply (flt_writable mem HJ); lia].
    + constructor; [|constructor].
      unfold gk_rod, region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
      split; [unfold SRC2_RO_LO, SRC2_RO_HI; lia|]. split; [unfold SRC2_RO_LO, SRC2_RO_HI; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [c_off c_val c_len cv_len cbyte] in Hj |- *.
      destruct (ubs2_rod_bytes (SRC2_RO_LO + j) ltac:(lia)) as [b Hb]. exists b. unfold img_byte. rewrite Z.add_0_l.
      split; [exact Hb|]. rewrite (rodata_now mem HJ (SRC2_RO_LO + j)); [exact Hb|]. lia.
  - unfold gk_mem, gk_frame, gk_rod, gkw. subst c1 c2 c3.
    assert (Q1 : fmt <= fmt * W) by nia. assert (P0' : 0 <= fmt * i) by nia.
    assert (Rr1 : fmt * (i + 1) = fmt * i + fmt) by ring. assert (Rr2 : fmt * (i + W) = fmt * i + fmt * W) by ring.
    assert (Rr3 : fmt * (i + W - 1) = fmt * i + fmt * W - fmt) by ring. assert (Rr4 : fmt * (i + W + 1) = fmt * i + fmt * W + fmt) by ring.
    rewrite Rr1 in U44, Hcr. rewrite Rr2 in U45, Hcd. rewrite Rr3 in U46, Hcdl. rewrite Rr4 in U47, Hcdr.
    assert (Hrod : SRC2_RO_HI <= CEIL_MIN) by (unfold SRC2_RO_HI; lia).
    assert (QA : i mod W < W - 1 -> 2 * fmt <= fmt * W) by (intros; nia).
    assert (QB : i mod W <> 0 -> 2 * fmt <= fmt * W) by (intros Hm; assert (W <> 1) by (intros ->; apply Hm; apply Z.mod_1_r); nia).
    assert (QC : i mod W < W - 1 -> i mod W <> 0 -> 3 * fmt <= fmt * W) by (intros; nia).
    set (pI := fmt * i) in *. set (qW := fmt * W) in *.
    destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3;
    cbn [andb app pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [r_base r_lo r_hi base_val];
    rewrite ?U2, ?U35, ?U36, ?U40, ?U44, ?U45, ?U46, ?U47;
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    first [apply Bool.negb_true_iff in E3; apply Z.eqb_neq in E3 | apply Bool.negb_false_iff in E3; apply Z.eqb_eq in E3];
    clearbody pI qW; clear - P0' Q1 QA QB QC Hmod E1 E2 E3 Hflt0 Hflt1 Hfro Hgro S1 S2 Hfmt Hac HW1 Hci Hcr Hcd Hcdl Hcdr Hcidx Hi HWN' Hfimg0 Hfimg1 Hdisj Hrod;
    unfold SRC2_RO_LO, SRC2_RO_HI in *; repeat split; lia.
  - split; [|split].
    + unfold gk_facts. subst c1 c2 c3.
      assert (P0' : 0 <= fmt * i) by nia. assert (P1' : fmt * (i + W + 1) <= 2 ^ 19) by nia. assert (Q1 : fmt <= fmt * W) by nia.
      assert (Rr1 : fmt * (i + 1) = fmt * i + fmt) by ring. assert (Rr2 : fmt * (i + W) = fmt * i + fmt * W) by ring.
      assert (Rr3 : fmt * (i + W - 1) = fmt * i + fmt * W - fmt) by ring. assert (Rr4 : fmt * (i + W + 1) = fmt * i + fmt * W + fmt) by ring.
      rewrite Rr1 in U44, Hcr. rewrite Rr2 in U45, Hcd. rewrite Rr3 in U46, Hcdl. rewrite Rr4 in U47, Hcdr, P1'.
      assert (Q6 : 0 <= fmt * (W - 1) <= 2 ^ 19) by nia. assert (Q5 : 0 <= fmt * (W + 1) <= 2 ^ 19) by nia. assert (Q13 : 0 <= fmt * W <= 2 ^ 19) by nia.
      pose proof (MD4 (fmt * i)) as M0. pose proof (MD4 (fmt * i + fmt)) as M1. pose proof (MD4 (fmt * i + fmt * W)) as M2.
      pose proof (MD4 (fmt * i + fmt * W - fmt)) as M3. pose proof (MD4 (fmt * i + fmt * W + fmt)) as M4.
      assert (Hsp16 : spv mod 16 = 0) by exact S3.
      set (pI := fmt * i) in *. set (qW := fmt * W) in *.
      destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3;
      cbn [andb app f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
      rewrite ?U10, ?U23, ?U9, ?U19, ?U21, ?U22, ?U25, ?U26, ?U27, ?U24, ?U18, ?U2, ?U32, ?U33, ?U34, ?U35, ?U36, ?U37, ?U38, ?U39,
        ?U40, ?U41, ?U42, ?U43, ?U44, ?U45, ?U46, ?U47;
      change (2 ^ 2) with 4; change (2 ^ 4) with 16; change (2 ^ 0) with 1; rewrite !Z.mod_1_r;
      first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
      first [apply Bool.negb_true_iff in E3; apply Z.eqb_neq in E3 | apply Bool.negb_false_iff in E3; apply Z.eqb_eq in E3];
      set (q6 := fmt * (W - 1)) in *; set (q5 := fmt * (W + 1)) in *;
      clearbody pI qW q6 q5; clear - P0' P1' Q1 Q6 Q5 Q13 Hmod E1 E2 E3 Hflt0 Hflt1 Hflt16 S1 S2 Hsp16 Hfmt Hac HW1 Hci Hcr Hcd Hcdl Hcdr Hcidx Hi HWN' HNmax HNMv Hf4 M0 M1 M2 M3 M4 Hfimg0 Hfimg1 R0 R1 R2 Rp0 Rp1 Rp2;
      repeat split; lia.
    + unfold gk_conds, GK_REMU. cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. subst c1 c2 c3.
      assert (UR : U E0 (SMdw M_REMU (SOff 23 0) (SOff 18 0)) = i mod W).
      { apply U_remuw_small; [rewrite U_SOff, Z.add_0_r, U23; apply zcanon_id; unfold M64; lia | rewrite U_SOff, Z.add_0_r, U18; apply zcanon_id; unfold M64; lia | lia | lia]. }
      split; [|split; [|split; [|exact I]]].
      * destruct (i mod W <? W - 1) eqn:E1; [rewrite branch_ltu_U | rewrite branch_geu_U]; rewrite UR, !U_SOff, U21, !Z.add_0_r, !zcanon_id by (unfold M64; lia); rewrite E1; reflexivity.
      * destruct (i <? N - W) eqn:E2; [rewrite branch_ltu_U | rewrite branch_geu_U]; rewrite !U_SOff, U23, U27, !Z.add_0_r, !zcanon_id by (unfold M64; lia); rewrite E2; reflexivity.
      * destruct (negb (i mod W =? 0)) eqn:E3; [rewrite branch_ne_U | rewrite branch_eq_U]; rewrite UR, U_SLit, !zcanon_id by (unfold M64; lia);
        [exact E3 | apply Bool.negb_false_iff in E3; exact E3].
    + unfold gk_alias, gk_cell. cbn [f_alias alias_ok].
      assert (P0' : 0 <= fmt * i) by nia. assert (P1' : fmt * (i + W + 1) <= 2 ^ 19) by nia.
      assert (AL0 : forall (m : nat) b, bv_unsigned (ew E0 m) = b -> b = flt + 4 * (fmt * i) ->
        sv_denot E0 (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SOff 9 0) (SLit 2))) = sv_denot E0 (SOff m 0)).
      { intros m b Hm ->. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U24, U9, Hm, !Z.add_0_r.
        rewrite (zcanon_id flt), (zcanon_id (fmt * i)) by (unfold M64; lia). change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
        change (2 ^ 2) with 4. rewrite (zcanon_id (fmt * i * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
      assert (AL : forall (n m : nat) x b, bv_unsigned (ew E0 n) = x -> bv_unsigned (ew E0 m) = b -> 0 <= x <= 2 ^ 19 -> b = flt + 4 * (x + fmt * i) ->
        sv_denot E0 (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SLL (SAlu ALU_ADD (SOff n 0) (SOff 9 0)) (SLit 2))) = sv_denot E0 (SOff m 0)).
      { intros n m x b Hn Hm Hx ->. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
        rewrite !U_SOff, U_SLit, U24, U9, Hn, Hm, !Z.add_0_r.
        rewrite (zcanon_id flt), (zcanon_id (fmt * i)), (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (x + fmt * i)) by (unfold M64; lia).
        change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia.
        change (2 ^ 2) with 4. rewrite (zcanon_id ((x + fmt * i) * 4)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). lia. }
      split.
      { apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U34, U23, U35, !Z.add_0_r. zc. reflexivity. }
      split; [apply (AL0 36%nat _ U36); reflexivity|].
      split.
      { apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
        rewrite !U_SOff, U_SLit, U2, U10, U40, !Z.add_0_r. rewrite (zcanon_id (spv + 166)), (zcanon_id cidx), (zcanon_id 1) by (unfold M64; lia).
        change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
        zc. lia. }
      split; [apply (AL 32%nat 44%nat fmt _ U32 U44); [lia | ring]|].
      split; [apply (AL 25%nat 45%nat (fmt * W) _ U25 U45); [nia | ring]|].
      split; [apply (AL 22%nat 46%nat (fmt * (W - 1)) _ U22 U46); [nia | ring]|].
      split; [apply (AL 26%nat 47%nat (fmt * (W + 1)) _ U26 U47); [nia | ring]|].
      exact I. }
pose proof (st_ok_enterF ubs2segs fy 64 E0 (ss_GKx c1 c2 c3) _ HS0 ltac:(subst c1 c2 c3; destruct (i mod W <? W - 1), (i <? N - W), (negb (i mod W =? 0)); vm_compute; reflexivity) Hfrm) as HS1.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS1.
clear HS0 RW.
assert (W37 : ew E 37 = Z_to_bv 64 v0) by (rewrite HEE by lia; exact A37). assert (W38 : ew E 38 = Z_to_bv 64 v1) by (rewrite HEE by lia; exact A38).
assert (W39 : ew E 39 = Z_to_bv 64 v2) by (rewrite HEE by lia; exact A39). assert (W41 : ew E 41 = Z_to_bv 64 p0) by (rewrite HEE by lia; exact A41).
assert (W42 : ew E 42 = Z_to_bv 64 p1) by (rewrite HEE by lia; exact A42). assert (W43 : ew E 43 = Z_to_bv 64 p2) by (rewrite HEE by lia; exact A43).
assert (W82 : ew E 82 = nan_box (Z_to_bv 32 Shi)).
{ subst E. exact (eq_trans (ew_fregs_at E0 64 (@fp_regs fy) 18%bv) F18). }
assert (FC : forall (k : nat) c p, ew E (37 + k) = Z_to_bv 64 c -> 0 <= c < 2 ^ 32 -> s_in c 0 255 -> ew E (41 + k) = Z_to_bv 64 p -> 0 <= p < 256 ->
  Forall (fun cd => branch_taken (ac_c cd) (sv_denot E (ac_a cd)) (sv_denot E (ac_b cd)) = true) (gk_fconds c1 c2 k)).
{ intros k c p Hc Rc Hin Hp Rp. unfold gk_fconds, GK_KD, GK_KE.
  destruct (kl_err E (37 + k) (41 + k) c p Hc Rc Hp Rp Hin) as (e & He & HKE).
  apply Forall_app; split; [|apply Forall_app; split].
  - constructor; [|constructor; [|constructor]]; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, U_SLit.
    + rewrite (kl_chk1 E (37 + k) (41 + k) c p Hc Rc Hp Rp Hin). reflexivity.
    + rewrite (kl_chk2 E (37 + k) (41 + k) c p Hc Rc Hp Rp Hin 82 W82). reflexivity.
  - destruct c1; [|constructor]. constructor; [|constructor]. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
    rewrite (sov32_sub3 E _ e HKE ltac:(lia)). apply Z.eqb_refl.
  - destruct c2; [|constructor]. constructor; [|constructor]. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
    rewrite (sov32_add2 E _ e HKE ltac:(lia)). apply Z.eqb_refl. }
pose proof (st_okF_add_conds E _ _ (gk_fconds c1 c2 0 ++ gk_fconds c1 c2 1 ++ gk_fconds c1 c2 2) HS1
  ltac:(apply Forall_app; split; [|apply Forall_app; split];
        [apply (FC 0%nat v0 p0) | apply (FC 1%nat v1 p1) | apply (FC 2%nat v2 p2)]; assumption)) as HS.
clear HS1 FC.
rewrite <- !HEE in U2, U23, U9, U19, U21, U22, U25, U26, U27, U24, U18, U10, U32, U33, U34, U35, U36, U37, U38, U39, U40, U41, U42, U43, U44, U45, U46, U47 by lia.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_GR) mem (seg_rom ubs2segs))) in HJ.
assert (WRw : forall (a : nat) (d : nat) base rs, bv_unsigned (ew E a) = base -> flt <= base -> base + 12 <= flt + 4 * M ->
  wr_ok E rs RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) -> wr_ok E (gkw a d :: rs) RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros a d base rs Ha Hlo Hhi Hrs. eapply wr_ok_cons_gen; [reflexivity | exact Ha | | exact Hrs].
  cbn [gkw r_wlo r_whi]. intros x Hx. replace x with (flt + (x - flt)) by lia. apply Hwbf. lia. }
assert (Hwr : wr_ok E (gk_mem c1 c2 c3) RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ unfold gk_mem. apply wr_ok_cons_ro; [cbn; lia|].
  eapply wr_ok_cons_gen; [reflexivity | exact U35 | cbn [r_wlo r_whi]; intros x Hx; replace x with (fimg + i) by lia; apply Hwbg; lia |].
  apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. cbn [app].
  assert (Wtail : wr_ok E [gk_rod] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)) by (apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil]).
  subst c1 c2 c3. destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3; cbn [andb app];
  repeat (first [ apply (WRw 44%nat 0%nat _ _ U44); [specialize (Hcr eq_refl); lia | specialize (Hcr eq_refl); lia |]
                | apply (WRw 45%nat 1%nat _ _ U45); [specialize (Hcd eq_refl); lia | specialize (Hcd eq_refl); lia |]
                | apply (WRw 46%nat 2%nat _ _ U46); [specialize (Hcdl eq_refl eq_refl); lia | specialize (Hcdl eq_refl eq_refl); lia |]
                | apply (WRw 47%nat 3%nat _ _ U47); [specialize (Hcdr eq_refl eq_refl); lia | specialize (Hcdr eq_refl eq_refl); lia |] ]);
  exact Wtail. }
assert (POST : forall (ssx : sstate) (msx : machine_state), st_okF ubs2segs E ssx msx -> ss_resv ssx = None -> ss_pc ssx = PC_IN ->
  forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ssx) rr) (SOff (ridx rr) 0)) GK_KEEP = true ->
  sr_get (ss_regs ssx) 11%bv = SOff 23%nat 1 -> sr_get (ss_regs ssx) 7%bv = SOff 32%nat 0 ->
  (forall rr : reg, In rr GK_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr) ->
  journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem msx) mdq ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (flt <= a < flt + 4 * M) -> a <> fimg + i -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem a) ->
  GK_post fy regs mem i (mkCfg msx mdq)).
{ intros ssx msx HSx Hrv Hpc Hkb Q11 Q7 HFK HJx Hmb. exists (fp_of msx), (ms_regs msx), (ms_mem msx).
  split; [rewrite (st_okF_mkst ubs2segs E ssx msx HSx Hrv), Hpc; reflexivity|]. split; [exact HJx|]. split; [exact (st_okF_frm ubs2segs E _ _ HSx)|].
  split; [exact (st_okF_regs_kept ubs2segs E ssx msx _ GK_KEEP HSx ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) Hkb)|].
  split; [exact HFK|].
  split; [rewrite (st_okF_reg ubs2segs E ssx msx 11%bv HSx), Q11; cbn [sv_denot]; rewrite U23; reflexivity|].
  split; [rewrite (st_okF_reg ubs2segs E ssx msx 7%bv HSx), Q7; cbn [sv_denot]; rewrite Z.add_0_r, HEE, A32, Z_to_bv_bv_unsigned by lia; reflexivity|].
  exact Hmb. }
subst c1 c2 c3.
destruct (i mod W <? W - 1) eqn:E1; destruct (i <? N - W) eqn:E2; destruct (negb (i mod W =? 0)) eqn:E3;
(jrunF_to LAWS ubs2tbl_ok HS HJ PC_IN; [wr_ok_eval; exact Hwr|]);
cbn [ms_mem mkst] in HF, HJ; apply SR_ret;
lazymatch type of HS with st_okF _ _ ?ssx ?msx =>
  assert (HFK : forall rr : reg, In rr GK_FKEEP -> reg_get (ms_fregs msx) rr = reg_get (@fp_regs fy) rr)
    by (apply (st_okF_fregs_kept ubs2segs E ssx msx 64 (@fp_regs fy) GK_FKEEP HS);
        [intros rr; subst E; apply ew_fregs_at | vm_compute; reflexivity]) end;
(eapply (POST _ _ HS); [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | exact HFK | exact HJ |]);
intros a Ha Hna Hnb; mb_frames ltac:(exact Ha) ltac:(rewrite ?U35, ?U44, ?U45, ?U46, ?U47; first [lia | specialize (Hcr eq_refl); lia | specialize (Hcd eq_refl); lia | specialize (Hcdl eq_refl eq_refl); lia | specialize (Hcdr eq_refl eq_refl); lia]); reflexivity.
Qed.
Definition ss_IN : sstate := mkSS PC_IN sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 160 0 0 [mkChunk 104 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (7%nat, mkAF 3 4 0); (9%nat, mkAF 0 (2 ^ 20) 0); (11%nat, mkAF 0 (2 ^ 20) 0); (32%nat, mkAF 0 (2 ^ 20) 0); (2%nat, mkAF CEIL_MIN (2 ^ 63) 4) ] [] []).
Definition IN_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma IN_run : forall (fy : FPState) (regs : bvmap 5 word) mem (i : Z),
0 <= i < N ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> memI mem ->
getr regs 2 = Z_to_bv 64 spv -> getr regs 7 = Z_to_bv 64 fmt -> getr regs 11 = Z_to_bv 64 (i + 1) ->
getr regs 9 = Z_to_bv 64 (fmt * i) ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_IN) mem (seg_rom ubs2segs)) mdq)
(fun c' => exists regs',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 (if i + 1 <? N then PC_DIH else PC_DIX)) mem (seg_rom ubs2segs)) mdq /\
getr regs' 23 = Z_to_bv 64 (i + 1) /\ getr regs' 9 = Z_to_bv 64 (fmt * (i + 1)) /\
(forall rr : reg, In rr IN_KEEP -> getr regs' rr = getr regs rr)).
Proof.
intros fy regs mem i Hi HJ HMI G2 G7 G11 G9.
pose proof di_consts as (HRv & HF1 & HF16 & HNMv & HNSv & Hac). pose proof sp_facts as (S1 & S2 & S3).
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
assert (Hs104' := slot_now mem 104 _ HMI ltac:(lia) ltac:(lia) Hs104).
set (E := Ereg regs [Z_to_bv 64 N]).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (A32 : ew E 32 = Z_to_bv 64 N) by (subst E; apply (Ereg_vals regs [N] [] 0%nat); reflexivity).
assert (U7 : bv_unsigned (ew E 7) = fmt) by (rewrite (HE 7%nat 7%bv eq_refl), G7; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = fmt * i) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; nia).
assert (U11 : bv_unsigned (ew E 11) = i + 1) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = N) by (rewrite A32; apply unsigned_lit_small; lia).
assert (HS : @st_ok ubs2segs fy E ss_IN (@mkst fy regs (Z_to_bv 64 PC_IN) mem (seg_rom ubs2segs))).
{ unfold ss_IN. subst E. apply entry_st_ok_gen.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact Hs104'].
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U7, U9, U11, U32, U2. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
    repeat split; try lia; nia. }
assert (ADD : forall (a b : nat) x y, bv_unsigned (ew E a) = x -> bv_unsigned (ew E b) = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y)).
{ intros a b x y Ha Hb Hx0 Hy0 Hxy. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Ha, Hb, !Z.add_0_r.
  rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia). apply zcanon_id. unfold M64; lia. }
pure_to ubs2tbl_ok HS PC_DIX.
eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms).
assert (POST : forall ss1 regsx pc, @st_ok ubs2segs fy E ss1 (@mkst fy regsx (Z_to_bv 64 pc) mem (seg_rom ubs2segs)) ->
  ss_regs ss1 = ss_regs (fst (sym_run_toN ubs2segs ubs2tbl FUEL PC_DIX ss_IN)) ->
  getr regsx 23 = Z_to_bv 64 (i + 1) /\ getr regsx 9 = Z_to_bv 64 (fmt * (i + 1)) /\
  (forall rr : reg, In rr IN_KEEP -> getr regsx rr = getr regs rr)).
{ intros ss1 regsx pc HS1 Hr1.
  match type of Hr1 with _ = ss_regs (fst ?x) => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in Hr1 end.
  assert (RG : forall rr : reg, getr regsx rr = sv_denot E (sr_get (ss_regs ss1) rr)) by (intros rr; exact (st_ok_reg ubs2segs E ss1 _ rr HS1)).
  rewrite Hr1 in RG.
  split; [rewrite (RG 23%bv); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, (HE 11%nat 11%bv eq_refl), Z_to_bv_bv_unsigned; exact G11|].
  split; [rewrite (RG 9%bv); eval_sr_get; first [rewrite (ADD 9%nat 7%nat _ _ U9 U7) by nia | rewrite (ADD 7%nat 9%nat _ _ U7 U9) by nia]; f_equal; nia|].
  exact (regs_kept_of_st_ok _ _ _ _ regs _ IN_KEEP HS1 (env_agree_refl _ _) ltac:(rewrite Hr1; vm_compute; reflexivity)). }
pbranch ubs2tbl HS.
- rewrite branch_ne_U, !U_SOff, U11, U32, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
  destruct (Z_lt_ge_dec (i + 1) N) as [Hlt|Hge]; [| exfalso; destruct (Z.eqb_spec (i + 1) N); [discriminate Hc | lia]].
  pure_to ubs2tbl_ok HS PC_DIH. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
  exists regs2. replace (i + 1 <? N) with true by (symmetry; apply Z.ltb_lt; lia). split; [reflexivity|].
  apply (POST _ _ PC_DIH HS). reflexivity.
- rewrite branch_ne_U, !U_SOff, U11, U32, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
  destruct (Z_lt_ge_dec (i + 1) N) as [Hlt|Hge]; [exfalso; destruct (Z.eqb_spec (i + 1) N); [lia | discriminate Hc] |].
  pure_to ubs2tbl_ok HS PC_DIX. eapply (SR_msteps ubs2segs _ _ mdq _ Hh Hlz Hms0). apply SR_ret.
  exists regs2. replace (i + 1 <? N) with false by (symmetry; apply Z.ltb_ge; lia). split; [reflexivity|].
  apply (POST _ _ PC_DIX HS). reflexivity.
Qed.
End f.
End e.
End c.
