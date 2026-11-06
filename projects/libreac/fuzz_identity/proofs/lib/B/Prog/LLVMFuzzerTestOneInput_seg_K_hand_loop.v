(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* k_loop of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): +0x19f8 .. +0x1ad8 =
   fuzz_identity.asan-ubsan 0x8216c .. 0x8224c, over the frozen statement of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_stmt.v. 0x8216c..0x82198 sets the token loop up: the shadow
   base from mf+168, the abort test of the second strcmp at 0x82170 (not taken, a0 = 0), i = j = 0 and the
   dash flag 0, s2 = &count = SF+720 from mf+64, a0 = t0 = nm from mf+152, a6 = ~nm and a5 = ~tk for the
   UBSan pointer tests, a7 = '-'. The loop 0x8219c..0x82204 reads nm[i] through its ASan load1
   (0x8219c..0x821a8, slow block 0x82210), drops the first '-' (0x821b0, 0x821bc, 0x82208), and otherwise
   compares tk[j] - its own load1 0x821c8..0x821d4, slow block 0x8221c - with the lower-cased nm[i]
   (0x821d8..0x821ec). The UBSan pointer tests 0x821c0 and 0x82200 are decided by the atom ranges, and the
   branches into the aborts at 0x82610 / 0x82614 are refuted by the plain model. At the NUL (0x821b4) the
   walk leaves the loop, checks tk[j] = 0 (0x8222c..0x82248) and reaches +0x1ad8 with s2 = &count.
   The loop runs by induction on n_ln - i with the invariant of SEGMENTS.md lane 6: j = i - dropped(firstn i
   n_EXP_NM) and tk[j] = TOK(n_EXP_NM)[j]. No instruction of the span writes memory, so the journal and every
   byte of the cut state are carried through each run's frame. kl_low_U is the proof of
   lib/A/Prog/reac_box_name_L3.v's rl3_lower; the ~nm and ~tk words use YI08.U_not. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the listing's lower-casing 0x821d8..0x821e8 (the proof of lib/A/Prog/reac_box_name_L3.v rl3_lower) ---- *)
Lemma kl_low_U : forall E (n : nat) c, ew E n = Z_to_bv 64 c -> 0 <= c < 256 ->
  U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff n (-65)) (SLit 26)) (SLit 5)))
  = KModel.lw c.
Proof.
intros E n c Hn Hc.
assert (H0 : U E (SOff n 0) = c) by (apply (U_atom E n c Hn); lia).
assert (Hm : U E (SOff n (-65)) = (c - 65) mod M64)
  by (rewrite U_SOff, Hn, unsigned_lit_small by lia; reflexivity).
rewrite U_SAlu, H0. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hm, !U_SLit.
change (zcanon 26) with 26. change (zcanon 5) with 5. change (Z.land 5 63) with 5.
unfold KModel.lw.
destruct (Z.leb_spec 65 c) as [H1|H1]; destruct (Z.leb_spec c 90) as [H2|H2]; cbn [andb].
- rewrite (Z.mod_small (c - 65)) by (unfold M64; lia).
  replace (c - 65 <? 26) with true by (symmetry; apply Z.ltb_lt; lia).
  change (zcanon 1) with 1. change (Z.shiftl 1 5) with 32.
  change (zcanon 32) with 32. apply zcanon_id. unfold M64. lia.
- rewrite (Z.mod_small (c - 65)) by (unfold M64; lia).
  replace (c - 65 <? 26) with false by (symmetry; apply Z.ltb_ge; lia).
  change (zcanon 0) with 0. change (Z.shiftl 0 5) with 0.
  change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
- replace ((c - 65) mod M64) with (c - 65 + M64)
    by (rewrite <- (Z_mod_plus_full (c - 65) 1 M64); rewrite Z.mod_small; unfold M64; lia).
  replace (c - 65 + M64 <? 26) with false by (symmetry; apply Z.ltb_ge; unfold M64; lia).
  change (zcanon 0) with 0. change (Z.shiftl 0 5) with 0.
  change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
Qed.

(* ---- the model: a longer prefix drops at least as much ---- *)
Lemma kl_dropped_mono : forall l q q', (q <= q')%nat -> KModel.dropped l q <= KModel.dropped l q'.
Proof.
intros l q q' Hq. unfold KModel.dropped.
destruct (SlotModel.has_dash (firstn q l)) eqn:E1; [|destruct (SlotModel.has_dash (firstn q' l)); lia].
replace (SlotModel.has_dash (firstn q' l)) with true; [lia|].
symmetry. rewrite <- (firstn_skipn q (firstn q' l)), KModel.has_dash_app.
rewrite firstn_firstn, Nat.min_l by exact Hq. rewrite E1. reflexivity.
Qed.
Lemma kl_bytes_nth : forall (bs : list byte) q, (q < length bs)%nat ->
  nth q (map (fun b : byte => bv_unsigned b) bs) 0 = RcIdentModel.bz (RcIdentModel.nthb bs q).
Proof.
intros bs q Hq. unfold RcIdentModel.nthb, RcIdentModel.bz.
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; exact Hq).
rewrite (map_nth (fun b : byte => bv_unsigned b)). reflexivity.
Qed.

(* ---- the symbolic states ---- *)
Definition kl_PTR : afact := mkAF 4096 140737479966720 0.
Definition kl_NEG : afact := mkAF 18446603336221196288 18446744073709551615 0.
Definition kl_Bx : sv := SLit SB.
Definition kl_Bsp0 : Z * Z := (0, 0).
Definition kl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* +0x19f8: the three machine-frame words the stretch reads (mf+64 = SF, mf+152 = nm, mf+168 = the shadow
   base); a0 = 0 is pinned, so the abort test at 0x82170 is decided. *)
Definition kl_rs0 : smem :=
  [ YP09.mkRegion (Some 9%nat) 64 176 0 0
      [YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 152 (CVal 8 (SOff 33 0));
       YP09.mkChunk 168 (CVal 8 (SLit SB))] ].
Definition kl_G0 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (32%nat, kl_PTR); (33%nat, kl_PTR)] [] [].
Definition kl_ss0 : sstate := mkSS 6648 sr_atoms kl_rs0 None kl_G0.
(* +0x1a28, the loop head: atom 32 = tk + j (the alias of s5 + a2), 33 = nm[i], 34 = tk[j]. *)
Definition kl_rsL : smem :=
  [ YP09.mkRegion (Some 5%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
    YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition kl_GL : facts :=
  mkFacts [(5%nat, kl_PTR); (10%nat, kl_PTR); (12%nat, mkAF 0 39 0); (13%nat, mkAF 0 39 0);
           (14%nat, mkAF 0 1 0); (15%nat, kl_NEG); (16%nat, kl_NEG); (17%nat, mkAF 45 45 0);
           (21%nat, kl_PTR); (32%nat, kl_PTR); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)]
          []
          [(SAlu ALU_ADD (SOff 21 0) (SOff 12 0), SOff 32 0)].
Definition kl_ssL : sstate := mkSS 6696 sr_atoms kl_rsL None kl_GL.
Definition kl_SHL : list shent := [mkSHE 10 0 1; mkSHE 32 0 1].
Definition kl_LOW : sv :=
  SAlu ALU_ADD (SOff 33 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 33 (-65)) (SLit 26)) (SLit 5)).

(* every region of both states is read-only *)
Ltac kl_awr_ro :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
(* no region has a write window, so a run keeps every byte *)
Ltac kl_win :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros b wlo whi x Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hr; exfalso; clear - Hr; lia | ]);
  destruct Hin.
Ltac kl_ew Ei := first [ exact Ei | cbn [ew ewset extK havoc Nat.eqb Nat.ltb Nat.leb nth]; exact Ei ].
Ltac kl_in := repeat first [left; reflexivity | right].
Ltac kl_prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Lemma kl_reg_off : forall (E : env) (r : bvmap 5 word) (rr : bv 5) (n : nat) (c v : Z),
  getr r rr = sv_denot E (SOff n c) -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  getr r rr = w64 (v + c).
Proof.
intros E r rr n c v Hr Hn Hv Hc. rewrite Hr, denot_lit_U, (U_atom_off E n v c Hn Hv Hc). reflexivity.
Qed.
Lemma kl_reg_lit : forall (E : env) (r : bvmap 5 word) (rr : bv 5) (z : Z),
  getr r rr = sv_denot E (SLit z) -> 0 <= z < 2 ^ 64 -> getr r rr = w64 z.
Proof.
intros E r rr z Hr Hz. rewrite Hr, denot_lit_U, U_SLit. unfold w64. f_equal.
apply zcanon_id. unfold M64. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).
Hypothesis HPRE : KPREn.
Let LAWS := k_laws B RLO RHI LLVMF_STK arodata_okS G HPRE.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.

Lemma kl_geom :
  alloc_ceiling + 8192 <= mf - 8208 /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\
  e_sp0 g mod 16 = 0 /\ e_sp0 g - 336 <= mf /\ mf mod 32 = 0 /\ e_sp0 g - LLVMF_STK <= mf - 8208 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  frame_addr ly2 4 pos = SFa g pos /\
  shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8 /\ 0 <= shadow_addr (SFa g pos) /\
  shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\ In (4, pos) (frames S2).
Proof. eapply k_geom; [exact HPRE | exact HKH]. Qed.

Lemma kl_vm_hi : forall mem a n v, kkeep B g pos mf ly2 S2 W2 mem2 mem -> mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem) a n v.
Proof. intros mem a n v H1 H2 H3 H4. eapply k_vm_hi; eassumption. Qed.
Lemma kl_vm_blk : forall mem b n0 off n v, kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  In (b, n0) (ablocks B ly2 S2) -> 0 <= off -> off + Z.of_nat n <= req_size n0 ->
  val_mem SEGS (rd W2 mem2) (b + off) n v -> val_mem SEGS (rd W2 mem) (b + off) n v.
Proof. intros mem b n0 off n v H1 H2 H3 H4 H5. eapply k_vm_blk; eassumption. Qed.

(* ---- the plain model of the two strings ---- *)
#[local] Notation INP := (e_pl g).
Definition kl_nmb (i : Z) : Z :=
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.n_EXP_NM INP ++ [RcIdentModel.zb 0]) (Z.to_nat i)).
Definition kl_tkb (j : Z) : Z :=
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.n_TK INP ++ [RcIdentModel.zb 0]) (Z.to_nat j)).
Definition kl_d (i : Z) : Z := KModel.dropped (SlotModel.n_EXP_NM INP) (Z.to_nat i).
Definition kl_j (i : Z) : Z := i - kl_d i.

Lemma kl_model :
  SlotModel.n_ln INP < SlotModel.t_cap_name INP /\ SlotModel.t_cap_name INP <= 39 /\
  SlotModel.n_lt INP < SlotModel.t_cap_tok INP /\ SlotModel.t_cap_tok INP <= 39 /\
  0 <= SlotModel.n_ln INP /\ 0 <= SlotModel.n_lt INP /\
  Z.of_nat (length (SlotModel.n_EXP_NM INP)) = SlotModel.n_ln INP /\
  Z.of_nat (length (SlotModel.n_TK INP)) = SlotModel.n_lt INP /\
  KModel.nzb (SlotModel.n_EXP_NM INP) = true /\
  bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM INP ++ [RcIdentModel.zb 0]) /\
  bytes_at8 W2 mem2 tk (SlotModel.n_TK INP ++ [RcIdentModel.zb 0]) /\
  In (nm, Z.max (SlotModel.t_cap_name INP) 1) (ablocks B ly2 S2) /\
  In (tk, Z.max (SlotModel.t_cap_tok INP) 1) (ablocks B ly2 S2) /\
  zdisjoint (nm, req_size (Z.max (SlotModel.t_cap_name INP) 1))
            (tk, req_size (Z.max (SlotModel.t_cap_tok INP) 1)).
Proof.
pose proof HKH as (HJ2 & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & Hb0 & Hr0).
destruct (KModel.n_r0 INP Hr0) as [Hwok Hfits].
destruct (KModel.fits_unfold INP Hfits) as (F1 & F2 & _).
destruct (Hb0 Hr0) as (Hbnm & Hbtk & _).
destruct HHB as [Hperm _].
assert (Hinnm : In (nm, Z.max (SlotModel.t_cap_name INP) 1) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hintk : In (tk, Z.max (SlotModel.t_cap_tok INP) 1) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); right; left; reflexivity).
pose proof (KModel.tk_len INP) as Htk.
pose proof (Z.mod_pos_bound (SlotModel.tb INP 5) 40 ltac:(lia)) as M5.
pose proof (Z.mod_pos_bound (SlotModel.tb INP 6) 40 ltac:(lia)) as M6.
assert (Hln : 0 <= SlotModel.n_ln INP) by (unfold SlotModel.n_ln; lia).
split; [exact F1|]. split; [unfold SlotModel.t_cap_name; lia|].
split; [exact F2|]. split; [unfold SlotModel.t_cap_tok; lia|].
split; [exact Hln|]. split; [lia|].
split; [reflexivity|]. split; [exact Htk|].
split; [exact (KModel.nzb_EXP_NM INP Hwok)|].
split; [exact Hbnm|]. split; [exact Hbtk|]. split; [exact Hinnm|]. split; [exact Hintk|].
exact (sep_blocks_perm SEGS B LAWS ly2 S2 W2 mem2 md2
  (nm, Z.max (SlotModel.t_cap_name INP) 1) (tk, Z.max (SlotModel.t_cap_tok INP) 1)
  ([(dp, Z.max (SlotModel.t_cap_disp INP) 1)] ++ ablocks B (e_ly g) (e_S g)) (proj1 HJ2) Hperm).
Qed.
Lemma kl_bytes : forall mem a c (bs : list byte) (q : nat),
  kkeep B g pos mf ly2 S2 W2 mem2 mem -> In (a, c) (ablocks B ly2 S2) ->
  bytes_at8 W2 mem2 a bs -> (q < length bs)%nat -> Z.of_nat (length bs) <= req_size c ->
  val_mem SEGS (rd W2 mem) (a + Z.of_nat q) 1 (RcIdentModel.bz (RcIdentModel.nthb bs q)).
Proof.
intros mem a c bs q HKP Hin Hb Hq Hlen.
destruct (Hb q ltac:(rewrite length_map; exact Hq)) as [Hv _].
rewrite (kl_bytes_nth bs q Hq) in Hv.
exact (kl_vm_blk mem a c (Z.of_nat q) 1 _ HKP Hin ltac:(lia) ltac:(change (Z.of_nat 1) with 1; lia) Hv).
Qed.
Lemma kl_ra_blk : forall mem md a c (off : Z),
  AR SEGS B ly2 S2 W2 mem md -> In (a, c) (ablocks B ly2 S2) -> 0 <= off -> off + 1 <= req_size c ->
  range_addressable (aview SEGS (w_H W2) mem) SHADOW_OFF (a + off) 1 /\
  (forall x, a + off <= x < a + off + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
Proof.
intros mem md a c off HAR Hin H0 H1.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem md a c HAR Hin) as (_ & H4096 & Hceil & Happ & _).
split.
- exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem md a c (a + off) 1 HAR Hin
    ltac:(lia) ltac:(lia)).
- unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF.
  intros x Hx. lia.
Qed.

(* ---- the loop's model step ---- *)
Lemma kl_j_le : forall i, 0 <= i <= SlotModel.n_ln INP -> 0 <= kl_j i <= SlotModel.n_lt INP.
Proof.
intros i Hi. unfold kl_j, kl_d.
pose proof (KModel.dropped_range (SlotModel.n_EXP_NM INP) (Z.to_nat i)) as Hr.
pose proof (KModel.dropped_le (SlotModel.n_EXP_NM INP) (Z.to_nat i)) as Hle.
pose proof (KModel.dropped_range (SlotModel.n_EXP_NM INP) (length (SlotModel.n_EXP_NM INP))) as Hrn.
pose proof (KModel.tok_len_full (SlotModel.n_EXP_NM INP)) as Hfull.
pose proof kl_model as (_ & _ & _ & _ & Hln0 & Hlt0 & Hlen & Hlent & _).
pose proof (kl_dropped_mono (SlotModel.n_EXP_NM INP) (Z.to_nat i)
  (length (SlotModel.n_EXP_NM INP)) ltac:(lia)) as Hmono.
rewrite Z2Nat.id in Hle by lia.
unfold SlotModel.n_TK in Hlent.
destruct (Z.eq_dec i (SlotModel.n_ln INP)) as [->|Hne].
- replace (Z.to_nat (SlotModel.n_ln INP)) with (length (SlotModel.n_EXP_NM INP)) by lia. lia.
- lia.
Qed.
Lemma kl_d_range : forall i, 0 <= kl_d i <= 1.
Proof. intro i. apply KModel.dropped_range. Qed.
Lemma kl_nmb_range : forall i, 0 <= kl_nmb i < 256.
Proof. intro i. apply SlotModel.bz_range. Qed.
Lemma kl_tkb_range : forall j, 0 <= kl_tkb j < 256.
Proof. intro j. apply SlotModel.bz_range. Qed.
Lemma kl_nmb_in : forall i, 0 <= i < SlotModel.n_ln INP ->
  kl_nmb i = RcIdentModel.bz (RcIdentModel.nthb (SlotModel.n_EXP_NM INP) (Z.to_nat i)).
Proof.
intros i Hi. pose proof kl_model as (_ & _ & _ & _ & _ & _ & Hlen & _).
unfold kl_nmb, RcIdentModel.nthb. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma kl_nz : forall i, 0 <= i < SlotModel.n_ln INP -> kl_nmb i <> 0.
Proof.
intros i Hi. pose proof kl_model as (_ & _ & _ & _ & _ & _ & Hlen & _ & Hnz & _).
rewrite (kl_nmb_in i Hi). exact (KModel.nzb_nth _ (Z.to_nat i) Hnz ltac:(lia)).
Qed.
Lemma kl_end : kl_nmb (SlotModel.n_ln INP) = 0 /\ kl_j (SlotModel.n_ln INP) = SlotModel.n_lt INP /\
  kl_tkb (SlotModel.n_lt INP) = 0.
Proof.
pose proof kl_model as (_ & _ & _ & _ & Hln0 & Hlt0 & Hlen & Hlent & _).
pose proof (KModel.tok_len_full (SlotModel.n_EXP_NM INP)) as Hfull.
unfold kl_nmb, kl_tkb, kl_j, kl_d, RcIdentModel.nthb, SlotModel.n_TK in *.
assert (En : Z.to_nat (SlotModel.n_ln INP) = length (SlotModel.n_EXP_NM INP)) by lia.
assert (Et : Z.to_nat (SlotModel.n_lt INP) = length (SlotModel.TOK (SlotModel.n_EXP_NM INP))) by lia.
split; [|split].
- rewrite En, app_nth2, Nat.sub_diag by lia. reflexivity.
- rewrite En. lia.
- rewrite Et, app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma kl_tok : forall i, 0 <= i < SlotModel.n_ln INP -> ~ (kl_nmb i = 45 /\ kl_d i = 0) ->
  kl_tkb (kl_j i) = KModel.lw (kl_nmb i) /\ kl_j (i + 1) = kl_j i + 1 /\ kl_d (i + 1) = kl_d i.
Proof.
intros i Hi Hn.
pose proof kl_model as (_ & _ & _ & _ & Hln0 & Hlt0 & Hlen & Hlent & _).
unfold SlotModel.n_TK in Hlent.
rewrite (kl_nmb_in i Hi) in Hn.
destruct (KModel.tok_at (SlotModel.n_EXP_NM INP) (Z.to_nat i) ltac:(lia) Hn) as [Hlt Heq].
assert (ES : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
pose proof (KModel.tok_other_keep (SlotModel.n_EXP_NM INP) (Z.to_nat i) ltac:(lia) Hn) as Hkeep.
assert (Ej : Z.to_nat (Z.of_nat (Z.to_nat i) - KModel.dropped (SlotModel.n_EXP_NM INP) (Z.to_nat i))
  = Z.to_nat (kl_j i)) by (unfold kl_j, kl_d; rewrite Z2Nat.id by lia; reflexivity).
rewrite Ej in Hlt, Heq.
assert (Ed : kl_d (i + 1) = kl_d i) by (unfold kl_d; rewrite ES; exact Hkeep).
split.
- rewrite (kl_nmb_in i Hi).
  unfold kl_tkb, RcIdentModel.nthb, SlotModel.n_TK in Heq |- *.
  rewrite app_nth1 by lia. rewrite Heq, KModel.lower_lw. reflexivity.
- split; [unfold kl_j; lia | exact Ed].
Qed.
Lemma kl_dash : forall i, 0 <= i < SlotModel.n_ln INP -> kl_nmb i = 45 -> kl_d i = 0 ->
  kl_d (i + 1) = 1 /\ kl_j (i + 1) = kl_j i.
Proof.
intros i Hi H45 Hd.
pose proof kl_model as (_ & _ & _ & _ & Hln0 & Hlt0 & Hlen & _).
rewrite (kl_nmb_in i Hi) in H45.
assert (ES : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
assert (E1 : kl_d (i + 1) = 1)
  by (unfold kl_d in *; rewrite ES;
      exact (KModel.tok_dash_drop (SlotModel.n_EXP_NM INP) (Z.to_nat i) ltac:(lia) H45 Hd)).
split; [exact E1 | unfold kl_j; lia].
Qed.

(* ---- the numbers the symbolic states need ---- *)
Lemma kl_num :
  4096 <= nm /\ nm + SlotModel.n_ln INP + 1 <= alloc_ceiling /\
  4096 <= tk /\ tk + SlotModel.n_lt INP + 1 <= alloc_ceiling /\
  140735332483072 <= alloc_ceiling <= 140737479966720 /\
  0 <= SlotModel.n_ln INP <= 38 /\ 0 <= SlotModel.n_lt INP <= 38 /\
  req_size (Z.max (SlotModel.t_cap_name INP) 1) = Z.max (SlotModel.t_cap_name INP) 1 /\
  req_size (Z.max (SlotModel.t_cap_tok INP) 1) = Z.max (SlotModel.t_cap_tok INP) 1.
Proof.
pose proof HKH as (HJ2 & _).
pose proof kl_model as (F1 & C1' & F2 & C2' & Hln0 & Hlt0 & _ & _ & _ & _ & _ & Hinnm & Hintk & _).
pose proof asan_consts as (AC & _).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 nm _ (proj1 HJ2) Hinnm) as (_ & N1 & N2 & _).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 tk _ (proj1 HJ2) Hintk) as (_ & T1 & T2 & _).
assert (Rn : req_size (Z.max (SlotModel.t_cap_name INP) 1) = Z.max (SlotModel.t_cap_name INP) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_name INP) 1) 0); lia).
assert (Rt : req_size (Z.max (SlotModel.t_cap_tok INP) 1) = Z.max (SlotModel.t_cap_tok INP) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_tok INP) 1) 0); lia).
rewrite Rn in N2. rewrite Rt in T2.
repeat split; lia.
Qed.

(* ---- the state between two rounds of the loop ---- *)
Definition KI (i : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md /\
  0 <= i <= SlotModel.n_ln INP /\
  getr regs 18 = w64 (SFa g pos + V_cnt) /\ getr regs 29 = w64 SHADOW_OFF /\
  getr regs 10 = w64 (nm + i) /\ getr regs 5 = w64 (nm + i) /\
  getr regs 13 = w64 i /\ getr regs 12 = w64 (kl_j i) /\ getr regs 14 = w64 (kl_d i) /\
  getr regs 15 = w64 (2 ^ 64 - 1 - tk) /\ getr regs 16 = w64 (2 ^ 64 - 1 - nm) /\
  getr regs 17 = w64 45.

(* ---- a run of this span writes nothing, so every fact of the cut state survives ---- *)
Definition kl_same (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a.
Lemma kl_kkeep : forall mem mem', kl_same mem mem' ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem -> kkeep B g pos mf ly2 S2 W2 mem2 mem'.
Proof.
intros mem mem' HS (K1 & K2 & K3).
pose proof HKH as (HJ2 & _).
pose proof kl_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof asan_consts as (AC & _).
split; [|split].
- intros a Ha Hn. rewrite (HS a ltac:(lia)). exact (K1 a Ha Hn).
- intros b n0 i Hin Hi.
  destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b n0 (proj1 HJ2) Hin) as (_ & Q1 & Q2 & _).
  rewrite (HS (b + i) ltac:(lia)). exact (K2 b n0 i Hin Hi).
- intros a Ha Hc Hs. rewrite (HS a).
  + exact (K3 a Ha Hc Hs).
  + unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite G12 in Ha.
    change (fs_frame_bytes 4 / 8) with 128 in Ha. change (fs_frame_bytes 4) with 1024 in Ha.
    destruct Ha as [Ha | Ha]; clear - Ha G8 G9 G14 G15 AC; lia.
Qed.

(* ---- the symbolic state at +0x19f8 ---- *)
Lemma kl_entry0 : forall (regs : bvmap 5 word) mem md,
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])) kl_ss0
    (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x19f8)) mem (seg_rom SEGS))).
Proof.
intros regs mem md HKC.
destruct HKC as (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof HKH as (HJ2 & _ & _ & _ & _ & HEC & _ & _ & _ & _ & _ & _ & _ & V152 & _).
pose proof kl_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof kl_num as (N1 & N2 & T1 & T2 & AC & L1 & L2 & Rn & Rt).
destruct HEC as (_ & _ & _ & Hmfb & Hmf32 & _ & _ & V16 & V64 & V192 & V168 & _).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [w64 (SFa g pos); w64 nm])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 (SFa g pos); w64 nm]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 mf)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact Rs1).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nm)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SFa g pos) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = nm) by (rewrite E33; apply unsigned_lit_small; lia).
assert (VK : forall a n v, mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem) a n v)
  by (intros a n v Ha Hn Hv; exact (kl_vm_hi mem a n v HKP Ha Hn Hv)).
unfold kl_ss0. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold kl_rs0. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 32 0) (SFa g pos));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    apply VK; [lia | cbn; lia | exact V64].
  + apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 33 0) nm);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    apply VK; [lia | cbn; lia | exact V152].
  + apply (chunk_ok_val SEGS E _ mf 168 8 (SLit SB) SHADOW_OFF);
      [reflexivity | unfold SHADOW_OFF; zside | zside |].
    apply VK; [lia | cbn; lia | exact V168].
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- unfold kl_G0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok, kl_PTR. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ---- the symbolic state at the loop head +0x1a28 ---- *)
Definition kl_EL (regs : bvmap 5 word) (i : Z) : env :=
  Eimg (Ereg regs [w64 (tk + kl_j i); w64 (kl_nmb i); w64 (kl_tkb (kl_j i))]).
Lemma kl_entryL : forall (regs : bvmap 5 word) mem md i, KI i regs mem md ->
  st_ok_pi SEGS VAL (kl_EL regs i) kl_ssL
    (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1a28)) mem (seg_rom SEGS))) /\
  sh_ok SEGS kl_Bx kl_SHL (kl_EL regs i) (rd W2 mem).
Proof.
intros regs mem md i HI.
pose proof HI as (HKC & Hi & R18 & R29 & R10 & R5 & R13 & R12 & R14 & R15 & R16 & R17).
pose proof HKC as (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof (proj1 HJ) as HAR.
pose proof kl_model as (F1 & C1' & F2 & C2' & _ & _ & Hlen & Hlent & Hnz & Hbnm & Hbtk & Hinnm & Hintk & Hsep).
pose proof kl_num as (N1 & N2 & T1 & T2 & AC & L1 & L2 & Rn & Rt).
pose proof (kl_j_le i Hi) as Hj.
pose proof (kl_d_range i) as Hd.
pose proof (kl_nmb_range i) as Hcb.
pose proof (kl_tkb_range (kl_j i)) as Hdb.
assert (Vnm : val_mem SEGS (rd W2 mem) (nm + i) 1 (kl_nmb i)).
{ unfold kl_nmb. replace (nm + i) with (nm + Z.of_nat (Z.to_nat i)) by lia.
  apply (kl_bytes mem nm (Z.max (SlotModel.t_cap_name INP) 1) _ (Z.to_nat i) HKP Hinnm Hbnm);
    [ rewrite length_app; cbn [length]; clear - Hi Hlen; lia
    | rewrite length_app, Rn; cbn [length]; clear - Hlen F1; lia ]. }
assert (Vtk : val_mem SEGS (rd W2 mem) (tk + kl_j i) 1 (kl_tkb (kl_j i))).
{ unfold kl_tkb. replace (tk + kl_j i) with (tk + Z.of_nat (Z.to_nat (kl_j i))) by lia.
  apply (kl_bytes mem tk (Z.max (SlotModel.t_cap_tok INP) 1) _ (Z.to_nat (kl_j i)) HKP Hintk Hbtk);
    [ rewrite length_app; cbn [length]; clear - Hj Hlent; lia
    | rewrite length_app, Rt; cbn [length]; clear - Hlent F2; lia ]. }
destruct (kl_ra_blk mem md nm (Z.max (SlotModel.t_cap_name INP) 1) i HAR Hinnm
  ltac:(clear - Hi; lia) ltac:(clear - Hi Rn F1 Hlen; lia)) as [RAnm APnm].
destruct (kl_ra_blk mem md tk (Z.max (SlotModel.t_cap_tok INP) 1) (kl_j i) HAR Hintk
  ltac:(clear - Hj; lia) ltac:(clear - Hj Rt F2 Hlent; lia)) as [RAtk APtk].
set (E := kl_EL regs i).
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew E n = ew (Ereg regs [w64 (tk + kl_j i); w64 (kl_nmb i); w64 (kl_tkb (kl_j i))]) n)
  by (intros n Hn; subst E; unfold kl_EL; apply Eimg_low; exact Hn).
assert (E5 : ew E 5 = Z_to_bv 64 (nm + i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact R5).
assert (E10 : ew E 10 = Z_to_bv 64 (nm + i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E12 : ew E 12 = Z_to_bv 64 (kl_j i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 i)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
assert (E14 : ew E 14 = Z_to_bv 64 (kl_d i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E15 : ew E 15 = Z_to_bv 64 (2 ^ 64 - 1 - tk))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact R15).
assert (E16 : ew E 16 = Z_to_bv 64 (2 ^ 64 - 1 - nm))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact R16).
assert (E17 : ew E 17 = Z_to_bv 64 45)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact R17).
assert (E21 : ew E 21 = Z_to_bv 64 tk)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Rtk).
assert (E29 : ew E 29 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 29 29%bv eq_refl); exact R29).
assert (E32 : ew E 32 = Z_to_bv 64 (tk + kl_j i))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (kl_nmb i))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (kl_tkb (kl_j i)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U5 : bv_unsigned (ew E 5) = nm + i)
  by (rewrite E5; apply unsigned_lit_small; clear - N1 N2 AC Hi L1; lia).
assert (U10 : bv_unsigned (ew E 10) = nm + i)
  by (rewrite E10; apply unsigned_lit_small; clear - N1 N2 AC Hi L1; lia).
assert (U12 : bv_unsigned (ew E 12) = kl_j i)
  by (rewrite E12; apply unsigned_lit_small; clear - Hj L2; lia).
assert (U13 : bv_unsigned (ew E 13) = i)
  by (rewrite E13; apply unsigned_lit_small; clear - Hi L1; lia).
assert (U14 : bv_unsigned (ew E 14) = kl_d i)
  by (rewrite E14; apply unsigned_lit_small; clear - Hd; lia).
assert (U15 : bv_unsigned (ew E 15) = 2 ^ 64 - 1 - tk)
  by (rewrite E15; apply unsigned_lit_small; clear - T1 T2 AC L2; lia).
assert (U16 : bv_unsigned (ew E 16) = 2 ^ 64 - 1 - nm)
  by (rewrite E16; apply unsigned_lit_small; clear - N1 N2 AC L1; lia).
assert (U17 : bv_unsigned (ew E 17) = 45) by (rewrite E17; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = tk)
  by (rewrite E21; apply unsigned_lit_small; clear - T1 T2 AC L2; lia).
assert (U32 : bv_unsigned (ew E 32) = tk + kl_j i)
  by (rewrite E32; apply unsigned_lit_small; clear - T1 T2 AC Hj L2; lia).
assert (U33 : bv_unsigned (ew E 33) = kl_nmb i)
  by (rewrite E33; apply unsigned_lit_small; clear - Hcb; lia).
assert (U34 : bv_unsigned (ew E 34) = kl_tkb (kl_j i))
  by (rewrite E34; apply unsigned_lit_small; clear - Hdb; lia).
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Rn, Rt in Hsep.
split.
- rewrite restrict_mkst_fx. unfold kl_ssL. apply pa_entry_st_ok_full.
  + subst E. unfold kl_EL. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold kl_rsL. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U5. split; [clear - N1 Hi; lia|]. split; [clear - N1 N2 AC Hi L1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (nm + i) 0 1 (SOff 33 0) (kl_nmb i));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hcb; cbn; lia | zside |].
      rewrite Z.add_0_r. exact Vnm.
    * rewrite U32. split; [clear - T1 Hj; lia|]. split; [clear - T1 T2 AC Hj L2; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (tk + kl_j i) 0 1 (SOff 34 0) (kl_tkb (kl_j i)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hdb; cbn; lia | zside |].
      rewrite Z.add_0_r. exact Vtk.
  + apply pairwise_disjoint_of_extents. unfold kl_rsL, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U5, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; clear - Hsep Hi Hj F1 F2 Hlen Hlent; lia.
  + unfold kl_GL, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    * unfold afact_ok, kl_PTR, kl_NEG. cbn [af_lo af_hi af_al2].
      rewrite U5, U10, U12, U13, U14, U15, U16, U17, U21, U32, U33, U34.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I;
        clear - N1 N2 T1 T2 AC L1 L2 Hi Hj Hd Hcb Hdb; lia.
    * split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 21 tk E21 ltac:(clear - T1 T2 AC L2; lia)),
              (U_atom E 12 (kl_j i) E12 ltac:(clear - Hj L2; lia)),
              (U_atom E 32 (tk + kl_j i) E32 ltac:(clear - T1 T2 AC Hj L2; lia)).
      unfold zcanon, M64. rewrite Z.mod_small by (clear - T1 T2 AC Hj L2; lia). reflexivity.
- unfold sh_ok, kl_SHL. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W2) mem E kl_Bx 10%nat (nm + i) 1 (nm + i) 0 1 RAnm);
      [unfold kl_Bx; rewrite U_SLit; reflexivity
      | apply (U_atom E 10 (nm + i) E10); clear - N1 N2 AC Hi L1; lia
      | lia | lia | cbn [Z.min Z.max]; intros x Hx; apply APnm; clear - Hx; lia].
  + apply (shent_ok_of_range SEGS (w_H W2) mem E kl_Bx 32%nat (tk + kl_j i) 1 (tk + kl_j i) 0 1 RAtk);
      [unfold kl_Bx; rewrite U_SLit; reflexivity
      | apply (U_atom E 32 (tk + kl_j i) E32); clear - T1 T2 AC Hj L2; lia
      | lia | lia | cbn [Z.min Z.max]; intros x Hx; apply APtk; clear - Hx; lia].
Qed.

(* the state the loop head carries, assembled from its pieces *)
Lemma kl_mkKI : forall i' regs' mem' md',
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem' md' (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem' ->
  getr regs' 2 = w64 mf -> getr regs' 9 = w64 mf -> getr regs' 8 = w64 (e_sp0 g) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 21 = w64 tk ->
  getr regs' 23 = w64 (shadow_addr (SFa g pos)) ->
  0 <= i' <= SlotModel.n_ln INP ->
  getr regs' 18 = w64 (SFa g pos + V_cnt) -> getr regs' 29 = w64 SHADOW_OFF ->
  getr regs' 10 = w64 (nm + i') -> getr regs' 5 = w64 (nm + i') ->
  getr regs' 13 = w64 i' -> getr regs' 12 = w64 (kl_j i') -> getr regs' 14 = w64 (kl_d i') ->
  getr regs' 15 = w64 (2 ^ 64 - 1 - tk) -> getr regs' 16 = w64 (2 ^ 64 - 1 - nm) ->
  getr regs' 17 = w64 45 ->
  KI i' regs' mem' md'.
Proof.
intros i' regs' mem' md' HJ' HKP' H2 H9 H8 H3 H4 H21 H23 Hb H18 H29 H10 H5 H13 H12 H14 H15 H16 H17.
exact (conj (conj HJ' (conj HKP' (conj H2 (conj H9 (conj H8 (conj H3 (conj H4 (conj H21 H23))))))))
        (conj Hb (conj H18 (conj H29 (conj H10 (conj H5 (conj H13 (conj H12 (conj H14
          (conj H15 (conj H16 H17))))))))))).
Qed.
Lemma kl_mkKC : forall regs' mem' md',
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem' md' (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem' ->
  getr regs' 2 = w64 mf -> getr regs' 9 = w64 mf -> getr regs' 8 = w64 (e_sp0 g) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 21 = w64 tk ->
  getr regs' 23 = w64 (shadow_addr (SFa g pos)) ->
  KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md'.
Proof.
intros regs' mem' md' HJ' HKP' H2 H9 H8 H3 H4 H21 H23.
exact (conj HJ' (conj HKP' (conj H2 (conj H9 (conj H8 (conj H3 (conj H4 (conj H21 H23)))))))).
Qed.

Lemma kl_same_trans : forall m1 m2 m3, kl_same m1 m2 -> kl_same m2 m3 -> kl_same m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* the loop head's state from the registers a round leaves: the nine kept ones, then i, j and the flag *)
Ltac kl_fin KS HKR :=
  apply kl_mkKI;
  [ assumption
  | eapply kl_kkeep; [exact KS | assumption]
  | rewrite (HKR (2%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (9%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (8%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (3%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (4%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (21%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (23%bv : bv 5) ltac:(kl_in)); assumption
  | idtac
  | rewrite (HKR (18%bv : bv 5) ltac:(kl_in)); assumption
  | idtac | idtac | idtac | idtac | idtac | idtac
  | rewrite (HKR (15%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (16%bv : bv 5) ltac:(kl_in)); assumption
  | rewrite (HKR (17%bv : bv 5) ltac:(kl_in)); assumption ].
(* a run of this span keeps every byte: no region of its states has a write window *)
Ltac kl_keep Hfr := intros a Ha;
  refine (kept_of_frame _ _ _ _ _ (fun _ => False) Hfr _ a Ha _); [kl_win | intros []].
Ltac kl_w64 Q := first [exact Q | rewrite Q; unfold w64; f_equal; clear; lia].

(* ---- one round of the token loop ---- *)
Lemma kl_iter : forall i regs mem md (Q : world SEGS -> config -> Prop),
  KI i regs mem md ->
  (forall regs' mem' md', KI (i + 1) regs' mem' md' ->
     SRr SEGS W2 (cfg_at SEGS (BASE + 0x1a28) regs' mem' md') Q) ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
     getr regs' 18 = w64 (SFa g pos + V_cnt) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ad8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1a28) regs mem md) Q.
Proof.
intros i regs mem md Q HI FINL FINE.
pose proof HI as (HKC & Hi & R18 & R29 & R10 & R5 & R13 & R12 & R14 & R15 & R16 & R17).
pose proof HKC as (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof kl_model as (F1 & C1' & F2 & C2' & _ & _ & Hlen & Hlent & Hnz & Hbnm & Hbtk & Hinnm & Hintk & Hsep).
pose proof kl_num as (N1 & N2 & T1 & T2 & AC & L1 & L2 & Rn & Rt).
pose proof (kl_j_le i Hi) as Hj.
pose proof (kl_d_range i) as Hd.
pose proof (kl_nmb_range i) as Hcb.
pose proof (kl_tkb_range (kl_j i)) as Hdb.
destruct (kl_entryL regs mem md i HI) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (kl_EL regs i)) by (unfold kl_EL; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 (tk + kl_j i); w64 (kl_nmb i); w64 (kl_tkb (kl_j i))])
  (kl_EL regs i))
  by (split; [intros k Hk; unfold kl_EL; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E5 : ew (kl_EL regs i) 5 = Z_to_bv 64 (nm + i))
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact R5).
assert (E10 : ew (kl_EL regs i) 10 = Z_to_bv 64 (nm + i))
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E12 : ew (kl_EL regs i) 12 = Z_to_bv 64 (kl_j i))
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew (kl_EL regs i) 13 = Z_to_bv 64 i)
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
assert (E14 : ew (kl_EL regs i) 14 = Z_to_bv 64 (kl_d i))
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E17 : ew (kl_EL regs i) 17 = Z_to_bv 64 45)
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact R17).
assert (E33 : ew (kl_EL regs i) 33 = Z_to_bv 64 (kl_nmb i))
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (kl_EL regs i) 34 = Z_to_bv 64 (kl_tkb (kl_j i)))
  by (unfold kl_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U5 : bv_unsigned (ew (kl_EL regs i) 5) = nm + i)
  by (rewrite E5; apply unsigned_lit_small; clear - N1 N2 AC Hi L1; lia).
assert (U10 : bv_unsigned (ew (kl_EL regs i) 10) = nm + i)
  by (rewrite E10; apply unsigned_lit_small; clear - N1 N2 AC Hi L1; lia).
assert (U12 : bv_unsigned (ew (kl_EL regs i) 12) = kl_j i)
  by (rewrite E12; apply unsigned_lit_small; clear - Hj L2; lia).
assert (U13 : bv_unsigned (ew (kl_EL regs i) 13) = i)
  by (rewrite E13; apply unsigned_lit_small; clear - Hi L1; lia).
assert (U14 : bv_unsigned (ew (kl_EL regs i) 14) = kl_d i)
  by (rewrite E14; apply unsigned_lit_small; clear - Hd; lia).
pose proof (st_ok_pi_pin_reg' (kl_EL regs i) kl_ssL _ (29%bv : bv 5) SB HS
  ltac:(cbn [ms_regs restrict mkst]; exact R29) eq_refl) as HS'.
clear HS. rename HS' into HS.
unfold cfg_at. change (w64 (BASE + 0x1a28)) with (Z_to_bv 64 (BASE + 0x1a28)).
change mem with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 0x1a28)) mem (seg_rom SEGS))) in HJ.
paj_run_tok RUN HS HJ SHOK kl_Bspan; [kl_awr_ro |].
rename ms into msA. rename HFr into HFrA. clear HF HG.
assert (KA : kl_same mem (ms_mem msA)) by kl_keep HFrA.
clear HFrA.
(* 0x821b0: nm[i] = '-' ? *)
psrr_branch_tok RUN BR HS SHOK kl_Bspan.
- (* nm[i] = '-' *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (X33 : ew Ex 33 = Z_to_bv 64 (kl_nmb i)) by kl_ew E33;
    assert (X17 : ew Ex 17 = Z_to_bv 64 45) by kl_ew E17;
    rewrite branch_eq_U, (U_atom Ex 33 _ X33 ltac:(clear - Hcb; lia)),
            (U_atom Ex 17 45 X17 ltac:(lia)) in Hc end.
  apply Z.eqb_eq in Hc. rename Hc into Hc45.
  assert (Hlt : i < SlotModel.n_ln INP).
  { destruct (Z.eq_dec i (SlotModel.n_ln INP)) as [Ee|Ee]; [|clear - Hi Ee; lia].
    rewrite Ee, (proj1 kl_end) in Hc45. clear - Hc45. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
  rename ms into msB. rename HFr into HFrB. clear HF HG.
  assert (KB : kl_same (ms_mem msA) (ms_mem msB)) by kl_keep HFrB.
  clear HFrB.
  (* 0x821bc: was a '-' dropped before ? *)
  psrr_branch_tok RUN BR HS SHOK kl_Bspan.
  + (* no: this one is dropped *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (X14 : ew Ex 14 = Z_to_bv 64 (kl_d i)) by kl_ew E14;
      rewrite branch_eq_U, (U_atom Ex 14 _ X14 ltac:(clear - Hd; lia)), U_SLit in Hc end.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. rename Hc into Hc14.
    destruct (kl_dash i ltac:(clear - Hi Hlt; lia) Hc45 Hc14) as [Ed1 Ej1].
    paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
    rename ms into msC. rename HFr into HFrC. clear HF HG.
    assert (KC2 : kl_same (ms_mem msB) (ms_mem msC)) by kl_keep HFrC.
    clear HFrC.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;15;16;17;18;21;23]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict] in HKR.
    prreg HS (5%bv : bv 5) Q5. prreg HS (10%bv : bv 5) Q10. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (29%bv : bv 5) Q29.
    rewrite ?U5, ?E5 in Q5. rewrite ?U10, ?E10 in Q10. rewrite ?U12, ?E12 in Q12.
    rewrite ?U13, ?E13 in Q13. rewrite ?U14, ?E14 in Q14.
    pmkst HS. apply FINL.
    kl_fin (kl_same_trans _ _ _ (kl_same_trans _ _ _ KA KB) KC2) HKR;
      [ clear - Hi Hlt; lia | kl_w64 Q29 | kl_w64 Q10 | kl_w64 Q5 | kl_w64 Q13
      | rewrite Ej1; kl_w64 Q12 | rewrite Ed1; kl_w64 Q14 ].
  + (* yes: this '-' is kept and lower-cased *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (X14 : ew Ex 14 = Z_to_bv 64 (kl_d i)) by kl_ew E14;
      rewrite branch_eq_U, (U_atom Ex 14 _ X14 ltac:(clear - Hd; lia)), U_SLit in Hc end.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. rename Hc into Hc14.
    assert (Hne : ~ (kl_nmb i = 45 /\ kl_d i = 0)) by (intros [_ Hz]; exact (Hc14 Hz)).
    destruct (kl_tok i ltac:(clear - Hi Hlt; lia) Hne) as (Etk & Ej1 & Ed1).
    paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
    rename ms into msC. rename HFr into HFrC. clear HF HG.
    assert (KC2 : kl_same (ms_mem msB) (ms_mem msC)) by kl_keep HFrC.
    clear HFrC.
    (* 0x821ec: tk[j] is the lower-cased nm[i] *)
    psrr_branch_tok RUN BR HS SHOK kl_Bspan.
    * exfalso.
      lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        assert (X33b : ew Ex 33 = Z_to_bv 64 (kl_nmb i)) by kl_ew E33;
        assert (X34b : ew Ex 34 = Z_to_bv 64 (kl_tkb (kl_j i))) by kl_ew E34;
        rewrite branch_ne_U, (U_atom Ex 34 _ X34b ltac:(clear - Hdb; lia)),
                (kl_low_U Ex 33 (kl_nmb i) X33b ltac:(clear - Hcb; lia)) in Hc end.
      apply negb_true_iff, Z.eqb_neq in Hc. exact (Hc Etk).
    * paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
      rename ms into msD. rename HFr into HFrD. clear HF HG.
      assert (KD : kl_same (ms_mem msC) (ms_mem msD)) by kl_keep HFrD.
      clear HFrD.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;15;16;17;18;21;23]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
      cbn [ms_regs restrict] in HKR.
      prreg HS (5%bv : bv 5) Q5. prreg HS (10%bv : bv 5) Q10. prreg HS (12%bv : bv 5) Q12.
      prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (29%bv : bv 5) Q29.
      rewrite ?U5, ?E5 in Q5. rewrite ?U10, ?E10 in Q10. rewrite ?U12, ?E12 in Q12.
      rewrite ?U13, ?E13 in Q13. rewrite ?U14, ?E14 in Q14.
      pmkst HS. apply FINL.
      kl_fin (kl_same_trans _ _ _ (kl_same_trans _ _ _ (kl_same_trans _ _ _ KA KB) KC2) KD) HKR;
        [ clear - Hi Hlt; lia | kl_w64 Q29 | kl_w64 Q10 | kl_w64 Q5 | kl_w64 Q13
        | rewrite Ej1; kl_w64 Q12 | rewrite Ed1; kl_w64 Q14 ].
- (* nm[i] <> '-' *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (X33 : ew Ex 33 = Z_to_bv 64 (kl_nmb i)) by kl_ew E33;
    assert (X17 : ew Ex 17 = Z_to_bv 64 45) by kl_ew E17;
    rewrite branch_eq_U, (U_atom Ex 33 _ X33 ltac:(clear - Hcb; lia)),
            (U_atom Ex 17 45 X17 ltac:(lia)) in Hc end.
  apply Z.eqb_neq in Hc. rename Hc into Hc45.
  paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
  rename ms into msB. rename HFr into HFrB. clear HF HG.
  assert (KB : kl_same (ms_mem msA) (ms_mem msB)) by kl_keep HFrB.
  clear HFrB.
  (* 0x821b4: the NUL ? *)
  psrr_branch_tok RUN BR HS SHOK kl_Bspan.
  + (* yes: leave the loop *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (X33n : ew Ex 33 = Z_to_bv 64 (kl_nmb i)) by kl_ew E33;
      rewrite branch_eq_U, (U_atom Ex 33 _ X33n ltac:(clear - Hcb; lia)), U_SLit in Hc end.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. rename Hc into Hc0.
    assert (Hend : i = SlotModel.n_ln INP).
    { destruct (Z.eq_dec i (SlotModel.n_ln INP)) as [Ee|Ee]; [exact Ee|].
      exfalso. exact (kl_nz i ltac:(clear - Hi Ee; lia) Hc0). }
    pose proof kl_end as (_ & Ejn & Etn).
    assert (Etk0 : kl_tkb (kl_j i) = 0) by (rewrite Hend, Ejn; exact Etn).
    paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6872; [kl_awr_ro |].
    rename ms into msC. rename HFr into HFrC. clear HF HG.
    assert (KC2 : kl_same (ms_mem msB) (ms_mem msC)) by kl_keep HFrC.
    clear HFrC.
    (* 0x82248: tk[j] must be the NUL *)
    psrr_branch_tok RUN BR HS SHOK kl_Bspan.
    * exfalso.
      lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        assert (X34 : ew Ex 34 = Z_to_bv 64 (kl_tkb (kl_j i))) by kl_ew E34;
        rewrite branch_ne_U, (U_atom Ex 34 _ X34 ltac:(clear - Hdb; lia)), U_SLit in Hc end.
      change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      exact (Hc Etk0).
    * paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6872; [kl_awr_ro |].
      rename ms into msD. rename HFr into HFrD. clear HF HG.
      assert (KD : kl_same (ms_mem msC) (ms_mem msD)) by kl_keep HFrD.
      clear HFrD.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;21;23]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
      cbn [ms_regs restrict] in HKR.
      pmkst HS. apply FINE.
      -- apply kl_mkKC;
         [ assumption
         | eapply kl_kkeep;
           [ exact (kl_same_trans _ _ _ (kl_same_trans _ _ _ (kl_same_trans _ _ _ KA KB) KC2) KD)
           | assumption ]
         | rewrite (HKR (2%bv : bv 5) ltac:(kl_in)); assumption
         | rewrite (HKR (9%bv : bv 5) ltac:(kl_in)); assumption
         | rewrite (HKR (8%bv : bv 5) ltac:(kl_in)); assumption
         | rewrite (HKR (3%bv : bv 5) ltac:(kl_in)); assumption
         | rewrite (HKR (4%bv : bv 5) ltac:(kl_in)); assumption
         | rewrite (HKR (21%bv : bv 5) ltac:(kl_in)); assumption
         | rewrite (HKR (23%bv : bv 5) ltac:(kl_in)); assumption ].
      -- rewrite (HKR (18%bv : bv 5) ltac:(kl_in)). exact R18.
  + (* no: compare tk[j] with the lower-cased nm[i] *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (X33n : ew Ex 33 = Z_to_bv 64 (kl_nmb i)) by kl_ew E33;
      rewrite branch_eq_U, (U_atom Ex 33 _ X33n ltac:(clear - Hcb; lia)), U_SLit in Hc end.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. rename Hc into Hc0.
    assert (Hlt : i < SlotModel.n_ln INP).
    { destruct (Z.eq_dec i (SlotModel.n_ln INP)) as [Ee|Ee]; [|clear - Hi Ee; lia].
      exfalso. apply Hc0. rewrite Ee. exact (proj1 kl_end). }
    assert (Hne : ~ (kl_nmb i = 45 /\ kl_d i = 0)) by (intros [Hz _]; exact (Hc45 Hz)).
    destruct (kl_tok i ltac:(clear - Hi Hlt; lia) Hne) as (Etk & Ej1 & Ed1).
    paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
    rename ms into msC. rename HFr into HFrC. clear HF HG.
    assert (KC2 : kl_same (ms_mem msB) (ms_mem msC)) by kl_keep HFrC.
    clear HFrC.
    (* 0x821ec: tk[j] is the lower-cased nm[i] *)
    psrr_branch_tok RUN BR HS SHOK kl_Bspan.
    * exfalso.
      lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
        assert (X33b : ew Ex 33 = Z_to_bv 64 (kl_nmb i)) by kl_ew E33;
        assert (X34b : ew Ex 34 = Z_to_bv 64 (kl_tkb (kl_j i))) by kl_ew E34;
        rewrite branch_ne_U, (U_atom Ex 34 _ X34b ltac:(clear - Hdb; lia)),
                (kl_low_U Ex 33 (kl_nmb i) X33b ltac:(clear - Hcb; lia)) in Hc end.
      apply negb_true_iff, Z.eqb_neq in Hc. exact (Hc Etk).
    * paj_run_to_tok RUNTO HS HJ SHOK kl_Bspan 6696; [kl_awr_ro |].
      rename ms into msD. rename HFr into HFrD. clear HF HG.
      assert (KD : kl_same (ms_mem msC) (ms_mem msD)) by kl_keep HFrD.
      clear HFrD.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;15;16;17;18;21;23]%bv HS
        ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
      cbn [ms_regs restrict] in HKR.
      prreg HS (5%bv : bv 5) Q5. prreg HS (10%bv : bv 5) Q10. prreg HS (12%bv : bv 5) Q12.
      prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (29%bv : bv 5) Q29.
      rewrite ?U5, ?E5 in Q5. rewrite ?U10, ?E10 in Q10. rewrite ?U12, ?E12 in Q12.
      rewrite ?U13, ?E13 in Q13. rewrite ?U14, ?E14 in Q14.
      pmkst HS. apply FINL.
      kl_fin (kl_same_trans _ _ _ (kl_same_trans _ _ _ (kl_same_trans _ _ _ KA KB) KC2) KD) HKR;
        [ clear - Hi Hlt; lia | kl_w64 Q29 | kl_w64 Q10 | kl_w64 Q5 | kl_w64 Q13
        | rewrite Ej1; kl_w64 Q12 | rewrite Ed1; kl_w64 Q14 ].
Qed.

(* ---- the whole loop, by induction on the characters left ---- *)
Lemma kl_loop : forall (n : nat) i regs mem md (Q : world SEGS -> config -> Prop),
  Z.of_nat n = SlotModel.n_ln INP - i ->
  KI i regs mem md ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
     getr regs' 18 = w64 (SFa g pos + V_cnt) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ad8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1a28) regs mem md) Q.
Proof.
induction n as [|n IH]; intros i regs mem md Q Hn HI FINE.
- apply (kl_iter i regs mem md Q HI); [|exact FINE].
  intros regs' mem' md' HI'. exfalso.
  pose proof HI' as (_ & Hb' & _). pose proof HI as (_ & Hb & _). clear - Hn Hb Hb'. lia.
- apply (kl_iter i regs mem md Q HI); [|exact FINE].
  intros regs' mem' md' HI'.
  exact (IH (i + 1) regs' mem' md' Q ltac:(clear - Hn; lia) HI' FINE).
Qed.

(* ---- +0x19f8 .. +0x1a28: the loop's registers ---- *)
Lemma kl_head : forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 10 = w64 0 ->
  (forall regs' mem' md', KI 0 regs' mem' md' ->
     SRr SEGS W2 (cfg_at SEGS (BASE + 0x1a28) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19f8) regs mem md) Q.
Proof.
intros regs mem md Q HKC Ha0 FINL.
pose proof HKC as (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof kl_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof kl_num as (N1 & N2 & T1 & T2 & AC & L1 & L2 & Rn & Rt).
assert (Hd0 : kl_d 0 = 0) by reflexivity.
assert (Hj0 : kl_j 0 = 0) by (unfold kl_j; rewrite Hd0; reflexivity).
pose proof (kl_entry0 regs mem md HKC) as HS0.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 (SFa g pos); w64 nm]))) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (SFa g pos); w64 nm])
  (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])))
  by (split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E21 : ew (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])) 21 = Z_to_bv 64 tk)
  by (rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Rtk).
assert (E32 : ew (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])) 32 = Z_to_bv 64 (SFa g pos))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])) 33 = Z_to_bv 64 nm)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (SHOK : sh_ok SEGS kl_Bx (@nil shent) (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])) (rd W2 mem))
  by apply Forall_nil.
pose proof (st_ok_pi_pin_reg' (Eimg (Ereg regs [w64 (SFa g pos); w64 nm])) kl_ss0 _ (10%bv : bv 5) 0 HS0
  ltac:(cbn [ms_regs restrict mkst]; exact Ha0) eq_refl) as HS.
clear HS0.
unfold cfg_at. change (w64 (BASE + 0x19f8)) with (Z_to_bv 64 (BASE + 0x19f8)).
change mem with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 0x19f8)) mem (seg_rom SEGS))) in HJ.
paj_run_to_tok RUNTO HS HJ SHOK kl_Bsp0 6696; [kl_awr_ro |].
rename ms into msA. rename HFr into HFrA. clear HF HG.
assert (KA : kl_same mem (ms_mem msA)) by kl_keep HFrA.
clear HFrA.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;21;23]%bv HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
kl_prreg_raw HS (5%bv : bv 5) Q5. kl_prreg_raw HS (10%bv : bv 5) Q10.
kl_prreg_raw HS (12%bv : bv 5) Q12. kl_prreg_raw HS (13%bv : bv 5) Q13.
kl_prreg_raw HS (14%bv : bv 5) Q14. kl_prreg_raw HS (15%bv : bv 5) Q15.
kl_prreg_raw HS (16%bv : bv 5) Q16. kl_prreg_raw HS (17%bv : bv 5) Q17.
kl_prreg_raw HS (18%bv : bv 5) Q18. kl_prreg_raw HS (29%bv : bv 5) Q29.
lazymatch type of Q16 with _ = sv_denot ?Ex _ =>
  assert (X21 : ew Ex 21 = Z_to_bv 64 tk) by kl_ew E21;
  assert (X32 : ew Ex 32 = Z_to_bv 64 (SFa g pos)) by kl_ew E32;
  assert (X33 : ew Ex 33 = Z_to_bv 64 nm) by kl_ew E33;
  rewrite denot_lit_U, (U_atom_off Ex 33 nm 0 X33 ltac:(clear - N1 N2 AC L1; lia)
    ltac:(clear - N1 N2 AC L1; lia)) in Q5;
  rewrite denot_lit_U, (U_atom_off Ex 33 nm 0 X33 ltac:(clear - N1 N2 AC L1; lia)
    ltac:(clear - N1 N2 AC L1; lia)) in Q10;
  rewrite denot_lit_U, U_SLit in Q12; rewrite denot_lit_U, U_SLit in Q13;
  rewrite denot_lit_U, U_SLit in Q14; rewrite denot_lit_U, U_SLit in Q17;
  rewrite denot_lit_U, U_SLit in Q29;
  rewrite denot_lit_U, (U_not Ex 21 tk X21 ltac:(clear - T1 T2 AC L2; lia)) in Q15;
  rewrite denot_lit_U, (U_not Ex 33 nm X33 ltac:(clear - N1 N2 AC L1; lia)) in Q16;
  rewrite denot_lit_U, (U_atom_off Ex 32 (SFa g pos) 720 X32 ltac:(clear - G8 G9 AC; lia)
    ltac:(clear - G8 G9 AC; lia)) in Q18
end.
change (zcanon 0) with 0 in Q12, Q13, Q14.
change (zcanon 45) with 45 in Q17. change (zcanon 2147450880) with 2147450880 in Q29.
pmkst HS. apply FINL. apply kl_mkKI.
- assumption.
- eapply kl_kkeep; [exact KA | assumption].
- rewrite (HKR (2%bv : bv 5) ltac:(kl_in)); assumption.
- rewrite (HKR (9%bv : bv 5) ltac:(kl_in)); assumption.
- rewrite (HKR (8%bv : bv 5) ltac:(kl_in)); assumption.
- rewrite (HKR (3%bv : bv 5) ltac:(kl_in)); assumption.
- rewrite (HKR (4%bv : bv 5) ltac:(kl_in)); assumption.
- rewrite (HKR (21%bv : bv 5) ltac:(kl_in)); assumption.
- rewrite (HKR (23%bv : bv 5) ltac:(kl_in)); assumption.
- clear - L1. lia.
- exact Q18.
- exact Q29.
- exact Q10.
- exact Q5.
- exact Q13.
- rewrite Hj0. exact Q12.
- rewrite Hd0. exact Q14.
- exact Q15.
- exact Q16.
- exact Q17.
Qed.

Lemma kl_main : forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 10 = w64 0 ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
     getr regs' 18 = w64 (SFa g pos + V_cnt) ->
     SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ad8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19f8) regs mem md) Q.
Proof.
intros regs mem md Q HKC Ha0 FIN.
pose proof kl_num as (_ & _ & _ & _ & _ & L1 & _).
apply (kl_head regs mem md Q HKC Ha0). intros regs' mem' md' HI'.
exact (kl_loop (Z.to_nat (SlotModel.n_ln INP)) 0 regs' mem' md' Q ltac:(clear - L1; lia) HI' FIN).
Qed.

End run.

Lemma k_loop : k_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
unfold k_loop_stmt.
intros _ g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC Ha0 FIN.
exact (kl_main g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC Ha0 FIN).
Qed.
Check (k_loop : k_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G).

End c.
End b.
End a.
