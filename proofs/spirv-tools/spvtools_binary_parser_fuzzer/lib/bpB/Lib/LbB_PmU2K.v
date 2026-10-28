(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_TablStmt LbB_PmLeaf LbB_PmVops LbB_PmWords LbB_PmVup LbB_PmLeafW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition tbl_memb (ke : Z * expr) (tbl : list (Z * expr)) : bool :=
  existsb (fun ke' => (Z.eqb (fst ke) (fst ke') && expr_eqb (snd ke) (snd ke'))%bool) tbl.
Definition tbl_subb (tbl' tbl : list (Z * expr)) : bool := forallb (fun ke => tbl_memb ke tbl) tbl'.
Lemma tbl_incl : forall tbl' tbl, tbl_subb tbl' tbl = true -> incl tbl' tbl.
Proof.
  intros tbl' tbl Hs ke Hin. pose proof (proj1 (forallb_forall _ _) Hs ke Hin) as K. unfold tbl_memb in K.
  apply existsb_exists in K as (ke' & Hin' & K). apply andb_true_iff in K as [K1 K2].
  apply Z.eqb_eq in K1. apply expr_eqb_true in K2. destruct ke as [k e], ke' as [k' e']. cbn [fst snd] in K1, K2. subst. exact Hin'.
Qed.

Fixpoint zwords (k : Z) (q : nat) : list (Z * expr) :=
  match q with O => [] | S q' => (k, ELit 0) :: zwords (k + 8) q' end.
Lemma zwords_keys : forall k q j e, In (j, e) (zwords k q) -> e = ELit 0 /\ k <= j /\ j + 8 <= k + 8 * Z.of_nat q /\ (j - k) mod 8 = 0.
Proof.
  intros k q. revert k. induction q as [|q IH]; intros k j e Hin; [destruct Hin|]. cbn [zwords] in Hin.
  destruct Hin as [E|Hin]; [injection E as <- <-; split; [reflexivity|]; rewrite Z.sub_diag, Zmod_0_l; lia|].
  destruct (IH (k + 8) j e Hin) as (E1 & E2 & E3 & E4). split; [exact E1|]. split; [lia|]. split; [lia|].
  replace (j - k) with ((j - (k + 8)) + 1 * 8) by lia. rewrite Z_mod_plus_full. exact E4.
Qed.

Lemma skipn_repeatA : forall {A : Type} (x : A) i n, skipn i (repeat x n) = repeat x (n - i).
Proof. intros A x i. induction i as [|i IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.
Lemma firstn_repeatA : forall {A : Type} (x : A) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros A x k. induction k as [|k IH]; intros [|n] Hk; cbn; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed.

Lemma rw_cells_zero_word : forall m A n i, rw_cells asegs m A [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) 0)] ->
  0 <= i -> i + 8 <= n -> rw_cells asegs m (A + i) [C8 (Z_to_bv 64 0)].
Proof.
  intros m A n i C Hi Hin.
  destruct (rw_cells_CB_split asegs m A (Z.to_nat n) (Z.to_nat i) _ C ltac:(lia)) as [_ C2].
  rewrite Z2Nat.id in C2 by lia.
  destruct (rw_cells_CB_split asegs m (A + i) _ 8%nat _ C2 ltac:(lia)) as [C3 _].
  assert (E8 : firstn 8 (skipn (Z.to_nat i) (poison_bytes (Z.to_nat n) 0)) = cbytes (C8 (Z_to_bv 64 0))).
  { unfold poison_bytes. rewrite skipn_repeatA, firstn_repeatA by lia. vm_compute. reflexivity. }
  rewrite E8 in C3.
  destruct C3 as [[Hwf HB] HW]. split; [split|]; [cbn; tauto | | exact HW].
  cbn [cells_bytes app] in *. rewrite app_nil_r in *. exact HB.
Qed.

Lemma rw_cells_zero_split224 : forall m A, rw_cells asegs m A [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m A [C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m A [[Hwf HB] HW]. split; [split|]; [cbn; tauto | | cbn [cells_size csize Nat.add] in *; exact HW].
  cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact HB.
Qed.
Lemma rw_cells_zero_split44 : forall m A, rw_cells asegs m A [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m A [[Hwf HB] HW]. split; [split|]; [cbn; tauto | | cbn [cells_size csize Nat.add] in *; exact HW].
  cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact HB.
Qed.

Lemma and7_add3_w : forall x, 0 <= x < 2 ^ 64 -> x mod 8 = 0 ->
  alu64 ALU_ADD (alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7)) (Z_to_bv 64 3) = Z_to_bv 64 3.
Proof.
  intros x Hx Hal. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_add_unsigned, bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small x) by lia. change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  rewrite Hal. reflexivity.
Qed.

Definition ffkeepX {HCEIL : HeapCeil} {H : asr} (w : pmwA H) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
    Forall (fun on : Z * Z => k + Z.of_nat (cells_size cs) <= fst on \/ fst on + snd on <= k) X ->
    rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs.

Lemma ffkeepX_nil {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) m m', ffkeep w m m' -> ffkeepX w [] m m'.
Proof. intros w m m' K k cs Hk Hn _ C. exact (K k cs Hk Hn C). Qed.
Lemma ffkeepX_refl {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X m, ffkeepX w X m m.
Proof. intros w X m k cs _ _ _ C. exact C. Qed.
Lemma ffkeepX_mono {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X X' m m',
  ffkeepX w X m m' -> incl X X' -> ffkeepX w X' m m'.
Proof.
  intros w X X' m m' K HI k cs Hk Hn F C. apply (K k cs Hk Hn); [| exact C].
  apply Forall_forall. intros on Hin. exact (proj1 (Forall_forall _ _) F on (HI on Hin)).
Qed.
Lemma ffkeepX_trans {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X1 X2 X m1 m2 m3,
  ffkeepX w X1 m1 m2 -> ffkeepX w X2 m2 m3 -> incl X1 X -> incl X2 X -> ffkeepX w X m1 m3.
Proof.
  intros w X1 X2 X m1 m2 m3 A B I1 I2 k cs Hk Hn F C.
  assert (F1 : Forall (fun on : Z * Z => k + Z.of_nat (cells_size cs) <= fst on \/ fst on + snd on <= k) X1).
  { apply Forall_forall. intros on Hin. exact (proj1 (Forall_forall _ _) F on (I1 on Hin)). }
  assert (F2 : Forall (fun on : Z * Z => k + Z.of_nat (cells_size cs) <= fst on \/ fst on + snd on <= k) X2).
  { apply Forall_forall. intros on Hin. exact (proj1 (Forall_forall _ _) F on (I2 on Hin)). }
  exact (B k cs Hk Hn F2 (A k cs Hk Hn F1 C)).
Qed.

Lemma ffkeepX_munch {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X W m m',
  munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => wa_ff w + 16384 <= fst iv \/ snd iv <= wa_ff w
                           \/ Exists (fun on : Z * Z => wa_ff w + fst on <= fst iv /\ snd iv <= wa_ff w + fst on + snd on) X) W ->
  ffkeepX w X m m'.
Proof.
  intros w X W m m' MU WM FW k cs Hk Hn F C. eapply rw_cells_transport; [exact C | exact MU | exact WM |].
  clear - FW Hk Hn F. induction W as [|[lo hi] W IH]; [exact I|]. cbn [disjoint_from].
  pose proof (Forall_inv FW) as D. cbn [fst snd] in D. split; [| exact (IH (Forall_inv_tail FW))].
  destruct D as [D|[D|D]]; [lia | lia |].
  apply Exists_exists in D as ([o n] & Hin & D1 & D2). cbn [fst snd] in D1, D2.
  pose proof (proj1 (Forall_forall _ _) F _ Hin) as G. cbn [fst snd] in G. lia.
Qed.

Lemma ffkeepX_cell {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X m m' k cs,
  ffkeepX w X m m' -> rw_cells asegs m (wa_ff w + k) cs -> 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
  forallb (fun on : Z * Z => (k + Z.of_nat (cells_size cs) <=? fst on) || (fst on + snd on <=? k))%bool X = true ->
  rw_cells asegs m' (wa_ff w + k) cs.
Proof.
  intros w X m m' k cs K C Hk Hn Hb. apply (K k cs Hk Hn); [| exact C].
  apply Forall_forall. intros on Hin. pose proof (proj1 (forallb_forall _ _) Hb on Hin) as B. cbn beta in B.
  apply Bool.orb_true_iff in B. destruct B as [B|B]; apply Z.leb_le in B; lia.
Qed.

Lemma edenot_sext32 : forall E n x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
  edenot E (EExt true 0 4 (EVar n)) = Z_to_bv 64 (sx32A x).
Proof.
  intros E n x He Hx. rewrite <- (swrap32_sx32A x Hx).
  cbn [edenot]. cbn [edenot] in He. rewrite He. unfold ext_val, ext_Z. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z.div_1_r. rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small x (2 ^ 32)) by lia. reflexivity.
Qed.

Lemma edenot_zext : forall E n (wd : nat) x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ (8 * Z.of_nat wd) -> (wd <= 8)%nat ->
  edenot E (EExt false 0 wd (EVar n)) = Z_to_bv 64 x.
Proof.
  intros E n wd x He Hx Hwd. cbn [edenot]. cbn [edenot] in He. rewrite He. unfold ext_val, ext_Z. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  assert (2 ^ (8 * Z.of_nat wd) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small x) by lia. reflexivity.
Qed.
Lemma edenot_zext16 : forall E n x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 ->
  edenot E (EExt false 0 2 (EVar n)) = Z_to_bv 64 x.
Proof. intros E n x He Hx. apply (edenot_zext E n 2 x He); [exact Hx | lia]. Qed.

Lemma C4_sx32A : forall x, 0 <= x < 2 ^ 32 -> cbytes (C4 (Z_to_bv 64 (sx32A x))) = cbytes (C4 (Z_to_bv 64 x)).
Proof.
  intros x Hx. cbn [cbytes]. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  rewrite <- (Z_to_le_bytes_mod 4 ((sx32A x) mod 2 ^ 64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (x mod 2 ^ 64) 32) by (cbn; lia).
  rewrite !mod64_mod32. f_equal. unfold sx32A, PrsGrammar.sx32.
  destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|].
  replace (x + 2 ^ 64 - 2 ^ 32) with (x + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma rw_cells_C4_sx32A : forall m A x, 0 <= x < 2 ^ 32 ->
  rw_cells asegs m A [C4 (Z_to_bv 64 (sx32A x))] -> rw_cells asegs m A [C4 (Z_to_bv 64 x)].
Proof.
  intros m A x Hx [[Hwf HB] HW]. pose proof (C4_sx32A x Hx) as E.
  split; [split|]; [cbn; tauto | | cbn [cells_size csize] in *; exact HW].
  cbn [cells_bytes app] in *. rewrite app_nil_r in *. rewrite <- E. exact HB.
Qed.

Lemma br_eq0_nz : forall r, - 2 ^ 63 <= r < 2 ^ 63 -> r <> 0 -> branch_taken BC_EQ (Z_to_bv 64 r) (Z_to_bv 64 0) = false.
Proof.
  intros r Hr Hnz. cbn [branch_taken]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_0_l by lia. apply Z.eqb_neq. intros E. apply Hnz. Z.div_mod_to_equations. nia.
Qed.

Lemma ev_add2 : forall E (e1 e2 : expr) (x y : Z), edenot E e1 = Z_to_bv 64 x -> edenot E e2 = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> edenot E (EAlu ALU_ADD e1 e2) = Z_to_bv 64 (x + y).
Proof.
  intros E e1 e2 x y H1 H2 Hx Hy Hs. cbn [edenot]. cbn [edenot] in H1, H2. rewrite H1, H2.
  cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small x), (Z.mod_small y), (Z.mod_small (x + y)) by lia. reflexivity.
Qed.

Lemma ev_idx4b : forall E (n r : N) (y x : Z), edenot E (EVar n) = Z_to_bv 64 y -> edenot E (EVar r) = Z_to_bv 64 x ->
  0 <= x -> 0 <= y -> y + 4 * x < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EVar n) (EMd M_MUL (ELit 4) (EVar r))) = Z_to_bv 64 (y + 4 * x).
Proof.
  intros E n r y x Hy Hx H0 H1 H2. cbn [edenot]. change (ev E r) with (edenot E (EVar r)). change (ev E n) with (edenot E (EVar n)).
  rewrite Hx, Hy. rewrite w_mul_litA. cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (4 * x) (2 ^ 64)) by lia. rewrite (Z.mod_small y (2 ^ 64)) by lia.
  rewrite (Z.mod_small (y + 4 * x) (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma ev_subw_small : forall E (a b : N) (x y : Z), edenot E (EVar a) = Z_to_bv 64 x -> edenot E (EVar b) = Z_to_bv 64 y ->
  0 <= y <= x -> x < 2 ^ 31 -> edenot E (EAluw ALU_SUB (EVar a) (EVar b)) = Z_to_bv 64 (x - y).
Proof.
  intros E a b x y Ha Hb Hxy Hx. cbn [edenot]. cbn [edenot] in Ha, Hb. rewrite Ha, Hb. apply bv_eq.
  rewrite (u_subw_small _ _ (x - y)); [| lia | rewrite !u64_of_Z by lia; lia]. rewrite u64_of_Z by lia. reflexivity.
Qed.

Lemma ev_add_m1_zero : forall E (n : N), edenot E (EVar n) = Z_to_bv 64 0 ->
  edenot E (EAlu ALU_ADD (EVar n) (ELit (-1))) = Z_to_bv 64 (2 ^ 64 - 1).
Proof.
  intros E n H. cbn [edenot]. change (ev E n) with (edenot E (EVar n)). rewrite H. apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma w2lb4_sx32A : forall x, 0 <= x < 2 ^ 32 -> cbytes (C4 (Z_to_bv 64 x)) = word_to_le_bytes 4 (Z_to_bv 64 (sx32A x)).
Proof. intros x Hx. rewrite <- (C4_sx32A x Hx). reflexivity. Qed.

Definition rt_keepK (K : list reg) (RT : list (reg * expr)) : list (reg * expr) :=
  List.filter (fun re => existsb (fun x => bv_eqb (fst re) x) K) RT.
Lemma regs_keepK {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R R' RT (K : list reg),
  regs_tblX w X R RT -> (forall r, In r K -> PropExec.getr R' r = PropExec.getr R r) -> regs_tblX w X R' (rt_keepK K RT).
Proof.
  intros w X R R' RT K HT HK. unfold regs_tblX, rt_keepK in *. apply Forall_forall. intros [r e] Hin.
  apply filter_In in Hin as [Hin Hk]. cbn [fst snd] in *. rewrite (HK r (LbB_Call.inb_In r K Hk)).
  exact (proj1 (Forall_forall _ _) HT (r, e) Hin).
Qed.
Lemma regs_tbl_cons {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R RT r e,
  PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ X)) e -> regs_tblX w X R RT -> regs_tblX w X R ((r, e) :: RT).
Proof. intros w X R RT r e He HT. apply Forall_cons; [exact He | exact HT]. Qed.

Lemma pm_bud_scal : forall n c widx icount endian reqconv, pm_bud n c -> pm_bud n (set_scalA c widx icount endian reqconv).
Proof. intros n [] widx icount endian reqconv B. exact B. Qed.
Lemma pm_bud_v1cnt : forall n c k, pm_bud n c -> pm_bud n (set_v1A c (t3a (c_v1 c), k, t3c (c_v1 c))).
Proof. intros n [w i e r m1 m2 m3 [[a b] cp] v2 v3 tr] k B. exact B. Qed.
Lemma pm_bud_v2xs : forall n c xs, pm_bud n c -> pm_bud n (set_v2A c (t3a (c_v2 c), xs, t3c (c_v2 c))).
Proof. intros n [w i e r m1 m2 m3 v1 [[a b] cp] v3 tr] xs B. exact B. Qed.
Lemma pm_bud_v3xs : forall n c xs, pm_bud n c -> pm_bud n (set_v3A c (t3a (c_v3 c), xs, t3c (c_v3 c))).
Proof. intros n [w i e r m1 m2 m3 v1 v2 [[a b] cp] tr] xs B. exact B. Qed.
Lemma c_blocks_v1cnt : forall c k, c_blocks (set_v1A c (t3a (c_v1 c), k, t3c (c_v1 c))) = c_blocks c.
Proof. intros [w i e r m1 m2 m3 [[a b] cp] v2 v3 tr] k. reflexivity. Qed.
Lemma c_blocks_v2xs : forall c xs, c_blocks (set_v2A c (t3a (c_v2 c), xs, t3c (c_v2 c))) = c_blocks c.
Proof. intros [w i e r m1 m2 m3 v1 [[a b] cp] v3 tr] xs. reflexivity. Qed.
Lemma c_blocks_v3xs : forall c xs, c_blocks (set_v3A c (t3a (c_v3 c), xs, t3c (c_v3 c))) = c_blocks c.
Proof. intros [w i e r m1 m2 m3 v1 v2 [[a b] cp] tr] xs. reflexivity. Qed.
Lemma c_blocks_scal : forall c widx icount endian reqconv, c_blocks (set_scalA c widx icount endian reqconv) = c_blocks c.
Proof. intros [] widx icount endian reqconv. reflexivity. Qed.

Lemma pm_bud_v2cap : forall n c b xs cap, pm_bud n c -> 0 <= 4 * cap <= 2 ^ 20 -> pm_bud n (set_v2A c (b, xs, cap)).
Proof.
  intros n [w i e r m1 m2 m3 v1 v2 v3 tr] b xs cap (A & B1 & B2 & B3 & V1 & V2 & V3 & D & E) Hc.
  cbn in *. refine (conj A (conj B1 (conj B2 (conj B3 (conj V1 (conj _ (conj V3 (conj D E)))))))). cbn. lia.
Qed.
Lemma pm_bud_v3cap : forall n c b xs cap, pm_bud n c -> 0 <= 4 * cap <= 2 ^ 26 -> pm_bud n (set_v3A c (b, xs, cap)).
Proof.
  intros n [w i e r m1 m2 m3 v1 v2 v3 tr] b xs cap (A & B1 & B2 & B3 & V1 & V2 & V3 & D & E) Hc.
  cbn in *. refine (conj A (conj B1 (conj B2 (conj B3 (conj V1 (conj V2 (conj _ (conj D E)))))))). cbn. lia.
Qed.
Lemma pm_bud_v3bound : forall n c, pm_bud n c -> 0 <= 4 * t3c (c_v3 c) <= 2 ^ 26.
Proof. intros n [w i e r m1 m2 m3 v1 v2 v3 tr] (A & B1 & B2 & B3 & V1 & V2 & V3 & D & E). cbn in *. lia. Qed.

Lemma rw_cells_appA : forall m A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Lemma rw_cells_same : forall m m' A cs,
  rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] (W1 & W2 & W3)] Hs. pose proof HB as (B0 & B1 & B). rewrite (cells_bytes_length cs Hwf) in B1, B.
  split; [split; [exact Hwf|]|].
  - split; [exact B0|]. split; [rewrite (cells_bytes_length cs Hwf); exact B1|]. rewrite (cells_bytes_length cs Hwf).
    intros i Hi. unfold mrd, wa. rewrite (Hs (A + Z.of_nat i) ltac:(lia)). exact (B i Hi).
  - split; [exact W1|]. split; [exact W2|]. intros i Hi. unfold wview, wa. rewrite (Hs (A + i) ltac:(lia)). exact (W3 i Hi).
Qed.

Lemma mdef_of_rw_cells : forall m A cs, rw_cells asegs m A cs -> AIMG_TOP <= A -> mdef m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs C HA i Hi. apply (rw_cells_def_hi m A cs (A + i) C HA). lia. Qed.

Lemma c_blocks_v3_in : forall c b xs cap q k,
  In (q, k) (c_blocks (set_v3A c (b, xs, cap))) -> In (q, k) (c_blocks c) \/ k = 4 * cap.
Proof.
  intros [w i e r m1 m2 m3 v1 v2 [[a3 b3] c3] tr] b xs cap q k Hin. unfold c_blocks in *. cbn -[umap_blocks vec_opnd_blocks Z.mul Z.eqb] in *.
  rewrite !in_app_iff in Hin. rewrite !in_app_iff.
  destruct Hin as [A|[A|[A|[A|[A|[A|A]]]]]]; try tauto.
  destruct (b =? 0); [destruct A|]. destruct A as [A|[]]. injection A as <- <-. right. reflexivity.
Qed.

Lemma c_blocks_v2_in : forall c b xs cap q k,
  In (q, k) (c_blocks (set_v2A c (b, xs, cap))) -> In (q, k) (c_blocks c) \/ k = 4 * cap.
Proof.
  intros [w i e r m1 m2 m3 v1 [[a2 b2] c2] v3 tr] b xs cap q k Hin. unfold c_blocks in *. cbn -[umap_blocks vec_opnd_blocks Z.mul Z.eqb] in *.
  rewrite !in_app_iff in Hin. rewrite !in_app_iff.
  destruct Hin as [A|[A|[A|[A|[A|[A|A]]]]]]; try tauto.
  destruct (b =? 0); [destruct A|]. destruct A as [A|[]]. injection A as <- <-. right. reflexivity.
Qed.

Lemma granule_split : forall widx n, 0 <= widx < n ->
  4 * widx + 4 <= 8 * ((4 * n) / 8) \/ (4 * widx = 8 * ((4 * n) / 8) /\ (4 * n) mod 8 = 4).
Proof. intros widx n H. Z.div_mod_to_equations. lia. Qed.

Ltac inlist := cbn; repeat (first [left; reflexivity | right]).

Section U2K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Lemma pmxa_ftbl_zeros : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k n (q : nat),
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    rw_cells asegs m (wa_ff w + k) [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) 0)] -> 0 <= k -> 8 * Z.of_nat q <= n ->
    PMXAT H LINV w s LB LBs m mo c ins tbl (ftbl ++ zwords k q) TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k n q X C Hk Hq.
    destruct X; constructor; try assumption.
    unfold fslots_ok in *. apply Forall_app. split; [assumption|]. apply Forall_forall. intros [j e] Hin. cbn [fst snd].
    destruct (zwords_keys k q j e Hin) as (-> & J1 & J2 & J3). cbn [edenot].
    replace (wa_ff w + j) with (wa_ff w + k + (j - k)) by lia. apply (rw_cells_zero_word m (wa_ff w + k) n (j - k) C); lia.
  Qed.
End U2K.
