(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB LeptCellsB LeptRecs LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCreateST V2LeptPixCopyST V2LeptPixDestroyK V2LeptPixaCreate V2LeptPixaAdd V2LeptBl_iface V2LeptBilSegs V2LeptBilSegs2 V2LeptBilSegs2h V2LeptBilSegs2v V2LeptBilCSegs3.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Section BilCW3.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bc_kr (R : bvmap 5 word) (s spat rng : Z) (g3 : word) : Prop :=
  getr R 2 = Z_to_bv 64 (s - 320) /\ getr R 4 = Z_to_bv 64 0x56270 /\ getr R 8 = Z_to_bv 64 (-10) /\ getr R 18 = Z_to_bv 64 10 /\
  getr R 19 = Z_to_bv 64 (- 2 ^ 31) /\ getr R 20 = Z_to_bv 64 1 /\ getr R 21 = Z_to_bv 64 spat /\ getr R 22 = Z_to_bv 64 3 /\
  getr R 23 = Z_to_bv 64 rng /\ getr R 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng) /\ getr R 27 = Z_to_bv 64 1 /\ getr R 3 = g3.

(* [comment removed for export] *)
Definition bc_mem (C : lctx) (A7 A : AS) (m : word -> option byte) (parr w h i pix data : Z) : Prop :=
  (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (4096 <= data)%Z /\ (data + 4 * (wpl_of w 8 * h) <= alloc_top (c_vm C))%Z /\ pix <> data /\
  live A7 (Z_to_bv 64 pix) = None /\ live A7 (Z_to_bv 64 data) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A (Z_to_bv 64 pix) = Some 64%Z /\ live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z /\
  PIXat m pix (hdv w h 8 0 data) /\ rdn SEGS m (Z_to_bv 64 (parr + 8 * i)) 8 = Some (Z_to_le_bytes 8 pix).

(* [comment removed for export] *)
Definition bc_fl_ok (FL : list cell) : Prop :=
  Forall (fun c : cell => let '(o, n, _) := c in (0 <= o)%Z /\
    ((o + Z.of_nat n <= 8)%Z \/ (16 <= o /\ o + Z.of_nat n <= 40)%Z \/ (48 <= o /\ o + Z.of_nat n <= 56)%Z \/
     (64 <= o /\ o + Z.of_nat n <= 80)%Z \/ (152 <= o /\ o + Z.of_nat n <= 176)%Z \/ (192 <= o /\ o + Z.of_nat n <= 320)%Z)) FL.
Definition bc_fl2 (FL : list cell) (bil bsc nc : Z) : list cell :=
  FL ++ [(16%Z, 8%nat, bil); (24%Z, 8%nat, bsc); (32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)].
Definition bc_fl3 (FL : list cell) (bil bsc nc pa datas wpls w h : Z) : list cell :=
  bc_fl2 FL bil bsc nc ++ [(8%Z, 8%nat, pa); (96%Z, 8%nat, datas); (80%Z, 8%nat, wpls); (136%Z, 8%nat, w); (104%Z, 8%nat, h); (128%Z, 8%nat, 0%Z)].

Definition bc_inv (C : lctx) (A7 A : AS) (m7 m : word -> option byte) (s pa parr ba barr w h idx : Z) (pixes datad : Z -> Z) (FL : list cell) : Prop :=
  sub_live A7 A /\ POSTM C A7 s m7 m /\ cellsAt SEGS m (s - 320) FL /\
  pixa_cells m pa parr ba barr idx /\ pixa_blks C A pa parr ba barr /\
  live A7 (Z_to_bv 64 pa) = None /\ live A7 (Z_to_bv 64 parr) = None /\ live A7 (Z_to_bv 64 ba) = None /\ live A7 (Z_to_bv 64 barr) = None /\
  (forall i, (0 <= i < idx)%Z -> bc_mem C A7 A m parr w h i (pixes i) (datad i)) /\
  (forall q : word, ~ In q (map (Z_to_bv 64) [pa; parr; ba; barr]) -> (forall i, (0 <= i < idx)%Z -> q <> Z_to_bv 64 (pixes i) /\ q <> Z_to_bv 64 (datad i)) ->
                    live A q = live A7 q) /\
  parr <> barr /\ (forall i j, (0 <= i < j)%Z -> (j < idx)%Z -> datad i <> datad j /\ pixes i <> pixes j /\ pixes i <> datad j /\ datad i <> pixes j) /\
  (forall i, (0 <= i < idx)%Z -> ~ In (Z_to_bv 64 (pixes i)) (map (Z_to_bv 64) [pa; parr; ba; barr]) /\ ~ In (Z_to_bv 64 (datad i)) (map (Z_to_bv 64) [pa; parr; ba; barr])).

(* [comment removed for export] *)
Definition RK_it : Z := (RK_pixcopy + RK_pix)%Z.
Definition RB_it (w h : Z) : Z := (RB_pixT (4 * (wpl_of (w + 22) 8 * (h + 22))) + RB_pixT (4 * (wpl_of w 8 * h)))%Z.

(* [comment removed for export] *)
Definition bc_cst (A7 : AS) (m7 : word -> option byte) (bsc datas nc spat rng w h minv maxv : Z) : Prop :=
  hdr_ok (w + 22) (h + 22) 8 /\ hdr_ok w h 8 /\ (1 <= w)%Z /\ (1 <= h)%Z /\
  PIXat m7 bsc (hdv (w + 22) (h + 22) 8 0 datas) /\ live A7 (Z_to_bv 64 bsc) = Some 64%Z /\ live A7 (Z_to_bv 64 datas) = Some (4 * (wpl_of (w + 22) 8 * (h + 22)))%Z /\
  (0 <= nc < 2 ^ 64)%Z /\ live A7 (Z_to_bv 64 nc) = Some 40%Z /\
  (forall j, (0 <= j < 10)%Z -> rdn SEGS m7 (Z_to_bv 64 (nc + 4 * j)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv j))) /\ (0 <= minv <= 255)%Z /\ (0 <= maxv <= 255)%Z /\
  (0 <= spat < 2 ^ 64)%Z /\ live A7 (Z_to_bv 64 spat) = Some 44%Z /\ (0 <= rng < 2 ^ 64)%Z /\ live A7 (Z_to_bv 64 rng) = Some 1024%Z.

Lemma bc_u64 : forall x : word, (0 <= u x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.

Lemma bc_m16_4 : forall x, (x mod 16 = 0)%Z -> (x mod 4 = 0)%Z.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (4 * q)%Z. ring. Qed.

Lemma bc_m16_8 : forall x, (x mod 16 = 0)%Z -> (x mod 8 = 0)%Z.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (2 * q)%Z. ring. Qed.

Lemma bc_msub : forall x k d, (d <> 0)%Z -> (x mod d = 0)%Z -> (k mod d = 0)%Z -> ((x - k) mod d = 0)%Z.
Proof.
  intros x k d Hd Hx Hk. apply Z.mod_divide in Hx; [|exact Hd]. apply Z.mod_divide in Hk; [|exact Hd]. apply Z.mod_divide; [exact Hd|].
  destruct Hx as [a ->]. destruct Hk as [b ->]. exists (a - b)%Z. ring.
Qed.

Lemma bc_livk_at : forall A m m' (p k : Z) (x : word), LIVK A m m' -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> m' x = m x.
Proof.
  intros A m m' p k x L Hl H0 H1 Hx.
  pose proof (L (Z_to_bv 64 p) k (u x - p)%Z Hl ltac:(lia)) as E. unfold at_ in E.
  rewrite u_Z2bv in E by lia. replace (p + (u x - p))%Z with (u x) in E by lia.
  rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Lemma bc_rdn_keep : forall m m' (x : Z) (n : nat), (0 <= x)%Z -> (x + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall a : word, (x <= u a < x + Z.of_nat n)%Z -> m' a = m a) ->
  rdn SEGS m' (Z_to_bv 64 x) n = rdn SEGS m (Z_to_bv 64 x) n.
Proof.
  intros m m' x n H0 H1 H.
  apply (agree_rdn SEGS x (Z.of_nat n) m m' x n); [intros a Ha _; apply H; exact Ha | lia | lia | lia | lia].
Qed.

Lemma agree_win_trans : forall base len RO (m1 m2 m3 : word -> option byte),
  agree_win base len RO m1 m2 -> agree_win base len RO m2 m3 -> agree_win base len RO m1 m3.
Proof. intros base len RO m1 m2 m3 H1 H2 a Ha HR. rewrite (H2 a Ha HR). exact (H1 a Ha HR). Qed.

Lemma rinv_split : forall (R : list (Z * Z)) (a : word),
  (forall r, In r R -> ~ inreg (fst r) (snd r) a) \/ (exists r, In r R /\ inreg (fst r) (snd r) a).
Proof.
  induction R as [|r R IH]; intros a; [left; intros r []|].
  destruct (IH a) as [H|(r' & Hr' & Hi)]; [|right; exists r'; split; [right; exact Hr' | exact Hi]].
  unfold inreg.
  destruct (Z_le_gt_dec (fst r) (u a)) as [H1|H1]; [destruct (Z_lt_ge_dec (u a) (fst r + snd r)) as [H2|H2]|].
  - right. exists r. split; [left; reflexivity | unfold inreg; lia].
  - left. intros r0 [<-|Hr0]; [unfold inreg; lia | exact (H r0 Hr0)].
  - left. intros r0 [<-|Hr0]; [unfold inreg; lia | exact (H r0 Hr0)].
Qed.

Lemma rinv_POSTM : forall C Ar A m md m' (s : Z) (R : list (Z * Z)), Cok C -> W C A m md -> sub_live Ar A -> rinv R m m' ->
  Forall (fun r => (c_top C - LSTK <= fst r /\ fst r + snd r <= s)%Z \/
                   exists (p : word) n, live A p = Some n /\ live Ar p = None /\ (u p <= fst r)%Z /\ (fst r + snd r <= u p + n)%Z) R ->
  POSTM C Ar s m m'.
Proof.
  intros C Ar A m md m' s R CK HW SL RI FA.
  apply (POSTM_local C Ar A m md m' s CK HW SL).
  intros a Hne.
  destruct (rinv_split R a) as [H|(r & Hr & Hi)]; [exfalso; apply Hne; exact (proj2 RI a H)|].
  rewrite Forall_forall in FA. destruct (FA r Hr) as [[F1 F2]|(p & n & L1 & L2 & F1 & F2)]; unfold inreg in Hi.
  - left. unfold scratch. lia.
  - right. exists p, n. split; [exact L1|]. split; [exact L2|]. lia.
Qed.

Lemma fl_keep : forall FL base (m m' : word -> option byte) RO, bc_fl_ok FL -> (0 <= base)%Z -> (base + 320 <= 2 ^ 64)%Z ->
  Forall (fun r => (8 <= fst r /\ fst r + snd r <= 16) \/ (40 <= fst r /\ fst r + snd r <= 48) \/ (56 <= fst r /\ fst r + snd r <= 64) \/
                   (80 <= fst r /\ fst r + snd r <= 152) \/ (176 <= fst r /\ fst r + snd r <= 192))%Z RO ->
  agree_win base 320 RO m m' -> cellsAt SEGS m base FL -> cellsAt SEGS m' base FL.
Proof.
  intros FL base m m' RO OK H0 H1 FR AG CS.
  apply (cells_keep SEGS base 320 RO m m' FL H0 H1 AG); [|exact CS].
  apply forallb_forall. intros c Hc. unfold bc_fl_ok in OK. rewrite Forall_forall in OK. specialize (OK c Hc).
  destruct c as [[o n] z]. unfold cell_ok. cbn [c_off c_len fst snd] in *.
  apply andb_true_intro; split; [apply andb_true_intro; split; apply Z.leb_le; lia|].
  apply forallb_forall. intros r Hr. rewrite Forall_forall in FR. specialize (FR r Hr).
  apply orb_true_intro.
  destruct (Z_le_gt_dec (o + Z.of_nat n) (fst r)); [left; apply Z.leb_le; lia | right; apply Z.leb_le; lia].
Qed.

Definition bc_fx (bil bsc nc pa datas wpls w h : Z) : list cell :=
  [(16%Z, 8%nat, bil); (24%Z, 8%nat, bsc); (32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc);
   (8%Z, 8%nat, pa); (96%Z, 8%nat, datas); (80%Z, 8%nat, wpls); (136%Z, 8%nat, w); (104%Z, 8%nat, h); (128%Z, 8%nat, 0%Z)].

Lemma fl3_split : forall (m : word -> option byte) b FL bil bsc nc pa datas wpls w h,
  cellsAt SEGS m b (bc_fl3 FL bil bsc nc pa datas wpls w h) -> cellsAt SEGS m b FL /\ cellsAt SEGS m b (bc_fx bil bsc nc pa datas wpls w h).
Proof.
  intros m b FL bil bsc nc pa datas wpls w h H. unfold bc_fl3, bc_fl2, cellsAt in *.
  apply Forall_app in H as [H H3]. apply Forall_app in H as [H1 H2]. split; [exact H1|].
  unfold bc_fx. exact (proj2 (Forall_app _ _ _) (conj H2 H3)).
Qed.

Lemma fl3_join : forall (m : word -> option byte) b FL bil bsc nc pa datas wpls w h,
  cellsAt SEGS m b FL -> cellsAt SEGS m b (bc_fx bil bsc nc pa datas wpls w h) -> cellsAt SEGS m b (bc_fl3 FL bil bsc nc pa datas wpls w h).
Proof.
  intros m b FL bil bsc nc pa datas wpls w h H1 H2. unfold bc_fl3, bc_fl2, bc_fx, cellsAt in *.
  rewrite <- app_assoc. apply Forall_app; split; [exact H1|]. exact H2.
Qed.

Definition cv0 : cmapv := CMAPV 0 0 0 0 0.

Lemma wv_wv : forall h h' md, with_vmmaps h (with_vmmaps h' md) = with_vmmaps h md.
Proof. intros. reflexivity. Qed.

Local Ltac zlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Lemma kc_keep : forall A (m m' : word -> option byte) (arr n k : Z), kcell_ok arr n m -> LIVK A m m' -> live A (Z_to_bv 64 arr) = Some k ->
  (0 <= arr)%Z -> (arr + k <= 2 ^ 64)%Z -> (4 * n <= k)%Z -> kcell_ok arr n m'.
Proof.
  intros A m m' arr n k KC L Hl H0 H1 H2 i Hi.
  destruct (KC i Hi) as (x & R & F). exists x. split; [|exact F].
  rewrite (LIVK_rdn SEGS A m m' (Z_to_bv 64 arr) k (arr + 4 * i) 4 L Hl) by (rewrite u_Z2bv by lia; zlia). exact R.
Qed.

Lemma rdb_W : forall C A m md (p n : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some n -> (0 <= p)%Z -> (p + n < 2 ^ 64)%Z -> rd_bytes m p n.
Proof.
  intros C A m md p n CK HW Hl H0 H1 q Hq.
  destruct (V2LeptCmapDeser.blk_rdn C A m md (Z_to_bv 64 p) n q 1 CK HW Hl) as [bs Hbs]; [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlia |].
  pose proof (rdn_length _ _ _ _ _ Hbs) as HL.
  destruct bs as [|b [|b' bs]]; cbn in HL; try discriminate. exists b. exact Hbs.
Qed.

Lemma rinv_keep : forall (R : list (Z * Z)) (m m' : word -> option byte) (p k : Z), rinv R m m' ->
  Forall (fun r => (fst r + snd r <= p)%Z \/ (p + k <= fst r)%Z) R -> forall a : word, (p <= u a < p + k)%Z -> m' a = m a.
Proof.
  intros R m m' p k RI F a Ha. apply (proj2 RI). intros r Hr. rewrite Forall_forall in F. specialize (F r Hr). unfold inreg. lia.
Qed.

Lemma pixa_cells_keep : forall (m m' : word -> option byte) (pa parr ba barr n : Z), pixa_cells m pa parr ba barr n ->
  (0 <= pa)%Z -> (pa + 32 <= 2 ^ 64)%Z -> (0 <= ba)%Z -> (ba + 24 <= 2 ^ 64)%Z ->
  (forall a : word, (pa <= u a < pa + 32)%Z -> m' a = m a) -> (forall a : word, (ba <= u a < ba + 24)%Z -> m' a = m a) ->
  pixa_cells m' pa parr ba barr n.
Proof.
  intros m m' pa parr ba barr n PC H0 H1 H2 H3 Ka Kb.
  destruct PC as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  unfold pixa_cells.
  repeat split; (rewrite bc_rdn_keep with (m := m); [assumption | lia | zlia | intros a Ha; first [apply Ka; zlia | apply Kb; zlia]]).
Qed.

Definition bc_or (P Q : Prop) : Prop := P \/ Q.

Lemma bc_fsc_pass : forall fr fr', bc_fsc fr -> pass_fp fr fr' -> bc_fsc fr'.
Proof.
  intros fr fr' (F8 & F9 & F18) PF. unfold bc_fsc.
  rewrite !PF; [auto | vm_compute; intros HH; repeat destruct HH as [HH|HH]; try discriminate HH; exact HH ..].
Qed.

Lemma pass_fp_trans : forall a b c, pass_fp a b -> pass_fp b c -> pass_fp a c.
Proof. intros a b c H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma zne_live : forall X (p q : Z) k, live X (Z_to_bv 64 p) = Some k -> live X (Z_to_bv 64 q) = None -> q <> p.
Proof. intros X p q k H1 H2 E. subst q. congruence. Qed.

Lemma live_none_sub : forall X Y q, sub_live X Y -> live Y q = None -> live X q = None.
Proof. intros X Y q S H. destruct (live X q) eqn:E; [|reflexivity]. rewrite (S _ _ E) in H. discriminate. Qed.

Lemma zne_live2 : forall X (p q : Z) k, live X (Z_to_bv 64 p) = Some k -> live X (Z_to_bv 64 q) = None -> p <> q.
Proof. intros X p q k H1 H2 E. subst q. congruence. Qed.

Lemma nin_ne : forall (x y : Z) L, ~ In (Z_to_bv 64 x) (map (Z_to_bv 64) L) -> In y L -> x <> y.
Proof. intros x y L H Hy E. subst y. apply H. apply in_map. exact Hy. Qed.

Lemma out_of_sub : forall (p k q n q' n' y : Z), (p <= y < p + k)%Z -> bc_or (p + k <= q)%Z (q + n <= p)%Z ->
  (q <= q')%Z -> (q' + n' <= q + n)%Z -> ~ (q' <= y < q' + n')%Z.
Proof. intros p k q n q' n' y H [D|D] H1 H2; lia. Qed.

Lemma bc_fr_keep : forall (fr fr1 fr' : bvmap 5 word), (forall r : reg, ~ In (ridx r) [8; 9; 18]%nat -> reg_get fr1 r = reg_get fr r) -> pass_fp fr1 fr' ->
  forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r.
Proof.
  intros fr fr1 fr' F1 PF r H8 H9 H12 H13 H14 H15 H18.
  assert (N : forall k : nat, r <> Z_to_bv 5 (Z.of_nat k) -> ridx r <> k).
  { intros k H E. apply H. rewrite <- (ridx_roundtrip r), E. reflexivity. }
  assert (N8 : ridx r <> 8%nat) by (apply N; intro E; apply H8; rewrite E; apply bv_eq; reflexivity).
  assert (N9 : ridx r <> 9%nat) by (apply N; intro E; apply H9; rewrite E; apply bv_eq; reflexivity).
  assert (N12 : ridx r <> 12%nat) by (apply N; intro E; apply H12; rewrite E; apply bv_eq; reflexivity).
  assert (N13 : ridx r <> 13%nat) by (apply N; intro E; apply H13; rewrite E; apply bv_eq; reflexivity).
  assert (N14 : ridx r <> 14%nat) by (apply N; intro E; apply H14; rewrite E; apply bv_eq; reflexivity).
  assert (N15 : ridx r <> 15%nat) by (apply N; intro E; apply H15; rewrite E; apply bv_eq; reflexivity).
  assert (N18 : ridx r <> 18%nat) by (apply N; intro E; apply H18; rewrite E; apply bv_eq; reflexivity).
  rewrite (PF r); [apply F1; cbn [In]; lia | cbn [In]; lia].
Qed.

Lemma bc_iter_W : forall fr cs C A7 A m7 m md vm regs FL (s bsc datas nc spat rng pa parr ba barr w h minv maxv bil idx : Z) (pixes datad : Z -> Z) (S : TSet) (g3 : word),
  Cok C -> W C A m (with_vmmaps vm md) -> frm_zero cs -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 5120 <= s)%Z -> (s <= c_top C)%Z ->
  bc_cst A7 m7 bsc datas nc spat rng w h minv maxv -> (spat mod 16 = 0)%Z -> kcell_ok spat 11 m7 -> kcell_ok rng 256 m7 -> bc_fl_ok FL ->
  (0 <= idx < 10)%Z ->
  bc_inv C A7 A m7 m s pa parr ba barr w h idx pixes datad (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h) ->
  bc_kr regs s spat rng g3 -> getr regs 9 = Z_to_bv 64 idx -> bc_fsc fr ->
  forall (kR bR : Z), aroom A vm kR bR -> (RK_it <= kR)%Z -> (RB_it w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (pixes' datad' : Z -> Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     bc_inv C A7 A' m7 m' s pa parr ba barr w h (idx + 1) pixes' datad' (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h) ->
     bc_kr regs' s spat rng g3 -> getr regs' 9 = Z_to_bv 64 (idx + 1) -> pass_fp fr fr' ->
     aroom A' vm' (kR - RK_it) (bR - RB_it w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (Z_to_bv 64 (if (idx =? 9)%Z then 238888 else 237624)) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 237624) m al_rom) (with_vmmaps vm md)) S.
Proof.
  intros fr cs C A7 A m7 m md vm regs FL s bsc datas nc spat rng pa parr ba barr w h minv maxv bil idx pixes datad S g3
    CK HW FZ Hs16 Hstk Htop CST Hsp16 KS KG FLOK Hidx INV KRG R9 FSC kR bR AR HkR HbR K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. cbv [ll_img LLU16 snd] in Cimg.
  destruct CST as (HOKt & HOKd & Hw1 & Hh1 & PXb & Lb & Lds & Hnc & Lnc & NCV & Hmin & Hmax & Hsp & Lsp & Hrg & Lrg).
  destruct INV as (SL & PM & CLs & PCs & PB & N1 & N2 & N3 & N4 & MEM & LEQ & NEpb & DIST & NIN).
  destruct KRG as (G2 & G4 & G8 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27 & G3).
  apply fl3_split in CLs as [CF CX]. unfold bc_fx in CX.
  pose proof PXb as (Hb0 & Hb64 & _).
  pose proof HOKt as (DV & Hwt & Hht & Hszt). pose proof HOKd as (_ & Hwd & Hhd & Hszd).
  pose proof (wpl_of_range (w + 22) 8 ltac:(lia) DV) as WPt. pose proof (wpl_of_range w 8 ltac:(lia) DV) as WPd.
  pose proof (wf_data _ (proj1 (proj2 (proj2 PXb)))) as Hds. cbn [p_data hdv] in Hds.
  pose proof (SL _ _ Lb) as LAb. pose proof (SL _ _ Lds) as LAds. pose proof (SL _ _ Lnc) as LAnc.
  pose proof (SL _ _ Lsp) as LAsp. pose proof (SL _ _ Lrg) as LArg.
  destruct (blk_range C A m _ _ _ CK HW LAb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
  destruct (blk_range C A m _ _ _ CK HW LAds ltac:(nia)) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  destruct (blk_range C A m _ _ _ CK HW LAnc ltac:(lia)) as [Gnc TOPnc]. rewrite u_Z2bv in Gnc, TOPnc by lia.
  destruct (blk_range C A m _ _ _ CK HW LAsp ltac:(lia)) as [Gsp TOPsp]. rewrite u_Z2bv in Gsp, TOPsp by lia.
  destruct (blk_range C A m _ _ _ CK HW LArg ltac:(lia)) as [Grg TOPrg]. rewrite u_Z2bv in Grg, TOPrg by lia.
  assert (Rbsc : rdn SEGS m (Z_to_bv 64 (s - 296)) 8 = Some (Z_to_le_bytes 8 bsc)) by cell_from CX.
  assert (Hs47 : (s <= 2 ^ 47)%Z) by lia.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | exact (bc_N al_rom (mkFP fr cs) regs m s bsc ltac:(lia) ltac:(lia) Rbsc G2) |].
  intros fin (r1 & M1 & -> & -> & B1 & B2 & B10 & B11 & AGB).
  assert (PXb1 : PIXat m bsc (hdv (w + 22) (h + 22) 8 0 datas)).
  { eapply PIXat_frame; [exact PXb|]. intros x Hx. apply (bc_livk_at A7 m7 m bsc 64 x (proj2 PM) Lb); lia. }
  assert (HkR1 : (RK_pixcopy <= kR)%Z) by (unfold RK_it, RK_pix in HkR; lia).
  assert (HbR1 : (RB_pixT (4 * (wpl_of (w + 22) 8 * (h + 22))) + RB_cmapT 0 <= bR)%Z).
  { rewrite RB_cmapT_0. unfold RB_it in HbR. pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))). lia. }
  replace (Z_to_bv 64 0x1a314) with (0x1a314 : word) by (apply bv_eq; reflexivity).
  apply (pixCopy_sureT_W (fx := mkFP fr cs) C A m (with_vmmaps vm md) r1 (s - 320) bsc (w + 22) (h + 22) 8 0 datas cv0 (Z_to_bv 64 237636) S CK HW B2
           (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold LSF; lia) ltac:(lia) B1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) B10 B11 PXb1 HOKt ltac:(lia) ltac:(lia) LAb LAds (or_introl eq_refl) kR bR AR HkR1 HbR1).
  intros A2 m2 vm2 r2 W2 CS2 PM2 (pixt & cd & datat & R10 & PTN) AR2.
  rewrite wv_wv in W2 |- *.
  destruct PTN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0 & K0 & L00 & K00 & L1 & K1 & PXt & CMR).
  destruct CMR as [[Hcd LEQ2] | (ad & CMOK & _)]; [| destruct CMOK as [CMd _]; cbn [cv0 c_d] in CMd; lia]. subst cd.
  pose proof (agree_of_FRM C (s - 320) m m2 (s - 320) 320 [] CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia)) as AG2.
  keep_cells CX AG2 CX2.
  pose proof (fl_keep FL (s - 320) m m2 [] FLOK ltac:(lia) ltac:(lia) (Forall_nil _) AG2 CF) as CF2.
  assert (Hk : (0 <= nc_val minv maxv idx <= 255)%Z) by (apply nc_val_rng; lia).
  assert (Rk : rdn SEGS m2 (Z_to_bv 64 (nc + 4 * idx)) 4 = Some (Z_to_le_bytes 4 (nc_val minv maxv idx))).
  { rewrite (LIVK_rdn SEGS A m m2 (Z_to_bv 64 nc) 40 (nc + 4 * idx) 4 (proj2 PM2) LAnc) by (rewrite u_Z2bv by lia; lia).
    rewrite (LIVK_rdn SEGS A7 m7 m (Z_to_bv 64 nc) 40 (nc + 4 * idx) 4 (proj2 PM) Lnc) by (rewrite u_Z2bv by lia; lia).
    exact (NCV idx ltac:(lia)). }
  eapply rz_reach; [exact (w_pure _ _ _ _ W2) |
    exact (bc_O al_rom (mkFP fr cs) r2 m2 s pixt nc idx datat (wpl_of (w + 22) 8) (nc_val minv maxv idx) h ltac:(lia) Hs16 Gp ltac:(lia)
             (bc_m16_8 _ ALp) ltac:(lia) ltac:(lia) Hidx ltac:(lia) ltac:(lia) Hk ltac:(lia)
             (PIX_rd_data SEGS m2 pixt _ PXt) (PIX_rd_wpl SEGS m2 pixt _ PXt) Rk ltac:(cell_from CX2) ltac:(cell_from CX2) ltac:(cell_from CX2) ltac:(cell_from CX2)
             (W_sok_win C A2 m2 _ (s - 320) 320 CK W2 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R10 FZ) |].
  intros fin (r3 & M3 & -> & RI3 & C280 & C208 & C200 & C176 & O1 & O2 & O9 & O10 & O11 & O24 & O25 & O29 & AGO).
  assert (SLA2 : sub_live A A2) by exact (sub_live_new2 A A2 (Z_to_bv 64 pixt) (Z_to_bv 64 datat) _ _ L0 K0 L1 K1 LEQ2).
  assert (SL2 : sub_live A7 A2) by exact (sub_live_trans _ _ _ SL SLA2).
  pose proof (POSTM_mono C A (s - 320) s m m2 ltac:(lia) PM2) as PMA2.
  destruct (rinv_WP2 C A A2 m2 _ M3 _ s CK W2 SLA2 Htop RI3) as [W3 PMA3].
  { repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia. }
  pose proof (POSTM_trans C A s m m2 M3 PMA2 PMA3) as PMA3'. clear PMA3.
  assert (AG3 : agree_win (s - 320) 320 [(40%Z, 8%Z); (112%Z, 16%Z); (144%Z, 8%Z)] m2 M3).
  { apply (agree_of_rinv _ _ _ _ _ _ RI3).
    apply Forall_cons; [right; exists (40, 8)%Z; cbn [In fst snd]; split; [left; reflexivity | lia] |].
    apply Forall_cons; [right; exists (112, 16)%Z; cbn [In fst snd]; split; [right; left; reflexivity | lia] |].
    apply Forall_cons; [right; exists (144, 8)%Z; cbn [In fst snd]; split; [right; right; left; reflexivity | lia] |].
    apply Forall_nil. }
  keep_cells CX2 AG3 CX3.
  pose proof (fl_keep FL (s - 320) m2 M3 [(40%Z, 8%Z); (112%Z, 16%Z); (144%Z, 8%Z)] FLOK ltac:(lia) ltac:(lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) AG3 CF2) as CF3.
  assert (CI3 : cellsAt SEGS M3 (s - 320) [(40%Z, 8%nat, idx)]).
  { unfold cellsAt.
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 40)%Z with (s - 280)%Z by lia; exact C280 |].
    apply Forall_nil. }
  assert (CO3 : cellsAt SEGS M3 (s - 320) [(112%Z, 8%nat, datat); (120%Z, 8%nat, bc_cptr); (144%Z, 8%nat, pixt)]).
  { unfold cellsAt.
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 112)%Z with (s - 208)%Z by lia; exact C208 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 120)%Z with (s - 200)%Z by lia; exact C200 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 144)%Z with (s - 176)%Z by lia; exact C176 |].
    apply Forall_nil. }
  assert (KSm : kcell_ok spat 11 m) by exact (kc_keep A7 m7 m spat 11 44 KS (proj2 PM) Lsp ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (KGm : kcell_ok rng 256 m) by exact (kc_keep A7 m7 m rng 256 1024 KG (proj2 PM) Lrg ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (LA2ds : live A2 (Z_to_bv 64 datas) = Some (4 * (wpl_of (w + 22) 8 * (h + 22)))%Z) by exact (SLA2 _ _ LAds).
  assert (LA2sp : live A2 (Z_to_bv 64 spat) = Some 44%Z) by exact (SLA2 _ _ LAsp).
  assert (LA2rg : live A2 (Z_to_bv 64 rng) = Some 1024%Z) by exact (SLA2 _ _ LArg).
  pose proof (ai_live_hull A m _ _ _ (w_inv _ _ _ _ HW) LAds) as (_ & ALds & _). rewrite u_Z2bv in ALds by lia.
  assert (Hlt : (0 < 4 * (wpl_of (w + 22) 8 * (h + 22)))%Z) by nia.
  assert (DTS : bc_or (datat + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= datas)%Z (datas + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= datat)%Z).
  { unfold bc_or. apply (exW_blk_apart C A2 m2 _ datat datas _ _ CK W2 K1 LA2ds); [intro E; rewrite E in K0; congruence | lia | lia | lia | lia]. }
  assert (DTP : bc_or (datat + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= spat)%Z (spat + 44 <= datat)%Z).
  { unfold bc_or. apply (exW_blk_apart C A2 m2 _ datat spat _ _ CK W2 K1 LA2sp); [intro E; rewrite E in K0; congruence | lia | lia | lia | lia]. }
  assert (DTR : bc_or (datat + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= rng)%Z (rng + 1024 <= datat)%Z).
  { unfold bc_or. apply (exW_blk_apart C A2 m2 _ datat rng _ _ CK W2 K1 LA2rg); [intro E; rewrite E in K0; congruence | lia | lia | lia | lia]. }
  assert (DTC : bc_or (datat + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= bc_chalf)%Z (bc_chalf + 8 <= datat)%Z).
  { unfold bc_or. pose proof (exW_blk_img_apart C A2 m2 _ datat _ CK W2 K1 Hlt ltac:(lia) ltac:(lia) ltac:(cbv [ll_img LLU16 fst snd]; lia)) as HI.
    cbv [ll_img LLU16 fst snd] in HI. unfold bc_chalf. lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ W3) |
    exact (bc_hpass al_rom fr cs r3 M3 s datas datat (wpl_of (w + 22) 8) w h spat rng (nc_val minv maxv idx) FZ FSC ltac:(lia) Hs16 Hw1 Hh1 ltac:(lia) ltac:(lia) eq_refl Hszt
             Gds ltac:(lia) (bc_m16_4 _ ALds) Gd ltac:(lia) (bc_m16_4 _ ALd) Gsp ltac:(lia) (bc_m16_4 _ Hsp16) Grg ltac:(lia) Hk
             DTS ltac:(lia) DTP DTR DTC
             (rdb_W C A2 M3 _ datas _ CK W3 LA2ds ltac:(lia) ltac:(lia))
             (exW_sok_blk SEGS C A2 M3 _ datat _ datat (Z.to_nat (4 * (wpl_of (w + 22) 8 * (h + 22)))) p16_segs CK W3 K1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia))
             (kc_keep A m M3 spat 11 44 KSm (proj2 PMA3') LAsp ltac:(lia) ltac:(lia) ltac:(lia))
             (kc_keep A m M3 rng 256 1024 KGm (proj2 PMA3') LArg ltac:(lia) ltac:(lia) ltac:(lia))
             (fun j Hj => W_img16 C A2 M3 _ j W3 ltac:(unfold bc_chalf in Hj; lia))
             ltac:(cell_from CX3) ltac:(cell_from CX3) ltac:(cell_from CX3) ltac:(cell_from CO3) ltac:(cell_from CO3) ltac:(cell_from CX3) ltac:(cell_from CX3)
             O2 ltac:(csr; reflexivity) O9 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) O24 O25 ltac:(csr; reflexivity) ltac:(csr; reflexivity) O29) |].
  intros fin (fr4 & cs4 & r4 & M4 & -> & FZ4 & RI4 & AG4 & PF4).
  unfold HPL in AG4.
  destruct (rinv_WP2 C A A2 M3 _ M4 _ s CK W3 SLA2 Htop RI4) as [W4 PMA4].
  { apply Forall_cons; [|apply Forall_nil]. right. exists (Z_to_bv 64 datat), (4 * (wpl_of (w + 22) 8 * (h + 22)))%Z.
    split; [exact K1|]. split; [exact K0|]. split; [exact K00|]. cbn [fst snd]. rewrite u_Z2bv by lia. lia. }
  pose proof (POSTM_trans C A s m M3 M4 PMA3' PMA4) as PMA4'. clear PMA4.
  assert (AG4f : agree_win (s - 320) 320 [] M3 M4).
  { apply (agree_of_rinv _ _ _ _ _ _ RI4). apply Forall_cons; [|apply Forall_nil]. left. cbn [fst snd]. lia. }
  keep_cells CX3 AG4f CX4. keep_cells CO3 AG4f CO4. keep_cells CI3 AG4f CI4.
  pose proof (fl_keep FL (s - 320) M3 M4 [] FLOK ltac:(lia) ltac:(lia) (Forall_nil _) AG4f CF3) as CF4.
  eapply rz_reach; [exact (w_pure _ _ _ _ W4) | exact (bc_P al_rom (mkFP fr4 cs4) r4 M4 s w h ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cell_from CX4) ltac:(cell_from CX4) ltac:(csr; reflexivity)) |].
  intros fin (r5 & M5 & -> & EM5 & P1 & P2 & P10 & P11 & P12 & AGP). subst M5.
  replace (Z_to_bv 64 0x192d0) with (0x192d0 : word) by (apply bv_eq; reflexivity).
  assert (X4 : getr r5 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (RK1 : ret_ok (Z_to_bv 64 238256)) by (apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity).
  apply (pixCreate_sureT_W (fx := mkFP fr4 cs4) C A2 M4 (with_vmmaps vm2 md) r5 (s - 320) w h 8 (Z_to_bv 64 238256) S CK W4 P2
           (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl) ltac:(unfold LSF; lia) ltac:(lia) P1 RK1
           X4 P10 P11 P12 Hw1 Hh1 HOKd (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of (w + 22) 8 * (h + 22))) + RB_cmapT 0)) AR2
           ltac:(unfold RK_it in HkR; lia) ltac:(rewrite RB_cmapT_0; unfold RB_it in HbR; lia)).
  intros A3 m5 vm3 r6 pxd dtd W5 CSK5 PM5 R10d PRN AR3.
  rewrite wv_wv in W5 |- *.
  destruct PRN as (Gq & TOPq & ALq & Gdd & TOPdd & ALdd & NEqd & N0q & N0d & N00q & N00d & LQ & LD & LEQ3 & PXd & _).
  cbn [p_wpl p_h set_data pix_hdr] in TOPdd, LD.
  assert (SL23 : sub_live A2 A3) by exact (sub_live_new2 A2 A3 (Z_to_bv 64 pxd) (Z_to_bv 64 dtd) _ _ N0q N0d LQ LD LEQ3).
  assert (SLA3 : sub_live A A3) by exact (sub_live_trans _ _ _ SLA2 SL23).
  pose proof (POSTM_trans C A s m M4 m5 PMA4' (POSTM_sub C A A2 s M4 m5 SLA2 (POSTM_mono C A2 (s - 320) s M4 m5 ltac:(lia) PM5))) as PMA5.
  pose proof (agree_of_FRM C (s - 320) M4 m5 (s - 320) 320 [] CK (proj1 PM5) ltac:(lia) ltac:(lia) ltac:(lia)) as AG5.
  keep_cells CX4 AG5 CX5. keep_cells CO4 AG5 CO5. keep_cells CI4 AG5 CI5.
  pose proof (fl_keep FL (s - 320) M4 m5 [] FLOK ltac:(lia) ltac:(lia) (Forall_nil _) AG5 CF4) as CF5.
  eapply rz_reach; [exact (w_pure _ _ _ _ W5) |
    exact (bc_Q al_rom (mkFP fr4 cs4) r6 m5 s pxd dtd (wpl_of w 8) h ltac:(lia) Hs16 Gq ltac:(lia) (bc_m16_8 _ ALq) ltac:(lia) ltac:(lia) ltac:(lia)
             (PIX_rd_data SEGS m5 pxd _ PXd) (PIX_rd_wpl SEGS m5 pxd _ PXd) ltac:(cell_from CX5) ltac:(cell_from CX5)
             (W_sok_win C A3 m5 _ (s - 320) 320 CK W5 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity) R10d FZ4) |].
  intros fin (r7 & M6 & -> & RI6 & C264 & C232 & U1 & U2 & U10 & U11 & AGQ).
  destruct (rinv_WP2 C A A3 m5 _ M6 _ s CK W5 SLA3 Htop RI6) as [W6 PMA6].
  { repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia. }
  pose proof (POSTM_trans C A s m m5 M6 PMA5 PMA6) as PMA6'. clear PMA6.
  assert (AG6 : agree_win (s - 320) 320 [(56%Z, 8%Z); (88%Z, 8%Z)] m5 M6).
  { apply (agree_of_rinv _ _ _ _ _ _ RI6).
    apply Forall_cons; [right; exists (56%Z, 8%Z); cbn [In fst snd]; split; [left; reflexivity | lia] |].
    apply Forall_cons; [right; exists (88%Z, 8%Z); cbn [In fst snd]; split; [right; left; reflexivity | lia] |].
    apply Forall_nil. }
  keep_cells CX5 AG6 CX6. keep_cells CO5 AG6 CO6. keep_cells CI5 AG6 CI6.
  pose proof (fl_keep FL (s - 320) m5 M6 [(56%Z, 8%Z); (88%Z, 8%Z)] FLOK ltac:(lia) ltac:(lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) AG6 CF5) as CF6.
  assert (CQ6 : cellsAt SEGS M6 (s - 320) [(56%Z, 8%nat, pxd); (88%Z, 8%nat, dtd)]).
  { unfold cellsAt.
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 56)%Z with (s - 264)%Z by lia; exact C264 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 88)%Z with (s - 232)%Z by lia; exact C232 |].
    apply Forall_nil. }
  assert (LDt3 : live A3 (Z_to_bv 64 datat) = Some (4 * (wpl_of (w + 22) 8 * (h + 22)))%Z) by exact (SL23 _ _ K1).
  assert (LA3sp : live A3 (Z_to_bv 64 spat) = Some 44%Z) by exact (SL23 _ _ LA2sp).
  assert (LA3rg : live A3 (Z_to_bv 64 rng) = Some 1024%Z) by exact (SL23 _ _ LA2rg).
  assert (Hld : (0 < 4 * (wpl_of w 8 * h))%Z) by nia.
  assert (DDT : bc_or (dtd + 4 * (wpl_of w 8 * h) <= datat)%Z (datat + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= dtd)%Z).
  { unfold bc_or. apply (exW_blk_apart C A3 m5 _ dtd datat _ _ CK W5 LD LDt3); [exact (zne_live A2 datat dtd _ K1 N0d) | lia | lia | lia | lia]. }
  assert (DDP : bc_or (dtd + 4 * (wpl_of w 8 * h) <= spat)%Z (spat + 44 <= dtd)%Z).
  { unfold bc_or. apply (exW_blk_apart C A3 m5 _ dtd spat _ _ CK W5 LD LA3sp); [exact (zne_live A2 spat dtd _ LA2sp N0d) | lia | lia | lia | lia]. }
  assert (DDR : bc_or (dtd + 4 * (wpl_of w 8 * h) <= rng)%Z (rng + 1024 <= dtd)%Z).
  { unfold bc_or. apply (exW_blk_apart C A3 m5 _ dtd rng _ _ CK W5 LD LA3rg); [exact (zne_live A2 rng dtd _ LA2rg N0d) | lia | lia | lia | lia]. }
  assert (DDC : bc_or (dtd + 4 * (wpl_of w 8 * h) <= bc_chalf)%Z (bc_chalf + 8 <= dtd)%Z).
  { unfold bc_or. pose proof (exW_blk_img_apart C A3 m5 _ dtd _ CK W5 LD Hld ltac:(lia) ltac:(lia) ltac:(cbv [ll_img LLU16 fst snd]; lia)) as HI.
    cbv [ll_img LLU16 fst snd] in HI. unfold bc_chalf. lia. }
  assert (FSC4 : bc_fsc fr4) by exact (bc_fsc_pass fr fr4 FSC PF4).
  eapply rz_reach; [exact (w_pure _ _ _ _ W6) |
    exact (bc_vpass al_rom fr4 cs4 r7 M6 s datat dtd (wpl_of (w + 22) 8) (wpl_of w 8) w h spat rng (nc_val minv maxv idx) FZ4 FSC4 ltac:(lia) Hs16 Hw1 Hh1 ltac:(lia) ltac:(lia) eq_refl Hszt eq_refl
             Gd ltac:(lia) (bc_m16_4 _ ALd) Gdd ltac:(lia) (bc_m16_4 _ ALdd) Gsp ltac:(lia) (bc_m16_4 _ Hsp16) Grg ltac:(lia) Hk
             DDT ltac:(lia) DDP DDR DDC
             (rdb_W C A3 M6 _ datat _ CK W6 LDt3 ltac:(lia) ltac:(lia))
             (exW_sok_blk SEGS C A3 M6 _ dtd _ dtd (Z.to_nat (4 * (wpl_of w 8 * h))) p16_segs CK W6 LD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia))
             (kc_keep A m M6 spat 11 44 KSm (proj2 PMA6') LAsp ltac:(lia) ltac:(lia) ltac:(lia))
             (kc_keep A m M6 rng 256 1024 KGm (proj2 PMA6') LArg ltac:(lia) ltac:(lia) ltac:(lia))
             (fun j Hj => W_img16 C A3 M6 _ j W6 ltac:(unfold bc_chalf in Hj; lia))
             ltac:(cell_from CQ6) ltac:(cell_from CX6) ltac:(cell_from CO6) ltac:(cell_from CO6) ltac:(cell_from CX6) ltac:(cell_from CX6)
             U1 U2 ltac:(csr; reflexivity) ltac:(csr; reflexivity) U10 U11 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) |].
  intros fin (fr8 & cs8 & r8 & M7 & -> & FZ8 & RI7 & AG7 & PF8).
  unfold VPL in AG7.
  assert (N0dA : live A (Z_to_bv 64 dtd) = None) by exact (live_none_sub A A2 _ SLA2 N0d).
  destruct (rinv_WP2 C A A3 M6 _ M7 _ s CK W6 SLA3 Htop RI7) as [W7 PMA7].
  { apply Forall_cons; [|apply Forall_nil]. right. exists (Z_to_bv 64 dtd), (4 * (wpl_of w 8 * h))%Z.
    split; [exact LD|]. split; [exact N0dA|]. split; [exact N00d|]. cbn [fst snd]. rewrite u_Z2bv by lia. lia. }
  pose proof (POSTM_trans C A s m M6 M7 PMA6' PMA7) as PMA7'. clear PMA7.
  assert (AG7f : agree_win (s - 320) 320 [] M6 M7).
  { apply (agree_of_rinv _ _ _ _ _ _ RI7). apply Forall_cons; [|apply Forall_nil]. left. cbn [fst snd]. lia. }
  keep_cells CX6 AG7f CX7. keep_cells CO6 AG7f CO7. keep_cells CI6 AG7f CI7. keep_cells CQ6 AG7f CQ7.
  pose proof (fl_keep FL (s - 320) M6 M7 [] FLOK ltac:(lia) ltac:(lia) (Forall_nil _) AG7f CF6) as CF7.
  eapply rz_reach; [exact (w_pure _ _ _ _ W7) | exact (bc_R al_rom (mkFP fr8 cs8) r8 M7 s ltac:(lia) ltac:(csr; reflexivity)) |].
  intros fin (r9 & M8 & -> & EM8 & RR1 & RR2 & RR10 & AGR). subst M8.
  assert (DtP : bc_or (datat + 4 * (wpl_of (w + 22) 8 * (h + 22)) <= pixt)%Z (pixt + 64 <= datat)%Z).
  { unfold bc_or. apply (exW_blk_apart C A2 m2 _ datat pixt _ _ CK W2 K1 L1); [intro E; apply NEpd; symmetry; exact E | lia | lia | lia | lia]. }
  assert (DdP : bc_or (dtd + 4 * (wpl_of w 8 * h) <= pixt)%Z (pixt + 64 <= dtd)%Z).
  { unfold bc_or. apply (exW_blk_apart C A3 m5 _ dtd pixt _ _ CK W5 LD (SL23 _ _ L1)); [exact (zne_live A2 pixt dtd _ L1 N0d) | lia | lia | lia | lia]. }
  assert (PXt7 : PIXat M7 pixt (hdv (w + 22) (h + 22) 8 0 datat)).
  { eapply PIXat_frame; [exact PXt|]. intros x Hx.
    rewrite (rinv_keep _ M6 M7 pixt 64 RI7 ltac:(apply Forall_cons; [exact DdP | apply Forall_nil]) x Hx).
    rewrite (rinv_keep _ m5 M6 pixt 64 RI6 ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) x Hx).
    rewrite (bc_livk_at A2 M4 m5 pixt 64 x (proj2 PM5) L1 ltac:(lia) ltac:(lia) Hx).
    rewrite (rinv_keep _ M3 M4 pixt 64 RI4 ltac:(apply Forall_cons; [exact DtP | apply Forall_nil]) x Hx).
    exact (rinv_keep _ m2 M3 pixt 64 RI3 ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) x Hx). }
  replace (Z_to_bv 64 0x1982c) with (0x1982c : word) by (apply bv_eq; reflexivity).
  assert (RK2 : ret_ok (Z_to_bv 64 237592)) by (apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity).
  assert (X4b : getr r9 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (ALpp : ((s - 176) mod 8 = 0)%Z) by exact (bc_msub s 176 8 ltac:(lia) (bc_m16_8 _ Hs16) eq_refl).
  apply (pixDestroy_keep_W (fx := mkFP fr8 cs8) C A3 M7 (with_vmmaps vm3 md) r9 (s - 320) (s - 176) pixt 0 0 (4 * (wpl_of (w + 22) 8 * (h + 22)))
           (hdv (w + 22) (h + 22) 8 0 datat) cv0 (Z_to_bv 64 237592) S CK W7 RR2 (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl)
           ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) RR1 RK2 X4b ALpp RR10 ltac:(cell_from CO7) PXt7 eq_refl eq_refl eq_refl
           (SL23 _ _ L1) L00 LDt3 K00 Hlt ltac:(cbn [p_data hdv]; intro E; apply NEpd; symmetry; exact E) (or_introl eq_refl)).
  intros A4 m8 vm4 r10 W8 CSK8 PD8 PM8 Rpp8 KEEP8 RT8.
  rewrite wv_wv in W8 |- *.
  unfold V2LeptPixDestroy.pixd_post in PD8. cbn [p_data hdv c_arr cv0] in PD8.
  destruct PD8 as (PD1 & PD2 & _ & PD4).
  assert (DT4 : live A4 (Z_to_bv 64 datat) = None) by exact (PD2 ltac:(lia)).
  assert (LEQ4 : forall q, q <> Z_to_bv 64 pixt -> q <> Z_to_bv 64 datat -> live A4 q = live A3 q).
  { intros q H1 H2. apply PD4; [exact H1 | intros _; exact H2 | intros HH; exfalso; apply HH; reflexivity]. }
  assert (SLA4 : sub_live A A4).
  { intros q k Hq. rewrite LEQ4; [exact (SLA3 _ _ Hq) | intro E; subst q; congruence | intro E; subst q; congruence]. }
  assert (SL74 : sub_live A7 A4) by exact (sub_live_trans _ _ _ SL SLA4).
  pose proof (RT8 _ _ AR3 ltac:(unfold RK_it in HkR; lia) ltac:(rewrite RB_cmapT_0; unfold RB_it in HbR; lia)) as AR4.
  pose proof (POSTM_trans C A s m M7 m8 PMA7' (POSTM_sub C A A4 s M7 m8 SLA4 (POSTM_mono C A4 (s - 176 + 8) s M7 m8 ltac:(lia) PM8))) as PMA8.
  assert (AG8 : agree_win (s - 320) 320 [(144%Z, 8%Z)] M7 m8).
  { intros a Ha Hro. specialize (Hro (144%Z, 8%Z) ltac:(left; reflexivity)). cbn [fst snd] in Hro.
    destruct (Z_lt_ge_dec (u a) (s - 176)) as [Hlo|Hhi].
    - apply KEEP8. lia.
    - apply (agree_of_FRM C (s - 176 + 8) M7 m8 (s - 176 + 8) 168 [] CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia)); [lia | intros r []]. }
  keep_cells CX7 AG8 CX8. keep_cells CI7 AG8 CI8. keep_cells CQ7 AG8 CQ8.
  pose proof (fl_keep FL (s - 320) M7 m8 [(144%Z, 8%Z)] FLOK ltac:(lia) ltac:(lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) AG8 CF7) as CF8.
  destruct PB as (Hpa & Hparr & Hba & Hbarr & LApa & LAparr & LAba & LAbarr & C0pa & C0parr & C0ba & C0barr).
  destruct (blk_range C A m _ _ _ CK HW LApa ltac:(lia)) as [Gpa TOPpa]. rewrite u_Z2bv in Gpa, TOPpa by lia.
  destruct (blk_range C A m _ _ _ CK HW LAparr ltac:(lia)) as [Gparr TOPparr]. rewrite u_Z2bv in Gparr, TOPparr by lia.
  destruct (blk_range C A m _ _ _ CK HW LAba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
  eapply rz_reach; [exact (w_pure _ _ _ _ W8) | exact (bc_S al_rom (mkFP fr8 cs8) r10 m8 s pa pxd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cell_from CX8) ltac:(cell_from CQ8) ltac:(csr; reflexivity)) |].
  intros fin (r11 & M9 & -> & EM9 & S1 & S2 & S10 & S11 & S12 & AGS). subst M9.
  assert (PC8 : pixa_cells m8 pa parr ba barr idx).
  { apply (pixa_cells_keep m m8 pa parr ba barr idx PCs); try lia.
    - intros a Ha. exact (bc_livk_at A m m8 pa 32 a (proj2 PMA8) LApa ltac:(lia) ltac:(lia) Ha).
    - intros a Ha. exact (bc_livk_at A m m8 ba 24 a (proj2 PMA8) LAba ltac:(lia) ltac:(lia) Ha). }
  assert (PB8 : pixa_blks C A4 pa parr ba barr).
  { unfold pixa_blks.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (SLA4 _ _ LApa)|]. split; [exact (SLA4 _ _ LAparr)|]. split; [exact (SLA4 _ _ LAba)|]. split; [exact (SLA4 _ _ LAbarr)|].
    split; [exact C0pa|]. split; [exact C0parr|]. split; [exact C0ba|]. exact C0barr. }
  assert (RK3 : ret_ok (Z_to_bv 64 237608)) by (apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity).
  apply (pixaAddPix_ins_W (mkFP fr8 cs8) C A7 A4 m8 (with_vmmaps vm4 md) r11 (s - 320) pa parr ba barr idx pxd (Z_to_bv 64 237608) S CK W8 SL74 S2
           ltac:(lia) ltac:(lia) S1 RK3 S10 S11 S12 PC8 Hidx PB8 N1 N2 ltac:(lia)).
  intros m9 r12 W9 CSK9 PM9 KEEP9 PC9 RP9 R10b.
  pose proof (agree_of_FRM C (s - 320) m8 m9 (s - 320) 320 [] CK (proj1 PM9) ltac:(lia) ltac:(lia) ltac:(lia)) as AG9.
  keep_cells CX8 AG9 CX9. keep_cells CI8 AG9 CI9.
  pose proof (fl_keep FL (s - 320) m8 m9 [] FLOK ltac:(lia) ltac:(lia) (Forall_nil _) AG9 CF8) as CF9.
  assert (NEppa : parr <> pa) by (intro E; rewrite E in LAparr; congruence).
  assert (Dparr_pa : bc_or (parr + 80 <= pa)%Z (pa + 32 <= parr)%Z) by (unfold bc_or; apply (exW_blk_apart C A m _ parr pa _ _ CK HW LAparr LApa NEppa); lia).
  set (pixes' := fun i => if (i =? idx)%Z then pxd else pixes i).
  set (datad' := fun i => if (i =? idx)%Z then dtd else datad i).
  assert (NQt : Z_to_bv 64 pxd <> Z_to_bv 64 pixt) by (intro E; rewrite E in N0q; congruence).
  assert (NQd : Z_to_bv 64 pxd <> Z_to_bv 64 datat) by (intro E; rewrite E in N0q; congruence).
  assert (NDt : Z_to_bv 64 dtd <> Z_to_bv 64 pixt) by (intro E; rewrite E in N0d; congruence).
  assert (NDd : Z_to_bv 64 dtd <> Z_to_bv 64 datat) by (intro E; rewrite E in N0d; congruence).
  assert (LQ4 : live A4 (Z_to_bv 64 pxd) = Some 64%Z) by (rewrite LEQ4 by assumption; exact LQ).
  assert (LD4 : live A4 (Z_to_bv 64 dtd) = Some (4 * (wpl_of w 8 * h))%Z) by (rewrite LEQ4 by assumption; exact LD).
  assert (NEqpa : pxd <> pa) by exact (zne_live A2 pa pxd _ (SLA2 _ _ LApa) N0q).
  assert (NEqparr : pxd <> parr) by exact (zne_live A2 parr pxd _ (SLA2 _ _ LAparr) N0q).
  assert (DQpa : bc_or (pxd + 64 <= pa)%Z (pa + 32 <= pxd)%Z) by (unfold bc_or; apply (exW_blk_apart C A4 m8 _ pxd pa _ _ CK W8 LQ4 (SLA4 _ _ LApa) NEqpa); lia).
  assert (DQparr : bc_or (pxd + 64 <= parr)%Z (parr + 80 <= pxd)%Z) by (unfold bc_or; apply (exW_blk_apart C A4 m8 _ pxd parr _ _ CK W8 LQ4 (SLA4 _ _ LAparr) NEqparr); lia).
  assert (DdQ : bc_or (dtd + 4 * (wpl_of w 8 * h) <= pxd)%Z (pxd + 64 <= dtd)%Z).
  { unfold bc_or. apply (exW_blk_apart C A3 m5 _ dtd pxd _ _ CK W5 LD LQ ltac:(intro E; apply NEqd; symmetry; exact E)); lia. }
  assert (PXd9 : PIXat m9 pxd (hdv w h 8 0 dtd)).
  { eapply PIXat_frame; [exact PXd|]. intros x Hx.
    rewrite (KEEP9 x ltac:(lia) (out_of_sub pxd 64 parr 80 (parr + 8 * idx) 8 (u x) Hx DQparr ltac:(lia) ltac:(lia)) (out_of_sub pxd 64 pa 32 pa 4 (u x) Hx DQpa ltac:(lia) ltac:(lia))).
    rewrite (bc_livk_at A4 M7 m8 pxd 64 x (proj2 PM8) LQ4 ltac:(lia) ltac:(lia) Hx).
    rewrite (rinv_keep _ M6 M7 pxd 64 RI7 ltac:(apply Forall_cons; [exact DdQ | apply Forall_nil]) x Hx).
    exact (rinv_keep _ m5 M6 pxd 64 RI6 ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) x Hx). }
  assert (MEM' : forall i, (0 <= i < idx + 1)%Z -> bc_mem C A7 A4 m9 parr w h i (pixes' i) (datad' i)).
  { intros i Hi. unfold pixes', datad'. destruct (Z.eqb_spec i idx) as [->|Hne].
    - unfold bc_mem.
      split; [exact Gq|]. split; [exact TOPq|]. split; [exact Gdd|]. split; [exact TOPdd|]. split; [exact NEqd|].
      split; [exact (live_none_sub A7 A2 _ SL2 N0q)|]. split; [exact (live_none_sub A7 A2 _ SL2 N0d)|].
      split; [exact N00q|]. split; [exact N00d|]. split; [exact LQ4|]. split; [exact LD4|]. split; [exact PXd9 | exact RP9].
    - destruct (MEM i ltac:(lia)) as (Gpi & Tpi & Gdi & Tdi & NEi & N7p & N7d & N0p & N0dd & Lpi & Ldi & PXi & Rpi).
      destruct (NIN i ltac:(lia)) as [NINp _].
      assert (Dpa : bc_or (pixes i + 64 <= pa)%Z (pa + 32 <= pixes i)%Z).
      { unfold bc_or. apply (exW_blk_apart C A m _ (pixes i) pa _ _ CK HW Lpi LApa (nin_ne _ _ _ NINp ltac:(left; reflexivity))); lia. }
      assert (Dparr : bc_or (pixes i + 64 <= parr)%Z (parr + 80 <= pixes i)%Z).
      { unfold bc_or. apply (exW_blk_apart C A m _ (pixes i) parr _ _ CK HW Lpi LAparr (nin_ne _ _ _ NINp ltac:(right; left; reflexivity))); lia. }
      unfold bc_mem.
      split; [exact Gpi|]. split; [exact Tpi|]. split; [exact Gdi|]. split; [exact Tdi|]. split; [exact NEi|].
      split; [exact N7p|]. split; [exact N7d|]. split; [exact N0p|]. split; [exact N0dd|].
      split; [exact (SLA4 _ _ Lpi)|]. split; [exact (SLA4 _ _ Ldi)|].
      split.
      + eapply PIXat_frame; [exact PXi|]. intros x Hx.
        rewrite (KEEP9 x ltac:(lia) (out_of_sub (pixes i) 64 parr 80 (parr + 8 * idx) 8 (u x) Hx Dparr ltac:(lia) ltac:(lia)) (out_of_sub (pixes i) 64 pa 32 pa 4 (u x) Hx Dpa ltac:(lia) ltac:(lia))).
        exact (bc_livk_at A m m8 (pixes i) 64 x (proj2 PMA8) Lpi ltac:(lia) ltac:(lia) Hx).
      + rewrite (bc_rdn_keep m8 m9 (parr + 8 * i) 8 ltac:(lia) ltac:(zlia) (fun a Ha => KEEP9 a ltac:(zlia) ltac:(zlia) (out_of_sub parr 80 pa 32 pa 4 (u a) ltac:(zlia) Dparr_pa ltac:(lia) ltac:(lia)))).
        rewrite (LIVK_rdn SEGS A m m8 (Z_to_bv 64 parr) 80 (parr + 8 * i) 8 (proj2 PMA8) LAparr) by (rewrite u_Z2bv by lia; zlia).
        exact Rpi. }
  assert (LEQ' : forall q : word, ~ In q (map (Z_to_bv 64) [pa; parr; ba; barr]) ->
                   (forall i, (0 <= i < idx + 1)%Z -> q <> Z_to_bv 64 (pixes' i) /\ q <> Z_to_bv 64 (datad' i)) -> live A4 q = live A7 q).
  { intros q Hq Hn.
    destruct (Hn idx ltac:(lia)) as [Hq1 Hq2]. unfold pixes', datad' in Hq1, Hq2. rewrite Z.eqb_refl in Hq1, Hq2.
    destruct (decide (q = Z_to_bv 64 pixt)) as [->|Ht].
    { rewrite PD1. symmetry. exact (live_none_sub A7 A _ SL L0). }
    destruct (decide (q = Z_to_bv 64 datat)) as [->|Hd].
    { rewrite DT4. symmetry. exact (live_none_sub A7 A _ SL K0). }
    rewrite (LEQ4 q Ht Hd), (LEQ3 q Hq1 Hq2), (LEQ2 q Ht Hd).
    apply LEQ; [exact Hq|]. intros i Hi. destruct (Hn i ltac:(lia)) as [H1 H2]. unfold pixes', datad' in H1, H2.
    rewrite (proj2 (Z.eqb_neq i idx) ltac:(lia)) in H1, H2. split; assumption. }
  assert (DIST' : forall i j, (0 <= i < j)%Z -> (j < idx + 1)%Z -> datad' i <> datad' j /\ pixes' i <> pixes' j /\ pixes' i <> datad' j /\ datad' i <> pixes' j).
  { intros i j Hij Hj. unfold pixes', datad'. rewrite (proj2 (Z.eqb_neq i idx) ltac:(lia)).
    destruct (Z.eqb_spec j idx) as [->|Hne].
    - destruct (MEM i ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Lpi & Ldi & _).
      pose proof (SLA2 _ _ Lpi) as Lpi2. pose proof (SLA2 _ _ Ldi) as Ldi2.
      split; [exact (zne_live2 A2 _ _ _ Ldi2 N0d)|]. split; [exact (zne_live2 A2 _ _ _ Lpi2 N0q)|].
      split; [exact (zne_live2 A2 _ _ _ Lpi2 N0d) | exact (zne_live2 A2 _ _ _ Ldi2 N0q)].
    - exact (DIST i j Hij ltac:(lia)). }
  assert (NIN' : forall i, (0 <= i < idx + 1)%Z -> ~ In (Z_to_bv 64 (pixes' i)) (map (Z_to_bv 64) [pa; parr; ba; barr]) /\ ~ In (Z_to_bv 64 (datad' i)) (map (Z_to_bv 64) [pa; parr; ba; barr])).
  { intros i Hi. unfold pixes', datad'. destruct (Z.eqb_spec i idx) as [->|Hne].
    - pose proof (SLA2 _ _ LApa) as L2a. pose proof (SLA2 _ _ LAparr) as L2b. pose proof (SLA2 _ _ LAba) as L2c. pose proof (SLA2 _ _ LAbarr) as L2d.
      split; cbn [map In]; intros HH; repeat destruct HH as [HH|HH]; try (rewrite <- HH in N0q; congruence); try (rewrite <- HH in N0d; congruence); exact HH.
    - exact (NIN i ltac:(lia)). }
  assert (INV' : bc_inv C A7 A4 m7 m9 s pa parr ba barr w h (idx + 1) pixes' datad' (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h)).
  { unfold bc_inv.
    split; [exact SL74|].
    split; [exact (POSTM_trans C A7 s m7 m8 m9 (POSTM_trans C A7 s m7 m m8 PM (POSTM_sub C A7 A s m m8 SL PMA8)) (POSTM_mono C A7 (s - 320) s m8 m9 ltac:(lia) PM9))|].
    split; [exact (fl3_join m9 (s - 320) FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h CF9 CX9)|].
    split; [exact PC9|]. split; [exact PB8|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
    split; [exact MEM'|]. split; [exact LEQ'|]. split; [exact NEpb|]. split; [exact DIST' | exact NIN']. }
  assert (PF : pass_fp fr fr8) by exact (pass_fp_trans fr fr4 fr8 PF4 PF8).
  assert (AR' : aroom A4 vm4 (kR - RK_it) (bR - RB_it w h)).
  { apply (aroom_mono A4 vm4 _ _ _ _ AR4); unfold RK_it, RB_it in HkR, HbR |- *; rewrite ?RB_cmapT_0; lia. }
  destruct (Z.eq_dec idx 9) as [E9|N9].
  - subst idx.
    eapply rz_reach; [exact (w_pure _ _ _ _ W9) | exact (bc_T_last al_rom (mkFP fr8 cs8) r12 m9 s ltac:(lia) ltac:(cell_from CI9) ltac:(cell_from CX9) ltac:(csr; reflexivity)) |].
    intros fin (r13 & M10 & -> & EM10 & T2 & T9 & T10 & AGT). subst M10.
    apply (K fr8 cs8 A4 m9 vm4 r13 pixes' datad' W9 FZ8 INV'); [unfold bc_kr; split; [exact T2|]; do 10 (split; [csr; reflexivity|]); csr; reflexivity | exact T9 | exact PF | exact AR'].
  - eapply rz_reach; [exact (w_pure _ _ _ _ W9) | exact (bc_T_more al_rom (mkFP fr8 cs8) r12 m9 s idx ltac:(lia) ltac:(lia) ltac:(cell_from CI9) ltac:(cell_from CX9) ltac:(csr; reflexivity)) |].
    intros fin (r13 & M10 & -> & EM10 & T2 & T9 & T10 & AGT). subst M10.
    replace ((idx =? 9)%Z) with false in K by (symmetry; apply Z.eqb_neq; exact N9).
    apply (K fr8 cs8 A4 m9 vm4 r13 pixes' datad' W9 FZ8 INV'); [unfold bc_kr; split; [exact T2|]; do 10 (split; [csr; reflexivity|]); csr; reflexivity | exact T9 | exact PF | exact AR'].
Qed.

Lemma bc_loop_W : forall (n : nat) fr cs C A7 A m7 m md vm regs FL (s bsc datas nc spat rng pa parr ba barr w h minv maxv bil idx : Z) (pixes datad : Z -> Z) (S : TSet) (g3 : word),
  idx = (10 - Z.of_nat n)%Z -> (0 <= idx < 10)%Z ->
  Cok C -> W C A m (with_vmmaps vm md) -> frm_zero cs -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 5120 <= s)%Z -> (s <= c_top C)%Z ->
  bc_cst A7 m7 bsc datas nc spat rng w h minv maxv -> (spat mod 16 = 0)%Z -> kcell_ok spat 11 m7 -> kcell_ok rng 256 m7 -> bc_fl_ok FL ->
  bc_inv C A7 A m7 m s pa parr ba barr w h idx pixes datad (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h) ->
  bc_kr regs s spat rng g3 -> getr regs 9 = Z_to_bv 64 idx -> bc_fsc fr ->
  forall (kR bR : Z), aroom A vm kR bR -> ((10 - idx) * RK_it <= kR)%Z -> ((10 - idx) * RB_it w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (pixes' datad' : Z -> Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     bc_inv C A7 A' m7 m' s pa parr ba barr w h 10 pixes' datad' (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h) ->
     bc_kr regs' s spat rng g3 -> getr regs' 9 = Z_to_bv 64 10 -> pass_fp fr fr' ->
     aroom A' vm' (kR - (10 - idx) * RK_it) (bR - (10 - idx) * RB_it w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (Z_to_bv 64 238888) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 237624) m al_rom) (with_vmmaps vm md)) S.
Proof.
  induction n as [|n IH]; intros fr cs C A7 A m7 m md vm regs FL s bsc datas nc spat rng pa parr ba barr w h minv maxv bil idx pixes datad S g3
    Hn Hidx CK HW FZ Hs16 Hstk Htop CST Hsp16 KS KG FLOK INV KRG R9 FSC kR bR AR HkR HbR K; [cbn in Hn; lia|].
  assert (RK0 : (0 <= RK_it)%Z) by (unfold RK_it; room_consts; lia).
  assert (RB0 : (0 <= RB_it w h)%Z) by (unfold RB_it; pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 22) 8 * (h + 22)))); pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))); lia).
  apply (bc_iter_W fr cs C A7 A m7 m md vm regs FL s bsc datas nc spat rng pa parr ba barr w h minv maxv bil idx pixes datad S g3
           CK HW FZ Hs16 Hstk Htop CST Hsp16 KS KG FLOK Hidx INV KRG R9 FSC kR bR AR ltac:(nia) ltac:(nia)).
  intros fr' cs' A' m' vm' regs' pixes' datad' W' FZ' INV' KR' R9' PF' AR'.
  destruct (Z.eqb_spec idx 9) as [E9|N9].
  - assert (E10 : (idx + 1 = 10)%Z) by lia. rewrite E10 in INV', R9'.
    apply (K fr' cs' A' m' vm' regs' pixes' datad' W' FZ' INV' KR' R9' PF').
    replace (kR - (10 - idx) * RK_it)%Z with (kR - RK_it)%Z by (rewrite E9; lia).
    replace (bR - (10 - idx) * RB_it w h)%Z with (bR - RB_it w h)%Z by (rewrite E9; lia). exact AR'.
  - apply (IH fr' cs' C A7 A' m7 m' md vm' regs' FL s bsc datas nc spat rng pa parr ba barr w h minv maxv bil (idx + 1)%Z pixes' datad' S g3
             ltac:(lia) ltac:(lia) CK W' FZ' Hs16 Hstk Htop CST Hsp16 KS KG FLOK INV' KR' R9' (bc_fsc_pass fr fr' FSC PF') (kR - RK_it)%Z (bR - RB_it w h)%Z AR' ltac:(nia) ltac:(nia)).
    intros fr2 cs2 A2 m2 vm2 regs2 pixes2 datad2 W2 FZ2 INV2 KR2 R92 PF2 AR2.
    apply (K fr2 cs2 A2 m2 vm2 regs2 pixes2 datad2 W2 FZ2 INV2 KR2 R92 (pass_fp_trans _ _ _ PF' PF2)).
    replace (kR - (10 - idx) * RK_it)%Z with (kR - RK_it - (10 - (idx + 1)) * RK_it)%Z by ring.
    replace (bR - (10 - idx) * RB_it w h)%Z with (bR - RB_it w h - (10 - (idx + 1)) * RB_it w h)%Z by ring.
    exact AR2.
Qed.

(* [comment removed for export] *)
Lemma bc_comp_W : forall fr cs C A7 m7 md vm7 regs (FL : list cell) (s pixs bsc datas nc spat rng w h minv maxv bil : Z) (v : pixv) (S : TSet) (g3 : word),
  Cok C -> W C A7 m7 (with_vmmaps vm7 md) -> frm_zero cs -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 5120 <= s)%Z -> (s <= c_top C)%Z ->
  bc_cst A7 m7 bsc datas nc spat rng w h minv maxv -> (spat mod 16 = 0)%Z -> kcell_ok spat 11 m7 -> kcell_ok rng 256 m7 ->
  PIXat m7 pixs v -> p_w v = w -> p_h v = h -> live A7 (Z_to_bv 64 pixs) = Some 64%Z ->
  bc_fl_ok FL -> cellsAt SEGS m7 (s - 320) (bc_fl2 FL bil bsc nc) ->
  getr regs 1 = Z_to_bv 64 0x39efc -> getr regs 2 = Z_to_bv 64 (s - 320) -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 10 = Z_to_bv 64 10 ->
  getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 spat -> getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 rng ->
  getr regs 24 = Z_to_bv 64 pixs -> getr regs 3 = g3 -> reg_get fr 18 = Z_to_bv 64 4621819117588971520 ->
  forall (kR bR : Z), aroom A7 vm7 kR bR -> (4 + 10 * RK_it <= kR)%Z -> (4 * 2 ^ 17 + 10 * RB_it w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (pa parr ba barr : Z) (pixes datad : Z -> Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     bc_inv C A7 A' m7 m' s pa parr ba barr w h 10 pixes datad (bc_fl2 FL bil bsc nc ++ [(8%Z, 8%nat, pa)]) ->
     getr regs' 2 = Z_to_bv 64 (s - 320) -> getr regs' 4 = Z_to_bv 64 0x56270 -> getr regs' 3 = g3 ->
     (forall r : reg, r <> 8%bv -> r <> 9%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 18%bv -> reg_get fr' r = reg_get fr r) ->
     aroom A' vm' (kR - 4 - 10 * RK_it) (bR - 4 * 2 ^ 17 - 10 * RB_it w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (Z_to_bv 64 0x3a528) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x18258) m7 al_rom) (with_vmmaps vm7 md)) S.
Proof.
  intros fr cs C A7 m7 md vm7 regs FL s pixs bsc datas nc spat rng w h minv maxv bil v S g3
    CK HW FZ Hs16 Hstk Htop CST Hsp16 KS KG PXs Hvw Hvh Lps FLOK CL2 G1 G2 G4 G10 G20 G21 G22 G23 G24 G3 F18 kR bR AR HkR HbR K.
  pose proof CK as [Ctop Csp0 Csp0hi Cal Cimg].
  pose proof LSTK_val as LS. cbv [ll_img LLU16 snd] in Cimg.
  pose proof CST as (HOKt & HOKd & Hw1 & Hh1 & PXb & Lb & Lds & Hnc & Lnc & NCV & Hmin & Hmax & Hsp & Lsp & Hrg & Lrg).
  pose proof HOKt as (DV & Hwt & Hht & Hszt).
  pose proof (wpl_of_range (w + 22) 8 ltac:(lia) DV) as WPt.
  assert (RK0 : (0 <= RK_it)%Z) by (unfold RK_it; room_consts; lia).
  assert (RB0 : (0 <= RB_it w h)%Z) by (unfold RB_it; pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 22) 8 * (h + 22)))); pose proof (RB_pixT_nonneg (4 * (wpl_of w 8 * h))); lia).
  pose proof PXb as (Hb0 & Hb64 & _). pose proof PXs as (Hp0 & Hp64 & _).
  destruct (blk_range C A7 m7 _ _ _ CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
  destruct (blk_range C A7 m7 _ _ _ CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (wf_data _ (proj1 (proj2 (proj2 PXb)))) as Hds. cbn [p_data hdv] in Hds.
  destruct (blk_range C A7 m7 _ _ _ CK HW Lds ltac:(nia)) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  pose proof (ai_live_hull A7 m7 _ _ _ (w_inv _ _ _ _ HW) Lb) as (_ & ALb & _). rewrite u_Z2bv in ALb by lia.
  pose proof (ai_live_hull A7 m7 _ _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  assert (CFX : cellsAt SEGS m7 (s - 320) FL /\ cellsAt SEGS m7 (s - 320) [(16%Z, 8%nat, bil); (24%Z, 8%nat, bsc); (32%Z, 8%nat, 10%Z); (48%Z, 8%nat, 11%Z); (64%Z, 8%nat, (2 ^ 64 - 1 - nc)%Z); (72%Z, 8%nat, nc)])
    by (unfold bc_fl2, cellsAt in CL2 |- *; exact (proj1 (Forall_app _ _ _) CL2)).
  destruct CFX as [CF CX].
  assert (RK1 : ret_ok (Z_to_bv 64 0x39efc)) by (apply ret_ok_even; rewrite u_Z2bv by lia; reflexivity).
  apply (pixaCreate10_W (mkFP fr cs) C A7 m7 (with_vmmaps vm7 md) regs (s - 320) _ S CK HW G2 (bc_msub s 320 16 ltac:(lia) Hs16 eq_refl)
           ltac:(unfold PIXAC_WIN; lia) ltac:(lia) G1 RK1 G4 G10 kR bR AR ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r1 pa parr ba barr W1 CS1 PM1 SL1 R10 PN AR1.
  rewrite wv_wv in W1 |- *.
  destruct PN as (PC0 & PB & N1 & N2 & N3 & N4 & LEQ0 & NEpb).
  pose proof PB as (Hpa & Hparr & Hba & Hbarr & LApa & LAparr & LAba & LAbarr & _).
  destruct (blk_range C A1 m1 _ _ _ CK W1 LApa ltac:(lia)) as [Gpa TOPpa]. rewrite u_Z2bv in Gpa, TOPpa by lia.
  destruct (blk_range C A1 m1 _ _ _ CK W1 LAba ltac:(lia)) as [Gba TOPba]. rewrite u_Z2bv in Gba, TOPba by lia.
  assert (PXb1 : PIXat m1 bsc (hdv (w + 22) (h + 22) 8 0 datas)).
  { eapply PIXat_frame; [exact PXb|]. intros x Hx. apply (bc_livk_at A7 m7 m1 bsc 64 x (proj2 PM1) Lb); lia. }
  assert (PXs1 : PIXat m1 pixs v).
  { eapply PIXat_frame; [exact PXs|]. intros x Hx. apply (bc_livk_at A7 m7 m1 pixs 64 x (proj2 PM1) Lps); lia. }
  pose proof (agree_of_FRM C (s - 320) m7 m1 (s - 320) 320 [] CK (proj1 PM1) ltac:(lia) ltac:(lia) ltac:(lia)) as AG1.
  keep_cells CX AG1 CX1.
  pose proof (fl_keep FL (s - 320) m7 m1 [] FLOK ltac:(lia) ltac:(lia) (Forall_nil _) AG1 CF) as CF1.
  eapply rz_reach; [exact (w_pure _ _ _ _ W1) |
    exact (bc_M al_rom fr cs r1 m1 s pa bsc pixs (w + 22) (h + 22) (wpl_of (w + 22) 8) datas w h rng FZ ltac:(lia) Hs16
             Gb ltac:(lia) (bc_m16_8 _ ALb) Gps ltac:(lia) (bc_m16_8 _ ALps) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             (fun j Hj => W_img16 C A1 m1 _ j W1 ltac:(lia)) (fun j Hj => W_img16 C A1 m1 _ j W1 ltac:(lia)) ltac:(lia)
             (PIX_rd_w SEGS m1 bsc _ PXb1) (PIX_rd_h SEGS m1 bsc _ PXb1) (PIX_rd_wpl SEGS m1 bsc _ PXb1) (PIX_rd_data SEGS m1 bsc _ PXb1)
             ltac:(rewrite <- Hvw; exact (PIX_rd_w SEGS m1 pixs v PXs1)) ltac:(rewrite <- Hvh; exact (PIX_rd_h SEGS m1 pixs v PXs1))
             ltac:(cell_from CX1) (W_sok_win C A1 m1 _ (s - 320) 320 CK W1 ltac:(lia) ltac:(lia))
             ltac:(csr; reflexivity) R10 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) F18) |].
  intros fin (fr1 & cs1 & r2 & m2 & -> & FZ1 & RI2 & M312 & M240 & M224 & M216 & M192 & M184 & B2 & B8 & B9 & B18 & B19 & B22 & B26 & B27 & AGM & FSC1 & FRK).
  destruct (rinv_WP2 C A7 A1 m1 _ m2 _ s CK W1 SL1 Htop RI2) as [W2 PM12].
  { repeat apply Forall_cons; try apply Forall_nil; left; cbn [fst snd]; lia. }
  pose proof (POSTM_trans C A7 s m7 m1 m2 (POSTM_mono C A7 (s - 320) s m7 m1 ltac:(lia) PM1) PM12) as PM0.
  assert (AG2 : agree_win (s - 320) 320 [(8%Z, 8%Z); (80%Z, 64%Z); (176%Z, 16%Z)] m1 m2).
  { apply (agree_of_rinv _ _ _ _ _ _ RI2).
    apply Forall_cons; [right; exists (8%Z, 8%Z); cbn [In fst snd]; split; [left; reflexivity | lia] |].
    apply Forall_cons; [right; exists (80%Z, 64%Z); cbn [In fst snd]; split; [right; left; reflexivity | lia] |].
    apply Forall_cons; [right; exists (176%Z, 16%Z); cbn [In fst snd]; split; [right; right; left; reflexivity | lia] |].
    apply Forall_nil. }
  keep_cells CX1 AG2 CX2.
  pose proof (fl_keep FL (s - 320) m1 m2 [(8%Z, 8%Z); (80%Z, 64%Z); (176%Z, 16%Z)] FLOK ltac:(lia) ltac:(lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) AG2 CF1) as CF2.
  assert (CM2 : cellsAt SEGS m2 (s - 320) [(8%Z, 8%nat, pa); (96%Z, 8%nat, datas); (80%Z, 8%nat, wpl_of (w + 22) 8); (136%Z, 8%nat, w); (104%Z, 8%nat, h); (128%Z, 8%nat, 0%Z)]).
  { unfold cellsAt.
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 8)%Z with (s - 312)%Z by lia; exact M312 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 96)%Z with (s - 224)%Z by lia; exact M224 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 80)%Z with (s - 240)%Z by lia; exact M240 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 136)%Z with (s - 184)%Z by lia; exact M184 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 104)%Z with (s - 216)%Z by lia; exact M216 |].
    apply Forall_cons; [cbn [c_off c_len c_val fst snd]; replace (s - 320 + 128)%Z with (s - 192)%Z by lia; exact M192 |].
    apply Forall_nil. }
  assert (FL3 : cellsAt SEGS m2 (s - 320) (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h)).
  { apply fl3_join; [exact CF2|]. unfold bc_fx, cellsAt. exact (proj2 (Forall_app _ _ _) (conj CX2 CM2)). }
  assert (PC2 : pixa_cells m2 pa parr ba barr 0).
  { apply (pixa_cells_keep m1 m2 pa parr ba barr 0 PC0); try lia.
    - intros a Ha. exact (rinv_keep _ m1 m2 pa 32 RI2 ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) a Ha).
    - intros a Ha. exact (rinv_keep _ m1 m2 ba 24 RI2 ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) a Ha). }
  assert (INV0 : bc_inv C A7 A1 m7 m2 s pa parr ba barr w h 0 (fun _ => 0%Z) (fun _ => 0%Z) (bc_fl3 FL bil bsc nc pa datas (wpl_of (w + 22) 8) w h)).
  { unfold bc_inv.
    split; [exact SL1|]. split; [exact PM0|]. split; [exact FL3|]. split; [exact PC2|]. split; [exact PB|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
    split; [intros i Hi; lia|].
    split; [intros q Hq _; apply LEQ0; intro HH; apply Hq; cbn [map In] in *; tauto|].
    split; [exact NEpb|]. split; [intros i j Hij Hj; lia | intros i Hi; lia]. }
  assert (KR2 : bc_kr r2 s spat rng g3).
  { unfold bc_kr.
    split; [exact B2|]. split; [csr; reflexivity|]. split; [exact B8|]. split; [exact B18|]. split; [exact B19|].
    split; [csr; reflexivity|]. split; [csr; reflexivity|]. split; [exact B22|]. split; [csr; reflexivity|].
    split; [exact B26|]. split; [exact B27|]. csr; reflexivity. }
  apply (bc_loop_W 10 fr1 cs1 C A7 A1 m7 m2 md vm1 r2 FL s bsc datas nc spat rng pa parr ba barr w h minv maxv bil 0 (fun _ => 0%Z) (fun _ => 0%Z) S g3
           ltac:(reflexivity) ltac:(lia) CK W2 FZ1 Hs16 Hstk Htop CST Hsp16 KS KG FLOK INV0 KR2 B9 FSC1 (kR - 4) (bR - 4 * 2 ^ 17) AR1 ltac:(lia) ltac:(lia)).
  intros fr' cs' A' m' vm' regs' pixes' datad' W' FZ' INV' KR' R9' PF' AR'.
  destruct KR' as (K2 & K4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & K3).
  apply (K fr' cs' A' m' vm' regs' pa parr ba barr pixes' datad' W' FZ').
  - destruct INV' as (I1 & I2 & I3 & I4).
    split; [exact I1|]. split; [exact I2|]. split; [|exact I4].
    unfold bc_fl3, cellsAt in I3. apply Forall_app in I3 as [Ia Ib].
    unfold cellsAt. apply Forall_app. split; [exact Ia|]. apply Forall_cons; [exact (Forall_inv Ib) | apply Forall_nil].
  - exact K2.
  - exact K4.
  - exact K3.
  - exact (bc_fr_keep fr fr1 fr' FRK PF').
  - exact AR'.
Qed.
End BilCW3.
