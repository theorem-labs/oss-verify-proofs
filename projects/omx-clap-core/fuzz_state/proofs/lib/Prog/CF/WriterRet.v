(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 649 of its 743 lines of code are new or changed and 328 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts WriterApp WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import put_c put_kb.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition new_calls (st : wst) (P : list (list Z)) : list Z :=
  skipn (length (w_calls st)) (w_calls (putN st P)).

Lemma skipn_len_app : forall {T} (l1 l2 : list T), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros T l1 l2. induction l1 as [|x l1 IH]; [reflexivity|]. exact IH. Qed.

Lemma put1_calls : forall st bs, exists l, w_calls (put1 st bs) = w_calls st ++ l.
Proof.
  intros [f t c n fl cs] bs. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  destruct (negb (f =? 0)); [exists []; rewrite app_nil_r; reflexivity|].
  destruct (_ <=? c); [exists []; cbn; rewrite app_nil_r; reflexivity|].
  destruct (n =? fl); cbn [w_calls]; eexists; reflexivity.
Qed.

Lemma putN_calls_ex : forall P st, exists l, w_calls (putN st P) = w_calls st ++ l.
Proof.
  induction P as [|bs P IH]; intros st; [exists []; rewrite app_nil_r; reflexivity|].
  rewrite putN_cons. destruct (put1_calls st bs) as [l1 E1]. destruct (IH (put1 st bs)) as [l2 E2].
  exists (l1 ++ l2). rewrite E2, E1, app_assoc. reflexivity.
Qed.

Lemma putN_calls : forall P st, w_calls (putN st P) = w_calls st ++ new_calls st P.
Proof.
  intros P st. unfold new_calls. destruct (putN_calls_ex P st) as [l E]. rewrite E, skipn_len_app. reflexivity.
Qed.

Lemma new_calls_nil : forall st, new_calls st [] = [].
Proof. intros st. unfold new_calls. rewrite putN_nil. rewrite <- (app_nil_r (w_calls st)) at 2. apply skipn_len_app. Qed.

Lemma new_calls_app : forall st P Q, new_calls st (P ++ Q) = new_calls st P ++ new_calls (putN st P) Q.
Proof.
  intros st P Q. apply (app_inv_head (w_calls st)). rewrite <- putN_calls, putN_app, putN_calls, putN_calls.
  symmetry. apply app_assoc.
Qed.

Lemma dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (need <=? c); [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma newcap_ge : forall c need, 0 <= c -> c <= newcap c need.
Proof.
  intros c need Hc. unfold newcap. destruct (Z.eqb_spec c 0) as [->|H].
  - pose proof (dbl_ge 64 4096 need ltac:(lia)). lia.
  - apply dbl_ge. exact Hc.
Qed.

Lemma put1_cap : forall st bs, 0 <= w_cap st -> w_cap st <= w_cap (put1 st bs).
Proof.
  intros [f t c n fl cs] bs Hc. cbn [w_cap] in Hc. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  destruct (negb (f =? 0)); [cbn; lia|]. destruct (_ <=? c); [cbn; lia|].
  pose proof (newcap_ge c (Z.of_nat (length t) + Z.of_nat (length bs) + 1) Hc).
  destruct (n =? fl); cbn [w_cap]; lia.
Qed.

Lemma putN_cap : forall P st, 0 <= w_cap st -> w_cap st <= w_cap (putN st P).
Proof.
  induction P as [|bs P IH]; intros st Hc; [rewrite putN_nil; lia|].
  rewrite putN_cons. pose proof (put1_cap st bs Hc). specialize (IH (put1 st bs) ltac:(lia)). lia.
Qed.

Lemma put1_text : forall st bs,
  Z.of_nat (length (w_text (put1 st bs))) <= Z.of_nat (length (w_text st)) + Z.of_nat (length bs).
Proof.
  intros [f t c n fl cs] bs. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  destruct (negb (f =? 0)); [cbn; lia|].
  destruct (_ <=? c); [cbn [w_text]; rewrite length_app; lia|].
  destruct (n =? fl); cbn [w_text]; rewrite ?length_app; lia.
Qed.

Lemma putN_text : forall P st,
  Z.of_nat (length (w_text (putN st P))) <= Z.of_nat (length (w_text st)) + Z.of_nat (length (concat P)).
Proof.
  induction P as [|bs P IH]; intros st; [rewrite putN_nil; cbn; lia|].
  rewrite putN_cons. pose proof (put1_text st bs). specialize (IH (put1 st bs)).
  cbn [concat]. rewrite length_app. lia.
Qed.

Lemma nodup_head : forall (x : Z * Z) l l1 l2, NoDup (map fst (x :: l)) -> x :: l = l1 ++ x :: l2 -> l = l1 ++ l2.
Proof.
  intros x l l1 l2 ND E. destruct l1 as [|y l1].
  - cbn in E. injection E as E. exact E.
  - cbn in E. injection E as Ey El. exfalso. cbn [map] in ND. inversion ND as [|? ? Hn _].
    apply Hn. rewrite El, map_app. cbn [map]. clear.
    induction (map fst l1) as [|a r IH]; cbn [app]; [left | right; exact IH].
Qed.

Lemma with_vmmaps_twice : forall vm1 vm2 md, with_vmmaps vm2 (with_vmmaps vm1 md) = with_vmmaps vm2 md.
Proof. intros vm1 vm2 [fd [h lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma layout_le_trans : forall A A1 L L1 L2,
  layout_le A L L1 -> layout_le A1 L1 L2 -> (length (st_regions A) <= length (st_regions A1))%nat ->
  layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (C1 & S1 & B1 & R1) (C2 & S2 & B2 & R2) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (R2 r ltac:(lia)). apply R1. exact Hr.
Qed.

Lemma in_mid : forall {T} (x e : T) l1 l2, In x (l1 ++ e :: l2) -> x <> e -> In x (l1 ++ l2).
Proof.
  intros T x e l1 l2 H Hne. apply in_app_iff in H. apply in_app_iff.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma CAPOK_w : CAPOK CAPMAX (2 ^ 40) (2 ^ 28 + 16).
Proof. unfold CAPOK. split; [|split; [|split]]; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Lemma newcap_wmax : forall c need,
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> c < need <= WMAX -> newcap c need <= WMAX.
Proof.
  intros c need Hc Hn. unfold WMAX in *. exact (newcap_le28 c need Hc Hn).
Qed.

Lemma wbc_grow : forall b c c1, 0 <= c -> c1 <> 0 ->
  (if c =? 0 then sb_malloc (wbc b c) (c1 + 16) else sb_realloc (wbc b c) (c + 16) (c1 + 16)) = wbc b c1.
Proof.
  intros b c c1 Hc Hc1. unfold wbc. rewrite (proj2 (Z.eqb_neq c1 0) Hc1).
  destruct (Z.eqb_spec c 0) as [->|Hn]; [reflexivity|].
  unfold sb_realloc, sb_malloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma wbc_nz : forall b c, c <> 0 -> wbc b c = sb_malloc b (c + 16).
Proof. intros b c H. unfold wbc. rewrite (proj2 (Z.eqb_neq c 0) H). reflexivity. Qed.

Lemma wr_room_put : forall b c need, wr_room b ->
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> c < need <= WMAX ->
  room_ag (wbc b c) (newcap c need + 16).
Proof.
  intros b c need (H1 & H2 & H3) Hc Hn.
  pose proof ag_cap_le as AC. pose proof ag_bytes_le as AB.
  pose proof (newcap_wmax c need Hc Hn) as Hw.
  assert (Hc0 : 0 <= c).
  { destruct Hc as [->|(j & Hj & ->)]; [lia|]. assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
  pose proof (newcap_ge c need Hc0) as Hge.
  assert (E1 : 2 ^ 29 = 2 * 2 ^ 28) by reflexivity.
  unfold WMAX in *. unfold room_ag, room_slots, wbc.
  destruct (Z.eqb_spec c 0) as [C0|Cn]; cbn [sb_live sb_bytes sb_cap sb_malloc].
  - split; [|split; lia]. split; [lia|]. split; [lia|].
    apply (CAPOK_mono CAPMAX (sb_cap b) (2 ^ 40) (sb_bytes b + (newcap c need + 16)) (2 ^ 28 + 16)
      (newcap c need + 16)); [lia | lia | lia | exact CAPOK_w].
  - split; [|split; lia]. split; [lia|]. split; [lia|].
    apply (CAPOK_mono CAPMAX (sb_cap b) (2 ^ 40) (sb_bytes b + (c + 16) + (newcap c need + 16)) (2 ^ 28 + 16)
      (newcap c need + 16)); [lia | lia | lia | exact CAPOK_w].
Qed.

Lemma newcap_pos : forall c need, 0 <= c -> 0 < newcap c need.
Proof.
  intros c need Hc. unfold newcap. destruct (Z.eqb_spec c 0) as [C0|Cn].
  - pose proof (dbl_ge 64 4096 need ltac:(lia)). lia.
  - pose proof (dbl_ge 64 c need Hc). lia.
Qed.

Lemma put1_cap_or : forall st bs, w_cap (put1 st bs) = w_cap st \/
  w_cap (put1 st bs) = newcap (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length bs) + 1).
Proof.
  intros [f t c n fl cs] bs. unfold put1. cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  destruct (negb (f =? 0)); [left; reflexivity|].
  destruct (_ <=? c); [left; reflexivity|].
  destruct (n =? fl); [left; reflexivity | right; reflexivity].
Qed.

Definition wnext (F : ResForm) (b : rf_R F) (st : wst) (bs : list Z) : rf_R F :=
  if w_cap (put1 st bs) =? w_cap st then b else wstep F b (w_cap st) (w_cap (put1 st bs)).

Fixpoint wfold (F : ResForm) (b : rf_R F) (st : wst) (P : list (list Z)) : rf_R F :=
  match P with
  | [] => b
  | bs :: P' => wfold F (wnext F b st bs) (put1 st bs) P'
  end.

Fixpoint wr_rooms (F : ResForm) (b : rf_R F) (st : wst) (P : list (list Z)) : Prop :=
  match P with
  | [] => True
  | bs :: P' =>
      (w_failed st = 0 -> w_cap st < Z.of_nat (length (w_text st)) + Z.of_nat (length bs) + 1 ->
       rf_room F b (newcap (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length bs) + 1) + 16)) /\
      wr_rooms F (wnext F b st bs) (put1 st bs) P'
  end.

Lemma wfold_app : forall F P Q b st, wfold F b st (P ++ Q) = wfold F (wfold F b st P) (putN st P) Q.
Proof.
  intros F P. induction P as [|bs P IH]; intros Q b st; [reflexivity|].
  cbn [app wfold]. rewrite IH. reflexivity.
Qed.

Lemma wr_rooms_app : forall F P Q b st,
  wr_rooms F b st (P ++ Q) <-> wr_rooms F b st P /\ wr_rooms F (wfold F b st P) (putN st P) Q.
Proof.
  intros F P. induction P as [|bs P IH]; intros Q b st.
  - cbn [app wr_rooms wfold]. rewrite putN_nil. tauto.
  - cbn [app wr_rooms wfold]. rewrite IH. rewrite putN_cons. tauto.
Qed.

Lemma wnext_sb : forall b st bs, 0 <= w_cap st ->
  wnext sb_form (wbc b (w_cap st)) st bs = wbc b (w_cap (put1 st bs)).
Proof.
  intros b st bs Hc. unfold wnext.
  destruct (Z.eqb_spec (w_cap (put1 st bs)) (w_cap st)) as [E|N]; [rewrite E; reflexivity|].
  destruct (put1_cap_or st bs) as [E|E]; [contradiction|].
  rewrite E. pose proof (newcap_pos (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length bs) + 1) Hc).
  unfold wstep. cbn [rf_malloc rf_realloc sb_form].
  exact (wbc_grow b (w_cap st) (newcap (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length bs) + 1))
    Hc ltac:(lia)).
Qed.

Lemma wfold_sb : forall P b st, 0 <= w_cap st ->
  wfold sb_form (wbc b (w_cap st)) st P = wbc b (w_cap (putN st P)).
Proof.
  induction P as [|bs P IH]; intros b st Hc; [reflexivity|].
  cbn [wfold]. rewrite (wnext_sb b st bs Hc). rewrite putN_cons. apply IH.
  pose proof (put1_cap st bs Hc). lia.
Qed.

Lemma wr_rooms_sb : forall P b st, wr_room b ->
  (w_cap st = 0 \/ exists j, 0 <= j <= 51 /\ w_cap st = 4096 * 2 ^ j) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat P)) + 1 <= WMAX ->
  wr_rooms sb_form (wbc b (w_cap st)) st P.
Proof.
  induction P as [|bs P IH]; intros b st HR Hc HL; [exact I|].
  cbn [concat] in HL. rewrite length_app, Nat2Z.inj_add in HL.
  pose proof (Nat2Z.is_nonneg (length (concat P))) as N1. pose proof (Nat2Z.is_nonneg (length bs)) as N2.
  pose proof (Nat2Z.is_nonneg (length (w_text st))) as N3.
  assert (Hc0 : 0 <= w_cap st).
  { destruct Hc as [->|(j & Hj & ->)]; [lia|]. assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
  cbn [wr_rooms]. split.
  - intros _ Hlt. cbn [rf_room sb_form]. apply wr_room_put; [exact HR | exact Hc | lia].
  - rewrite (wnext_sb b st bs Hc0). apply IH; [exact HR | |].
    + destruct (put1_cap_or st bs) as [E|E]; rewrite E; [exact Hc|]. right.
      assert (H63 : WMAX <= 2 ^ 63) by (unfold WMAX; apply Z.pow_le_mono_r; lia).
      destruct (newcap_bound (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length bs) + 1) Hc
        ltac:(lia)) as (j & Hj & Ej & _). exists j. split; [exact Hj | exact Ej].
    + pose proof (put1_text st bs). lia.
Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Let MR := aa_MR API.

Definition errno_at (a : Z) : Prop := errno_addr B <= a < errno_addr B + 4.

Definition wr_rel (lo hi : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (o buf : Z) (st : wst) (Lam : list (Z * Z)) (peak : Z) (b : rf_R RF) (P : list (list Z))
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model)
    (buf' : Z) (Lam' : list (Z * Z)) (peak' : Z) (b' : rf_R RF) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ (ro_agree (ms_segs B) mem' /\ guard_kept B mem mem') /\
  pj_out_ok B mem' Lam' o buf' (Z.of_nat (length (w_text (putN st P)))) (w_cap (putN st P))
    (w_failed (putN st P)) (w_text (putN st P)) /\
  ledger B L' A' mem' Lam' peak' (w_cnt (putN st P)) (w_fail (putN st P)) /\
  rf_ok RF A' b' /\ b' = wfold RF b st P /\
  ((w_cap (putN st P) = w_cap st /\ buf' = buf /\ Lam' = Lam /\ peak' = peak) \/
   (w_cap st < w_cap (putN st P) /\ exists l1 l2,
      (w_cap st = 0 /\ l1 = [] /\ l2 = Lam \/ w_cap st <> 0 /\ Lam = l1 ++ (buf, w_cap st) :: l2) /\
      Lam' = (buf', w_cap (putN st P)) :: l1 ++ l2 /\
      peak' = Z.max peak (lsum (l1 ++ l2) + w_cap (putN st P)))) /\
  layout_le A L L' /\ (length (st_regions A) <= length (st_regions A'))%nat /\
  (st_init_done A = true -> st_init_done A' = true) /\ (exists vm', md' = with_vmmaps vm' md) /\
  (forall p n, In (p, n) (user_blocks A) -> (ptr_addr L p, n) <> (buf - 16, w_cap st + 16) ->
     In (p, n) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) /\
  keeps B L A mem mem' (buf - 16) /\
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> (a, k) <> (buf - 16, w_cap st + 16) -> a <> buf' - 16) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ (lo <= a < hi) -> ~ errno_at a -> ~ (o <= a < o + 32) -> ~ alloc_statics a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
  (forall a, (lo <= a < hi \/ errno_at a) -> writable_at (ms_segs B) mem a -> writable_at (ms_segs B) mem' a).

Definition wr_ret (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (o buf : Z) (st : wst) (Lam : list (Z * Z)) (peak : Z) (b : rf_R RF) (P : list (list Z)) (c' : config) : Prop :=
  exists L' A' regs' mem' md' buf' Lam' peak' b',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    regs_preserved regs regs' /\
    wr_rel (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P L' A' mem' md' buf' Lam' peak' b'.

Lemma statics_low : forall a, alloc_statics a -> a < alloc_ceiling.
Proof.
  intros a Ha. pose proof ceil_big. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, IMG_TOP in *. lia.
Qed.

Lemma img_low : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof using SEGS. intros a Ha. pose proof (in_img_low B SEGS a Ha). pose proof ceil_big. lia. Qed.

Lemma dom_range : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> 0 <= a < 2 ^ 64.
Proof using SEGS.
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  intros a [H|H]; [lia | pose proof (img_low a H); lia].
Qed.

Lemma block_not_img : forall L A mem md x k i, MR L A mem md -> In (x, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (x + i).
Proof.
  intros L A mem md x k i HM Hin Hi. destruct (blocks_user L A x k Hin) as (q & Hq & <-).
  exact (ax_blocks_img AX L A mem md q k i HM Hq Hi).
Qed.

Lemma blk_out : forall L A mem md x k a, MR L A mem md -> In (x, k) (blocks L A) -> x <= a < x + k ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> False.
Proof.
  intros L A mem md x k a HM Hin Ha [H|H].
  - pose proof (block_range B API _ _ _ _ _ _ HM Hin). lia.
  - apply (block_not_img L A mem md x k (a - x) HM Hin ltac:(lia)). replace (x + (a - x)) with a by lia. exact H.
Qed.

Lemma lblock_in : forall L A mem Lam peak cnt fail x k, ledger B L A mem Lam peak cnt fail -> In (x, k) Lam ->
  0 <= k /\ In (x - 16, k + 16) (blocks L A).
Proof.
  intros L A mem Lam peak cnt fail x k HL Hin. destruct HL as (_ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. destruct (HF _ Hin) as (Hk & Hb & _). split; [exact Hk | exact Hb].
Qed.

Lemma errno_dec : forall a, errno_at a \/ ~ errno_at a.
Proof.
  intros a. unfold errno_at. destruct (Z_le_gt_dec (errno_addr B) a); destruct (Z_lt_ge_dec a (errno_addr B + 4));
    [left; lia | right; lia | right; lia | right; lia].
Qed.

Lemma not_owned_hi : forall L A mem md a, MR L A mem md -> alloc_ceiling <= a -> ~ owned B L A a.
Proof. intros L A mem md a HM Ha Ho. pose proof (owned_low B API _ _ _ _ _ HM Ho). lia. Qed.

Lemma owned_mid : forall L A mem md L1 A1 mem1 md1 a, MR L A mem md -> MR L1 A1 mem1 md1 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L1 A1 a.
Proof.
  intros L A mem md L1 A1 mem1 md1 a HM HM1 Hd Ho Ho1. destruct Hd as [Hd|Himg].
  - exact (not_owned_hi L1 A1 mem1 md1 a HM1 ltac:(lia) Ho1).
  - destruct Ho1 as [Hal|Hst].
    + apply Ho. apply (CTX L A mem md a HM). exact (ax_img AX L1 A1 mem1 md1 a HM1 Himg Hal).
    + apply Ho. right. exact Hst.
Qed.

Lemma pj_out_eqm : forall m m' Lam o buf len cap f t,
  pj_out_ok B m Lam o buf len cap f t ->
  (forall i, 0 <= i < 32 -> mbyte (ms_segs B) m' (o + i) = mbyte (ms_segs B) m (o + i) /\
     (writable_at (ms_segs B) m (o + i) -> writable_at (ms_segs B) m' (o + i))) ->
  (cap <> 0 -> forall i, 0 <= i < len + 1 -> mbyte (ms_segs B) m' (buf + i) = mbyte (ms_segs B) m (buf + i)) ->
  pj_out_ok B m' Lam o buf len cap f t.
Proof.
  intros m m' Lam o buf len cap f t PJ HR HB.
  destruct PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BO & LT & CAP).
  unfold pj_out_ok. split; [exact H8|]. split; [exact Ho|]. split; [exact Ho32|].
  split.
  { intros i Hi. destruct (HRW i Hi) as [W (v & Hv)]. destruct (HR i Hi) as [E1 E2].
    split; [exact (E2 W)|]. exists v. rewrite E1. exact Hv. }
  split; [exact Rb|]. split; [exact Rl|]. split; [exact Rc|].
  split; [intros k Hk; rewrite (proj1 (HR (Z.of_nat k) ltac:(lia))); exact (Wb k Hk)|].
  split; [intros k Hk; replace (o + 8 + Z.of_nat k) with (o + (8 + Z.of_nat k)) by lia;
          rewrite (proj1 (HR (8 + Z.of_nat k) ltac:(lia))); replace (o + (8 + Z.of_nat k)) with (o + 8 + Z.of_nat k) by lia;
          exact (Wl k Hk)|].
  split; [intros k Hk; replace (o + 16 + Z.of_nat k) with (o + (16 + Z.of_nat k)) by lia;
          rewrite (proj1 (HR (16 + Z.of_nat k) ltac:(lia))); replace (o + (16 + Z.of_nat k)) with (o + 16 + Z.of_nat k) by lia;
          exact (Wc k Hk)|].
  split; [intros k Hk; unfold word4_mem in Wf; replace (o + 24 + Z.of_nat k) with (o + (24 + Z.of_nat k)) by lia;
          rewrite (proj1 (HR (24 + Z.of_nat k) ltac:(lia))); replace (o + (24 + Z.of_nat k)) with (o + 24 + Z.of_nat k) by lia;
          exact (Wf k Hk)|].
  split; [exact Hf|]. split; [exact BO|]. split; [exact LT|].
  destruct CAP as [C0|(Hj & Hin & Hst & Hlt & Hz)]; [left; exact C0|right].
  split; [exact Hj|]. split; [exact Hin|]. split; [exact Hst|]. split; [exact Hlt|].
  assert (Hc : cap <> 0) by (destruct Hj as (j & _ & ->); pose proof (Z.pow_pos_nonneg 2 j); lia).
  intros i Hi. rewrite (HB Hc i ltac:(rewrite length_app in Hi; cbn in Hi; lia)). apply Hz. exact Hi.
Qed.

Lemma same_addr : forall L A mem md a k j, MR L A mem md -> In (a, k) (blocks L A) -> In (a, j) (blocks L A) ->
  0 < k -> 0 < j -> k = j.
Proof.
  intros L A mem md a k j HM H1 H2 Hk Hj. destruct (Z.eq_dec k j) as [E|E]; [exact E|]. exfalso.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as D.
  destruct (pairwise_In _ _ _ _ D H1 H2 ltac:(intros X; injection X as X; lia)) as [R|R];
    unfold ranges_disjoint in R; cbn [fst snd] in R; lia.
Qed.

Lemma buf_gone : forall L A mem md Lam peak cnt fail o buf len cap f t a k,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail -> pj_out_ok B mem Lam o buf len cap f t ->
  In (a, k) (blocks L A) -> 0 < k -> (a, k) <> (buf - 16, cap + 16) -> a <> buf - 16.
Proof.
  intros L A mem md Lam peak cnt fail o buf len cap f t a k HM LG PJ Hin Hk Hne E. subst a.
  pose proof PJ as (_ & _ & _ & _ & _ & _ & Rc & _ & _ & _ & _ & _ & _ & _ & CAP).
  destruct CAP as [(C0 & B0 & _)|(_ & Hin2 & _)].
  - pose proof (block_range B API _ _ _ _ _ _ HM Hin). lia.
  - destruct (lblock_in _ _ _ _ _ _ _ _ _ LG Hin2) as [Hc Hb]. apply Hne. f_equal.
    exact (same_addr L A mem md _ k (cap + 16) HM Hin Hb Hk ltac:(lia)).
Qed.

Lemma ptr_keep : forall L L' A p n, WF A -> layout_le A L L' -> In (p, n) (user_blocks A) ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros L L' A p n HW (_ & _ & _ & HR) Hin.
  destruct (YN03.block_region A p n HW Hin) as (k & o & rg & -> & Hrg & _).
  cbn [ptr_addr loc_addr]. rewrite HR; [reflexivity|].
  unfold region_of in Hrg. apply nth_error_Some. rewrite Hrg. discriminate.
Qed.

Lemma wr_rel_nil : forall lo hi L A mem md o buf st Lam peak b,
  MR L A mem md -> WF A -> bounded A -> ro_agree (ms_segs B) mem ->
  pj_out_ok B mem Lam o buf (Z.of_nat (length (w_text st))) (w_cap st) (w_failed st) (w_text st) ->
  ledger B L A mem Lam peak (w_cnt st) (w_fail st) -> rf_ok RF A b ->
  wr_rel lo hi L A mem md o buf st Lam peak b [] L A mem md buf Lam peak b.
Proof.
  intros lo hi L A mem md o buf st Lam peak b HM HW HB HI PJ LG RS.
  unfold wr_rel. rewrite putN_nil.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [split; [exact HI | intros i Hi; reflexivity]|].
  split; [exact PJ|]. split; [exact LG|]. split; [exact RS|]. split; [reflexivity|].
  split; [left; repeat split|].
  split; [apply layout_le_refl|]. split; [lia|]. split; [tauto|].
  split; [exists (m_vmmaps md); apply model_eta|].
  split; [intros p n Hp _; split; [exact Hp | reflexivity]|].
  split; [intros a k i _ _ _; reflexivity|].
  split; [intros a k Hin Hk Hne; exact (buf_gone L A mem md Lam peak _ _ o buf _ _ _ _ a k HM LG PJ Hin Hk Hne)|].
  split; [intros a _ _ _ _ _ _ _; split; [reflexivity | tauto]|].
  intros a _ W. exact W.
Qed.

Lemma wr_rel_app : forall lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 Q
    L2 A2 mem2 md2 buf2 Lam2 peak2 b2,
  MR L A mem md -> 0 <= w_cap st ->
  wr_rel lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  wr_rel lo hi L1 A1 mem1 md1 o buf1 (putN st P) Lam1 peak1 b1 Q L2 A2 mem2 md2 buf2 Lam2 peak2 b2 ->
  wr_rel lo hi L A mem md o buf st Lam peak b (P ++ Q) L2 A2 mem2 md2 buf2 Lam2 peak2 b2.
Proof using AX CTX SEGS.
  intros lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 Q
    L2 A2 mem2 md2 buf2 Lam2 peak2 b2 HM0 HC0 R1 R2.
  destruct R1 as (HM1 & HW1 & HB1 & HI1 & PJ1 & LG1 & RS1 & EB1 & LM1 & LL1 & RG1 & IN1 & MD1 & PT1 & KP1 & FM1
    & FR1 & WR1).
  destruct R2 as (HM2 & HW2 & HB2 & HI2 & PJ2 & LG2 & RS2 & EB2 & LM2 & LL2 & RG2 & IN2 & MD2 & PT2 & KP2 & FM2
    & FR2 & WR2).
  rewrite <- putN_app in PJ2, LG2.
  assert (Hpers : forall a k, In (a, k) (blocks L A) -> (a, k) <> (buf - 16, w_cap st + 16) -> In (a, k) (blocks L1 A1)).
  { intros a k Hin Hne. destruct (blocks_user L A a k Hin) as (q & Hq & Eq). subst a.
    destruct (PT1 q k Hq Hne) as [Hq1 Ep]. unfold blocks. apply in_map_iff. exists (q, k).
    cbn [fst snd]. rewrite Ep. split; [reflexivity | exact Hq1]. }
  pose proof (putN_cap P st HC0) as CP0.
  unfold wr_rel. split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split; [split; [exact (proj1 HI2) | exact (guard_trans B mem mem1 mem2 (proj2 HI1) (proj2 HI2))]|].
  split; [exact PJ2|]. split; [exact LG2|]. split; [exact RS2|].
  split; [rewrite EB2, EB1, wfold_app; reflexivity|].
  split.
  { pose proof (putN_cap P st HC0) as CP1. pose proof (putN_cap Q (putN st P) ltac:(lia)) as CP2.
    rewrite putN_app.
    destruct LM1 as [(Ec1 & Eb1 & El1 & Ep1) | (Gc1 & l1 & l2 & Hl & El1 & Ep1)];
    destruct LM2 as [(Ec2 & Eb2 & El2 & Ep2) | (Gc2 & l1' & l2' & Hl' & El2 & Ep2)].
    - left. split; [congruence|]. split; [congruence|]. split; congruence.
    - right. split; [lia|]. exists l1', l2'. rewrite Ec1, Eb1, El1, Ep1 in *. split; [exact Hl'|].
      split; [exact El2 | exact Ep2].
    - right. split; [lia|]. exists l1, l2. split; [exact Hl|]. rewrite El2, Ep2, Eb2, Ec2. split; [exact El1 | exact Ep1].
    - right. split; [lia|]. exists l1, l2. split; [exact Hl|].
      destruct Hl' as [(Hz & _ & _) | (_ & Hd)]; [lia|].
      assert (Ell : l1 ++ l2 = l1' ++ l2').
      { destruct LG1 as (_ & _ & _ & _ & ND & _). rewrite El1 in ND, Hd.
        exact (nodup_head _ _ _ _ ND Hd). }
      split; [rewrite El2, Ell; reflexivity|]. rewrite Ep2, Ep1, <- Ell. lia. }
  split; [exact (layout_le_trans A A1 L L1 L2 LL1 LL2 RG1)|]. split; [lia|]. split; [tauto|].
  split; [destruct MD1 as [vm1 ->]; destruct MD2 as [vm2 ->]; exists vm2; apply with_vmmaps_twice|].
  split.
  { intros p n Hp Hne. destruct (PT1 p n Hp Hne) as [Hp1 Ep1].
    assert (Hne1 : (ptr_addr L1 p, n) <> (buf1 - 16, w_cap (putN st P) + 16)).
    { rewrite Ep1. intros E. injection E as Ea En.
      apply (FM1 (ptr_addr L p) n); [| lia | exact Hne | exact Ea].
      unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp]. }
    destruct (PT2 p n Hp1 Hne1) as [Hp2 Ep2]. split; [exact Hp2 | congruence]. }
  split.
  { intros a k i Hin Hne Hi.
    assert (Hne' : (a, k) <> (buf - 16, w_cap st + 16)) by (intros E; injection E as E _; exact (Hne E)).
    rewrite (KP2 a k i (Hpers a k Hin Hne') (FM1 a k Hin ltac:(lia) Hne') Hi).
    exact (KP1 a k i Hin Hne Hi). }
  split.
  { intros a k Hin Hk Hne. pose proof (FM1 a k Hin Hk Hne) as F1.
    apply (FM2 a k (Hpers a k Hin Hne) Hk). intros E. injection E as E _. exact (F1 E). }
  split.
  { intros a Hd Ho0 Ho2 Hs He Hr Hst.
    pose proof (owned_mid L A mem md L1 A1 mem1 md1 a HM0 HM1 Hd Ho0) as Ho1.
    destruct (FR1 a Hd Ho0 Ho1 Hs He Hr Hst) as [F1 G1].
    destruct (FR2 a Hd Ho1 Ho2 Hs He Hr Hst) as [F2 G2].
    split; [congruence | tauto]. }
  intros a Ha W. apply WR2; [exact Ha|]. apply WR1; [exact Ha | exact W].
Qed.

Lemma wr_rel_munch : forall lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 W mem2,
  wr_rel lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  munch W mem1 mem2 -> wmono rsegs mem1 mem2 -> rm mem1 mem2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> lo <= x < hi /\ ~ (o <= x < o + 32)) ->
  alloc_ceiling <= lo ->
  wr_rel lo hi L A mem md o buf st Lam peak b P L1 A1 mem2 md1 buf1 Lam1 peak1 b1.
Proof using SEGS.
  intros lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 W mem2 R1 MU WM RM HW HLO.
  destruct R1 as (HM1 & HW1 & HB1 & HI1 & PJ1 & LG1 & RS1 & EB1 & LM1 & LL1 & RG1 & IN1 & MD1 & PT1 & KP1 & FM1
    & FR1 & WR1).
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  assert (Olo : forall x, 0 <= x < alloc_ceiling -> outside W x).
  { intros x Hx. destruct (outside_dec W x) as [Ho|Hn]; [exact Ho|]. exfalso.
    destruct (HW x ltac:(lia) Hn) as [H _]. lia. }
  assert (Eq_lo : forall x, 0 <= x < alloc_ceiling -> mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem1 x /\
            (writable_at (ms_segs B) mem1 x <-> writable_at (ms_segs B) mem2 x)).
  { intros x Hx. apply raw_mbyte. apply (munch_raw W); [exact MU | lia | exact (Olo x Hx)]. }
  rewrite <- SEGS in WM.
  unfold wr_rel. split.
  { eapply (mr_munch B API); [exact HM1 | exact MU | exact RM |].
    intros a Ho. pose proof (owned_low B API _ _ _ _ _ HM1 Ho). apply Olo. lia. }
  split; [exact HW1|]. split; [exact HB1|].
  split.
  { destruct HI1 as [RO1 GK1]. split.
    - rewrite SEGS in RO1 |- *. apply (ro_agree_same rsegs mem1 mem2 RO1). intros x Hx. apply MU. apply Olo.
      pose proof (ro_unsigned_low x Hx) as Hr. unfold IMG_TOP in Hr. lia.
    - apply (guard_trans B mem mem1 mem2 GK1). apply (guard_munch B API L1 A1 mem1 md1 W mem1 mem2 HM1 MU).
      intros i Hi. destruct (got_low B API L1 A1 mem1 md1 i HM1 Hi) as [_ GL]. apply Olo. lia. }
  split.
  { eapply pj_out_eqm; [exact PJ1 | |].
    - intros i Hi. pose proof PJ1 as (_ & Ho & Ho32 & _).
      assert (Out : outside W (o + i)).
      { destruct (outside_dec W (o + i)) as [Ho'|Hn]; [exact Ho'|]. exfalso.
        destruct (HW (o + i) ltac:(lia) Hn) as [_ H]. lia. }
      destruct (raw_mbyte (ms_segs B) mem1 mem2 (o + i) (munch_raw W mem1 mem2 (o + i) MU ltac:(lia) Out)) as [E1 E2].
      split; [exact E1 | tauto].
    - intros Hc i Hi. pose proof PJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LT & CAP).
      destruct CAP as [(C0 & _)|(_ & Hin & _ & Hlt & _)]; [lia|].
      destruct (lblock_in _ _ _ _ _ _ _ _ _ LG1 Hin) as [_ Hb].
      pose proof (block_range B API _ _ _ _ _ _ HM1 Hb). apply Eq_lo. lia. }
  split.
  { eapply (ledger_munch B API); [exact HM1 | exact LG1 | exact MU | |].
    - intros a Ha. apply Olo. pose proof (statics_low a Ha). unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. lia.
    - intros x k i Hin Hi. destruct (lblock_in _ _ _ _ _ _ _ _ _ LG1 Hin) as [Hk Hb].
      pose proof (block_range B API _ _ _ _ _ _ HM1 Hb). apply Olo. lia. }
  split; [exact RS1|]. split; [exact EB1|]. split; [exact LM1|]. split; [exact LL1|]. split; [exact RG1|].
  split; [exact IN1|]. split; [exact MD1|]. split; [exact PT1|].
  split.
  { intros a k i Hin Hne Hi. rewrite <- (KP1 a k i Hin Hne Hi).
    destruct (blocks_user L A a k Hin) as (q & Hq & Eq).
    destruct (PT1 q k Hq ltac:(intros E; injection E as E _; congruence)) as [Hq1 Ep].
    assert (Hb1 : In (a, k) (blocks L1 A1)).
    { unfold blocks. apply in_map_iff. exists (q, k). cbn [fst snd]. rewrite Ep, Eq. split; [reflexivity | exact Hq1]. }
    pose proof (block_range B API _ _ _ _ _ _ HM1 Hb1). apply Eq_lo. lia. }
  split; [exact FM1|].
  split.
  { intros a Hd Ho0 Ho1 Hs He Hr Hst. destruct (FR1 a Hd Ho0 Ho1 Hs He Hr Hst) as [F1 G1].
    pose proof (dom_range a Hd) as Ra.
    assert (Out : outside W a).
    { destruct (outside_dec W a) as [Ho'|Hn]; [exact Ho'|]. exfalso. destruct (HW a Ra Hn) as [H _]. lia. }
    destruct (raw_mbyte (ms_segs B) mem1 mem2 a (munch_raw W mem1 mem2 a MU Ra Out)) as [E1 E2].
    split; [congruence | tauto]. }
  intros a Ha Wa. apply WM. exact (WR1 a Ha Wa).
Qed.

Lemma wr_rel_widen : forall lo hi lo' hi' L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1,
  MR L A mem md -> lo' <= lo -> hi <= hi' -> alloc_ceiling <= lo' -> hi' <= 2 ^ 64 ->
  wr_rel lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  wr_rel lo' hi' L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1.
Proof.
  intros lo hi lo' hi' L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 HM0 H1 H2 H3 H4 R1.
  destruct R1 as (HM1 & HW1 & HB1 & HI1 & PJ1 & LG1 & RS1 & EB1 & LM1 & LL1 & RG1 & IN1 & MD1 & PT1 & KP1 & FM1
    & FR1 & WR1).
  unfold wr_rel. do 16 (split; [assumption|]).
  split.
  { intros a Hd Ho0 Ho1 Hs He Hr Hst. apply FR1; try assumption. lia. }
  intros a Ha Wa. destruct (Z_le_gt_dec lo a) as [La|La]; [destruct (Z_lt_ge_dec a hi) as [Lb|Lb]|].
  - apply WR1; [left; lia | exact Wa].
  - destruct Ha as [Ha|Ha]; [|apply WR1; [right; exact Ha | exact Wa]].
    destruct (Z_le_gt_dec o a) as [Oa|Oa]; [destruct (Z_lt_ge_dec a (o + 32)) as [Ob|Ob]|].
    + pose proof PJ1 as (_ & _ & _ & HRW & _). replace a with (o + (a - o)) by lia. exact (proj1 (HRW (a - o) ltac:(lia))).
    + destruct (errno_dec a) as [Ea|Ea]; [apply WR1; [right; exact Ea | exact Wa]|].
      apply (FR1 a ltac:(left; lia) (not_owned_hi _ _ _ _ a HM0 ltac:(lia)) (not_owned_hi _ _ _ _ a HM1 ltac:(lia))
        ltac:(lia) Ea ltac:(lia) ltac:(intros S; pose proof (statics_low a S); lia)). exact Wa.
    + destruct (errno_dec a) as [Ea|Ea]; [apply WR1; [right; exact Ea | exact Wa]|].
      apply (FR1 a ltac:(left; lia) (not_owned_hi _ _ _ _ a HM0 ltac:(lia)) (not_owned_hi _ _ _ _ a HM1 ltac:(lia))
        ltac:(lia) Ea ltac:(lia) ltac:(intros S; pose proof (statics_low a S); lia)). exact Wa.
  - destruct Ha as [Ha|Ha]; [|apply WR1; [right; exact Ha | exact Wa]].
    destruct (Z_le_gt_dec o a) as [Oa|Oa]; [destruct (Z_lt_ge_dec a (o + 32)) as [Ob|Ob]|].
    + pose proof PJ1 as (_ & _ & _ & HRW & _). replace a with (o + (a - o)) by lia. exact (proj1 (HRW (a - o) ltac:(lia))).
    + destruct (errno_dec a) as [Ea|Ea]; [apply WR1; [right; exact Ea | exact Wa]|].
      apply (FR1 a ltac:(left; lia) (not_owned_hi _ _ _ _ a HM0 ltac:(lia)) (not_owned_hi _ _ _ _ a HM1 ltac:(lia))
        ltac:(lia) Ea ltac:(lia) ltac:(intros S; pose proof (statics_low a S); lia)). exact Wa.
    + destruct (errno_dec a) as [Ea|Ea]; [apply WR1; [right; exact Ea | exact Wa]|].
      apply (FR1 a ltac:(left; lia) (not_owned_hi _ _ _ _ a HM0 ltac:(lia)) (not_owned_hi _ _ _ _ a HM1 ltac:(lia))
        ltac:(lia) Ea ltac:(lia) ltac:(intros S; pose proof (statics_low a S); lia)). exact Wa.
Qed.

Lemma put1_failed : forall st bs, w_failed st <> 0 -> put1 st bs = st.
Proof.
  intros st bs H. unfold put1. destruct (Z.eqb_spec (w_failed st) 0); [lia | reflexivity].
Qed.

Lemma nc_none : forall st bs, w_calls (put1 st bs) = w_calls st -> new_calls st [bs] = [].
Proof.
  intros st bs E. unfold new_calls. change (putN st [bs]) with (put1 st bs). rewrite E.
  rewrite <- (app_nil_r (w_calls st)) at 2. apply skipn_len_app.
Qed.

Lemma nc_one : forall st bs c, w_calls (put1 st bs) = w_calls st ++ [c] -> new_calls st [bs] = [c].
Proof.
  intros st bs c E. unfold new_calls. change (putN st [bs]) with (put1 st bs). rewrite E. apply skipn_len_app.
Qed.

Lemma keeps_zero : forall L A mem md mem' g, MR L A mem md -> keeps B L A mem mem' 0 -> keeps B L A mem mem' g.
Proof.
  intros L A mem md mem' g HM K a k i Hin _ Hi. apply (K a k i Hin); [|exact Hi].
  pose proof (block_range B API _ _ _ _ _ _ HM Hin). lia.
Qed.

Lemma ptr_zero : forall L A mem md A' L', MR L A mem md ->
  (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> 0 -> In (p, n) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) ->
  forall g p n, In (p, n) (user_blocks A) -> (ptr_addr L p, n) <> g ->
    In (p, n) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p.
Proof.
  intros L A mem md A' L' HM H g p n Hp _. apply H; [exact Hp|].
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp). lia.
Qed.

Lemma put_frame : forall K E gone L A regs mem md L' A' regs' mem' md' lo hi o,
  call_post_e B API K L A regs mem md E gone L' A' regs' mem' md' ->
  lo <= spZ regs - K -> spZ regs <= hi ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> E a -> o <= a < o + 32 \/ alloc_statics a) ->
  forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
    ~ (lo <= a < hi) -> ~ errno_at a -> ~ (o <= a < o + 32) -> ~ alloc_statics a ->
    mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros K E gone L A regs mem md L' A' regs' mem' md' lo hi o POST H1 H2 HE a Hd Ho0 Ho1 Hs He Hr Hst.
  destruct POST as (_ & _ & _ & _ & _ & _ & _ & HFR & _). apply (HFR a Hd Ho0 Ho1).
  - intros [S|S]; [apply Hs; lia | exact (He S)].
  - intros HEa. destruct (HE a Hd HEa); contradiction.
Qed.

Lemma put_writable : forall K E gone L A regs mem md L' A' regs' mem' md' lo hi o Lam' buf' len' cap' f' t',
  call_pre_k B MR K L A regs mem md ->
  call_post_e B API K L A regs mem md E gone L' A' regs' mem' md' ->
  lo <= spZ regs - K -> spZ regs <= hi -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> E a -> o <= a < o + 32 \/ alloc_statics a) ->
  pj_out_ok B mem' Lam' o buf' len' cap' f' t' ->
  forall a, (lo <= a < hi \/ errno_at a) -> writable_at (ms_segs B) mem a -> writable_at (ms_segs B) mem' a.
Proof.
  intros K E gone L A regs mem md L' A' regs' mem' md' lo hi o Lam' buf' len' cap' f' t' PRE POST H1 H2 H3 H4 HE PJ a Ha Wa.
  pose proof PRE as (HM & _). pose proof POST as (HM' & _ & _ & _ & _ & _ & _ & HFR & _ & HSW).
  destruct (scratch_dec B K regs a) as [S|S]; [exact (HSW a S)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply S; right; exact Ha].
  destruct (Z_le_gt_dec o a) as [Oa|Oa]; [destruct (Z_lt_ge_dec a (o + 32)) as [Ob|Ob]|].
  - pose proof PJ as (_ & _ & _ & HRW & _). replace a with (o + (a - o)) by lia. exact (proj1 (HRW (a - o) ltac:(lia))).
  - apply (HFR a ltac:(left; lia) (not_owned_hi _ _ _ _ a HM ltac:(lia)) (not_owned_hi _ _ _ _ a HM' ltac:(lia)) S).
    + intros HEa. destruct (HE a ltac:(left; lia) HEa) as [R|R]; [lia | pose proof (statics_low a R); lia].
    + exact Wa.
  - apply (HFR a ltac:(left; lia) (not_owned_hi _ _ _ _ a HM ltac:(lia)) (not_owned_hi _ _ _ _ a HM' ltac:(lia)) S).
    + intros HEa. destruct (HE a ltac:(left; lia) HEa) as [R|R]; [lia | pose proof (statics_low a R); lia].
    + exact Wa.
Qed.

Lemma fresh_grow : forall L A L' A' mem' md' buf cap buf' c1 c1' c2',
  MR L' A' mem' md' -> 0 <= c1 ->
  blocks L' A' = c1' ++ (buf' - 16, c1 + 16) :: c2' ->
  (cap = 0 /\ c1' ++ c2' = blocks L A \/
   cap <> 0 /\ exists b1 b2, blocks L A = b1 ++ (buf - 16, cap + 16) :: b2 /\ c1' ++ c2' = b1 ++ b2) ->
  forall a k, In (a, k) (blocks L A) -> 0 < k -> (a, k) <> (buf - 16, cap + 16) -> a <> buf' - 16.
Proof.
  intros L A L' A' mem' md' buf cap buf' c1 c1' c2' HM' Hc EQ HB a k Hin Hk Hne.
  assert (Hin' : In (a, k) (c1' ++ c2')).
  { destruct HB as [(_ & E)|(_ & b1 & b2 & E1 & E2)]; [rewrite E; exact Hin|].
    rewrite E2. rewrite E1 in Hin. apply (in_mid _ _ _ _ Hin). exact Hne. }
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') as D. rewrite EQ in D.
  destruct (pairwise_mid _ _ _ _ _ D Hin') as [R|R]; unfold ranges_disjoint in R; cbn [fst snd] in R; lia.
Qed.

Lemma wr_rel_put : forall lo hi L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b c',
  call_pre_k B MR PUT_K L A regs mem md ->
  pj_out_ok B mem Lam o buf len cap failed text ->
  ledger B L A mem Lam peak cnt fail ->
  Z.of_nat (length bs) = n -> len + n + 1 <= WMAX ->
  lo <= spZ regs - PUT_K -> spZ regs <= hi -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  put_ret B API RF L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b c' ->
  exists L' A' regs' mem' md' buf' Lam' peak' b',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\ regs_preserved regs regs' /\
    wr_rel lo hi L A mem md o buf (mkW failed text cap cnt fail calls) Lam peak b [bs] L' A' mem' md' buf' Lam' peak' b'.
Proof using AX SEGS.
  intros lo hi L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b c'
    PRE PJ LG LN NEED H1 H2 H3 H4 PR.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  pose proof PJ as (H8 & Ho & Ho32 & HRW & Rb & Rl & Rc & Wb & Wl & Wc & Wf & Hf & BOt & LT & CAP).
  pose proof (Nat2Z.is_nonneg (length bs)) as NN.
  destruct PR as (L' & A' & regs' & mem' & md' & buf' & Lam' & peak' & bp & Ec & HI' & GK' & HIN & HRG & PJ' & LG' & RS'
    & ARMS).
  exists L', A', regs', mem', md', buf', Lam', peak', bp. split; [exact Ec|].
  assert (CAPB : cap <> 0 -> In (buf - 16, cap + 16) (blocks L A)).
  { intros Hc. destruct CAP as [(C0 & _)|(_ & Hin & _)]; [lia|]. exact (proj2 (lblock_in _ _ _ _ _ _ _ _ _ LG Hin)). }
  unfold wr_rel. change (putN (mkW failed text cap cnt fail calls) [bs]) with (put1 (mkW failed text cap cnt fail calls) bs).
  destruct ARMS as [ARM|[ARM|[ARM|ARM]]].
  - destruct ARM as (HF & -> & -> & -> & -> & -> & -> & -> & KP & UK & POST).
    pose proof POST as (HM' & HWF' & HB' & HLL & HPT & HRP & HMD & HFR & HBK & HSW).
    assert (E1 : put1 (mkW failed text cap cnt fail calls) bs = mkW failed text cap cnt fail calls)
      by (apply put1_failed; cbn; exact HF).
    rewrite E1 in *. split; [exact HRP|].
    split; [exact HM'|]. split; [exact HWF'|]. split; [exact HB'|]. split; [split; [exact HI' | exact GK']|].
    split; [exact PJ'|].
    split; [exact LG'|]. split; [exact RS'|].
    split; [cbn [wfold]; unfold wnext; rewrite E1; cbn [w_cap]; rewrite Z.eqb_refl; reflexivity|].
    split; [left; repeat split|].
    split; [exact HLL|]. split; [exact HRG|]. split; [exact HIN|]. split; [exact HMD|].
    split; [exact (ptr_zero L A mem md A L HM HPT _)|].
    split; [exact (keeps_zero L A mem md mem' _ HM KP)|].
    split; [intros a k Hin Hk Hne; exact (buf_gone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM LG PJ Hin Hk Hne)|].
    split; [eapply put_frame; [exact POST | exact H1 | exact H2 | intros a _ []]|].
    eapply put_writable; [exact PRE | exact POST | exact H1 | exact H2 | exact H3 | exact H4 | intros a _ [] | exact PJ'].
  - destruct ARM as (-> & HN & -> & -> & -> & -> & -> & -> & -> & KP & UK & POST).
    pose proof POST as (HM' & HWF' & HB' & HLL & HPT & HRP & HMD & HFR & HBK & HSW).
    assert (E1 : put1 (mkW 0 text cap cnt fail calls) bs = mkW 0 (text ++ bs) cap cnt fail calls)
      by (apply put1_fit; lia).
    rewrite E1 in *. split; [exact HRP|].
    split; [exact HM'|]. split; [exact HWF'|]. split; [exact HB'|]. split; [split; [exact HI' | exact GK']|].
    split; [exact PJ'|].
    split; [exact LG'|]. split; [exact RS'|].
    split; [cbn [wfold]; unfold wnext; rewrite E1; cbn [w_cap]; rewrite Z.eqb_refl; reflexivity|].
    split; [left; repeat split|].
    split; [exact HLL|]. split; [exact HRG|]. split; [exact HIN|]. split; [exact HMD|].
    split; [exact (ptr_zero L A mem md A L HM HPT _)|].
    split; [exact KP|].
    split; [intros a k Hin Hk Hne; exact (buf_gone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM LG PJ Hin Hk Hne)|].
    assert (HE : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> fast_writes o buf len n a ->
                 o <= a < o + 32 \/ alloc_statics a).
    { intros a Hd [Hw|Hw]; [left; lia|]. exfalso.
      exact (blk_out L A mem md (buf - 16) (cap + 16) a HM (CAPB ltac:(lia)) ltac:(lia) Hd). }
    split; [eapply put_frame; [exact POST | exact H1 | exact H2 | exact HE]|].
    eapply put_writable; [exact PRE | exact POST | exact H1 | exact H2 | exact H3 | exact H4 | exact HE | exact PJ'].
  - destruct ARM as (-> & HG & HCF & -> & -> & -> & -> & BEQ & KP & UK & POST).
    pose proof POST as (HM' & HWF' & HB' & HLL & HPT & HRP & HMD & HFR & HBK & HSW).
    assert (E1 : put1 (mkW 0 text cap cnt fail calls) bs =
                 mkW 1 text cap ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) (calls ++ [newcap cap (len + n + 1)]))
      by (rewrite put1_starve by lia; rewrite LT, LN; reflexivity).
    rewrite E1 in *. split; [exact HRP|].
    split; [exact HM'|]. split; [exact HWF'|]. split; [exact HB'|]. split; [split; [exact HI' | exact GK']|].
    split; [exact PJ'|].
    split; [exact LG'|]. split; [exact RS'|].
    split; [cbn [wfold]; unfold wnext; rewrite E1; cbn [w_cap]; rewrite Z.eqb_refl; reflexivity|].
    split; [left; repeat split|].
    split; [exact HLL|]. split; [exact HRG|]. split; [exact HIN|]. split; [exact HMD|].
    split; [exact (ptr_zero L A mem md A' L' HM HPT _)|].
    split; [exact (keeps_zero L A mem md mem' _ HM KP)|].
    split; [intros a k Hin Hk Hne; exact (buf_gone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM LG PJ Hin Hk Hne)|].
    assert (HE : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> null_writes o buf cap a ->
                 o <= a < o + 32 \/ alloc_statics a).
    { intros a Hd [Hw|[Hw|(Hc & Hw)]]; [left; lia | right; exact Hw|]. exfalso.
      exact (blk_out L A mem md (buf - 16) (cap + 16) a HM (CAPB Hc) ltac:(lia) Hd). }
    split; [eapply put_frame; [exact POST | exact H1 | exact H2 | exact HE]|].
    eapply put_writable; [exact PRE | exact POST | exact H1 | exact H2 | exact H3 | exact H4 | exact HE | exact PJ'].
  - destruct ARM as (-> & HG & HCF & Hb' & -> & KP & UK & POST & (c1' & c2' & BEQ & BOLD) & l1 & l2 & HL & -> & ->).
    pose proof POST as (HM' & HWF' & HB' & HLL & HPT & HRP & HMD & HFR & HBK & HSW).
    assert (Hcp : cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j)
      by (destruct CAP as [(C0 & _)|(Hj & _)]; [left; exact C0 | right; exact Hj]).
    destruct (newcap_bound cap (len + n + 1) Hcp ltac:(unfold WMAX in NEED; lia)) as (j & Hj & Hnc & Hneed & H63 & Hcle).
    assert (E1 : put1 (mkW 0 text cap cnt fail calls) bs =
                 mkW 0 (text ++ bs) (newcap cap (len + n + 1)) ((cnt + 1) mod 2 ^ 64) fail
                   (calls ++ [newcap cap (len + n + 1)]))
      by (rewrite put1_grow by lia; rewrite LT, LN; reflexivity).
    rewrite E1 in *. split; [exact HRP|].
    split; [exact HM'|]. split; [exact HWF'|]. split; [exact HB'|]. split; [split; [exact HI' | exact GK']|].
    split; [exact PJ'|].
    split; [exact LG'|]. split; [exact RS'|].
    split; [cbn [wfold]; unfold wnext; rewrite E1; cbn [w_cap];
      rewrite (proj2 (Z.eqb_neq (newcap cap (len + n + 1)) cap) ltac:(lia)); reflexivity|].
    split; [right; cbn [w_cap]; split; [lia|]; exists l1, l2; split; [exact HL|]; split; reflexivity|].
    split; [exact HLL|]. split; [exact HRG|]. split; [exact HIN|]. split; [exact HMD|].
    split; [intros p q Hp Hne; split; [exact (UK p q Hp Hne) | exact (ptr_keep L L' A p q HWF HLL Hp)]|].
    split; [exact KP|].
    split; [exact (fresh_grow L A L' A' mem' md' buf cap buf' (newcap cap (len + n + 1)) c1' c2' HM' ltac:(lia) BEQ BOLD)|].
    assert (Hnew : In (buf' - 16, newcap cap (len + n + 1) + 16) (blocks L' A'))
      by (rewrite BEQ; apply in_or_app; right; left; reflexivity).
    assert (HE : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
                 grow_writes o buf cap buf' (newcap cap (len + n + 1)) a -> o <= a < o + 32 \/ alloc_statics a).
    { intros a Hd [Hw|[Hw|[(Hc & Hw)|Hw]]]; [left; lia | right; exact Hw | |]; exfalso.
      - exact (blk_out L A mem md (buf - 16) (cap + 16) a HM (CAPB Hc) ltac:(lia) Hd).
      - exact (blk_out L' A' mem' md' (buf' - 16) _ a HM' Hnew ltac:(lia) Hd). }
    split; [eapply put_frame; [exact POST | exact H1 | exact H2 | exact HE]|].
    eapply put_writable; [exact PRE | exact POST | exact H1 | exact H2 | exact H3 | exact H4 | exact HE | exact PJ'].
Qed.

Lemma wr_ret_put : forall L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b c',
  call_pre_k B MR PUT_K L A regs mem md ->
  pj_out_ok B mem Lam o buf len cap failed text ->
  ledger B L A mem Lam peak cnt fail ->
  Z.of_nat (length bs) = n -> len + n + 1 <= WMAX ->
  put_ret B API RF L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b c' ->
  wr_ret PUT_K L A regs mem md o buf (mkW failed text cap cnt fail calls) Lam peak b [bs] c'.
Proof using AX SEGS.
  intros L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b c' PRE PJ LG LN NEED PR.
  pose proof PRE as (_ & _ & _ & _ & _ & Hceil & Hsp & _).
  destruct (wr_rel_put (spZ regs - PUT_K) (spZ regs) L A regs mem md o n buf len cap failed text bs Lam peak cnt fail
    calls b c' PRE PJ LG LN NEED ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PR)
    as (L' & A' & regs' & mem' & md' & buf' & Lam' & peak' & b' & Ec & RP & R).
  exists L', A', regs', mem', md', buf', Lam', peak', b'. split; [exact Ec|]. split; [exact RP | exact R].
Qed.

End W.
