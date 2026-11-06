From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition MALLOC_K : Z := ALLOC_STACK + 32.
Definition FREE_K : Z := ALLOC_STACK.
Definition REALLOC_K : Z := REALLOC_STACK + 48.
Definition LITERAL_K : Z := 64.
Definition STRDUP_K : Z := ALLOC_STACK + 64.

Definition PJ_FREE_F : Z := 48.
Definition GROW_F : Z := 48.
Definition PARSE_STRING_F : Z := 128.
Definition PARSE_VALUE_F : Z := 64.
Definition PARSE_ITEMS_F : Z := 96.
Definition PJ_PARSE_F : Z := 48.
Definition PJ_GET_F : Z := 80.
Definition PJ_STRING_F : Z := 32.
Definition PJ_SET_F : Z := 48.

Definition PJ_FREE_K (d : nat) : Z := PJ_FREE_F * (Z.of_nat d + 1) + FREE_K.
Definition GROW_K : Z := GROW_F + REALLOC_K.
Definition PARSE_STRING_K : Z := PARSE_STRING_F + Z.max MALLOC_K FREE_K.

Definition PV_LEAF : Z := Z.max PARSE_STRING_K (Z.max LITERAL_K (Z.max MALLOC_K strtod_c.STRTOD_K)).
Definition PI_LEAF : Z := Z.max GROW_K (Z.max PARSE_STRING_K FREE_K).

Fixpoint kv_up (k : nat) : Z :=
  match k with
  | O => PARSE_VALUE_F + Z.max PV_LEAF PARSE_ITEMS_F
  | S k' => PARSE_VALUE_F + Z.max PV_LEAF (PARSE_ITEMS_F + Z.max PI_LEAF (kv_up k'))
  end.

Definition PARSE_VALUE_K (d : nat) : Z := kv_up (MAXD - d).

Definition PARSE_ITEMS_K (d : nat) : Z :=
  if (d <? MAXD)%nat then PARSE_ITEMS_F + Z.max PI_LEAF (PARSE_VALUE_K (S d)) else PARSE_ITEMS_F.

Definition PJ_PARSE_K : Z := PJ_PARSE_F + Z.max (PARSE_VALUE_K 0) (PJ_FREE_K 33).

Definition PJ_GET_K : Z := PJ_GET_F.
Definition PJ_STRING_K : Z := PJ_STRING_F + STRDUP_K.
Definition PJ_SET_K (d : nat) : Z := PJ_SET_F + Z.max PJ_GET_K (Z.max (PJ_FREE_K d) (Z.max GROW_K STRDUP_K)).

Definition jr_strtod (txt : list Z) : Z * Z :=
  match strtod_c.strtod_model txt with
  | Some (bits, c) => (c, bits)
  | None => (0, 0)
  end.

Definition zb (bs : list byte) : list Z := map (fun b : byte => bv_unsigned b) bs.

Definition rest_at (tb : list byte) (text p : Z) : list Z := zb (skipn (Z.to_nat (p - text)) tb).

Definition lin (Lam : list (Z * Z)) (a k : Z) : Prop := In (a, k) Lam.

Definition freed (D : list (Z * Z)) (a n : Z) : Prop := In (a + 16, n - 16) D.

Definition blk_set (D : list (Z * Z)) (x : Z) : Prop := exists a k, In (a, k) D /\ a - 16 <= x < a + k.

Definition cap2 (cap : Z) : Z := if cap =? 0 then 8 else 2 * cap.

Definition kids_blk (kids cap : Z) : list (Z * Z) := if cap =? 0 then [] else [(kids, 56 * cap)].

Definition keys_blk (ty keys cap : Z) : list (Z * Z) :=
  if (cap =? 0) || negb (ty =? 6) then [] else [(keys, 8 * cap)].

Definition pj_in_set (q x : Z) : Prop := q <= x < q + 8 \/ q + 16 <= x < q + 20.

Definition rd_writes (q v : Z) (D : list (Z * Z)) (x : Z) : Prop :=
  v <= x < v + 56 \/ pj_in_set q x \/ blk_set D x \/ alloc_statics x.

Fixpoint hpeak (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => Z.max 0 (held_ev e + hpeak r)
  end.

Definition oks (ok : list bool) (cnt fail : Z) (k : nat) : Prop :=
  forall i, (i < k)%nat -> nth i ok true = negb (cnt + Z.of_nat i =? fail).

Definition fail_after (cnt fail : Z) (k : nat) (fail' : Z) : Prop :=
  (cnt <= fail < cnt + Z.of_nat k -> fail' = 2 ^ 64 - 1) /\
  (~ (cnt <= fail < cnt + Z.of_nat k) -> fail' = fail).

Definition fregs_kept (f f' : YK11.FPState) : Prop :=
  forall r, r = 8 \/ r = 9 \/ 18 <= r <= 27 ->
    reg_get (@fp_regs f') (Z_to_bv 5 r) = reg_get (@fp_regs f) (Z_to_bv 5 r).

Section Reader.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rf_grow (b : rf_R F) (m n : Z) : rf_R F :=
  if m =? 0 then rf_malloc F b (n + 16) else rf_realloc F b (m + 16) (n + 16).

Definition rf_ev (b : rf_R F) (e : ev) : rf_R F :=
  match e with
  | EAlloc n => rf_malloc F b (Z.of_nat n + 16)
  | EGrow m n => rf_grow b (Z.of_nat m) (Z.of_nat n)
  | EFail _ => b
  | EFree n => rf_free F b (Z.of_nat n + 16)
  end.

Definition rf_run (b : rf_R F) (tr : list ev) : rf_R F := fold_left rf_ev tr b.

Fixpoint room_run (b : rf_R F) (tr : list ev) : Prop :=
  match tr with
  | [] => True
  | e :: r =>
      (is_call e = true -> rf_room F b (Z.of_nat (esize e) + 16) /\ Z.of_nat (esize e) + 16 <= 2 ^ 28) /\
      room_run (rf_ev b e) r
  end.

Definition rf_frees (b : rf_R F) (D : list (Z * Z)) : rf_R F :=
  fold_left (fun b' ak => rf_free F b' (snd ak + 16)) D b.

Definition nlive_ev (e : ev) : Z :=
  match e with
  | EAlloc _ => 1
  | EGrow O _ => 1
  | EGrow (S _) _ => 0
  | EFail _ => 0
  | EFree _ => -1
  end.

Fixpoint nlive (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => nlive_ev e + nlive r
  end.

Definition rd_cells (mem : word -> option byte) : Prop :=
  U.MemNorm.ro_agree segs mem /\
  word_mem segs mem (ms_got_guard B) (ms_guard B) /\
  exists g, word_mem segs mem (ms_guard B) g.

Definition reader_env (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) : Prop :=
  ms_segs B = rsegs /\ ms_tp B = strtod_c.STRTOD_TP /\ errno_addr B = strtod_c.STRTOD_ERRNO /\
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD /\ ms_guard B = strtod_c.STRTOD_GUARD /\
  call_pre_k B MR K L A regs mem md /\
  spZ regs <= 2 ^ 47 /\ strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - K /\
  frm_zero fp_csr /\
  rd_cells mem.

Definition new_blks (L : layout) (A : astate) (D : list (Z * Z)) : Prop :=
  forall a k, In (a, k) D -> ~ In (a - 16, k + 16) (blocks L A).

Definition rpost (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (E : Z -> Prop) (gone : Z -> Z -> Prop)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (st_init_done A' = false -> forall i, 0 <= i < 8 ->
     mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> ~ gone (ptr_addr L p) n -> In (p, n) (user_blocks A')) /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> (forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 -> ~ owned B L0 A0 a) ->
     ~ scratch_k B K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B K regs a -> writable_at segs mem' a).

Definition rplace (L : layout) (A : astate) (Lam : list (Z * Z)) (regs : bvmap 5 word) (mem : word -> option byte)
    (p : Z) : Prop :=
  pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) (spZ regs) (2 ^ 64) p /\
  (spZ regs <= p -> st_init_done A = false -> auxv_pre B (ly_sec L) (p + 56) mem) /\
  (forall i, 0 <= i < 56 ->
     ~ owned B L A (p + i) /\ ~ alloc_statics (p + i) /\ ~ (errno_addr B <= p + i < errno_addr B + 4) /\
     ~ in_img B (p + i)).

Definition text_ok (L : layout) (A : astate) (Lam : list (Z * Z)) (regs : bvmap 5 word) (text len : Z) : Prop :=
  (spZ regs <= text \/ (forall i, 0 <= i < len -> in_img B (text + i)) \/
   (exists a k, In (a, k) (blocks L A) /\ ~ lin Lam (a + 16) (k - 16) /\ a <= text /\ text + len <= a + k) \/
   exists a k, lin Lam a k /\ a <= text /\ text + len <= a + k) /\
  (forall i, 0 <= i < len ->
     ~ owned B L A (text + i) /\ ~ alloc_statics (text + i) /\ ~ (errno_addr B <= text + i < errno_addr B + 4)).

Definition cstr_ok (Lam : list (Z * Z)) (s n : Z) : Prop :=
  (forall i, 0 <= i < n -> Mem.ro_addr segs (Z_to_bv 64 (s + i)) = true) \/
  exists a k, lin Lam a k /\ a <= s /\ s + n <= a + k.

Definition pj_in_after (mem : word -> option byte) (q text len lo hi : Z) : Prop :=
  exists p' d', text <= p' <= text + len /\ lo <= d' <= hi /\
    Mem.bytes_at segs mem q (Mem.le8 (Z_to_bv 64 p')) /\
    Mem.bytes_at segs mem (q + 8) (Mem.le8 (Z_to_bv 64 (text + len))) /\
    Mem.bytes_at segs mem (q + 16) (Mem.le4 (Z_to_bv 64 d')) /\
    Mem.wr_at segs mem q 24.

End Reader.

Lemma rf_frees_app : forall F b D1 D2, rf_frees F b (D1 ++ D2) = rf_frees F (rf_frees F b D1) D2.
Proof. intros F b D1 D2. unfold rf_frees. apply fold_left_app. Qed.

Fixpoint rm1n (k : nat) (s : list nat) : list nat :=
  match s with
  | [] => []
  | x :: r => if Nat.eqb x k then r else x :: rm1n k r
  end.

Definition lsz_ev (s : list nat) (e : ev) : list nat :=
  match e with
  | EAlloc n => n :: s
  | EGrow O n => n :: s
  | EGrow m n => n :: rm1n m s
  | EFail _ => s
  | EFree n => rm1n n s
  end.

Definition lsz (tr : list ev) : list nat := fold_left lsz_ev tr [].

Fixpoint zl (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: r => x + zl r
  end.

Lemma zl_perm : forall l l', Permutation l l' -> zl l = zl l'.
Proof. intros l l' H. induction H; cbn [zl]; lia. Qed.

Lemma zl_app : forall l1 l2, zl (l1 ++ l2) = zl l1 + zl l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn [app zl]; [lia | rewrite IH; lia]. Qed.

Lemma lsum_zl : forall D, lsum D = zl (map snd D).
Proof. induction D as [|[a k] D IH]; cbn [lsum map zl snd]; lia. Qed.

Lemma rm1_hit : forall k s t, In k s ->
  Z.of_nat (length (rm1n k s)) + 1 = Z.of_nat (length s) /\
  zl (map Z.of_nat (rm1n k s)) + Z.of_nat k = zl (map Z.of_nat s) /\
  rm1n k (s ++ t) = rm1n k s ++ t.
Proof.
  intros k s t. induction s as [|x s IH]; intros H; [destruct H|].
  cbn [rm1n app]. destruct (Nat.eqb_spec x k) as [->|Hne].
  - cbn [length map zl]. split; [lia|]. split; [lia | reflexivity].
  - destruct H as [H|H]; [contradiction|].
    destruct (IH H) as (H1 & H2 & H3). cbn [length map zl app]. rewrite H3.
    split; [lia|]. split; [lia | reflexivity].
Qed.

Lemma rm1_miss : forall k s, ~ In k s -> rm1n k s = s.
Proof.
  intros k s. induction s as [|x s IH]; intros H; [reflexivity|].
  cbn [rm1n]. destruct (Nat.eqb_spec x k) as [->|Hne]; [exfalso; apply H; left; reflexivity|].
  rewrite IH; [reflexivity|]. intros Hk. apply H. right. exact Hk.
Qed.

Lemma lsz_ev_ge : forall s e, Z.of_nat (length s) + nlive_ev e <= Z.of_nat (length (lsz_ev s e)).
Proof.
  intros s e. destruct e as [n|[|m] n|n|n]; cbn [lsz_ev nlive_ev length]; try lia.
  - destruct (in_dec Nat.eq_dec (S m) s) as [H|H].
    + destruct (rm1_hit (S m) s [] H) as (H1 & _). lia.
    + rewrite (rm1_miss _ _ H). lia.
  - destruct (in_dec Nat.eq_dec n s) as [H|H].
    + destruct (rm1_hit n s [] H) as (H1 & _). lia.
    + rewrite (rm1_miss _ _ H). lia.
Qed.

Lemma lsz_ev_eq : forall s e t, Z.of_nat (length (lsz_ev s e)) = Z.of_nat (length s) + nlive_ev e ->
  zl (map Z.of_nat (lsz_ev s e)) = zl (map Z.of_nat s) + held_ev e /\ lsz_ev (s ++ t) e = lsz_ev s e ++ t.
Proof.
  intros s e t. destruct e as [n|[|m] n|n|n]; cbn [lsz_ev nlive_ev held_ev length map zl app]; intros H.
  - split; [lia | reflexivity].
  - split; [lia | reflexivity].
  - destruct (in_dec Nat.eq_dec (S m) s) as [Hi|Hi].
    + destruct (rm1_hit (S m) s t Hi) as (H1 & H2 & H3). rewrite H3. split; [lia | reflexivity].
    + rewrite (rm1_miss _ _ Hi) in H. lia.
  - split; [lia | reflexivity].
  - destruct (in_dec Nat.eq_dec n s) as [Hi|Hi].
    + destruct (rm1_hit n s t Hi) as (H1 & H2 & H3). rewrite H3. split; [lia | reflexivity].
    + rewrite (rm1_miss _ _ Hi) in H. lia.
Qed.

Lemma lszf_ge : forall tr s, Z.of_nat (length s) + nlive tr <= Z.of_nat (length (fold_left lsz_ev tr s)).
Proof.
  induction tr as [|e tr IH]; intros s; cbn [fold_left nlive]; [lia|].
  pose proof (lsz_ev_ge s e). pose proof (IH (lsz_ev s e)). lia.
Qed.

Lemma lszf_eq : forall tr s t, Z.of_nat (length (fold_left lsz_ev tr s)) = Z.of_nat (length s) + nlive tr ->
  zl (map Z.of_nat (fold_left lsz_ev tr s)) = zl (map Z.of_nat s) + held tr /\
  fold_left lsz_ev tr (s ++ t) = fold_left lsz_ev tr s ++ t.
Proof.
  induction tr as [|e tr IH]; intros s t H; cbn [fold_left nlive held] in *; [split; [lia | reflexivity]|].
  pose proof (lsz_ev_ge s e) as G1. pose proof (lszf_ge tr (lsz_ev s e)) as G2.
  assert (E1 : Z.of_nat (length (lsz_ev s e)) = Z.of_nat (length s) + nlive_ev e) by lia.
  assert (E2 : Z.of_nat (length (fold_left lsz_ev tr (lsz_ev s e))) = Z.of_nat (length (lsz_ev s e)) + nlive tr)
    by lia.
  destruct (lsz_ev_eq s e t E1) as (S1 & S2). destruct (IH (lsz_ev s e) t E2) as (T1 & T2).
  rewrite S2, T2. split; [lia | reflexivity].
Qed.

Lemma lsz_held : forall tr, Z.of_nat (length (lsz tr)) = nlive tr -> zl (map Z.of_nat (lsz tr)) = held tr.
Proof.
  intros tr H. unfold lsz in *. destruct (lszf_eq tr [] [] ltac:(cbn [length]; lia)) as (H1 & _).
  cbn [map zl] in H1. lia.
Qed.

Lemma lsz_app : forall tr1 tr2, Z.of_nat (length (lsz tr2)) = nlive tr2 -> lsz (tr1 ++ tr2) = lsz tr2 ++ lsz tr1.
Proof.
  intros tr1 tr2 H. unfold lsz in *. rewrite fold_left_app.
  destruct (lszf_eq tr2 [] (fold_left lsz_ev tr1 []) ltac:(cbn [length]; lia)) as (_ & H2). exact H2.
Qed.

Lemma lsz_counts : forall D tr, Permutation (map snd D) (map Z.of_nat (lsz tr)) -> Z.of_nat (length D) = nlive tr ->
  lsum D = held tr.
Proof.
  intros D tr HP HN. rewrite lsum_zl, (zl_perm _ _ HP). apply lsz_held.
  rewrite <- HN, <- (length_map Z.of_nat (lsz tr)), <- (Permutation_length HP), length_map. reflexivity.
Qed.

Lemma sb_form_malloc : forall (b : sbound) n, rf_malloc sb_form b n = sb_malloc b n.
Proof. reflexivity. Qed.

Lemma sb_form_free : forall (b : sbound) n, rf_free sb_form b n = sb_free b n.
Proof. reflexivity. Qed.

Lemma sb_form_realloc : forall (b : sbound) k n, rf_realloc sb_form b k n = sb_realloc b k n.
Proof. reflexivity. Qed.

Lemma sb_run_eq : forall tr (b : sbound),
  rf_run sb_form b tr = SB (sb_live b + nlive tr) (sb_bytes b + held tr + 16 * nlive tr) (sb_cap b).
Proof.
  unfold rf_run. induction tr as [|e tr IH]; intros b; cbn [fold_left nlive held].
  - destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
  - rewrite IH. destruct e as [n|[|m] n|n|n]; cbn [rf_ev nlive_ev held_ev].
    + rewrite sb_form_malloc. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    + unfold rf_grow. change (Z.of_nat 0) with 0. rewrite Z.eqb_refl, sb_form_malloc. unfold sb_malloc.
      cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    + unfold rf_grow. rewrite (proj2 (Z.eqb_neq (Z.of_nat (S m)) 0)) by lia. rewrite sb_form_realloc.
      unfold sb_realloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
    + f_equal; lia.
    + rewrite sb_form_free. unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma sb_frees_eq : forall D (b : sbound),
  rf_frees sb_form b D =
  SB (sb_live b - Z.of_nat (length D)) (sb_bytes b - lsum D - 16 * Z.of_nat (length D)) (sb_cap b).
Proof.
  unfold rf_frees. induction D as [|[a k] D IH]; intros b; cbn [fold_left length lsum snd].
  - destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
  - rewrite IH, sb_form_free. unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma sb_frees_run : forall (b : sbound) tr D, Permutation (map snd D) (map Z.of_nat (lsz tr)) ->
  Z.of_nat (length D) = nlive tr -> rf_frees sb_form (rf_run sb_form b tr) D = b.
Proof.
  intros b tr D HP HN. pose proof (lsz_counts D tr HP HN) as HL. rewrite sb_frees_eq, sb_run_eq.
  destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma sb_frees_perm : forall (b : sbound) D D', Permutation D D' ->
  rf_frees sb_form b D = rf_frees sb_form b D'.
Proof.
  intros b D D' HP. revert b. unfold rf_frees.
  induction HP as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; intros b; cbn [fold_left].
  - reflexivity.
  - apply IH.
  - f_equal. change (sb_free (sb_free b (snd y + 16)) (snd x + 16) = sb_free (sb_free b (snd x + 16)) (snd y + 16)).
    unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
  - rewrite IH1. apply IH2.
Qed.
