From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Open Scope Z_scope.

Section PjStruct.
Variable segs : list Segment.

Definition pj_rw (m : word -> option byte) (p : Z) : Prop :=
  p mod 8 = 0 /\ stk segs m p (p + 56).

Definition pj_u64 (m : word -> option byte) (a v : Z) : Prop :=
  0 <= v < 2 ^ 64 /\ bytes_at segs m a (le8 (Z_to_bv 64 v)).

Definition pj_u32 (m : word -> option byte) (a v : Z) : Prop :=
  0 <= v < 2 ^ 32 /\ bytes_at segs m a (le4 (Z_to_bv 64 v)).

Definition pj_hdr (m : word -> option byte) (p ty num str kids keys n cap : Z) : Prop :=
  pj_rw m p /\ pj_u32 m p ty /\ pj_u64 m (p + 8) num /\ pj_u64 m (p + 16) str /\
  pj_u64 m (p + 24) kids /\ pj_u64 m (p + 32) keys /\ pj_u64 m (p + 40) n /\ pj_u64 m (p + 48) cap.

Definition pj_cbytes (m : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\ bytes_at segs m a (map (Z_to_bv 8) (s ++ [0])).

Definition pj_cstr (m : word -> option byte) (lblk : Z -> Z -> Prop) (a k : Z) (s : list Z) : Prop :=
  lblk a k /\ Z.of_nat (length s) + 1 <= k /\ pj_cbytes m a s.

Definition pj_holds (b : Z * Z) (x : Z) : Prop := fst b <= x < fst b + snd b.

Definition pj_apart (D : list (Z * Z)) (p : Z) : Prop :=
  forall b x, In b D -> pj_holds b x -> ~ (p <= x < p + 56).

Definition pj_foot (p : Z) (D : list (Z * Z)) (x : Z) : Prop :=
  (p <= x < p + 56) \/ exists b, In b D /\ pj_holds b x.

Fixpoint pj_items (P : Z -> jv -> list (Z * Z) -> Prop) (a : Z) (l : list jv) (D : list (Z * Z)) : Prop :=
  match l with
  | [] => D = []
  | u :: r => exists D1 D2, D = D1 ++ D2 /\ P a u D1 /\ pj_items P (a + 56) r D2
  end.

Fixpoint pj_mems (m : word -> option byte) (lblk : Z -> Z -> Prop) (P : Z -> jv -> list (Z * Z) -> Prop)
    (a ka : Z) (l : list (list Z * jv)) (D : list (Z * Z)) : Prop :=
  match l with
  | [] => D = []
  | (nm, u) :: r => exists x k D1 D2, D = (x, k) :: D1 ++ D2 /\ pj_u64 m ka x /\ pj_cstr m lblk x k nm /\
      P a u D1 /\ pj_mems m lblk P (a + 56) (ka + 8) r D2
  end.

Fixpoint pj_node (m : word -> option byte) (lblk : Z -> Z -> Prop) (p : Z) (t : jv) (D : list (Z * Z))
    {struct t} : Prop :=
  NoDup D /\ pj_apart D p /\
  exists num str kids keys n cap,
    pj_hdr m p (tag t) num str kids keys n cap /\
    match t with
    | JNull | JFalse | JTrue => str = 0 /\ kids = 0 /\ keys = 0 /\ n = 0 /\ cap = 0 /\ D = []
    | JNum txt bits => num = bits /\ kids = 0 /\ keys = 0 /\ n = 0 /\ cap = 0 /\
        exists k, pj_cstr m lblk str k txt /\ D = [(str, k)]
    | JStr s => kids = 0 /\ keys = 0 /\ n = 0 /\ cap = 0 /\
        exists k, pj_cstr m lblk str k s /\ D = [(str, k)]
    | JArr items => str = 0 /\ keys = 0 /\ n = Z.of_nat (length items) /\ n <= cap /\
        (cap = 0 /\ kids = 0 \/ 0 < cap /\ lblk kids (56 * cap)) /\
        exists Di, D = (if cap =? 0 then [] else [(kids, 56 * cap)]) ++ Di /\
          pj_items (pj_node m lblk) kids items Di
    | JObj members => str = 0 /\ n = Z.of_nat (length members) /\ n <= cap /\
        (cap = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap)) /\
        exists Di, D = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di /\
          pj_mems m lblk (pj_node m lblk) kids keys members Di
    end.

Definition pj_key (m : word -> option byte) (lblk : Z -> Z -> Prop) (ks : bool) (ka : Z) (Dk : list (Z * Z)) : Prop :=
  if ks then exists x, pj_u64 m ka x /\ (x = 0 /\ Dk = [] \/ exists k, lblk x k /\ Dk = [(x, k)])
  else Dk = [].

Fixpoint pf_items (m : word -> option byte) (lblk : Z -> Z -> Prop) (P : Z -> list (Z * Z) -> Prop)
    (ks : bool) (a ka : Z) (n : nat) (D : list (Z * Z)) : Prop :=
  match n with
  | O => D = []
  | S n' => exists Dk D1 D2, D = Dk ++ D1 ++ D2 /\ pj_key m lblk ks ka Dk /\ P a D1 /\
      pf_items m lblk P ks (a + 56) (ka + 8) n' D2
  end.

Definition pj_fshape (m : word -> option byte) (lblk : Z -> Z -> Prop)
    (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) (p : Z) (D : list (Z * Z)) : Prop :=
  NoDup D /\ pj_apart D p /\
  exists ty num str kids keys n cap ks Ds Dk Dy Di,
    pj_hdr m p ty num str kids keys n cap /\
    (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) /\
    (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) /\
    (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) /\
    Permutation D (Ds ++ Dk ++ Dy ++ Di) /\
    Pi ks kids keys n Di.

Fixpoint pj_fd (m : word -> option byte) (lblk : Z -> Z -> Prop) (d : nat) (p : Z) (D : list (Z * Z))
    {struct d} : Prop :=
  match d with
  | O => pj_fshape m lblk (fun _ _ _ n Di => n = 0 /\ Di = []) p D
  | S d' => pj_fshape m lblk (fun ks kids keys n Di => pf_items m lblk (pj_fd m lblk d') ks kids keys (Z.to_nat n) Di) p D
  end.

Definition pj_freeable (m : word -> option byte) (lblk : Z -> Z -> Prop) (p : Z) (D : list (Z * Z)) : Prop :=
  exists d, pj_fd m lblk d p D.

Definition pj_zero (m : word -> option byte) (p : Z) : Prop :=
  pj_rw m p /\ bytes_at segs m p (repeat (Z_to_bv 8 0) 56).

Definition pj_slots_at (lblk : Z -> Z -> Prop) (ty kids keys n cap : Z) : Prop :=
  (ty = 5 \/ ty = 6) /\ n <= cap <= 2 ^ 54 /\
  (cap = 0 -> kids = 0 /\ (ty = 6 -> keys = 0)) /\
  (0 < cap -> lblk kids (56 * cap) /\ (ty = 6 -> lblk keys (8 * cap))).

Definition pj_slots (m : word -> option byte) (lblk : Z -> Z -> Prop) (p : Z) : Prop :=
  exists ty num str kids keys n cap, pj_hdr m p ty num str kids keys n cap /\ pj_slots_at lblk ty kids keys n cap.

Definition pj_open_n (m : word -> option byte) (lblk : Z -> Z -> Prop) (p o nf : Z) (ts : list jv)
    (ns : list (list Z)) (D : list (Z * Z)) : Prop :=
  NoDup D /\ pj_apart D p /\
  exists num kids keys cap Di,
    pj_hdr m p (5 + o) num 0 kids keys nf cap /\ pj_slots_at lblk (5 + o) kids keys nf cap /\
    (o = 0 /\ keys = 0 /\ D = (if cap =? 0 then [] else [(kids, 56 * cap)]) ++ Di /\
       pj_items (pj_node m lblk) kids ts Di \/
     o = 1 /\ length ns = length ts /\ D = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di /\
       pj_mems m lblk (pj_node m lblk) kids keys (combine ns ts) Di).

Definition pj_open (m : word -> option byte) (lblk : Z -> Z -> Prop) (p o k : Z) (ts : list jv)
    (ns : list (list Z)) (D : list (Z * Z)) : Prop :=
  k = Z.of_nat (length ts) /\ pj_open_n m lblk p o k ts ns D.

Definition pj_place (lblk hblk : Z -> Z -> Prop) (sl sh p : Z) : Prop :=
  sl <= p /\ p + 56 <= sh \/
  (exists a k, hblk a k /\ ~ lblk (a + 16) (k - 16) /\ a <= p /\ p + 56 <= a + k) \/
  (exists a k, lblk a k /\ a <= p /\ p + 56 <= a + k).

Lemma pj_list_ext : forall (A : Type) (l l' : list A), length l = length l' ->
  (forall i, (i < length l)%nat -> nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros A l. induction l as [|x l IH]; intros [|y l'] Hl H; cbn in Hl; try lia; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(cbn; lia)). cbn in H. congruence.
  - apply IH; [lia|]. intros i Hi. apply (H (S i)). cbn; lia.
Qed.

Lemma pj_nth_repeat : forall (A : Type) (z : A) n i, (i < n)%nat -> nth_error (repeat z n) i = Some z.
Proof. intros A z n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i as [|i]; cbn; [reflexivity|]. apply IH; lia. Qed.

Lemma pj_combine_len : forall (A B : Type) (l1 : list A) (l2 : list B), length l1 = length l2 ->
  length (combine l1 l2) = length l2.
Proof. intros A B l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in *; try lia. f_equal. apply IH. lia. Qed.

Lemma pj_bytes_uniq : forall m a bs cs, bytes_at segs m a bs -> bytes_at segs m a cs -> length bs = length cs -> bs = cs.
Proof.
  intros m a bs cs (_ & _ & H1) (_ & _ & H2) Hl. apply pj_list_ext; [exact Hl|].
  intros i Hi. rewrite <- (H1 i Hi), <- (H2 i) by lia. reflexivity.
Qed.

Lemma pj_u64_uniq : forall m a v v', pj_u64 m a v -> pj_u64 m a v' -> v = v'.
Proof.
  intros m a v v' (Hv & Bv) (Hv' & Bv').
  assert (E : le8 (Z_to_bv 64 v) = le8 (Z_to_bv 64 v')).
  { apply (pj_bytes_uniq m a); [exact Bv | exact Bv' | rewrite !length_le8; reflexivity]. }
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal (@bv_unsigned 64)) in E.
  change (Z_to_bv 64 v) with (wa v) in E. change (Z_to_bv 64 v') with (wa v') in E.
  rewrite !wa_unsigned in E by lia. exact E.
Qed.

Lemma pj_bytes_eq : forall m m' a bs, bytes_at segs m a bs ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x) ->
  bytes_at segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) E. split; [lia|]. split; [lia|].
  intros i Hi. specialize (H i Hi). unfold mrd in H |- *. rewrite E; [exact H|].
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma pj_stk_eq : forall m m' lo hi, stk segs m lo hi ->
  (forall x : word, lo <= bv_unsigned x < hi -> m' x = m x) -> stk segs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) E. split; [lia|]. split; [lia|].
  intros a Ha. assert (Ea : m' (wa a) = m (wa a)) by (apply E; rewrite wa_unsigned by lia; lia).
  destruct (H a Ha) as [W [b R]]. split.
  - unfold wview in *. rewrite Ea. exact W.
  - exists b. unfold mrd in *. rewrite Ea. exact R.
Qed.

Lemma pj_u64_eq : forall m m' a v, pj_u64 m a v ->
  (forall x : word, a <= bv_unsigned x < a + 8 -> m' x = m x) -> pj_u64 m' a v.
Proof.
  intros m m' a v (Hv & B) E. split; [exact Hv|]. apply (pj_bytes_eq m m'); [exact B|].
  intros x Hx. apply E. rewrite length_le8 in Hx. lia.
Qed.

Lemma pj_hdr_eq : forall m m' p ty num str kids keys n cap,
  pj_hdr m p ty num str kids keys n cap ->
  (forall x : word, p <= bv_unsigned x < p + 56 -> m' x = m x) ->
  pj_hdr m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap ((Ha & Hs) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) E.
  assert (F : forall a bs, bytes_at segs m a bs -> p <= a -> a + Z.of_nat (length bs) <= p + 56 -> bytes_at segs m' a bs).
  { intros a bs B Hpa Hab. apply (pj_bytes_eq m m'); [exact B|]. intros x Hx. apply E. lia. }
  split; [split; [exact Ha | exact (pj_stk_eq m m' p (p + 56) Hs E)]|].
  split; [split; [exact T0 | apply F; [exact T1 | lia | rewrite length_le4; lia]]|].
  split; [split; [exact N0 | apply F; [exact N1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact S0 | apply F; [exact S1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact K0 | apply F; [exact K1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact Y0 | apply F; [exact Y1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact C0 | apply F; [exact C1 | lia | rewrite length_le8; lia]]|].
  split; [exact P0 | apply F; [exact P1 | lia | rewrite length_le8; lia]].
Qed.

Lemma pj_cstr_eq : forall m lblk m' lblk' a k s,
  pj_cstr m lblk a k s -> lblk' a k ->
  (forall x : word, pj_holds (a, k) (bv_unsigned x) -> m' x = m x) ->
  pj_cstr m' lblk' a k s.
Proof.
  intros m lblk m' lblk' a k s (Hl & Hk & Hf & Hb) Hl' E.
  split; [exact Hl'|]. split; [exact Hk|]. split; [exact Hf|].
  apply (pj_bytes_eq m m'); [exact Hb|]. intros x Hx. apply E. unfold pj_holds; cbn [fst snd].
  rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma pj_bytes_move : forall m p p' bs off cs,
  length bs = 56%nat -> bytes_at segs m p bs -> bytes_at segs m p' bs ->
  bytes_at segs m (p + off) cs -> 0 <= off -> off + Z.of_nat (length cs) <= 56 ->
  bytes_at segs m (p' + off) cs.
Proof.
  intros m p p' bs off cs Hl (Hp & Hpl & HP) (Hq & Hql & HQ) (Hc & Hcl & HC) Ho Hoc.
  split; [lia|]. split; [lia|].
  intros i Hi.
  assert (E1 := HQ (Z.to_nat off + i)%nat ltac:(lia)).
  assert (E2 := HP (Z.to_nat off + i)%nat ltac:(lia)).
  replace (p' + off + Z.of_nat i) with (p' + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite E1, <- E2.
  replace (p + Z.of_nat (Z.to_nat off + i)) with (p + off + Z.of_nat i) by lia.
  apply HC. exact Hi.
Qed.

Lemma pj_hdr_move : forall m p p' bs ty num str kids keys n cap,
  pj_hdr m p ty num str kids keys n cap -> length bs = 56%nat ->
  bytes_at segs m p bs -> bytes_at segs m p' bs -> pj_rw m p' ->
  pj_hdr m p' ty num str kids keys n cap.
Proof.
  intros m p p' bs ty num str kids keys n cap (_ & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) Hl B B' Hrw.
  assert (F : forall off cs, bytes_at segs m (p + off) cs -> 0 <= off -> off + Z.of_nat (length cs) <= 56 ->
    bytes_at segs m (p' + off) cs).
  { intros off cs Hc Ho Hoc. exact (pj_bytes_move m p p' bs off cs Hl B B' Hc Ho Hoc). }
  split; [exact Hrw|].
  split; [split; [exact T0 | rewrite <- (Z.add_0_r p'); apply F; [rewrite Z.add_0_r; exact T1 | lia | rewrite length_le4; lia]]|].
  split; [split; [exact N0 | apply F; [exact N1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact S0 | apply F; [exact S1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact K0 | apply F; [exact K1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact Y0 | apply F; [exact Y1 | lia | rewrite length_le8; lia]]|].
  split; [split; [exact C0 | apply F; [exact C1 | lia | rewrite length_le8; lia]]|].
  split; [exact P0 | apply F; [exact P1 | lia | rewrite length_le8; lia]].
Qed.

Lemma pj_apart_app : forall A B p, pj_apart A p -> pj_apart B p -> pj_apart (A ++ B) p.
Proof.
  intros A B p HA HB b x Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HA b x Hb) | exact (HB b x Hb)].
Qed.

Lemma pj_items_mono : forall (P Q : Z -> jv -> list (Z * Z) -> Prop) l a D,
  (forall i u D1, (i < length l)%nat -> In u l -> incl D1 D ->
     P (a + 56 * Z.of_nat i) u D1 -> Q (a + 56 * Z.of_nat i) u D1) ->
  pj_items P a l D -> pj_items Q a l D.
Proof.
  intros P Q l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_items] in *.
  - exact Hl.
  - destruct Hl as (D1 & D2 & E & HP & HR). exists D1, D2. split; [exact E|]. split.
    + specialize (H 0%nat u D1). replace (a + 56 * Z.of_nat 0) with a in H by lia.
      apply H; [cbn; lia | left; reflexivity | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact HP].
    + apply (IH (a + 56) D2); [|exact HR].
      intros i v D3 Hi Hv Hinc HP3.
      replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
      apply H; [cbn; lia | right; exact Hv | subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb | exact HP3].
Qed.

Lemma pj_mems_mono : forall m lblk m' lblk' (P Q : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  (forall i nm u x k D1, (i < length l)%nat -> In (nm, u) l -> In (x, k) D -> incl D1 D ->
     pj_u64 m (ka + 8 * Z.of_nat i) x -> pj_cstr m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     pj_u64 m' (ka + 8 * Z.of_nat i) x /\ pj_cstr m' lblk' x k nm /\ Q (a + 56 * Z.of_nat i) u D1) ->
  pj_mems m lblk P a ka l D -> pj_mems m' lblk' Q a ka l D.
Proof.
  intros m lblk m' lblk' P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_mems] in *.
  - exact Hl.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
    assert (G : pj_u64 m' ka x /\ pj_cstr m' lblk' x k nm /\ Q a u D1).
    { specialize (H 0%nat nm u x k D1).
      replace (ka + 8 * Z.of_nat 0) with ka in H by lia. replace (a + 56 * Z.of_nat 0) with a in H by lia.
      apply H; [cbn; lia | left; reflexivity | subst D; left; reflexivity
               | subst D; intros b Hb; right; apply in_or_app; left; exact Hb | exact Hx | exact Hc | exact HP]. }
    destruct G as (Hx' & Hc' & HQ).
    exists x, k, D1, D2. split; [exact E|]. split; [exact Hx'|]. split; [exact Hc'|]. split; [exact HQ|].
    apply (IH (a + 56) (ka + 8) D2); [|exact HR].
    intros i nm' v x' k' D3 Hi Hv Hxk Hinc Hx3 Hc3 HP3.
    replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in Hx3 |- * by lia.
    replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
    apply H; [cbn; lia | right; exact Hv | subst D; right; apply in_or_app; right; exact Hxk
             | subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb
             | exact Hx3 | exact Hc3 | exact HP3].
Qed.

Lemma pj_node_frame : forall t m lblk m' lblk' p D,
  pj_node m lblk p t D ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x : word, pj_foot p D (bv_unsigned x) -> m' x = m x) ->
  pj_node m' lblk' p t D.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m lblk m' lblk' p D H HL HM; cbn [pj_node] in H |- *;
    destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
    (split; [apply (pj_hdr_eq m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (pj_cstr_eq m lblk m' lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
    intros x Hx. apply HM. right. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (pj_cstr_eq m lblk m' lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
    intros x Hx. apply HM. right. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0)]; [left; exact Hcap | right; split; [exact Hp | apply HL; apply (Hin Hp)]]|].
    exists Di. split; [exact ED|].
    apply (pj_items_mono (pj_node m lblk) (pj_node m' lblk')); [|exact Hi].
    intros i u D1 Hil Hu Hinc HP.
    assert (Hp : 0 < cap) by lia.
    rewrite Forall_forall in IH.
    apply (IH u Hu m lblk m' lblk' _ D1 HP).
    + intros a k Hak. apply HL. apply HDi. apply Hinc. exact Hak.
    + intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
      * right. exists (kids, 56 * cap). split; [apply (Hin Hp) | unfold pj_holds; cbn [fst snd]; lia].
      * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
  - destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0 & L1)];
            [left; exact Hcap | right; split; [exact Hp|]; split; [apply HL; apply (proj1 (Hin Hp)) | apply HL; apply (proj2 (Hin Hp))]]|].
    exists Di. split; [exact ED|].
    apply (pj_mems_mono m lblk m' lblk' (pj_node m lblk) (pj_node m' lblk')); [|exact Hi].
    intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
    assert (Hp : 0 < cap) by lia.
    split; [|split].
    + apply (pj_u64_eq m m'); [exact Hx|]. intros y Hy. apply HM. right. exists (keys, 8 * cap).
      split; [apply (proj2 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
    + apply (pj_cstr_eq m lblk m' lblk'); [exact Hcs | apply HL; apply HDi; exact Hxk |].
      intros y Hy. apply HM. right. exists (x, k). split; [apply HDi; exact Hxk | exact Hy].
    + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (IH m lblk m' lblk' _ D1 HP).
      * intros a k' Hak. apply HL. apply HDi. apply Hinc. exact Hak.
      * intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
        -- right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
        -- right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

Lemma pj_node_munch : forall W m lblk m' lblk' p t D,
  pj_node m lblk p t D ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  munch W m m' -> (forall z, pj_foot p D z -> outside W z) ->
  pj_node m' lblk' p t D.
Proof.
  intros W m lblk m' lblk' p t D H HL HW HO.
  apply (pj_node_frame t m lblk m' lblk' p D H HL). intros x Hx. exact (HW x (HO _ Hx)).
Qed.

Lemma pj_node_move : forall m lblk p p' t D bs,
  pj_node m lblk p t D -> p' mod 8 = 0 -> stk segs m p' (p' + 56) ->
  length bs = 56%nat -> bytes_at segs m p bs -> bytes_at segs m p' bs -> pj_apart D p' ->
  pj_node m lblk p' t D.
Proof.
  intros m lblk p p' t D bs H Ha' Hs' Hl B B' Hap.
  destruct t; cbn [pj_node] in H |- *;
    destruct H as (Hn & _ & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Hap|]); exists num, str, kids, keys, n, cap;
    (split; [apply (pj_hdr_move m p p' bs); [exact Hh | exact Hl | exact B | exact B' | split; assumption] | exact Hb]).
Qed.

Lemma pj_fshape_move : forall m lblk Pi p p' D bs,
  pj_fshape m lblk Pi p D -> p' mod 8 = 0 -> stk segs m p' (p' + 56) ->
  length bs = 56%nat -> bytes_at segs m p bs -> bytes_at segs m p' bs -> pj_apart D p' ->
  pj_fshape m lblk Pi p' D.
Proof.
  intros m lblk Pi p p' D bs (Hn & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Hh & R)
    Ha' Hs' Hl B B' Hap.
  split; [exact Hn|]. split; [exact Hap|].
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di. split; [|exact R].
  apply (pj_hdr_move m p p' bs); [exact Hh | exact Hl | exact B | exact B' | split; assumption].
Qed.

Lemma pj_freeable_move : forall m lblk p p' D bs,
  pj_freeable m lblk p D -> p' mod 8 = 0 -> stk segs m p' (p' + 56) ->
  length bs = 56%nat -> bytes_at segs m p bs -> bytes_at segs m p' bs -> pj_apart D p' ->
  pj_freeable m lblk p' D.
Proof.
  intros m lblk p p' D bs (d & H) Ha' Hs' Hl B B' Hap. exists d.
  destruct d; cbn [pj_fd] in H |- *; eapply pj_fshape_move; eassumption.
Qed.

Lemma pf_items_mono : forall m lblk (P Q : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a D1, P a D1 -> Q a D1) -> pf_items m lblk P ks a ka n D -> pf_items m lblk Q ks a ka n D.
Proof.
  intros m lblk P Q ks n. induction n as [|n IH]; intros a ka D H Hp; cbn [pf_items] in *.
  - exact Hp.
  - destruct Hp as (Dk & D1 & D2 & E & Hk & HP & HR). exists Dk, D1, D2.
    split; [exact E|]. split; [exact Hk|]. split; [exact (H a D1 HP) | exact (IH (a + 56) (ka + 8) D2 H HR)].
Qed.

Lemma pf_items_snoc : forall m lblk (P : Z -> list (Z * Z) -> Prop) ks n a ka D1 Dk Dt,
  pf_items m lblk P ks a ka n D1 -> pj_key m lblk ks (ka + 8 * Z.of_nat n) Dk ->
  P (a + 56 * Z.of_nat n) Dt -> pf_items m lblk P ks a ka (S n) (D1 ++ Dk ++ Dt).
Proof.
  intros m lblk P ks n. induction n as [|n IH]; intros a ka D1 Dk Dt H Hk HP.
  - cbn [pf_items] in H |- *. subst D1. exists Dk, Dt, [].
    replace (ka + 8 * Z.of_nat 0) with ka in Hk by lia. replace (a + 56 * Z.of_nat 0) with a in HP by lia.
    split; [rewrite app_nil_r; reflexivity|]. split; [exact Hk|]. split; [exact HP | reflexivity].
  - cbn [pf_items] in H. destruct H as (Dk0 & D10 & D20 & E & Hk0 & HP0 & HR).
    cbn [pf_items]. exists Dk0, D10, (D20 ++ Dk ++ Dt).
    split; [subst D1; rewrite <- !app_assoc; reflexivity|]. split; [exact Hk0|]. split; [exact HP0|].
    apply (IH (a + 56) (ka + 8) D20 Dk Dt HR).
    + replace (ka + 8 + 8 * Z.of_nat n) with (ka + 8 * Z.of_nat (S n)) by lia. exact Hk.
    + replace (a + 56 + 56 * Z.of_nat n) with (a + 56 * Z.of_nat (S n)) by lia. exact HP.
Qed.

Lemma pj_fshape_mono : forall m lblk (Pi Pi' : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) p D,
  (forall ks kids keys n Di, Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshape m lblk Pi p D -> pj_fshape m lblk Pi' p D.
Proof.
  intros m lblk Pi Pi' p D H (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact Hn|]. split; [exact Ha|]. exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  exact (H _ _ _ _ _ H6).
Qed.

Lemma pj_fd_succ : forall m lblk d p D, pj_fd m lblk d p D -> pj_fd m lblk (S d) p D.
Proof.
  intros m lblk d. induction d as [|d IH]; intros p D H; cbn [pj_fd] in H |- *.
  - eapply (pj_fshape_mono m lblk); [|exact H].
    intros ks kids keys n Di (En & EDi). cbv beta. subst n Di. exact eq_refl.
  - eapply (pj_fshape_mono m lblk); [|exact H].
    intros ks kids keys n Di Hi. cbv beta in Hi |- *.
    apply (pf_items_mono m lblk (pj_fd m lblk d)); [|exact Hi].
    intros a D1 H1. exact (IH a D1 H1).
Qed.

Lemma pj_fd_mono : forall m lblk d d' p D, (d <= d')%nat -> pj_fd m lblk d p D -> pj_fd m lblk d' p D.
Proof.
  intros m lblk d d' p D Hle. induction Hle as [|d' Hle IH]; intros H; [exact H|].
  apply pj_fd_succ. apply IH. exact H.
Qed.

Lemma pj_items_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, In u l -> P a u D1 -> Q a D1) ->
  pj_items P a l D -> pf_items m lblk Q false a ka (length l) D.
Proof.
  intros m lblk P Q l. induction l as [|u r IH]; intros a ka D H Hl; cbn [pj_items pf_items length] in *.
  - exact Hl.
  - destruct Hl as (D1 & D2 & E & HP & HR). exists [], D1, D2.
    split; [exact E|]. split; [exact eq_refl|]. split; [apply (H a u D1); [left; reflexivity | exact HP]|].
    apply IH; [intros a' v D3 Hv HP3; apply (H a' v D3); [right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma pj_mems_pf : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) (Q : Z -> list (Z * Z) -> Prop) l a ka D,
  (forall a u D1, (exists nm, In (nm, u) l) -> P a u D1 -> Q a D1) ->
  pj_mems m lblk P a ka l D -> pf_items m lblk Q true a ka (length l) D.
Proof.
  intros m lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_mems pf_items length] in *.
  - exact Hl.
  - destruct Hl as (x & k & D1 & D2 & E & Hx & (Hb & _) & HP & HR). exists [(x, k)], D1, D2.
    split; [exact E|].
    split; [unfold pj_key; exists x; split; [exact Hx | right; exists k; split; [exact Hb | reflexivity]]|].
    split; [apply (H a u D1); [exists nm; left; reflexivity | exact HP]|].
    apply IH; [intros a' v D3 (nm' & Hv) HP3; apply (H a' v D3); [exists nm'; right; exact Hv | exact HP3] | exact HR].
Qed.

Lemma pj_node_fd : forall t m lblk p D, pj_node m lblk p t D -> pj_fd m lblk (depth t) p D.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H;
    cbn [pj_node] in H.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fd]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JNull), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fd]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JFalse), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & ED).
    cbn [depth pj_fd]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag JTrue), num, str, kids, keys, n, cap, false, [], [], [], [].
    split; [exact Hh|]. split; [left; split; [exact E1 | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E1 & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
    cbn [depth pj_fd]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag (JNum txt bits)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
    split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & E2 & E3 & E4 & E5 & k & (Hb & _) & ED).
    cbn [depth pj_fd]. split; [exact Hn|]. split; [exact Ha|].
    exists (tag (JStr s)), num, str, kids, keys, n, cap, false, [(str, k)], [], [], [].
    split; [exact Hh|]. split; [right; exists k; split; [exact Hb | reflexivity]|].
    split; [left; split; [exact E2 | split; [exact E4 | reflexivity]]|].
    split; [left; split; [exact E3 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|]. split; [exact E4 | reflexivity].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    remember (depth (JArr items)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
    cbn [pj_fd]. unfold pj_fshape.
    split; [exact Hn|]. split; [exact Ha|].
    assert (HI : pf_items m lblk (pj_fd m lblk d') false kids keys (Z.to_nat n) Di).
    { rewrite En, Nat2Z.id. apply (pj_items_pf m lblk (pj_node m lblk)); [|exact Hi].
      intros a u D1 Hu HP. rewrite Forall_forall in IH.
      apply (pj_fd_mono m lblk (depth u)); [|exact (IH u Hu m lblk a D1 HP)].
      pose proof (depth_item items u Hu). lia. }
    destruct Hcap as [(Hc0 & Hk0)|(Hc0 & Hl)].
    + subst cap.
      exists (tag (JArr items)), num, str, kids, keys, n, 0, false, [], [], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
      split; [left; split; [exact Ek | split; reflexivity]|].
      split; [subst D; cbn; apply Permutation_refl|]. exact HI.
    + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
      exists (tag (JArr items)), num, str, kids, keys, n, cap, false, [], [(kids, 56 * cap)], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact Hl | split; [lia | reflexivity]]|].
      split; [left; split; [exact Ek | split; reflexivity]|].
      split; [subst D; cbn [app]; apply Permutation_refl|]. exact HI.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
    remember (depth (JObj members)) as dd eqn:Edd. destruct dd as [|d']; [cbn [depth] in Edd; discriminate|].
    cbn [pj_fd]. unfold pj_fshape.
    split; [exact Hn|]. split; [exact Ha|].
    destruct Hcap as [(Hc0 & Hk0 & Hy0)|(Hc0 & L0 & L1)].
    + subst cap. destruct members as [|mb members]; cbn [length] in En; [|lia].
      cbn [pj_mems] in Hi.
      exists (tag (JObj [])), num, str, kids, keys, n, 0, false, [], [], [], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [left; split; [exact Hk0 | split; [lia | reflexivity]]|].
      split; [left; split; [exact Hy0 | split; reflexivity]|].
      split; [subst D; cbn; apply Permutation_refl|].
      cbv beta. replace (Z.to_nat n) with 0%nat by lia. exact Hi.
    + rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
      exists (tag (JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], Di.
      split; [exact Hh|]. split; [left; split; [exact Es | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity | exists (8 * cap); split; [exact L1 | split; [lia | reflexivity]]]|].
      split; [subst D; cbn [app]; apply Permutation_refl|].
      cbv beta. rewrite En, Nat2Z.id. apply (pj_mems_pf m lblk (pj_node m lblk)); [|exact Hi].
      intros a u D1 (nm & Hu) HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (pj_fd_mono m lblk (depth u)); [|exact (IH m lblk a D1 HP)].
      pose proof (depth_member members nm u Hu). lia.
Qed.

Lemma pj_node_freeable : forall m lblk p t D, pj_node m lblk p t D -> pj_freeable m lblk p D.
Proof. intros m lblk p t D H. exists (depth t). exact (pj_node_fd t m lblk p D H). Qed.

Lemma pj_le8_0 : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

Lemma pj_le4_0 : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. reflexivity. Qed.

Lemma pj_zero_sub : forall m p off len, bytes_at segs m p (repeat (Z_to_bv 8 0) 56) ->
  0 <= off -> off + Z.of_nat len <= 56 -> bytes_at segs m (p + off) (repeat (Z_to_bv 8 0) len).
Proof.
  intros m p off len (H1 & H2 & H) Ho Hl. rewrite repeat_length in H2.
  split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi.
  replace (p + off + Z.of_nat i) with (p + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite H by (rewrite repeat_length; lia).
  rewrite !pj_nth_repeat by lia. reflexivity.
Qed.

Lemma pj_zero_u64 : forall m p off, bytes_at segs m p (repeat (Z_to_bv 8 0) 56) -> 0 <= off <= 48 ->
  pj_u64 m (p + off) 0.
Proof. intros m p off H Ho. split; [lia|]. rewrite pj_le8_0. apply pj_zero_sub; [exact H | lia | lia]. Qed.

Lemma pj_zero_node : forall m lblk p, pj_zero m p -> pj_node m lblk p JNull [].
Proof.
  intros m lblk p (Hrw & Hz). cbn [pj_node].
  split; [constructor|]. split; [intros b x Hb; destruct Hb|].
  exists 0, 0, 0, 0, 0, 0. split.
  - cbn [tag]. split; [exact Hrw|].
    split; [split; [lia | rewrite pj_le4_0, <- (Z.add_0_r p); apply pj_zero_sub; [exact Hz | lia | lia]]|].
    split; [apply pj_zero_u64; [exact Hz | lia]|].
    split; [apply pj_zero_u64; [exact Hz | lia]|].
    split; [apply pj_zero_u64; [exact Hz | lia]|].
    split; [apply pj_zero_u64; [exact Hz | lia]|].
    split; [apply pj_zero_u64; [exact Hz | lia]|].
    apply pj_zero_u64; [exact Hz | lia].
  - repeat split.
Qed.

Lemma pj_zero_freeable : forall m lblk p, pj_zero m p -> pj_freeable m lblk p [].
Proof. intros m lblk p H. exact (pj_node_freeable m lblk p JNull [] (pj_zero_node m lblk p H)). Qed.

Lemma pj_node_slots : forall m lblk p t D cap,
  pj_node m lblk p t D -> (tag t = 5 \/ tag t = 6) -> pj_u64 m (p + 48) cap -> cap <= 2 ^ 54 ->
  pj_slots m lblk p.
Proof.
  intros m lblk p t D cap0 H Ht Hc0 Hle.
  destruct t as [| | | txt bits | s | items | members]; cbn [tag] in Ht; try lia; cbn [pj_node] in H.
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & Hc48).
    assert (Ec : cap0 = cap) by exact (pj_u64_uniq m (p + 48) cap0 cap Hc0 Hc48). subst cap0.
    exists (tag (JArr items)), num, str, kids, keys, n, cap. split; [exact Hh|].
    cbn [tag]. split; [left; reflexivity|]. split; [lia|].
    split; [intros E0; destruct Hcap as [(_ & Hk0)|(Hc1 & _)]; [split; [exact Hk0 | intros; lia] | lia]|].
    intros Hp. destruct Hcap as [(Hc1 & _)|(_ & Hl)]; [lia | split; [exact Hl | intros; lia]].
  - destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
    pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & Hc48).
    assert (Ec : cap0 = cap) by exact (pj_u64_uniq m (p + 48) cap0 cap Hc0 Hc48). subst cap0.
    exists (tag (JObj members)), num, str, kids, keys, n, cap. split; [exact Hh|].
    cbn [tag]. split; [right; reflexivity|]. split; [lia|].
    split; [intros E0; destruct Hcap as [(_ & Hk0 & Hy0)|(Hc1 & _)]; [split; [exact Hk0 | intros; exact Hy0] | lia]|].
    intros Hp. destruct Hcap as [(Hc1 & _)|(_ & L0 & L1)]; [lia | split; [exact L0 | intros; exact L1]].
Qed.

Lemma pj_open_slots : forall m lblk p o nf ts ns D, pj_open_n m lblk p o nf ts ns D -> pj_slots m lblk p.
Proof.
  intros m lblk p o nf ts ns D (_ & _ & num & kids & keys & cap & Di & Hh & Hs & _).
  exists (5 + o), num, 0, kids, keys, nf, cap. split; [exact Hh | exact Hs].
Qed.

Lemma pj_open_arr : forall m lblk p k ts ns D, pj_open m lblk p 0 k ts ns D -> pj_node m lblk p (JArr ts) D.
Proof.
  intros m lblk p k ts ns D (Ek & Hn & Ha & num & kids & keys & cap & Di & Hh & Hs & Hb).
  destruct Hb as [(_ & Hk0 & ED & Hi)|(O1 & _)]; [|lia].
  cbn [pj_node]. split; [exact Hn|]. split; [exact Ha|].
  exists num, 0, kids, keys, k, cap. split; [exact Hh|].
  destruct Hs as (_ & Hkc & Hc0 & Hcp).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hcr & _)).
  split; [reflexivity|]. split; [exact Hk0|]. split; [exact Ek|]. split; [lia|].
  split; [destruct (Z.eq_dec cap 0) as [E0|E0];
          [left; split; [exact E0 | exact (proj1 (Hc0 E0))] | right; split; [lia | exact (proj1 (Hcp ltac:(lia)))]]|].
  exists Di. split; [exact ED | exact Hi].
Qed.

Lemma pj_open_obj : forall m lblk p k ts ns D, pj_open m lblk p 1 k ts ns D ->
  pj_node m lblk p (JObj (combine ns ts)) D.
Proof.
  intros m lblk p k ts ns D (Ek & Hn & Ha & num & kids & keys & cap & Di & Hh & Hs & Hb).
  destruct Hb as [(O0 & _)|(_ & Hl & ED & Hi)]; [lia|].
  cbn [pj_node]. split; [exact Hn|]. split; [exact Ha|].
  exists num, 0, kids, keys, k, cap. split; [exact Hh|].
  destruct Hs as (_ & Hkc & Hc0 & Hcp).
  pose proof Hh as (_ & _ & _ & _ & _ & _ & _ & (Hcr & _)).
  split; [reflexivity|]. split; [rewrite pj_combine_len by exact Hl; exact Ek|]. split; [lia|].
  split; [destruct (Z.eq_dec cap 0) as [E0|E0];
          [left; destruct (Hc0 E0) as (K0 & K1); split; [exact E0|]; split; [exact K0 | apply K1; reflexivity]
          | right; destruct (Hcp ltac:(lia)) as (L0 & L1); split; [lia|]; split; [exact L0 | apply L1; reflexivity]]|].
  exists Di. split; [exact ED | exact Hi].
Qed.

Lemma pj_open_freeable : forall m lblk p o k ts ns D, pj_open m lblk p o k ts ns D -> pj_freeable m lblk p D.
Proof.
  intros m lblk p o k ts ns D H.
  pose proof H as (_ & _ & _ & ? & ? & ? & ? & ? & _ & _ & Hb).
  destruct Hb as [(-> & _)|(-> & _)].
  - exact (pj_node_freeable m lblk p (JArr ts) D (pj_open_arr m lblk p k ts ns D H)).
  - exact (pj_node_freeable m lblk p (JObj (combine ns ts)) D (pj_open_obj m lblk p k ts ns D H)).
Qed.

Lemma pj_open_freeable_next : forall m lblk p o k ts ns D kids keys Dn Dt,
  pj_open_n m lblk p o (k + 1) ts ns D -> k = Z.of_nat (length ts) ->
  pj_u64 m (p + 24) kids -> pj_u64 m (p + 32) keys ->
  pj_freeable m lblk (kids + 56 * k) Dt ->
  (o = 0 /\ Dn = [] \/ o = 1 /\ pj_key m lblk true (keys + 8 * k) Dn) ->
  NoDup (D ++ Dn ++ Dt) -> pj_apart (Dn ++ Dt) p ->
  pj_freeable m lblk p (D ++ Dn ++ Dt).
Proof.
  intros m lblk p o k ts ns D kids keys Dn Dt (Hn & Ha & num & kids0 & keys0 & cap & Di & Hh & Hs & Hb) Ek Hkids Hkeys
    (dt & Ht) Hk HN HA.
  pose proof Hh as (_ & _ & _ & _ & Hk24 & Hk32 & _ & (Hcr & _)).
  assert (E1 : kids0 = kids) by exact (pj_u64_uniq m (p + 24) kids0 kids Hk24 Hkids).
  assert (E2 : keys0 = keys) by exact (pj_u64_uniq m (p + 32) keys0 keys Hk32 Hkeys).
  subst kids0 keys0.
  destruct Hs as (_ & Hkc & Hc0 & Hcp).
  assert (Hcp' : 0 < cap) by lia.
  set (d' := Nat.max dt (list_max (map depth ts))).
  assert (Hdep : forall u, In u ts -> (depth u <= d')%nat).
  { intros u Hu. pose proof (depth_item ts u Hu) as G. cbn [depth] in G. unfold d'. lia. }
  assert (Hdt : pj_fd m lblk d' (kids + 56 * Z.of_nat (length ts)) Dt).
  { apply (pj_fd_mono m lblk dt); [unfold d'; lia | rewrite <- Ek; exact Ht]. }
  exists (S d'). cbn [pj_fd]. unfold pj_fshape.
  split; [exact HN|]. split; [exact (pj_apart_app D (Dn ++ Dt) p Ha HA)|].
  rewrite (proj2 (Z.eqb_neq cap 0)) in Hb by lia.
  destruct Hb as [(O0 & Hk0 & ED & Hi)|(O1 & Hl & ED & Hi)]; subst o.
  - destruct Hk as [(_ & EDn)|(O1 & _)]; [|lia]. subst Dn.
    exists (5 + 0), num, 0, kids, keys, (k + 1), cap, false, [], [(kids, 56 * cap)], [], (Di ++ [] ++ Dt).
    split; [exact Hh|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap); split; [exact (proj1 (Hcp Hcp')) | split; [lia | reflexivity]]|].
    split; [left; split; [exact Hk0 | split; reflexivity]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. replace (Z.to_nat (k + 1)) with (S (length ts)) by lia. apply pf_items_snoc.
    + apply (pj_items_pf m lblk (pj_node m lblk)); [|exact Hi].
      intros a u D1 Hu HP. apply (pj_fd_mono m lblk (depth u)); [exact (Hdep u Hu) | exact (pj_node_fd u m lblk a D1 HP)].
    + exact eq_refl.
    + exact Hdt.
  - destruct Hk as [(O0 & _)|(_ & HK)]; [lia|].
    destruct (Hcp Hcp') as (L0 & L1).
    exists (5 + 1), num, 0, kids, keys, (k + 1), cap, true, [], [(kids, 56 * cap)], [(keys, 8 * cap)], (Di ++ Dn ++ Dt).
    split; [exact Hh|]. split; [left; split; reflexivity|].
    split; [right; exists (56 * cap); split; [exact L0 | split; [lia | reflexivity]]|].
    split; [right; split; [reflexivity | exists (8 * cap); split; [apply L1; reflexivity | split; [lia | reflexivity]]]|].
    split; [subst D; cbn [app]; apply Permutation_refl|].
    cbv beta. replace (Z.to_nat (k + 1)) with (S (length ts)) by lia. apply pf_items_snoc.
    + rewrite <- (pj_combine_len _ _ ns ts Hl). apply (pj_mems_pf m lblk (pj_node m lblk)); [|exact Hi].
      intros a u D1 (nm & Hu) HP. apply in_combine_r in Hu.
      apply (pj_fd_mono m lblk (depth u)); [exact (Hdep u Hu) | exact (pj_node_fd u m lblk a D1 HP)].
    + rewrite <- Ek. exact HK.
    + exact Hdt.
Qed.

End PjStruct.
