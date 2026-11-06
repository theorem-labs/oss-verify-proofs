From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO03 YO0m YO0n YO0o PlaceCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocSI AllocGS AllocMB AllocPack.
Import ListNotations.
Local Open Scope Z_scope.

Definition mis_ok (s : astate) (c : Z) (e : sptr * Z) : bool :=
  (snd e =? c) && existsb (fun b => sptr_eqb (fst b) (fst e) && (band (snd b) =? c - 1)) (ub_cls s c).

Definition count_mis (M : list (sptr * Z)) (c : Z) : Z := Z.of_nat (length (filter (fun e => snd e =? c) M)).

Definition mis_in (s : astate) (M : list (sptr * Z)) (c : Z) : Z := Z.of_nat (length (filter (mis_ok s c) M)).

Definition mis_del (M : list (sptr * Z)) (p : sptr) : list (sptr * Z) := filter (fun e => negb (sptr_eqb (fst e) p)) M.

Definition mis_lookup (M : list (sptr * Z)) (p : sptr) : option Z :=
  option_map snd (find (fun e => sptr_eqb (fst e) p) M).

Definition UPB3 (s : astate) (L : list Z) (M : list (sptr * Z)) : Prop :=
  (forall k, 0 <= k < 49 -> bcount s k <= znth k L) /\
  (forall c, 1 <= c < 48 -> bcount s c + upc s c <= znth c L + COARSE + mis_in s M c).

Definition MIS (s : astate) (M : list (sptr * Z)) (mc : list Z) : Prop :=
  NoDup (map fst M) /\ (forall e, In e M -> 1 <= snd e < 48 /\ exists n, In (fst e, n) (user_blocks s)) /\
  (forall c, 1 <= c < 48 -> count_mis M c <= znth c mc).

Definition nf3_next (caps mc acc : list Z) (c : Z) : Z :=
  (znth c caps + COARSE + znth c mc + zsumZ (fun c' => if jof c' (FC c') =? c then znth c' acc else 0) (zseq 0 c)
    + RED * c) / FC c + 1.

Fixpoint nf3_build (caps mc : list Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => let acc := nf3_build caps mc k' in acc ++ [nf3_next caps mc acc (Z.of_nat k')]
  end.

Definition NF3 (caps mc : list Z) : list Z := nf3_build caps mc 48.

Definition GALL3 (caps mc : list Z) : Z := zsumZ (fun c => znth c (NF3 caps mc) + RED) (zseq 0 48) + znth 48 caps.

Definition GMAP3 (caps mc : list Z) : Z :=
  zsumZ (fun c => if nestF c then 0 else znth c (NF3 caps mc) + RED) (zseq 0 48) + znth 48 caps.

Definition PKC3 (X : list sptr) (caps mc : list Z) (s : astate) : Prop :=
  forall c, 0 <= c < 48 -> gcountX X s (gfull c) <= znth c (NF3 caps mc) /\ gcountX X s (gred c) <= RED.

Record pbound3 := PB3 { p3_live : list Z; p3_bytes : Z; p3_cap : list Z; p3_mis : list (sptr * Z); p3_mcap : list Z }.

Definition res_ok_pack3 (A : astate) (b : pbound3) : Prop :=
  II A /\ SI A /\ GS A /\ NL A /\ noraw A /\ MB A /\ PKS [] A /\ PKC3 [] (p3_cap b) (p3_mcap b) A /\
  UPB3 A (p3_live b) (p3_mis b) /\ MIS A (p3_mis b) (p3_mcap b) /\
  ubytes A <= p3_bytes b /\ length (p3_live b) = 49%nat /\ length (p3_cap b) = 49%nat /\
  length (p3_mcap b) = 49%nat /\
  (forall k, 0 <= k < 49 -> 0 <= znth k (p3_live b) <= znth k (p3_cap b) /\ 0 <= znth k (p3_mcap b)) /\
  0 <= p3_bytes b /\ hand A <= GALL3 (p3_cap b) (p3_mcap b).

Definition room_pack3 (b : pbound3) (n : Z) : Prop :=
  0 <= n /\ znth (band n) (p3_live b) + 1 <= znth (band n) (p3_cap b) /\
  (band n + 1 < 48 -> count_mis (p3_mis b) (band n + 1) + 1 <= znth (band n + 1) (p3_mcap b)) /\
  CAPOK2 (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)) (p3_bytes b + n) n.

Definition pb3_malloc (b : pbound3) (n : Z) : pbound3 :=
  PB3 (lv_add (p3_live b) (band n) 1) (p3_bytes b + n) (p3_cap b) (p3_mis b) (p3_mcap b).

Definition pb3_free (b : pbound3) (n : Z) (p : sptr) : pbound3 :=
  PB3 (lv_add (p3_live b) (band n) (-1)) (p3_bytes b - n) (p3_cap b) (mis_del (p3_mis b) p) (p3_mcap b).

Definition mis_realloc (M : list (sptr * Z)) (k n : Z) (p q : sptr) : list (sptr * Z) :=
  if sptr_eqb q p && (band n + 1 <? 48) &&
     ((band n + 1 =? band k) || match mis_lookup M p with Some c => c =? band n + 1 | None => false end)
  then (p, band n + 1) :: mis_del M p else mis_del M p.

Definition pb3_realloc (b : pbound3) (k n : Z) (p q : sptr) : pbound3 :=
  PB3 (lv_add (lv_add (p3_live b) (band k) (-1)) (band n) 1) (p3_bytes b - k + n) (p3_cap b)
    (mis_realloc (p3_mis b) k n p q) (p3_mcap b).
