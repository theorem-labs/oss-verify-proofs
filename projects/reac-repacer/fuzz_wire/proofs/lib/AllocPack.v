From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0d YO03 YO0m YO0n YO0o PlaceCap.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import AllocSI AllocGS AllocMB.
Import ListNotations.
Local Open Scope Z_scope.

Definition band (n : Z) : Z := if MMAP_THRESHOLD <=? n then 48 else size_to_class n.

Definition bcount (s : astate) (k : Z) : Z :=
  Z.of_nat (length (filter (fun b => band (snd b) =? k) (user_blocks s))).

Definition ub_cls (s : astate) (c : Z) : list (sptr * Z) :=
  flat_map (fun gm : sptr * ameta =>
    let am := snd gm in
    if (am_sc am =? c) && (1 <=? am_last am) then
      flat_map (fun i => match ss_fr (nth_slot am i) with
        | Some fr => match fr_kind fr with
          | FUser => [(padd (slot_start am i) (UNIT * fr_off fr), fr_n fr)]
          | FGroup => []
          end
        | None => []
        end) (zseq 0 (am_last am + 1))
    else []) (used_metas s).

Definition upc (s : astate) (c : Z) : Z :=
  Z.of_nat (length (filter (fun b => band (snd b) =? c - 1) (ub_cls s c))).

Definition COARSE : Z := 13.

Definition RED : Z := 128.

Definition FC (c : Z) : Z := initial_cnt c 128.

Definition jof (c k : Z) : Z := size_to_class (UNIT + class_size c * k - IB).

Definition nestF (c : Z) : bool := class_size c * FC c + UNIT <=? PGSZ / 2.

Definition zsumZ (f : Z -> Z) (l : list Z) : Z := fold_right (fun x acc => f x + acc) 0 l.

Definition nf_next (caps acc : list Z) (c : Z) : Z :=
  (znth c caps + COARSE + zsumZ (fun c' => if jof c' (FC c') =? c then znth c' acc else 0) (zseq 0 c) + RED * c)
    / FC c + 1.

Fixpoint nf_build (caps : list Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => let acc := nf_build caps k' in acc ++ [nf_next caps acc (Z.of_nat k')]
  end.

Definition NF (caps : list Z) : list Z := nf_build caps 48.

Definition GALL (caps : list Z) : Z := zsumZ (fun c => znth c (NF caps) + RED) (zseq 0 48) + znth 48 caps.

Definition GMAP (caps : list Z) : Z :=
  zsumZ (fun c => if nestF c then 0 else znth c (NF caps) + RED) (zseq 0 48) + znth 48 caps.

Definition gcountX (X : list sptr) (s : astate) (f : ameta -> bool) : Z :=
  Z.of_nat (length (filter (fun g => match MTX X s g with Some (MUsed am) => f am | _ => false end) (keys s))).

Definition gfull (c : Z) (am : ameta) : bool := (am_sc am =? c) && (am_last am + 1 =? FC c).

Definition gred (c : Z) (am : ameta) : bool := (am_sc am =? c) && (am_last am + 1 <? FC c).

Definition PKS (X : list sptr) (s : astate) : Prop :=
  (forall g am i fr, usedX X s g am -> am_sc am < 48 -> 0 <= i <= am_last am ->
     ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser ->
     fr_n fr < MMAP_THRESHOLD /\ am_sc am <= size_to_class (fr_n fr) + 1) /\
  (forall g am i fr c ac, usedX X s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
     fr_kind fr = FGroup -> usedX X s c ac -> am_maplen ac = 0 -> am_mem ac = slot_start am i ->
     am_sc am = jof (am_sc ac) (am_last ac + 1)) /\
  (forall g am, usedX X s g am -> am_sc am < 48 -> am_last am + 1 <= FC (am_sc am)) /\
  (forall g am, usedX X s g am -> am_sc am < 48 -> 0 < am_maplen am -> nestF (am_sc am) = false).

Definition PKC (X : list sptr) (caps : list Z) (s : astate) : Prop :=
  forall c, 0 <= c < 48 -> gcountX X s (gfull c) <= znth c (NF caps) /\ gcountX X s (gred c) <= RED.

Definition UPB (s : astate) (L : list Z) : Prop :=
  (forall k, 0 <= k < 49 -> bcount s k <= znth k L) /\
  (forall c, 1 <= c < 48 -> bcount s c + upc s c <= znth c L + COARSE).

Definition NA2 (H : Z) : Z := H / METAS_PER_AREA + 1.

Definition AREA2 (H : Z) : Z := 2 * PGSZ * (H / METAS_PER_AREA + 41).

Definition SLOTS2 (H M : Z) : Z := M + (NA2 H + 1) + 40.

Definition LIVE2 (H M bytes : Z) : Z := MMAX * M + bytes + PGSZ * (NA2 H + 1) + AREA2 H.

Definition RQ2 (H n : Z) : Z := Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (AREA2 H).

Definition CAPOK2 (H M bytes n : Z) : Prop :=
  LIVE2 H M bytes + 3 * PGSZ + AREA2 H + Z.max MMAX (page_round (n + IB + UNIT)) <= MG_LIVE /\
  SLOTS2 H M + 5 + KRES <= slot_cap (RQ2 H n) /\ RQ2 H n + PGSZ <= MG_REQ /\
  H < METAS_PER_AREA * (2 ^ 40 - 41).

Record pbound := PB { pb_live : list Z; pb_bytes : Z; pb_cap : list Z }.

Definition res_ok_pack (A : astate) (b : pbound) : Prop :=
  II A /\ SI A /\ GS A /\ NL A /\ noraw A /\ MB A /\ PKS [] A /\ PKC [] (pb_cap b) A /\ UPB A (pb_live b) /\
  ubytes A <= pb_bytes b /\ length (pb_live b) = 49%nat /\ length (pb_cap b) = 49%nat /\
  (forall k, 0 <= k < 49 -> 0 <= znth k (pb_live b) <= znth k (pb_cap b)) /\ 0 <= pb_bytes b /\
  hand A <= GALL (pb_cap b).

Definition room_pack (b : pbound) (n : Z) : Prop :=
  0 <= n /\ znth (band n) (pb_live b) + 1 <= znth (band n) (pb_cap b) /\
  CAPOK2 (GALL (pb_cap b)) (GMAP (pb_cap b)) (pb_bytes b + n) n.

Definition lv_add (L : list Z) (k d : Z) : list Z := zset k (znth k L + d) L.

Definition lv_realloc (L : list Z) (k n : Z) : list Z :=
  if band n <? band k then lv_add L (band n) 1 else lv_add (lv_add L (band k) (-1)) (band n) 1.

Definition pb_malloc (b : pbound) (n : Z) : pbound := PB (lv_add (pb_live b) (band n) 1) (pb_bytes b + n) (pb_cap b).

Definition pb_free (b : pbound) (n : Z) : pbound := PB (lv_add (pb_live b) (band n) (-1)) (pb_bytes b - n) (pb_cap b).

Definition pb_realloc (b : pbound) (k n : Z) : pbound :=
  PB (lv_realloc (pb_live b) k n) (pb_bytes b - k + n) (pb_cap b).

Lemma FC_tab : forallb (fun c => (8 <=? FC c) && (FC c <=? 32)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
