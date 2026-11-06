(* fuzz_preset, program part (the kit's PRH_* family): the READER's memory predicates, restated over the cgif-core memory
   vocabulary (val_mem, garr8, writable_at over a reader m, which a text passes as mrestrict (w_H W) mem), so that the
   ASan texts of parse_value / parse_items (the recursive-reader slice) and the kit's pj_parse / pj_free / pj_string texts state over ONE set.
   Written by the recursive-reader author; its home is the kit (the kit owner, 22:35Z): the kit adopts this file rather than duplicating it.
   - The PURE spec layer is imported as it stands: Spec/PjTree (jv), Spec/PjGrammar (jr_value, jr_items, ev, calls,
     held_ev, MAXD) and CJ/Spec/FloatScan (the strtod model). They are machine-state-free, so none of the traps of
     preset's released PROGRAM contracts (mkst, SR conclusions, the plain machine state) comes with them. No lemma of a
     released program proof is cited, and no released lib/Prog file is Required.
   - The memory predicates are preset's plain lib/Prog/PjIn.v (pj_in_ok, pj_in_after) and lib/Prog/PjStruct.v
     (pj_node, pj_fd, ...) with the plain Lib/Mem byte predicates replaced: bytes_at m a (le8 v) -> val_mem m a 8 v,
     le4 -> val_mem m a 4, bytes of a list -> garr8, stk / wr_at -> writable_at on every byte. The text bytes are a
     list Z (values 0..255), not a list byte, so rest_atR is a plain skipn. The plain ReaderRes.v definitions taken
     here (zb dropped, lsz, hpeak, nlive) are pure and copied, not imported (ReaderRes imports the plain Contract).
   - Spec/PresetReqAt is Required, not imported, for its ncap alone (the model's capacity of a parsed container),
     which CAP's pj_ncapR (end of Section mem) states the header cap against.
   Definitions, and the frame lemmas of the tree predicates (Section frame, at the end). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure layer (plain ReaderRes.v:58-66, :226-246; PjGrammar's own names otherwise) ---- *)

(* the strtod oracle the reader model takes: (characters consumed, bits), from musl strtod's model *)
Definition prh_jr_strtod (txt : list Z) : Z * Z :=
  match FloatScan.scan_strtod (txt ++ [0]) with
  | Some (bits, c) => (c, bits)
  | None => (0, 0)
  end.

(* the unread rest of the text, from the cursor p *)
Definition rest_atR (tb : list Z) (text p : Z) : list Z := skipn (Z.to_nat (p - text)) tb.

Fixpoint rm1nR (k : nat) (s : list nat) : list nat :=
  match s with
  | [] => []
  | x :: r => if Nat.eqb x k then r else x :: rm1nR k r
  end.
Definition lsz_evR (s : list nat) (e : ev) : list nat :=
  match e with
  | EAlloc n => n :: s
  | EGrow O n => n :: s
  | EGrow m n => n :: rm1nR m s
  | EFail _ => s
  | EFree n => rm1nR n s
  end.
(* the sizes of the blocks a trace leaves live *)
Definition lszR (tr : list ev) : list nat := fold_left lsz_evR tr [].
(* the most user bytes a trace holds at once above its start *)
Fixpoint hpeakR (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => Z.max 0 (held_ev e + hpeakR r)
  end.
Definition nlive_evR (e : ev) : Z :=
  match e with
  | EAlloc _ => 1
  | EGrow O _ => 1
  | EGrow (S _) _ => 0
  | EFail _ => 0
  | EFree _ => -1
  end.
(* the number of blocks a trace leaves live *)
Fixpoint nliveR (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => nlive_evR e + nliveR r
  end.

(* the node bytes a reader call may write: the node, the cursor's two written words, the blocks it allocated
   (plain ReaderRes.v:73-84, with the allocator head width a parameter) *)
Definition pj_in_setR (q x : Z) : Prop := q <= x < q + 8 \/ q + 16 <= x < q + 20.

Section mem.
Variable segs : list Segment.

Definition rd_u64 (m : word -> option byte) (a v : Z) : Prop := 0 <= v < 2 ^ 64 /\ val_mem segs m a 8 v.
Definition rd_u32 (m : word -> option byte) (a v : Z) : Prop := 0 <= v < 2 ^ 32 /\ val_mem segs m a 4 v.
Definition rd_rw (m : word -> option byte) (a n : Z) : Prop := forall x, a <= x < a + n -> writable_at segs m x.

(* ---- the parser's cursor (plain PjIn.v:10-22): q points at {char *p; char *end; int depth} ---- *)
Definition pj_in_okR (m : word -> option byte) (q text len p d : Z) (tb : list Z) : Prop :=
  val_mem segs m q 8 p /\ val_mem segs m (q + 8) 8 (text + len) /\ val_mem segs m (q + 16) 4 d /\
  rd_rw m q 24 /\ q mod 8 = 0 /\
  0 < text /\ text + len < 2 ^ 62 /\ text <= p <= text + len /\
  Z.of_nat (length tb) = len /\ garr8 segs m text tb /\
  (q + 24 <= text \/ text + len <= q) /\ 0 <= d <= 32.

(* the cursor after a refused parse: some position, some depth in [lo, hi], end unchanged (plain ReaderRes.v:208-214) *)
Definition pj_in_afterR (m : word -> option byte) (q text len lo hi : Z) : Prop :=
  exists p' d', text <= p' <= text + len /\ lo <= d' <= hi /\
    val_mem segs m q 8 p' /\ val_mem segs m (q + 8) 8 (text + len) /\ val_mem segs m (q + 16) 4 d' /\ rd_rw m q 24.

(* a zeroed 56-byte node (pj_value is 56 bytes: type, num, str, kids, keys, n, cap) *)
Definition pj_zeroR (m : word -> option byte) (v : Z) : Prop := garr8 segs m v (repeat 0 56).

(* ---- the tree representation (plain PjStruct.v:11-100) ---- *)
Definition pj_rwR (m : word -> option byte) (p : Z) : Prop := p mod 8 = 0 /\ rd_rw m p 56.

Definition pj_hdrR (m : word -> option byte) (p ty num str kids keys n cap : Z) : Prop :=
  pj_rwR m p /\ rd_u32 m p ty /\ rd_u64 m (p + 8) num /\ rd_u64 m (p + 16) str /\
  rd_u64 m (p + 24) kids /\ rd_u64 m (p + 32) keys /\ rd_u64 m (p + 40) n /\ rd_u64 m (p + 48) cap.

Definition pj_cbytesR (m : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\ garr8 segs m a (s ++ [0]).

Definition pj_cstrR (m : word -> option byte) (lblk : Z -> Z -> Prop) (a k : Z) (s : list Z) : Prop :=
  (* the reader's strings are shorter than 2 ^ 32 - 1 (the kit owner's ruling): the engine's strlen / strcmp rules take
     `k + 1 < 2 ^ 32` (YGcfStr.v:128, :153), and pj_parse supplies it from maxrun tl < 2 ^ 30 (PRH_FnPj.v:267) *)
  lblk a k /\ Z.of_nat (length s) + 1 <= k /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ pj_cbytesR m a s.

Definition pj_holdsR (b : Z * Z) (x : Z) : Prop := fst b <= x < fst b + snd b.

Definition pj_apartR (D : list (Z * Z)) (p : Z) : Prop :=
  forall b x, In b D -> pj_holdsR b x -> ~ (p <= x < p + 56).

Fixpoint pj_itemsR (P : Z -> jv -> list (Z * Z) -> Prop) (a : Z) (l : list jv) (D : list (Z * Z)) : Prop :=
  match l with
  | [] => D = []
  | u :: r => exists D1 D2, D = D1 ++ D2 /\ P a u D1 /\ pj_itemsR P (a + 56) r D2
  end.

Fixpoint pj_memsR (m : word -> option byte) (lblk : Z -> Z -> Prop) (P : Z -> jv -> list (Z * Z) -> Prop)
    (a ka : Z) (l : list (list Z * jv)) (D : list (Z * Z)) : Prop :=
  match l with
  | [] => D = []
  | (nm, u) :: r => exists x k D1 D2, D = (x, k) :: D1 ++ D2 /\ rd_u64 m ka x /\ pj_cstrR m lblk x k nm /\
      P a u D1 /\ pj_memsR m lblk P (a + 56) (ka + 8) r D2
  end.

(* the node at p represents t; D lists the blocks its subtree owns *)
Fixpoint pj_nodeR (m : word -> option byte) (lblk : Z -> Z -> Prop) (p : Z) (t : jv) (D : list (Z * Z))
    {struct t} : Prop :=
  NoDup D /\ pj_apartR D p /\
  exists num str kids keys n cap,
    pj_hdrR m p (tag t) num str kids keys n cap /\
    match t with
    | JNull | JFalse | JTrue => str = 0 /\ kids = 0 /\ keys = 0 /\ n = 0 /\ cap = 0 /\ D = []
    | JNum txt bits => num = bits /\ kids = 0 /\ keys = 0 /\ n = 0 /\ cap = 0 /\
        exists k, pj_cstrR m lblk str k txt /\ D = [(str, k)]
    | JStr s => kids = 0 /\ keys = 0 /\ n = 0 /\ cap = 0 /\
        exists k, pj_cstrR m lblk str k s /\ D = [(str, k)]
    | JArr items => str = 0 /\ keys = 0 /\ n = Z.of_nat (length items) /\ n <= cap /\
        (cap = 0 /\ kids = 0 \/ 0 < cap /\ lblk kids (56 * cap)) /\
        exists Di, D = (if cap =? 0 then [] else [(kids, 56 * cap)]) ++ Di /\
          pj_itemsR (pj_nodeR m lblk) kids items Di
    | JObj members => str = 0 /\ n = Z.of_nat (length members) /\ n <= cap /\
        (cap = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap)) /\
        exists Di, D = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di /\
          pj_memsR m lblk (pj_nodeR m lblk) kids keys members Di
    end.

Definition pj_keyR (m : word -> option byte) (lblk : Z -> Z -> Prop) (ks : bool) (ka : Z) (Dk : list (Z * Z)) : Prop :=
  if ks then exists x, rd_u64 m ka x /\ (x = 0 /\ Dk = [] \/ exists k, lblk x k /\ Dk = [(x, k)])
  else Dk = [].

Fixpoint pf_itemsR (m : word -> option byte) (lblk : Z -> Z -> Prop) (P : Z -> list (Z * Z) -> Prop)
    (ks : bool) (a ka : Z) (n : nat) (D : list (Z * Z)) : Prop :=
  match n with
  | O => D = []
  | S n' => exists Dk D1 D2, D = Dk ++ D1 ++ D2 /\ pj_keyR m lblk ks ka Dk /\ P a D1 /\
      pf_itemsR m lblk P ks (a + 56) (ka + 8) n' D2
  end.

Definition pj_fshapeR (m : word -> option byte) (lblk : Z -> Z -> Prop)
    (Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop) (p : Z) (D : list (Z * Z)) : Prop :=
  NoDup D /\ pj_apartR D p /\
  exists ty num str kids keys n cap ks Ds Dk Dy Di,
    pj_hdrR m p ty num str kids keys n cap /\
    (str = 0 /\ Ds = [] \/ exists k, lblk str k /\ Ds = [(str, k)]) /\
    (kids = 0 /\ n = 0 /\ Dk = [] \/ exists k, lblk kids k /\ 56 * n <= k /\ Dk = [(kids, k)]) /\
    (keys = 0 /\ ks = false /\ Dy = [] \/ ks = true /\ exists k, lblk keys k /\ 8 * n <= k /\ Dy = [(keys, k)]) /\
    Permutation D (Ds ++ Dk ++ Dy ++ Di) /\
    Pi ks kids keys n Di.

(* a partly built (refused) tree, freeable by pj_free to depth d: what a refused parse leaves (plain PjStruct.v:94) *)
Fixpoint pj_fdR (m : word -> option byte) (lblk : Z -> Z -> Prop) (d : nat) (p : Z) (D : list (Z * Z))
    {struct d} : Prop :=
  match d with
  | O => pj_fshapeR m lblk (fun _ _ _ n Di => n = 0 /\ Di = []) p D
  | S d' => pj_fshapeR m lblk (fun ks kids keys n Di => pf_itemsR m lblk (pj_fdR m lblk d') ks kids keys (Z.to_nat n) Di) p D
  end.
(* ---- the four plain names the reader-texts author asked for (gap G1 of lib/A/PRH_FnReader.v), restated here so its prhReader_
   copies switch by rename: plain ReaderRes.v:74-79 cap2 / kids_blk / keys_blk and PjStruct.v:109-112 pj_slots_at.
   They are machine-state-free, so they take no memory argument. ---- *)
Definition cap2R (cap : Z) : Z := if cap =? 0 then 8 else 2 * cap.

Definition kids_blkR (kids cap : Z) : list (Z * Z) := if cap =? 0 then [] else [(kids, 56 * cap)].

Definition keys_blkR (ty keys cap : Z) : list (Z * Z) :=
  if (cap =? 0) || negb (ty =? 6) then [] else [(keys, 8 * cap)].

Definition pj_slots_atR (lblk : Z -> Z -> Prop) (ty kids keys n cap : Z) : Prop :=
  (ty = 5 \/ ty = 6) /\ n <= cap <= 2 ^ 54 /\
  (cap = 0 -> kids = 0 /\ (ty = 6 -> keys = 0)) /\
  (0 < cap -> lblk kids (56 * cap) /\ (ty = 6 -> lblk keys (8 * cap))).

(* ---- three more shared names the kit's walks use (added on the walk-kit branch, in the tree `preset-tree-at-2026-10-29T08-45-51Z.tsv (sha256 5158fa4d0b4f; internal record)`, by the kit owner's ruling; same
   bodies as plain PjStruct.v pj_slots / pj_foot / pj_freeable, restated over pj_hdrR / pj_holdsR / pj_fdR) ---- *)
Definition pj_slotsR (m : word -> option byte) (lblk : Z -> Z -> Prop) (p : Z) : Prop :=
  exists ty num str kids keys n cap, pj_hdrR m p ty num str kids keys n cap /\ pj_slots_atR lblk ty kids keys n cap.
Definition pj_footR (p : Z) (D : list (Z * Z)) (x : Z) : Prop :=
  (p <= x < p + 56) \/ exists b, In b D /\ pj_holdsR b x.
Definition pj_freeableR (m : word -> option byte) (lblk : Z -> Z -> Prop) (p : Z) (D : list (Z * Z)) : Prop :=
  exists d, pj_fdR m lblk d p D.

(* ---- CAP: THE READER'S CAPACITY, per container node (the kit owner's order, 2026-10-29) ----
   pj_ncapR m p t: every array or object node of the tree t at p, recursively through its kids, has the header cap
   (the word at p + 48) Z.of_nat (PresetReqAt.ncap n) for its count n, the length of its item or member list (pj_nodeR
   ties the header's n to that length). ncap is PjRoundTrip.gcap iterated from 0 (PresetReqAt.v:203-205), the
   capacity prhPj_set_evs_supply's premise F6 names (PRH_FnPj.v). The kids are reached as pj_nodeR reaches them: item
   i at kids + 56 * i, kids the word at p + 24 (pj_kidsR). A leaf states nothing (pj_nodeR already has its cap = 0).
   WHY pj_nodeR DOES NOT GIVE IT, and the size multiset of the blocks does not either (the kit owner's counterexample,
   vm_compute-checked): ms = [(repeat 97 7, JStr (repeat 98 55))], header n = 1, cap = 1, D = [(kids, 56); (keys, 8);
   (x, 448); (str, 64)] satisfies pj_nodeR (n <= cap; pj_cstrR needs only len + 1 <= k), and map (snd + 16) D =
   [72; 24; 464; 80] is a Permutation of PresetReqAtNoMiss.tblk (JObj ms) = [464; 80; 24; 72], yet cap = 1 <> 8 =
   ncap 1. A PERMUTATION OF SIZES IDENTIFIES NO BLOCK: anything a consumer needs about a PARTICULAR block is stated
   about that block, so the capacity is stated here per node.
   TRUE OF THE BINARY (the library source src/preset_file.c, sha256 34d5664a4829a366): every node parse_value fills
   starts zeroed - pj_parse's memset (out, 0, ..) at :300 and parse_items' memset (&v->kids[v->n], 0, ..) at :243 - so a
   container's parse_items (:211-264, which sets only the type, :213) starts at n = 0, cap = 0. An empty container
   returns at :218-223 with cap = 0 = ncap 0. Otherwise each item first calls grow (:226), which keeps cap when
   n < cap (:48-49) and else takes cap = cap ? cap * 2 : 8 (:50, stored at :62 once its reallocs succeed), and the
   accepted item then makes n++ (:249): that is PjRoundTrip.gcap n cap per item from (0, 0), so after the k items of
   an ACCEPTED container cap = ncap k. A grow's realloc (:51, :57) moves the kids array with its contents, so each
   kid keeps the cap its own parse_items left. A refused reading leaves no tree (pj_parse frees and zeroes out, :307
   -> pj_free's memset at :349), so the texts state pj_ncapR on their ACCEPTED arms only: tpj_parse_specX's Some arm
   (PRH_FnPj.v), tparse_noting_specX's Some arm and tround_trip_text_specX's r = 0, copy <> 0 arm (PRH_FnCheck.v; the
   copy is the read-back tree's header moved verbatim by `*copy = back`, base fuzz_preset.c:707). *)
(* P holds of each item of l at its 56-byte slot from a: item i at a + 56 * i *)
Fixpoint pj_kidsR {A : Type} (P : Z -> A -> Prop) (a : Z) (l : list A) {struct l} : Prop :=
  match l with
  | [] => True
  | x :: r => P a x /\ pj_kidsR P (a + 56) r
  end.

Fixpoint pj_ncapR (m : word -> option byte) (p : Z) (t : jv) {struct t} : Prop :=
  match t with
  | JArr items => rd_u64 m (p + 48) (Z.of_nat (PresetReqAt.ncap (length items))) /\
      exists kids, rd_u64 m (p + 24) kids /\ pj_kidsR (pj_ncapR m) kids items
  | JObj members => rd_u64 m (p + 48) (Z.of_nat (PresetReqAt.ncap (length members))) /\
      exists kids, rd_u64 m (p + 24) kids /\
        pj_kidsR (fun a (mb : list Z * jv) => let (_, u) := mb in pj_ncapR m a u) kids members
  | _ => True
  end.

End mem.

(* ---- FRAME lemmas of the tree predicates (added by walk slice S6 at the kit owner's ruling, 2026-10-29): a tree whose
   footprint pj_footR keeps its bytes, and its writable bytes writable, is the same tree in the new memory. A walk
   uses them to carry a tree across a step (a call, a store elsewhere). Transcribed from preset's plain
   lib/Prog/CrsNode.v:39-134 (cn_u64 / cn_hdr / cn_cstr_mframe / cn_node_mframe over plain PjStruct.pj_node); no plain
   lemma is cited. Numerals: the node layout only (LENGTH: 56 node bytes, 8 / 4 field widths, 8..48 field offsets,
   8 key-pointer stride). ---- *)
Section frame.
Variable segs : list Segment.

(* two memories agree on a byte set: the byte values, and a writable byte stays writable *)
Definition pj_agreeR (m m' : word -> option byte) (X : Z -> Prop) : Prop :=
  forall x, X x -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x).

Lemma pj_valR_frame : forall m m' a n v, val_mem segs m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) -> val_mem segs m' a n v.
Proof. intros m m' a n v Hv Hfr k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma rd_u64_frame : forall m m' a v, rd_u64 segs m a v ->
  (forall x, a <= x < a + 8 -> mbyte segs m' x = mbyte segs m x) -> rd_u64 segs m' a v.
Proof.
intros m m' a v (Hr & Hv) E. split; [exact Hr|]. apply (pj_valR_frame m m' a 8 v Hv). intros x Hx. apply E. cbn in Hx. lia.
Qed.

Lemma rd_u32_frame : forall m m' a v, rd_u32 segs m a v ->
  (forall x, a <= x < a + 4 -> mbyte segs m' x = mbyte segs m x) -> rd_u32 segs m' a v.
Proof.
intros m m' a v (Hr & Hv) E. split; [exact Hr|]. apply (pj_valR_frame m m' a 4 v Hv). intros x Hx. apply E. cbn in Hx. lia.
Qed.

Lemma garr8R_frame : forall m m' a l, garr8 segs m a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) -> garr8 segs m' a l.
Proof.
intros m m' a l H E j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pj_valR_frame m m' (a + Z.of_nat j) 1 (nth j l 0) Hv). intros x Hx. apply E. cbn in Hx. lia.
Qed.

Lemma pj_hdrR_frame : forall m m' p ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap -> pj_agreeR m m' (fun x => p <= x < p + 56) ->
  pj_hdrR segs m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap ((Ha & Hrw) & T & N & Sx & K & Y & Nn & C) E.
assert (F : forall a w, p <= a -> a + w <= p + 56 -> forall x, a <= x < a + w -> mbyte segs m' x = mbyte segs m x)
  by (intros a w H1 H2 x Hx; apply (proj1 (E x ltac:(lia)))).
split; [split; [exact Ha | intros x Hx; apply (proj2 (E x Hx)); exact (Hrw x Hx)]|].
split; [apply (rd_u32_frame m m' p ty T); apply (F p 4); lia|].
split; [apply (rd_u64_frame m m' (p + 8) num N); apply (F (p + 8) 8); lia|].
split; [apply (rd_u64_frame m m' (p + 16) str Sx); apply (F (p + 16) 8); lia|].
split; [apply (rd_u64_frame m m' (p + 24) kids K); apply (F (p + 24) 8); lia|].
split; [apply (rd_u64_frame m m' (p + 32) keys Y); apply (F (p + 32) 8); lia|].
split; [apply (rd_u64_frame m m' (p + 40) n Nn); apply (F (p + 40) 8); lia|].
apply (rd_u64_frame m m' (p + 48) cap C); apply (F (p + 48) 8); lia.
Qed.

Lemma pj_cstrR_frame : forall m m' lblk a k s, pj_cstrR segs m lblk a k s ->
  (forall x, a <= x < a + k -> mbyte segs m' x = mbyte segs m x) -> pj_cstrR segs m' lblk a k s.
Proof.
intros m m' lblk a k s (Hl & Hk & Hn & Hf & Hb) E.
split; [exact Hl|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Hf|].
apply (garr8R_frame m m' a (s ++ [0]) Hb). intros x Hx. apply E. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

(* the items of an array: each item at a + 56 i, with its blocks among the list's *)
Lemma pj_itemsR_mono : forall (P P' : Z -> jv -> list (Z * Z) -> Prop) l a D,
  pj_itemsR P a l D ->
  (forall i u D1, nth_error l i = Some u -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 -> P' (a + 56 * Z.of_nat i) u D1) ->
  pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u r IH]; intros a D H HP; cbn [pj_itemsR] in H |- *; [exact H|].
destruct H as (D1 & D2 & -> & H1 & H2). exists D1, D2. split; [reflexivity|]. split.
- specialize (HP 0%nat u D1 eq_refl (incl_appl D2 (incl_refl D1))).
  replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) D2 H2). intros i u' D1' Hi Hinc HPi.
  specialize (HP (S i) u' D1' Hi (incl_appr D1 Hinc)). replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi).
Qed.

(* the members of an object: value i at a + 56 i, key pointer i at ka + 8 i, the key string a block of the list *)
Lemma pj_memsR_mono : forall m m' lblk (P P' : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall i nm u x k D1, nth_error l i = Some (nm, u) -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk x k nm /\ P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m' lblk P' a ka l D.
Proof.
intros m m' lblk P P' l. induction l as [|[nm u] r IH]; intros a ka D H HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
pose proof (HP 0%nat nm u x k D1 eq_refl (or_introl eq_refl)
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. replace (ka + 8 * Z.of_nat 0) with ka in HP0 by lia.
destruct (HP0 Hx Hc H1) as (Hx' & Hc' & H1'). split; [exact Hx'|]. split; [exact Hc'|].
split; [exact H1'|].
apply (IH (a + 56) (ka + 8) D2 H2). intros i nm' u' x' k' D1' Hi Hin Hinc Hx2 Hc2 HP2.
specialize (HP (S i) nm' u' x' k' D1' Hi (in_cons _ _ _ (in_or_app _ _ _ (or_intror Hin)))
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) in HP by lia.
exact (HP Hx2 Hc2 HP2).
Qed.

Lemma pj_nth_lenR : forall {X} (l : list X) i u, nth_error l i = Some u -> (i < length l)%nat.
Proof. intros X l i u H. apply nth_error_Some. rewrite H. discriminate. Qed.

(* THE FRAME LEMMA of the tree: a tree whose footprint keeps its bytes (and writability) is the same tree *)
Lemma pj_nodeR_frame : forall t m m' lblk p D, pj_nodeR segs m lblk p t D ->
  pj_agreeR m m' (pj_footR p D) -> pj_nodeR segs m' lblk p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m m' lblk p D H HM; cbn [pj_nodeR] in H |- *;
  assert (HM1 : forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; exact (proj1 (HM x Hx)));
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
  (split; [apply (pj_hdrR_frame m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pj_cstrR_frame m m'); [exact Hc|].
  intros x Hx. apply HM1. right. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pj_cstrR_frame m m'); [exact Hc|].
  intros x Hx. apply HM1. right. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk) items kids Di Hi).
  intros i u D1 Hil Hinc HP.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m m' lblk _ D1 HP).
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_memsR_mono m m' lblk (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk) members kids keys Di Hi).
  intros i nm u x k D1 Hil Hxk Hinc Hx Hcs HP.
  pose proof (pj_nth_lenR members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
  split; [|split].
  + apply (rd_u64_frame m m'); [exact Hx|]. intros y Hy. apply HM1. right. exists (keys, 8 * cap).
    split; [exact (proj2 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply (pj_cstrR_frame m m'); [exact Hcs|].
    intros y Hy. apply HM1. right. exists (x, k).
    split; [apply HDi; exact Hxk | unfold pj_holdsR; cbn [fst snd]; exact Hy].
  + rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m m' lblk _ D1 HP).
    intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
    * right. exists (kids, 56 * cap). split; [exact (proj1 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
    * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

(* the zeroed node *)
Lemma pj_zeroR_frame : forall m m' v, pj_zeroR segs m v ->
  (forall x, v <= x < v + 56 -> mbyte segs m' x = mbyte segs m x) -> pj_zeroR segs m' v.
Proof. intros m m' v H E. apply (garr8R_frame m m' v (repeat 0 56) H). intros x Hx. apply E. cbn [length repeat] in Hx. lia. Qed.

End frame.
