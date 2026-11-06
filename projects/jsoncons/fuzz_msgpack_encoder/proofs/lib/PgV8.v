(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmTxtSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGV8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive v8 : Type := V8Null | V8Blk (b n c : Z).
Definition v8_size (x : v8) : Z := match x with V8Null => 0 | V8Blk _ n _ => n end.
Definition v8_cap (x : v8) : Z := match x with V8Null => 0 | V8Blk _ _ c => c end.
Definition v8_data (x : v8) : Z := match x with V8Null => 0 | V8Blk b _ _ => b end.
Definition v8_own (x : v8) : list (Z * Z) := match x with V8Null => [] | V8Blk b _ c => [(b, c)] end.
(* [comment removed for export] *)
Definition v8_clear (x : v8) : v8 := match x with V8Null => V8Null | V8Blk b _ c => V8Blk b 0 c end.

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
(* [comment removed for export] *)
Definition v8_at (M : word -> option byte) (v : Z) (x : v8) : Prop :=
  L5.defined M v 24 /\ acc M v 24 /\
  match x with
  | V8Null => L5.u64_at segs M v 0 /\ L5.u64_at segs M (v + 8) 0 /\ L5.u64_at segs M (v + 16) 0
  | V8Blk b n c => L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + n) /\ L5.u64_at segs M (v + 16) (b + c)
                   /\ 0 <= n <= c /\ 1 <= c <= 2 ^ 27 /\ 4096 <= b /\ b mod 16 = 0
                   /\ L5.defined M b c /\ acc M b n /\ ann M b n c
  end.
End Model.

(* [comment removed for export] *)
Definition v8_ok (x : v8) (g : Z) : Prop :=
  match x with V8Null => g = 0 | V8Blk _ _ c => 1 <= g <= 28 /\ 2 ^ (g - 1) <= c end.
(* [comment removed for export] *)
Definition pot_v8 (L : heap_layout) (x : v8) (g : Z) : credit :=
  (hl_k_per_malloc L * (28 - g), (2 ^ 28 - 2 * v8_cap x) + (28 - g) * hl_b_overhead L).
(* [comment removed for export] *)
Definition v8_grow_ok (x : v8) (n : Z) : Prop := n <= v8_cap x \/ (v8_cap x <= 2 ^ 26 /\ n <= 2 ^ 27).

(* [comment removed for export] *)
Definition v8_room (x : v8) (u : Z) : Prop :=
  match x with
  | V8Null => True
  | V8Blk _ _ c => exists a0 j, 0 <= j /\ c = a0 * 2 ^ j /\ 1 <= a0 <= 2 ^ 14 /\ a0 + u <= 2 ^ 26
  end.
Lemma v8_room_mono x u u' : u' <= u -> v8_room x u -> v8_room x u'.
Proof. destruct x as [|b n c]; cbn; [tauto|]. intros Hu (a0 & j & H1 & H2 & H3 & H4). exists a0, j. repeat split; lia. Qed.
Lemma v8_room_clear x u : v8_room x u -> v8_room (v8_clear x) u.
Proof. destruct x; cbn; tauto. Qed.
Lemma v8_room_cap x x' u : v8_cap x' = v8_cap x -> x' <> V8Null -> x <> V8Null -> v8_room x u -> v8_room x' u.
Proof. destruct x, x'; cbn; intros E N1 N2 H; [tauto| exfalso; exact (N2 eq_refl)| exfalso; exact (N1 eq_refl)| subst; exact H]. Qed.

Lemma v8_ok_cap x g : v8_ok x g -> 0 <= g <= 28 /\ (g = 0 <-> x = V8Null).
Proof. destruct x as [|b n c]; cbn; [intros ->; split; [lia| tauto]| intros [H1 H2]; split; [lia| split; [lia| discriminate]]]. Qed.

Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation iss_at := (PM.iss_at segs A PMSP.T3).
Abbreviation nullis_at := (PM.nullis_at segs A PMSP.T3).
Abbreviation src_fields_at := (PM.src_fields_at segs PMSP.T3).
Abbreviation v8_atP := (v8_at segs PMSP.T3 PMSP.T4).
Abbreviation entry := (PMSP.entry A L).
Abbreviation pm_scr := PMSP.pm_scr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vu8_grow_spec (pc : Z) (is_append : bool) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (v a sp r g : Z) (x : v8),
    hi_heap HI (v8_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 a -> sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 ->
    v8_atP M v x -> v8_ok x g ->
    (* [comment removed for export] *)
    (if is_append then 1 <= a /\ v8_size x + a < 2 ^ 64 else 0 <= a < 2 ^ 64) ->
    v8_grow_ok x (if is_append then v8_size x + a else a) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : v8) (g' : Z) (cr' : credit),
        regs_preserved R R' -> v8_atP M' v x' -> v8_size x' = (if is_append then v8_size x + a else a) -> v8_ok x' g' ->
        v8_cap x <= v8_cap x' ->
        (v8_size x' <= v8_cap x -> v8_own x' = v8_own x /\ v8_cap x' = v8_cap x /\ g' = g) ->
        (v8_cap x' = v8_cap x \/ v8_cap x' = Z.max (2 * v8_cap x) (if is_append then v8_size x + a else a)) ->   (* [comment removed for export] *)
        L5C.hpres L LB sp (pm_scr 1) [(v, 24)] M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (v8_own x' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.
Definition vu8_resize_spec (pc : Z) : Prop := vu8_grow_spec pc false.
Definition vu8_append_spec (pc : Z) : Prop := vu8_grow_spec pc true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record vowner : Type := VOWN {
  vw_at  : (word -> option byte) -> PM.srcst -> v8 -> Z -> list (Z * Z) -> Prop;
  vw_os  : Z; vw_ois : Z; vw_ov : Z; vw_lo : Z; vw_hi : Z
}.
Record vowner_ok (V : vowner) : Prop := {
  vo_src : forall M src x g OB, vw_at V M src x g OB ->
             src_fields_at M (vw_os V) (vw_ois V) (vw_ois V + 16) src /\ nullis_at M (vw_os V + 8) /\ L5.defined M (vw_os V) 296
             /\ v8_atP M (vw_ov V) x /\ v8_ok x g;
  vo_lay : vw_lo V <= vw_os V /\ vw_os V + 296 <= vw_hi V /\ vw_lo V <= vw_ois V /\ vw_ois V + 272 <= vw_hi V
           /\ vw_lo V <= vw_ov V /\ vw_ov V + 24 <= vw_hi V /\ vw_hi V <= hl_sptop L /\ vw_hi V <= 2 ^ 47
           /\ vw_os V mod 8 = 0 /\ vw_ois V mod 8 = 0 /\ vw_ov V mod 8 = 0 /\ 4096 <= vw_lo V
           /\ (vw_os V + 296 <= vw_ois V \/ vw_ois V + 272 <= vw_os V)
           /\ (vw_ov V + 24 <= vw_os V \/ vw_os V + 296 <= vw_ov V) /\ (vw_ov V + 24 <= vw_ois V \/ vw_ois V + 272 <= vw_ov V);
  (* [comment removed for export] *)
  vo_upd : forall (LBX : list (Z * Z)) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte) (src src' : PM.srcst)
             (x x' : v8) (g g' : Z) (OB : list (Z * Z)) (cr : credit) (VM : VmMaps),
             sp <= vw_lo V -> vw_at V M src x g OB ->
             hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M VM ->
             (* [comment removed for export] *)
             Forall (fun b => fst b + snd b <= vw_lo V \/ vw_hi V <= fst b) (PM.src_own src ++ v8_own x ++ OB) ->
             (forall b, In b OB -> (fst b + snd b <= PM.sr_qc src \/ PM.sr_qc src + PM.CHUNK <= fst b)
                                   /\ (forall B' m', In (B', m') (v8_own x) -> fst b + snd b <= B' \/ B' + m' <= fst b)) ->
             (* [comment removed for export] *)
             Forall (fun r => (fst r + snd r <= vw_lo V \/ vw_hi V <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r)) Wx ->
             L5C.hpres L (OB ++ LBX) sp scr (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)] ++ Wx) M M' ->
             src_fields_at M' (vw_os V) (vw_ois V) (vw_ois V + 16) src' -> PM.sr_qc src' = PM.sr_qc src ->
             v8_atP M' (vw_ov V) x' -> v8_ok x' g' ->
             vw_at V M' src' x' g' OB
}.
(* [comment removed for export] *)
Definition src_of_vw (V : vowner) (x : v8) (g : Z) : PGS.owner :=
  {| PGS.ow_at := fun M src OB' => exists OB, OB' = v8_own x ++ OB /\ vw_at V M src x g OB;
     PGS.ow_os := vw_os V; PGS.ow_ois := vw_ois V; PGS.ow_lo := vw_lo V; PGS.ow_hi := vw_hi V;
     PGS.ow_win := fun M src OB' p k => 0 <= k /\ exists b n c, x = V8Blk b n c /\ b <= p /\ p + k <= b + c |}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_span_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 6 ->
    sp <= vw_lo V ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 len -> getr R 12%bv = Z_to_bv 64 (vw_ov V) -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> v8_room x (PM.unread src sm) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
        PMSP.consumed src src' sm sm' = n ->
        ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ v8_own x' ++ OB) ptr n) ->
        L5.defined M' ptr n ->
        (n = len -> v8_room x' (PM.unread src' sm')) ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 6) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

(* [comment removed for export] *)
Definition srd_read_v_specG (pc : Z) : Prop :=
  forall (V : vowner), vowner_ok V ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (OB LBX : list (Z * Z)) (cr : credit) (sp r len : Z) (src : PM.srcst) (x : v8) (g : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.src_own src ++ v8_own x ++ OB ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 5 ->
    sp <= vw_lo V ->
    getr R 10%bv = Z_to_bv 64 (vw_os V) -> getr R 11%bv = Z_to_bv 64 (vw_ov V) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    vw_at V M src x g OB -> iss_at M (vw_ois V) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX -> PM.unread src sm < 2 ^ 26 -> v8_size x = 0 -> v8_room x (PM.unread src sm) ->
    PMSP.credit_le (pot_v8 L x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed src src' sm sm' = d -> v8_size x' = d ->
        (d = len -> v8_room x' (PM.unread src' sm')) ->
        vw_at V M' src' x' g' OB -> iss_at M' (vw_ois V) str sm' ->
        PMSP.src_step src src' sm sm' ->
        L5C.hpres L LBX sp (pm_scr 5) (PGS.W_srcfG (vw_os V) (vw_ois V) ++ [(vw_ov V, 24)]) M M' ->
        PMSP.credit_keep cr cr' (pot_v8 L x g) (pot_v8 L x' g') ->
        model_but_vm model model' -> hi_heap HI (PM.src_own src' ++ v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pot_v8_grow L x g c' :
  0 <= hl_k_per_malloc L -> v8_ok x g -> 2 * v8_cap x <= c' ->
  forall b' n', v8_ok (V8Blk b' n' c') (g + 1) ->
  fst (pot_v8 L x g) - hl_k_per_malloc L = fst (pot_v8 L (V8Blk b' n' c') (g + 1))
  /\ snd (pot_v8 L x g) - (c' + hl_b_overhead L) >= snd (pot_v8 L (V8Blk b' n' c') (g + 1)).
Proof. intros K OK Hc b' n' OK'. unfold pot_v8. cbn [fst snd v8_cap]. split; lia. Qed.

(* [comment removed for export] *)
Lemma v8_ok_grow x g b' n' c' :
  v8_ok x g -> 2 * v8_cap x <= c' -> 1 <= c' <= 2 ^ 27 -> v8_ok (V8Blk b' n' c') (g + 1).
Proof.
  intros OK H2 Hc. destruct x as [|b n c]; cbn in *.
  - subst g. cbn. split; [lia|]. change (2 ^ 0) with 1. lia.
  - destruct OK as [Hg Hp]. cbn. replace (g + 1 - 1) with ((g - 1) + 1) by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    split; [|lia].
    (* [comment removed for export] *)
    destruct (Z_le_gt_dec (g + 1) 28) as [H|H]; [lia|exfalso].
    assert (2 ^ 27 <= 2 ^ (g - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

End PGV8.
