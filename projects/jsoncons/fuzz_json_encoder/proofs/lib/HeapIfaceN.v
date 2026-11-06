(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface HeapIfaceA IcptIfaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition NB : Z := 2 ^ 33 + 2 ^ 17.
Lemma NB_ge_27 : 2 ^ 27 <= NB.  Proof. unfold NB. lia. Qed.

Section NIface.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IL : icpt_layout.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition amalloc_specN : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NB -> acredit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    amalloc_post L ar scfg HI fx R M model LB FF LK cr A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.

Lemma amalloc_spec_of_N : amalloc_specN -> amalloc_spec L ar scfg HI.
Proof.
  intros H fx R M model LB FF LK cr A n K RI Hh HMI H10 Hn HC H4 Hr AST K0 POST.
  apply (H fx R M model LB FF LK cr A n K RI Hh HMI H10); [pose proof NB_ge_27; lia|assumption..].
Qed.

(* [comment removed for export] *)
Definition amem_preN (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv HI LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= NB /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_mem L) (bv_unsigned (getr R 2%bv)) /\
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.

Definition amemcpy_specN_at (pc : Z) (may_overlap : bool) : Prop :=
  forall fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amem_preN fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->
    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (may_overlap = false -> dst + n <= src \/ src + n <= dst) ->
    amem_post L ar scfg HI fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.
Definition amemcpy_libc_specN : Prop := amemcpy_specN_at (icl_memcpy IL) false.
Definition amemmove_libc_specN : Prop := amemcpy_specN_at (icl_memmove IL) false.

Lemma amem_pre_of_N : forall fx R M model LB FF LK cr A dst n K,
  amem_pre L ar HI fx R M model LB FF LK cr A dst n K -> amem_preN fx R M model LB FF LK cr A dst n K.
Proof.
  intros fx R M model LB FF LK cr A dst n K (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof NB_ge_27 as HNB.
  unfold amem_preN. repeat (split; [first [assumption|lia]|]). exact P7.
Qed.
Lemma amemcpy_spec_at_of_N : forall pc ov, amemcpy_specN_at pc ov -> amemcpy_spec_at L ar scfg HI pc ov.
Proof.
  intros pc ov H fx R M model LB FF LK cr A dst src n bs K PRE. apply H. apply amem_pre_of_N. exact PRE.
Qed.
End NIface.
