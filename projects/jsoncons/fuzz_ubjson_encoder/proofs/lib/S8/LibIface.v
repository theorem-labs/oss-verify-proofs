(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record lib_layout : Type := LL {
  ll_heap   : heap_layout;
  ll_entry  : Z;
  ll_gp     : Z;
  ll_empty  : Z;
  ll_initc  : list (Z * Z);
  ll_init_img : list (Z * Z);
  ll_td_self : Z; ll_td_tid : Z; ll_td_locale : Z; ll_locale : Z; ll_td_canary : Z; ll_guard : Z; ll_auxvp : Z;

  ll_phdr : Z; ll_phent : Z; ll_phnum : Z;
  ll_rw_lo  : Z;
  ll_stack  : Z;
  ll_credit : Z -> credit;
  ll_foot   : list (Z * Z)       ;
  ll_init_cells : list (Z * Z * Z)
}.

Definition in_foot (Lay : lib_layout) (a : Z) : Prop :=
  exists iv, In iv (ll_foot Lay) /\ fst iv <= a < snd iv.

Definition in_initc (Lay : lib_layout) (a : Z) : Prop :=
  (exists iv, In iv (ll_initc Lay) /\ fst iv <= a < snd iv) \/ (hl_sptop (ll_heap Lay) <= a < 2 ^ 64).

Definition cellz (segs : list Segment) (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

Definition auxv_words (Lay : lib_layout) (uid rnd hw : Z) : list Z :=
  [3; ll_phdr Lay; 4; ll_phent Lay; 5; ll_phnum Lay; 16; hw; 6; 4096; 11; uid; 12; uid; 23; 0; 25; rnd; 0; 0].

Definition lib_init_facts (Lay : lib_layout) (av uid rnd tid canary hw : Z) (M : word -> option byte) : Prop :=
  let segs := hl_segs (ll_heap Lay) in let sptop := hl_sptop (ll_heap Lay) in
     (forall iv a, In iv (ll_init_img Lay) -> fst iv <= a < snd iv -> M (Z_to_bv 64 a) = None)
  /\ cellz segs M (ll_td_self Lay) 8 (ll_td_self Lay)
  /\ cellz segs M (ll_td_tid Lay) 4 tid /\ 1 <= tid < 2 ^ 22
  /\ cellz segs M (ll_td_locale Lay) 8 (ll_locale Lay)
  /\ (forall k, (k < 6)%nat -> cellz segs M (ll_locale Lay + 8 * Z.of_nat k) 8 0)
  /\ cellz segs M (ll_td_canary Lay) 8 canary
  /\ cellz segs M (ll_guard Lay) 8 canary /\ 0 <= canary < 2 ^ 64
  /\ cellz segs M (ll_auxvp Lay) 8 av /\ sptop <= av /\ av + 160 <= 2 ^ 47 /\ av mod 8 = 0
  /\ (forall j, (j < 20)%nat -> cellz segs M (av + 8 * Z.of_nat j) 8 (nth j (auxv_words Lay uid rnd hw) 0))
  /\ 0 <= uid < 2 ^ 32 /\ 0 <= hw < 2 ^ 64
  /\ sptop <= rnd /\ rnd + 16 <= 2 ^ 64
  /\ Forall (fun c : Z * Z * Z => cellz segs M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (ll_init_cells Lay).

Section LibIface.
Variable Lay : lib_layout.
Let L := ll_heap Lay.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable HI : heap_iface.

Record lib_statics : Type := LS {
  ls_state : Type;
  ls_ok    : ls_state -> (word -> option byte) -> Prop;

  ls_g0    : ls_state
}.
Variable LSt : lib_statics.

Definition credit_le (c c' : credit) : Prop := fst c <= fst c' /\ snd c <= snd c'.
Definition credit_sub (c d : credit) : credit := (fst c - fst d, snd c - snd d).

Record lib_pre (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := LIB_PRE {
  lp_ra : getr R 1%bv = Z_to_bv 64 ra;
  lp_ra_ok : 0 <= ra < 2 ^ 47 /\ ra mod 2 = 0;
  lp_sp : getr R 2%bv = Z_to_bv 64 sp;
  lp_gp : getr R 3%bv = Z_to_bv 64 (ll_gp Lay);
  lp_tp : getr R 4%bv = Z_to_bv 64 (hl_tp L);
  lp_a0 : getr R 10%bv = Z_to_bv 64 ptr;
  lp_a1 : getr R 11%bv = Z_to_bv 64 (Z.of_nat (length payload));
  lp_len : Z.of_nat (length payload) < 2 ^ 26;
  lp_ptr : (length payload = 0%nat /\ ptr = ll_empty Lay)
           \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB);
  lp_payload : rdn (hl_segs L) M (Z_to_bv 64 ptr) (length payload) = Some payload;

  lp_stack : sp mod 16 = 0 /\ hl_ceil L + ll_stack Lay <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\
             (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= ll_stack Lay ->
                 store_ok (hl_segs L) M (Z_to_bv 64 (sp - ll_stack Lay + d)) m = true)
             /\ (forall a, sp - ll_stack Lay <= a < sp -> M (Z_to_bv 64 a) <> None);
  lp_credit : credit_le (ll_credit Lay (Z.of_nat (length payload))) cr;
  lp_statics : ls_ok LSt g M
}.

Lemma lib_pre_floor : forall g LB cr sp ptr ra payload R M,
  lib_pre g LB cr sp ptr ra payload R M -> 0x7fff7f800000 + ll_stack Lay <= sp.
Proof. intros * P. pose proof (lp_stack _ _ _ _ _ _ _ _ _ P) as (_ & H & _ & (Hlo & _) & _). revert H Hlo. unfold L. intros. lia. Qed.

Record lib_post (g' : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp : Z) (payload : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) (cr' : credit) : Prop := LIB_POST {
  lq_a0 : getr R 10%bv = Z_to_bv 64 0;
  lq_regs : regs_preserved R0 R;
  lq_credit : credit_le (credit_sub cr (ll_credit Lay (Z.of_nat (length payload)))) cr';

  lq_frame : forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (ll_stack Lay) a -> ~ in_foot Lay a -> ~ in_errno L a ->
             M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
  lq_scratch : forall a, sp - ll_stack Lay <= a < sp -> M (Z_to_bv 64 a) <> None;

  lq_statics : ls_ok LSt g' M
}.

Definition lib_cfg {fx : FPState} (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

Definition lib_call_ok : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_pre g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        lib_post g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs L) scfg (@lib_cfg fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfg fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

Definition lib_statics_init : Prop :=
  forall av uid rnd tid canary hw M, lib_init_facts Lay av uid rnd tid canary hw M -> ls_ok LSt (ls_g0 LSt) M.

Definition lib_statics_frame : Prop :=
  forall g M M', ls_ok LSt g M ->
    (forall a, 0 <= a < 2 ^ 64 -> in_foot Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, bv_unsigned a < ll_rw_lo Lay -> M a = None -> M' a = None) ->
    (forall a, 0 <= a < 2 ^ 64 -> in_initc Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  ls_ok LSt g M'.

Record lib_iface_ok : Prop := LIOK {
  lio_call : lib_call_ok;
  lio_init : lib_statics_init;
  lio_frame : lib_statics_frame
}.
End LibIface.
