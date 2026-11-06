(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record lib_layoutA : Type := LLA {
  lla_L      : asan_layout;      (* [comment removed for export] *)
  lla_entry  : Z;                (* [comment removed for export] *)
  lla_gp     : Z;                (* [comment removed for export] *)
  lla_empty  : Z;                (* [comment removed for export] *)
  lla_initc  : list (Z * Z);     (* [comment removed for export] *)
  lla_init_img : list (Z * Z);   (* [comment removed for export] *)
  lla_td_self : Z; lla_td_tid : Z; lla_td_locale : Z; lla_locale : Z; lla_td_canary : Z; lla_guard : Z; lla_auxvp : Z;
  lla_phdr : Z; lla_phent : Z; lla_phnum : Z;
  lla_rw_lo  : Z;                (* [comment removed for export] *)
  lla_stack  : Z;                (* [comment removed for export] *)
  lla_frames : Z -> Z;           (* [comment removed for export] *)
  lla_leak   : Z -> Z;           (* [comment removed for export] *)
  lla_credit : Z -> credit;      (* [comment removed for export] *)
  lla_foot   : list (Z * Z);     (* [comment removed for export] *)
  lla_junk   : list (Z * Z);     (* [comment removed for export] *)
  lla_init_cells : list (Z * Z * Z)   (* [comment removed for export] *)
}.
Definition in_junk (Lay : lib_layoutA) (a : Z) : Prop := exists iv, In iv (lla_junk Lay) /\ fst iv <= a < snd iv.

(* [comment removed for export] *)
Definition heap_view (L : asan_layout) (ar : asan_run) : heap_layout :=
  {| HeapIface.hl_segs := hl_segs L; HeapIface.hl_malloc := hl_malloc L; HeapIface.hl_free := hl_free L;
     HeapIface.hl_aligned_alloc := hl_aligned_alloc L; HeapIface.hl_tp := hl_tp L; hl_errno := 0;
     HeapIface.hl_img_lo := hl_img_lo L; HeapIface.hl_img_hi := hl_img_hi L; hl_alloc_static := fun _ => False; hl_alloc_ro := fun _ => False;
     hl_stack := 0; hl_sptop := ar_sptop ar; HeapIface.hl_k_per_malloc := hl_k_per_malloc L; HeapIface.hl_b_overhead := hl_b_overhead L;
     HeapIface.hl_K0 := HeapIfaceA.hl_K0 L; HeapIface.hl_B0 := HeapIfaceA.hl_B0 L |}.
Definition lib_view (Lay : lib_layoutA) (ar : asan_run) : lib_layout :=
  {| ll_heap := heap_view (lla_L Lay) ar; ll_entry := lla_entry Lay; ll_gp := lla_gp Lay; ll_empty := lla_empty Lay; ll_initc := lla_initc Lay;
     ll_init_img := lla_init_img Lay; ll_td_self := lla_td_self Lay; ll_td_tid := lla_td_tid Lay; ll_td_locale := lla_td_locale Lay;
     ll_locale := lla_locale Lay; ll_td_canary := lla_td_canary Lay; ll_guard := lla_guard Lay; ll_auxvp := lla_auxvp Lay;
     ll_phdr := lla_phdr Lay; ll_phent := lla_phent Lay; ll_phnum := lla_phnum Lay; ll_rw_lo := lla_rw_lo Lay; ll_stack := lla_stack Lay;
     ll_credit := lla_credit Lay; ll_foot := lla_foot Lay; ll_init_cells := [] |}.   (* [comment removed for export] *)

Section LibIfaceA.
Variable Lay : lib_layoutA.
Variable ar : asan_run.
Let L := lla_L Lay.
Let LV := lib_view Lay ar.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.
Variable LSt : lib_statics.

Record lib_preA (g : ls_state LSt) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (sp ptr ra : Z) (payload : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := LIB_PREA {
  lpa_ra : getr R 1%bv = Z_to_bv 64 ra;
  lpa_ra_ok : 0 <= ra < 2 ^ 47 /\ ra mod 2 = 0;
  lpa_sp : getr R 2%bv = Z_to_bv 64 sp;
  lpa_gp : getr R 3%bv = Z_to_bv 64 (lla_gp Lay);
  lpa_tp : getr R 4%bv = Z_to_bv 64 (hl_tp L);
  lpa_a0 : getr R 10%bv = Z_to_bv 64 ptr;
  lpa_a1 : getr R 11%bv = Z_to_bv 64 (Z.of_nat (length payload));
  lpa_len : Z.of_nat (length payload) < 2 ^ 26;
  lpa_ptr : (length payload = 0%nat /\ ptr = lla_empty Lay)
            \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB);
  lpa_payload : rdn (hl_segs L) M (Z_to_bv 64 ptr) (length payload) = Some payload;
  (* [comment removed for export] *)
  lpa_stack : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + lla_stack Lay <= sp /\ sp <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47
              /\ defined M (sp - lla_stack Lay) (lla_stack Lay) /\ defined M sp (ar_stack_top ar - sp);
  lpa_credit : credit_le (lla_credit Lay (Z.of_nat (length payload))) cr;
  (* [comment removed for export] *)
  lpa_ffroom : forall k, In k [0; 1; 2; 3; 4] -> Z.of_nat (ff_count k (FF ++ LK)) + lla_frames Lay k <= ff_cap k;      (* [comment removed for export] *)
  lpa_ffrs : forall f, In f FF -> sp + 32 <= ff_rs f;
  (* [comment removed for export] *)
  lpa_stksh : shadow_zero M (sp - lla_stack Lay) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - lla_stack Lay)) / 8);
  lpa_statics : ls_ok LSt g M
}.

Record lib_postA (g' : ls_state LSt) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (sp : Z) (payload : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) (cr' : credit) : Prop := LIB_POSTA {
  lqa_a0 : getr R 10%bv = Z_to_bv 64 0;
  lqa_regs : regs_preserved R0 R;
  lqa_credit : credit_le (credit_sub cr (lla_credit Lay (Z.of_nat (length payload)))) cr';
  (* [comment removed for export] *)
  lqa_frame : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (lla_stack Lay) a -> ~ in_foot LV a -> ~ in_junk Lay a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);      (* [comment removed for export] *)
  lqa_scratch : defined M (sp - lla_stack Lay) (lla_stack Lay);
  lqa_grows : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (lla_stack Lay) a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None;
  lqa_stksh : shadow_zero M (sp - lla_stack Lay) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - lla_stack Lay)) / 8);     (* [comment removed for export] *)
  lqa_statics : ls_ok LSt g' M
}.

Definition lib_cfgA {fx : FPState} (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition lib_call_okA : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (sp ptr ra : Z) (payload : list byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_preA g LB FF LK cr sp ptr ra payload R M ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        lib_postA g' LB FF cr sp payload R M R' M' cr' ->
        model_rt model model' -> incl A A' -> m_halted model' = None -> MInv A' model' ->
        (forall k, In k [0; 1; 2; 3; 4] -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->      (* [comment removed for export] *)
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (@lib_cfgA fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfgA fx R (Z_to_bv 64 (lla_entry Lay)) M model) K.

(* [comment removed for export] *)
Definition lib_init_factsA (av uid rnd tid canary hw : Z) (M : word -> option byte) : Prop :=
  lib_init_facts LV av uid rnd tid canary hw M
  /\ Forall (fun c => cellz (hl_segs L) M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (lla_init_cells Lay).
Definition lib_statics_initA : Prop :=
  forall av uid rnd tid canary hw M, lib_init_factsA av uid rnd tid canary hw M -> ls_ok LSt (ls_g0 LSt) M.
Definition lib_statics_frameA : Prop := lib_statics_frame LV LSt.

Record lib_iface_okA : Prop := LIOKA {
  lioa_call : lib_call_okA;
  lioa_init : lib_statics_initA;
  lioa_frame : lib_statics_frameA
}.
End LibIfaceA.
