(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module paths and module names changed; 109 of its 133 lines of code are new or changed and 132 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import
  YK15 YM06 YO0j YO0m YO03 YO0f YO0g YO0x YK0i YK0o YK0s YK0h YK14 YK1b YK1a YK1i YK0n YP0n YP0m YP02 YN3f
  YO0p YO0l YO0n YO0k YO0o YL01 YL00
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YP09 YH00 YH02 YI06 YI14 YI16 YL0g YL0i YL0k YL0s YN03 YN2b YN33 YM0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT SlotKept SlotPack AllocPack
  AllocPack3 SlotPack3 AllocPackGSF SlotAgree AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section CFT.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Variable F : ResFormT.

Definition malloc_contract_rt : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    rt_ok F A b -> rt_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret_rt B API F ALLOC_STACK L A regs mem md n b).

Definition free_contract_rt : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    rt_ok F A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rt_ok F A' (rt_free F b n p)).

Definition realloc_contract_rt (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    rt_ok F A b -> rt_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + k) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
         (exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (res, n) :: c2 /\
            c1 ++ c2 = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k', In (q, k') (user_blocks A) -> q <> p -> In (q, k') (user_blocks A')) /\
         (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         exists q, In (q, n) (user_blocks A') /\ ptr_addr L' q = res /\ rt_ok F A' (rt_realloc F b k n p q)).

Definition realloc_null_contract_rt (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    rt_ok F A b -> rt_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret_rt B API F REALLOC_STACK L A regs mem md n b).

Definition calloc_contract_rt (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
    ms_calloc B = Some pc ->
    rt_ok F A b -> rt_room F b (m * n) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret_rt B API F CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n -> mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

End CFT.

Definition frame_allocator {rc : RunCeil} {fx : FPState} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  malloc_contract_rt B API pack3_ag_formT /\ free_contract_rt B API pack3_ag_formT /\ free_null_contract B /\
  (forall pc, ms_realloc B = Some pc ->
     realloc_contract_rt B API pack3_ag_formT pc /\ realloc_null_contract_rt B API pack3_ag_formT pc) /\
  (forall pc, ms_calloc B = Some pc -> calloc_contract_rt B API pack3_ag_formT pc) /\
  block_slack_present B API /\ ctx_owned B API /\ blocks_low B API /\ blocks_nodup B API /\ blocks_writable B API /\ errno_unowned B API /\
  guard_rw B API /\
  AllocExtra B (aa_MR API) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a) /\
  (forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_RELRO a -> ~ owned B L A a).

Section AgreeP3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.

Definition lib_post_cgp3 (cs MC : list Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : pbound3) (l : lleaf) (T T' : list (Z * Z))
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  lib_post_p3 B API cs MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\ GSF A'.

Definition lib_contract_cgp3 (CS : list byte -> list Z) (MC : list Z) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b T (K : lleaf -> TSet),
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    res_ok_pack3 A b /\ GSF A ->
    pack3_entry CS MC pl T b ->
    p3_mis b = [] ->
    GI j T mem ->
    tb_live L A T ->
    (0 < n -> ~ In (p, n) T) ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md' T',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_cgp3 (CS pl) MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\
          GI (S j) T' mem') ->
       crealizes B c' (K l)) ->
    crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

End AgreeP3.

Lemma ra_ne_malloc (B : malloc_syms) (regs : bvmap 5 word) (ra mpc : Z) :
  getr regs 1 = Z_to_bv 64 ra -> ms_malloc B = mpc ->
  Z.eqb (bv_unsigned (Z_to_bv 64 ra)) (bv_unsigned (Z_to_bv 64 mpc)) = false ->
  getr regs 1 <> Z_to_bv 64 (ms_malloc B).
Proof. intros E M N Hc. rewrite E, M in Hc. rewrite Hc, Z.eqb_refl in N. discriminate. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
