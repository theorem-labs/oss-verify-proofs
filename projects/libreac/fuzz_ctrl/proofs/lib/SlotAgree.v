From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Export AgreeLim AgreeRoom AgreeCap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Uniform.
Import ListNotations.
Local Open Scope Z_scope.

Section Agree.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition crealizes (c : config) (T : TSet) : Prop := realizes segs c T /\ cut_free segs c /\ uniform segs c.

Lemma crealizes_realizes : forall c T, crealizes c T -> realizes segs c T.
Proof. intros c T H. exact (proj1 H). Qed.

Lemma crealizes_cut_free : forall c T, crealizes c T -> cut_free segs c.
Proof. intros c T H. exact (proj1 (proj2 H)). Qed.

Lemma crealizes_uniform : forall c T, crealizes c T -> uniform segs c.
Proof. intros c T H. exact (proj2 (proj2 H)). Qed.

Lemma crealizes_intro : forall c T, realizes segs c T -> cut_free segs c -> uniform segs c -> crealizes c T.
Proof. intros c T H1 H2 H3. exact (conj H1 (conj H2 H3)). Qed.

Definition SRcf (c : config) (Q : config -> Prop) : Prop :=
  forall T, (forall c', Q c' -> crealizes c' T) -> crealizes c T.

Definition malloc_contract_cf : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_cf md b n ->
    SRcf (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret B API ALLOC_STACK L A regs mem md n b).

Definition free_contract_cf : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    res_ok_slots A b ->
    SRcf (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_free b n)).

Definition free_null_contract_cf : Prop :=
  forall regs mem md,
    YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 -> m_halted md = None -> m_vm_lazy md = [] ->
    SRcf (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).

Definition calloc_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
    ms_calloc B = Some pc ->
    res_ok_slots A b -> room_cf md b (m * n) ->
    SRcf (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n -> mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

Definition realloc_post_cf (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : sptr) (k n : Z) (old : list byte) (P : astate -> Prop) (c' : config) : Prop :=
  exists L' A' regs' mem' md' res,
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
    P A'.

Definition realloc_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    res_ok_slots A b -> room_cf md b n ->
    SRcf (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (realloc_post_cf L A regs mem md p k n old (fun A' => res_ok_slots A' (sb_realloc b k n))).

(* realloc (NULL, n) enters malloc's body with the caller's return address; the cut-free certificate needs that
   address to differ from malloc's entry. *)
Definition realloc_null_contract_cf (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    res_ok_slots A b -> room_cf md b n ->
    SRcf (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret B API REALLOC_STACK L A regs mem md n b).

Definition lib_contract_cg (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       crealizes c' (K l)) ->
    crealizes (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

End Agree.
