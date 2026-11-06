From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Exec MState Mem Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Export MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Export AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require AllocPack.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lib_msteps_frame : forall segs ms final, Exec.msteps segs ms final -> YK0i.msteps segs ms final.
Proof.
  intros segs ms final H. induction H as [ms|ms mid final [HS HV] HT IH].
  - constructor.
  - econstructor; eassumption.
Qed.

Lemma evt_SR : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SR segs (mkCfg ms' md) P) -> SR segs (mkCfg ms md) P.
Proof.
  intros segs ms Q md P [final [Hs HQ]] Hh Hl K T HK.
  eapply YK15.rz_msteps; [exact Hh | exact Hl | apply lib_msteps_frame; exact Hs |].
  exact (K final HQ T HK).
Qed.

Lemma evt_SR_canon : forall segs ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt segs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR segs (mkCfg ms' md) P) ->
  SR segs (mkCfg ms md) P.
Proof.
  intros segs ms Q md P H Hh Hl K.
  exact (evt_SR segs ms _ md P (RegisterBridge.canonical_contract_transport segs Q ms H) Hh Hl K).
Qed.

Record ResForm := {
  rf_R : Type;
  rf_ok : astate -> rf_R -> Prop;
  rf_room : rf_R -> Z -> Prop;
  rf_malloc : rf_R -> Z -> rf_R;
  rf_free : rf_R -> Z -> rf_R;
  rf_realloc : rf_R -> Z -> Z -> rf_R
}.

Definition sb_form : ResForm := {|
  rf_R := sbound; rf_ok := res_ok_slots; rf_room := room_slots;
  rf_malloc := sb_malloc; rf_free := sb_free; rf_realloc := sb_realloc |}.

Definition pack_form : ResForm := {|
  rf_R := AllocPack.pbound; rf_ok := AllocPack.res_ok_pack; rf_room := AllocPack.room_pack;
  rf_malloc := AllocPack.pb_malloc; rf_free := AllocPack.pb_free; rf_realloc := AllocPack.pb_realloc |}.

Section Contracts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition guard_kept (mem mem' : word -> option byte) : Prop :=
  forall i, 0 <= i < 8 -> mbyte segs mem' (ms_got_guard B + i) = mbyte segs mem (ms_got_guard B + i).

Definition blocks_kept (L : layout) (A : astate) (mem mem' : word -> option byte) (gone : Z -> Prop) : Prop :=
  forall a k i, In (a, k) (blocks L A) -> ~ gone a -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i).

Definition fresh_block (res n : Z) : Prop :=
  4096 <= res /\ res + n <= alloc_ceiling /\ forall i, 0 <= i < n -> ~ in_img B (res + i).

Definition malloc_ret (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (n : Z) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 res /\
    res <> 0 /\ res mod 16 = 0 /\ fresh_block res n /\
    (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept L A mem mem' (fun _ => False) /\
    ro_agree segs mem' /\ guard_kept mem mem' /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (sb_malloc b n).

Definition malloc_contract : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_slots b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret ALLOC_STACK L A regs mem md n b).

Definition free_contract : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    res_ok_slots A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_free b n)).

Definition free_null_contract : Prop :=
  forall regs mem md,
    YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 -> m_halted md = None -> m_vm_lazy md = [] ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).

Definition realloc_contract (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    res_ok_slots A b -> room_slots b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + k) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block res n /\
         (exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (res, n) :: c2 /\
            c1 ++ c2 = b1 ++ b2) /\
         blocks_kept L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept mem mem' /\
         (forall q k', In (q, k') (user_blocks A) -> q <> p -> In (q, k') (user_blocks A')) /\
         (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_realloc b k n)).

Definition realloc_null_contract (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n ->
    res_ok_slots A b -> room_slots b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret REALLOC_STACK L A regs mem md n b).

Definition calloc_contract (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
    ms_calloc B = Some pc ->
    res_ok_slots A b -> room_slots b (m * n) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n -> mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

Section Forms.
Variable F : ResForm.

Definition malloc_ret_r (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (n : Z) (b : rf_R F) (c' : config) : Prop :=
  exists L' A' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 res /\
    res <> 0 /\ res mod 16 = 0 /\ fresh_block res n /\
    (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept L A mem mem' (fun _ => False) /\
    ro_agree segs mem' /\ guard_kept mem mem' /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    rf_ok F A' (rf_malloc F b n).

Definition malloc_contract_r : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    rf_ok F A b -> rf_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret_r ALLOC_STACK L A regs mem md n b).

Definition free_contract_r : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    rf_ok F A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rf_ok F A' (rf_free F b n)).

Definition realloc_contract_r (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    rf_ok F A b -> rf_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + k) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block res n /\
         (exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (res, n) :: c2 /\
            c1 ++ c2 = b1 ++ b2) /\
         blocks_kept L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept mem mem' /\
         (forall q k', In (q, k') (user_blocks A) -> q <> p -> In (q, k') (user_blocks A')) /\
         (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rf_ok F A' (rf_realloc F b k n)).

Definition realloc_null_contract_r (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n ->
    rf_ok F A b -> rf_room F b n ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret_r REALLOC_STACK L A regs mem md n b).

Definition calloc_contract_r (pc : Z) : Prop :=
  forall L A regs mem md m n b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n -> 0 <= m -> 0 <= n -> m * n < 4096 ->
    ms_calloc B = Some pc ->
    rf_ok F A b -> rf_room F b (m * n) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret_r CALLOC_STACK L A regs mem md (m * n) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < m * n -> mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).

End Forms.

Lemma malloc_contract_sb : malloc_contract_r sb_form <-> malloc_contract.
Proof. reflexivity. Qed.
Lemma free_contract_sb : free_contract_r sb_form <-> free_contract.
Proof. reflexivity. Qed.
Lemma realloc_contract_sb : forall pc, realloc_contract_r sb_form pc <-> realloc_contract pc.
Proof. reflexivity. Qed.
Lemma realloc_null_contract_sb : forall pc, realloc_null_contract_r sb_form pc <-> realloc_null_contract pc.
Proof. reflexivity. Qed.
Lemma calloc_contract_sb : forall pc, calloc_contract_r sb_form pc <-> calloc_contract pc.
Proof. reflexivity. Qed.

Definition block_slack_present : Prop :=
  forall L A mem md p n a,
    MR L A mem md -> In (p, n) (blocks L A) -> p + n <= a < 8 * ((p + n + 7) / 8) -> present mem a.

Definition ctx_owned : Prop :=
  forall L A mem md a, MR L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE -> owned B L A a.

Definition blocks_low : Prop :=
  forall L A mem md p n, MR L A mem md -> In (p, n) (blocks L A) -> 4096 <= p.

Definition blocks_nodup : Prop :=
  forall L A mem md, MR L A mem md -> NoDup (map fst (blocks L A)).

Definition libc_no_locks : Prop :=
  forall L A mem md, MR L A mem md -> mbyte segs mem (ms_libc B + 3) = Some (Z_to_bv 8 0).

Definition blocks_writable : Prop :=
  forall L A mem md p n i, MR L A mem md -> In (p, n) (blocks L A) -> 0 <= i < n -> writable_at segs mem (p + i).

Definition errno_unowned : Prop :=
  forall L A mem md a, MR L A mem md -> errno_addr B <= a < errno_addr B + 4 -> ~ owned B L A a.

Definition guard_rw : Prop :=
  forall L A mem md i, MR L A mem md -> 0 <= i < 8 ->
    writable_at segs mem (ms_got_guard B + i) /\ writable_at segs mem (ms_guard B + i).

Definition call_pre_t (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) : Prop :=
  call_pre_k B MR stk L A regs mem md /\ spZ regs <= TASK_SIZE.

Definition in_globals (G : list (Z * Z)) (a : Z) : Prop :=
  exists lo len, In (lo, len) G /\ lo <= a < lo + len.

Definition G_local_c (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) : Prop :=
  forall j m m', (forall a, in_globals G a -> mbyte segs m' a = mbyte segs m a) -> GI j m -> GI j m'.

Definition G_img_c (G : list (Z * Z)) (mem : word -> option byte) : Prop :=
  forall a, in_globals G a -> mbyte segs mem a = seg_rom segs (Z_to_bv 64 a).

Definition lib_post_g (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
  getr regs' 10 = Z_to_bv 64 0 /\
  regs_preserved regs regs' /\
  (exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
  (forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_globals G a -> writable_at segs mem a <-> writable_at segs mem' a) /\
  (forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
  ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  sink_none B mem' md' /\
  ro_agree segs mem' /\
  res_ok_slots A' (lib_delta n b) /\
  (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).

Definition lib_contract_body (RZ : list Segment -> config -> TSet -> Prop)
    (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    GI j mem ->
    G_img_c R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_g G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       RZ segs c' (K l)) ->
    RZ segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Definition lib_contract_g (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  lib_contract_body (fun s c T => @realizes s AcfgMode c T) G R GI j pc ra empty stk.

End Contracts.

Definition lib_contract_gm {AM : AllocMode} {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}
    (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
    (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (j : nat) (pc ra empty stk : Z) : Prop :=
  @lib_contract_body fx rc LS B API SH SK (fun s c T => @realizes s AM c T) G R GI j pc ra empty stk.

Lemma lib_contract_g_gm : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}
    (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms} G R GI j pc ra empty stk,
  @lib_contract_g fx rc LS B API SH SK G R GI j pc ra empty stk =
  @lib_contract_gm AcfgMode fx rc LS B API SH SK G R GI j pc ra empty stk.
Proof. reflexivity. Qed.
