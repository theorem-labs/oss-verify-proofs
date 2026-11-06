From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require YO03.
Import ListNotations.
Local Open Scope Z_scope.

Definition NONHEAP_CF : Z := 2 ^ 31.
Definition CAP_AG : Z := 1024.
Lemma CAP_AG_fits : LIVE_BOUND CAP_AG (2 ^ 29) + NONHEAP_CF <= 2 ^ 34.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma CAP_AG_max : 2 ^ 34 < LIVE_BOUND 1680 (2 ^ 29) + NONHEAP_CF.
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

Section Agree.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition crealizes (c : config) (T : TSet) : Prop := realizes segs c T /\ cut_free segs c.

Definition SRcf (c : config) (Q : config -> Prop) : Prop :=
  forall T, (forall c', Q c' -> crealizes c' T) -> crealizes c T.

Definition room_cf (md : Model) (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ LIVE_BOUND (sb_cap b) (sb_bytes b + n) + NONHEAP_CF <= vm_limit (m_vmmaps md).

Lemma LIVE_BOUND_mono : forall c c' y y', 0 <= c <= c' -> y <= y' -> LIVE_BOUND c y <= LIVE_BOUND c' y'.
Proof.
  intros c c' y y' Hc Hy. unfold LIVE_BOUND, AREA_BOUND, P2, NA, HCAP.
  assert (D : (13 * c + 48) / METAS_PER_AREA <= (13 * c' + 48) / METAS_PER_AREA)
    by (apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | lia]).
  unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable.YO03.MMAX, PGSZ in *. nia.
Qed.

Lemma room_cf_of_limit : forall md b n, 2 ^ 34 <= vm_limit (m_vmmaps md) -> room_slots b n ->
  0 <= sb_cap b <= CAP_AG -> sb_bytes b + n <= 2 ^ 29 -> room_cf md b n.
Proof.
  intros md b n Hl Hr Hc Hb. split; [exact Hr|].
  pose proof (LIVE_BOUND_mono (sb_cap b) CAP_AG (sb_bytes b + n) (2 ^ 29) Hc Hb). pose proof CAP_AG_fits. lia.
Qed.

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
