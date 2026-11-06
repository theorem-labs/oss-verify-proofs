From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO03.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import AllocSlots AllocRoom SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import SlotNeeds_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSlotPlan.
Import ListNotations.
Local Open Scope Z_scope.

(* Cut-free twins of the six allocator glue segments of GrantSlotPlan: SR becomes SRcf and the
   malloc room premise room_slots becomes room_cf, matching malloc_contract_cf / free_contract_cf. *)

(* The room of a slot allocation from the frame's budget law (vm_limit at least 2 ^ 34) through
   SlotAgree.room_cf_of_limit. CAP_AG < 1680 comes from CAP_AG_fits and CAP_AG_max, so the heap capacity
   stays below CAPMAX without the value of CAP_AG. *)
Lemma room_cf_of : forall (md : Model) (b : sbound) (n k : Z),
  0 <= k <= 2 -> sb_live b <= 64 + k -> 0 <= sb_bytes b <= 2 ^ 28 + 8670 + 460 ->
  128 <= sb_cap b <= CAP_AG -> 0 <= n <= 8670 -> 2 ^ 34 <= vm_limit (m_vmmaps md) ->
  room_cf md b n.
Proof.
  intros md b n k Hk Hl Hb Hc Hn Hv.
  assert (HC : CAP_AG < 1680).
  { destruct (Z_lt_le_dec CAP_AG 1680) as [H|H]; [exact H|].
    pose proof (LIVE_BOUND_mono 1680 CAP_AG (2 ^ 29) (2 ^ 29) ltac:(lia) ltac:(lia)).
    pose proof CAP_AG_fits. pose proof CAP_AG_max. lia. }
  apply room_cf_of_limit; [exact Hv | | lia | lia].
  apply room_slots_small; unfold CAPMAX; lia.
Qed.

Section SRcf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition malloc_glue_cf (x : slot_ctx) (Pre : machine_state -> Prop) (Live : layout -> astate -> Prop) (n : Z)
    (Post : Z -> machine_state -> Prop) : Prop :=
  forall s md L A b, glue_pre B API x Pre s md L A b -> Live L A -> room_cf md b n ->
  SRcf B (mkCfg s md) (fun c' =>
    exists s' md' L' A' r,
      c' = mkCfg s' md' /\ glue_post B API x (Post r) Live s' md' L' A' (sb_malloc b n) /\ live_blk L' A' r n /\
      call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md (fun _ => False) L' A' (ms_regs s')
        (ms_mem s') md' /\
      fresh_block B r n /\ r mod 16 = 0 /\
      (exists b1 b2, blocks L' A' = b1 ++ (r, n) :: b2 /\ blocks L A = b1 ++ b2) /\
      blocks_kept B L A (ms_mem s) (ms_mem s') (fun _ => False) /\ guard_kept B (ms_mem s) (ms_mem s') /\
      (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A'))).

Definition free_glue_cf (x : slot_ctx) (Pre : machine_state -> Prop) (Live : layout -> astate -> Prop) (s0 n : Z)
    (Post : machine_state -> Prop) : Prop :=
  forall s md L A b q, glue_pre B API x Pre s md L A b -> Live L A -> In (q, n) (user_blocks A) -> ptr_addr L q = s0 ->
  SRcf B (mkCfg s md) (fun c' =>
    exists s' md' L' A',
      c' = mkCfg s' md' /\ glue_post B API x Post Live s' md' L' A' (sb_free b n) /\
      call_post B (aa_MR API) L A (ms_regs s) (ms_mem s) md (fun a => s0 <= a < s0 + n) L' A' (ms_regs s')
        (ms_mem s') md' /\
      (exists b1 b2, blocks L A = b1 ++ (s0, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
      blocks_kept B L A (ms_mem s) (ms_mem s') (fun a => a = s0) /\ guard_kept B (ms_mem s) (ms_mem s') /\
      (forall q' k, In (q', k) (user_blocks A) -> q' <> q -> In (q', k) (user_blocks A'))).

Definition seg_mallocT_cf : Prop := forall x, alloc_ceiling + LLVM_STACK <= x_S x ->
  malloc_glue_cf x (At_mallocT x) no_live 460 (fun t => At_mallocT_ret x t).
Definition seg_mallocSW1_cf : Prop := forall x t, alloc_ceiling + LLVM_STACK <= x_S x ->
  malloc_glue_cf x (At_mallocSW1 x t) (fun L A => live_blk L A t 460) (sw1_size x) (fun s => At_mallocSW1_ret x t s).
Definition seg_mallocSW2_cf : Prop := forall x t, alloc_ceiling + LLVM_STACK <= x_S x ->
  malloc_glue_cf x (At_mallocSW2 x t) (fun L A => live_blk L A t 460) 4352 (fun s => At_mallocSW2_ret x t s).
Definition seg_freeSW1_cf : Prop := forall x t s, alloc_ceiling + LLVM_STACK <= x_S x ->
  free_glue_cf x (At_freeSW1 x t s) (fun L A => live_blk L A t 460) s (sw1_size x) (At_raw x t PC_FREE_SW1_RET).
Definition seg_freeSW2_cf : Prop := forall x t s, alloc_ceiling + LLVM_STACK <= x_S x ->
  free_glue_cf x (At_freeSW2 x t s) (fun L A => live_blk L A t 460) s 4352 (At_freeSW2_ret x t).
Definition seg_freeT_cf : Prop := forall x t, alloc_ceiling + LLVM_STACK <= x_S x ->
  free_glue_cf x (At_freeT x t) no_live t 460 (At_ret0 x).

End SRcf.
