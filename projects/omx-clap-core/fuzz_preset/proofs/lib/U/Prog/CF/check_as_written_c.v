From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes ex_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require LedgerCells fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 ubsan twin unstripped/fuzz_preset/fuzz_preset.ubsan (sha256 27566683952ebd54...)
   of the pin 45b0357d18ff66cd...:
     check_as_written FUNC LOCAL 0x13ad4 size 280: addi sp, sp, -0x50 (the old one, 0x13b28, had 64); the pointer-overflow
     traps on data + size; expected inlined (malloc of size + 1, ex_value, jal ex_ws, free); then out_of_memory()
     inlined: lbu g_own_ran_out (0x35250), jal fuzz_alloc_ran_out (0x15f90);
     a0 = 1 when either is nonzero (fuzz_preset.c new:574-575), else the two abort checks and a0 = 0 (new:581-589).
   The only static store, g_own_ran_out = 1, is on the arm where expected's malloc returns NULL (new:362-366); rf_room
   excludes that arm, so the write set stays the frame. *)
Definition CHECK_AS_WRITTEN : Z := 0x13ad4.
Definition CAW_F : Z := 80.
Definition CAW_K : Z := CAW_F + ex_value_K 0.

Definition caw_agree (rcv : Z) (x : list byte) (t : jv) : Prop :=
  rcv = 0 /\ json_read jr_strtod (zb x) = Some t \/
  rcv <> 0 /\ json_read jr_strtod (zb x) = None.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition caw_inside (L : layout) (A : astate) (a n : Z) : Prop :=
  exists p k, In (p, k) (blocks L A) /\ p <= a /\ a + n <= p + k.

(* The return value, from out_of_memory(): g_own_ran_out (go) and g_ran_out (gr), one byte each, are the same bytes on
   entry and on return; a0 = 1 when either is nonzero (memory ran out, and the call ends), a0 = 0 when both are 0. *)
Definition caw_ran_out (mem mem' : word -> option byte) (r : word) : Prop :=
  exists go gr : Z, 0 <= go < 2 ^ 8 /\ 0 <= gr < 2 ^ 8 /\
    Mem.bytes_at segs mem LedgerCells.GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 go)) /\
    Mem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 gr)) /\
    Mem.bytes_at segs mem' LedgerCells.GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 go)) /\
    Mem.bytes_at segs mem' fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 gr)) /\
    (go = 0 /\ gr = 0 /\ r = Z_to_bv 64 0 \/ (go <> 0 \/ gr <> 0) /\ r = Z_to_bv 64 1).

Definition check_as_written_contract : Prop :=
  forall L A regs mem md (data rcv doc : Z) (x : list byte) (lblk : Z -> Z -> Prop) (t : jv)
         (D : list (Z * Z)) (b : rf_R F),
    reader_env B API CAW_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
    getr regs 12 = Z_to_bv 64 rcv -> getr regs 13 = Z_to_bv 64 doc ->
    0 <= rcv < 2 ^ 64 -> 0 <= doc < 2 ^ 64 ->
    Z.of_nat (length x) <= 3 * 2 ^ 20 -> 0 < data -> data + Z.of_nat (length x) < 2 ^ 62 ->
    Mem.bytes_at segs mem data x -> (x <> [] -> caw_inside L A data (Z.of_nat (length x))) ->
    (rcv = 0 -> pj_node segs mem lblk doc t D /\ spZ regs <= doc /\ doc + 56 <= 2 ^ 47 /\
       Forall (fun ak => caw_inside L A (fst ak) (snd ak) /\ fst ak mod 8 = 0) D) ->
    caw_agree rcv x t ->
    rf_ok F A b -> rf_room F b (Z.of_nat (length x) + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rpost B API CAW_K L A regs mem md (fun _ => False) (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\ st_init_done A' = true /\
         blocks L' A' = blocks L A /\
         Mem.bytes_at segs mem' data x /\
         rf_ok F A' (rf_free F (rf_malloc F b (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1)) /\
         caw_ran_out mem mem' (getr regs' 10)).

(* The caller's form (the entry calls check_as_written only after out_of_memory() read both bytes as 0): with both
   bytes 0 on entry, a0 = 0 and both bytes are still 0. *)
Definition check_as_written_contract_z : Prop :=
  forall L A regs mem md (data rcv doc : Z) (x : list byte) (lblk : Z -> Z -> Prop) (t : jv)
         (D : list (Z * Z)) (b : rf_R F),
    reader_env B API CAW_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
    getr regs 12 = Z_to_bv 64 rcv -> getr regs 13 = Z_to_bv 64 doc ->
    0 <= rcv < 2 ^ 64 -> 0 <= doc < 2 ^ 64 ->
    Z.of_nat (length x) <= 3 * 2 ^ 20 -> 0 < data -> data + Z.of_nat (length x) < 2 ^ 62 ->
    Mem.bytes_at segs mem data x -> (x <> [] -> caw_inside L A data (Z.of_nat (length x))) ->
    (rcv = 0 -> pj_node segs mem lblk doc t D /\ spZ regs <= doc /\ doc + 56 <= 2 ^ 47 /\
       Forall (fun ak => caw_inside L A (fst ak) (snd ak) /\ fst ak mod 8 = 0) D) ->
    caw_agree rcv x t ->
    rf_ok F A b -> rf_room F b (Z.of_nat (length x) + 1) ->
    Mem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    Mem.bytes_at segs mem LedgerCells.GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rpost B API CAW_K L A regs mem md (fun _ => False) (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\ st_init_done A' = true /\
         blocks L' A' = blocks L A /\
         Mem.bytes_at segs mem' data x /\
         rf_ok F A' (rf_free F (rf_malloc F b (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1)) /\
         getr regs' 10 = Z_to_bv 64 0 /\
         Mem.bytes_at segs mem' fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
         Mem.bytes_at segs mem' LedgerCells.GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0))).

Lemma caw_le1_inj : forall (m : word -> option byte) a u v, 0 <= u < 2 ^ 8 -> 0 <= v < 2 ^ 8 ->
  Mem.bytes_at segs m a (Mem.le1 (Z_to_bv 64 u)) -> Mem.bytes_at segs m a (Mem.le1 (Z_to_bv 64 v)) -> u = v.
Proof.
  intros m a u v Hu Hv (_ & _ & Eu) (_ & _ & Ev).
  pose proof (Eu 0%nat ltac:(rewrite Mem.length_le1; lia)) as E1.
  rewrite (Ev 0%nat ltac:(rewrite Mem.length_le1; lia)) in E1.
  unfold Mem.le1 in E1. cbn [Z_to_le_bytes nth_error] in E1.
  assert (E2 : bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v))) =
               bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 u)))) by congruence.
  rewrite !Z_to_bv_unsigned in E2. unfold bv_wrap, bv_modulus in E2.
  rewrite !(Z.mod_small u), !(Z.mod_small v) in E2 by (cbn; lia). lia.
Qed.

Lemma check_as_written_z : check_as_written_contract -> check_as_written_contract_z.
Proof.
  intros H. unfold check_as_written_contract_z.
  intros L A regs mem md data rcv doc x lblk t D b ENV R10 R11 R12 R13 Hrcv Hdoc Hlen Hd0 Hd1 HDB HDI HDOC HAG
    HRES HROOM HGR HGO.
  eapply SR_mono; [exact (H L A regs mem md data rcv doc x lblk t D b ENV R10 R11 R12 R13 Hrcv Hdoc Hlen Hd0 Hd1
    HDB HDI HDOC HAG HRES HROOM)|].
  intros c' (fx' & L' & A' & regs' & mem' & md' & E & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & RO).
  destruct RO as (go & gr & Hgo & Hgr & BO & BR & BO' & BR' & ARM).
  assert (Ego : go = 0) by (symmetry; exact (caw_le1_inj mem _ 0 go ltac:(lia) Hgo HGO BO)).
  assert (Egr : gr = 0) by (symmetry; exact (caw_le1_inj mem _ 0 gr ltac:(lia) Hgr HGR BR)).
  subst go gr.
  exists fx', L', A', regs', mem', md'.
  split; [exact E|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [destruct ARM as [(_ & _ & Er) | ([Hn | Hn] & _)]; [exact Er | lia | lia]|].
  split; [exact BR' | exact BO'].
Qed.

End K.
