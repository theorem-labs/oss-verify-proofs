From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_ran_out_c parse_noting_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 twin pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain (sha256
   c8f4d6b8e567b0b1...), the unstripped twin of the pinned fuzz_preset.plain 805604bb0907ae1b... (facts 8f3e7e1a07f1):
     check_no_overread FUNC LOCAL 0x13778 size 652: addi sp, sp, -0xf0; s0..s7 and ra saved at sp + 0xa8 .. sp + 0xe8;
     three padded copies inlined (malloc (n + 16), and when it is not NULL memcpy and a 16-byte memset; a NULL stores
     1 into g_own_ran_out (one byte, LedgerCells.GL_OWN_RAN_OUT, s7 - 0x18 with s7 = 0x347b8)); the three trees at
     sp + 0x70, sp + 0x38, sp zeroed by memset; three parse_noting calls (0x138b4, 0x13924, 0x13950), each behind
     out_of_memory() = lbu g_own_ran_out, then fuzz_alloc_ran_out; ran_out = out_of_memory() again (0x13958 .. 0x13964);
     the comparison only when it is 0; three pj_free, three free; a0 = s5 = ran_out (fuzz_preset.c #102 lines 524-558).
   The function returns 1 when memory ran out and 0 otherwise.  The ran-out arm needs g_own_ran_out or g_ran_out to be
   1 at one of the four out_of_memory() tests.  Both are 0 at the entry (the two premises the caller gives: the entry
   stores 0 into both just before the call), and under cno_room no malloc of the copies and no allocation of the
   readings is refused (malloc_contract_r, parse_noting_contract), so nothing sets either: only the normal arm runs,
   with a0 = 0 and both bytes still 0 at the return.  The same three copies, three readings and three frees happen as
   in the old harness, so cno_room, cno_mid and cno_free3 are unchanged. *)
Definition CHECK_NO_OVERREAD : Z := 0x13778.
Definition CNO_F : Z := 240.
Definition CNO_K : Z := CNO_F + PN_K.

Definition cno_writes (a : Z) : Prop := alloc_statics a \/ G_RAN_OUT <= a < G_RAN_OUT + 1.

Definition cno_tr (x : list byte) : list ev := snd (jr_run jr_strtod (zb x) []).

Definition cno_ok (x : list byte) : bool :=
  match json_read jr_strtod (zb x) with Some _ => true | None => false end.

Definition cno_dl (T : list ev) (E : list (Z * Z)) : Prop :=
  Permutation (map snd E) (map Z.of_nat (lsz T)) /\ Z.of_nat (length E) = nlive T.

Section R.
Variable F : ResForm.

Definition cno_b3 (b : rf_R F) (n : Z) : rf_R F :=
  rf_malloc F (rf_malloc F (rf_malloc F b (n + 16)) (n + 16)) (n + 16).

Definition cno_free3 (b : rf_R F) (n : Z) : rf_R F :=
  rf_free F (rf_free F (rf_free F b (n + 16)) (n + 16)) (n + 16).

Definition cno_mid (b : rf_R F) (n : Z) (T : list ev) (ok : bool) (E1 E2 E3 : list (Z * Z)) : rf_R F :=
  if ok then
    rf_frees F (rf_frees F (rf_frees F (rf_run F (rf_run F (rf_run F (cno_b3 b n) T) T) T) E1) E2) E3
  else
    rf_frees F (rf_run F (rf_frees F (rf_run F (rf_frees F (rf_run F (cno_b3 b n) T) E1) T) E2) T) E3.

Definition cno_room (b : rf_R F) (n : Z) (T : list ev) (ok : bool) : Prop :=
  rf_room F b (n + 16) /\ rf_room F (rf_malloc F b (n + 16)) (n + 16) /\
  rf_room F (rf_malloc F (rf_malloc F b (n + 16)) (n + 16)) (n + 16) /\
  room_run F (cno_b3 b n) T /\
  if ok then
    room_run F (rf_run F (cno_b3 b n) T) T /\ room_run F (rf_run F (rf_run F (cno_b3 b n) T) T) T
  else
    forall E1, cno_dl T E1 ->
      room_run F (rf_frees F (rf_run F (cno_b3 b n) T) E1) T /\
      forall E2, cno_dl T E2 ->
        room_run F (rf_frees F (rf_run F (rf_frees F (rf_run F (cno_b3 b n) T) E1) T) E2) T.

End R.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition check_no_overread_contract : Prop :=
  forall L A regs mem md Lam peak cnt b (data : Z) (x : list byte),
    reader_env B API CNO_K L A regs mem md ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt < 2 ^ 62 - 2 ^ 30 ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
    Z.of_nat (length x) <= 0x300000 ->
    Mem.bytes_at segs mem data x ->
    (x <> [] -> exists a k, In (a, k) (blocks L A) /\ a <= data /\ data + Z.of_nat (length x) <= a + k) ->
    rf_ok F A b -> cno_room F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x) ->
    Mem.bytes_at segs mem G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' peak' E1 E2 E3,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         rpost B API CNO_K L A regs mem md cno_writes (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\ st_init_done A' = true /\
         ledger B L' A' mem' Lam peak' (cnt + 3 * Z.of_nat (ncalls jr_strtod (zb x))) (2 ^ 64 - 1) /\
         peak <= peak' /\
         Mem.bytes_at segs mem' data x /\
         Mem.bytes_at segs mem' G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
         cno_dl (cno_tr x) E1 /\ cno_dl (cno_tr x) E2 /\ cno_dl (cno_tr x) E3 /\
         rf_ok F A' (cno_free3 F (cno_mid F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x) E1 E2 E3)
                       (Z.of_nat (length x))) /\
         getr regs' 10 = Z_to_bv 64 0 /\
         Mem.bytes_at segs mem' G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
         Mem.bytes_at segs mem' GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0))).

End K.
