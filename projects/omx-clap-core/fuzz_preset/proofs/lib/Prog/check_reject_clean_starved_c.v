From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue WriterRet pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require fuzz_alloc_ran_out_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 twin pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain (sha256
   c8f4d6b8e567b0b1...), the unstripped twin of the pinned fuzz_preset.plain 805604bb0907ae1b... (facts 8f3e7e1a07f1):
     check_reject_clean_starved FUNC LOCAL 0x13c08 size 592; frame 112 (addi sp, sp, -0x70), saves ra and s0-s5;
     g_own_ran_out OBJECT LOCAL 0x347a0 size 1 (LedgerCells.GL_OWN_RAN_OUT), read by `lbu a0, -0x510(s5)` after
     `auipc s5, 0x21` at 0x13cb0; g_ran_out 0x347a8 size 1 (fuzz_alloc_ran_out_c.G_RAN_OUT), read by fuzz_alloc_ran_out.
   Source (fuzz_preset.c of #102, lines 611-665): the body of the old function, with four more ways to end the call when
   out_of_memory() (g_own_ran_out || fuzz_alloc_ran_out()) holds: before the first write (`!doc || out_of_memory()`),
   after each full write (`count == before || out_of_memory()`), and after each starved write (`fuzz_free(text);
   return;`).  The caller hands in both flags 0 (its two call sites run behind an out_of_memory() test, after the entry
   set g_own_ran_out = 0 and called fuzz_alloc_ran_out_reset).  Under the rooms of this contract every allocation succeeds
   or is the one fuzz_alloc_fail chose, so no call in the body sets either flag: each out_of_memory() test reads 0 and
   the call runs on as the old one did.  So the post is the old post; the write set stays alloc_statics and the frame. *)
Definition CRCS : Z := 0x13c08.
Definition CRCS_F : Z := 112.
Definition CRCS_K (KW : Z) : Z := CRCS_F + Z.max PJ_PARSE_K (Z.max KW (Z.max FREE_K 16)).

Fixpoint djb2 (h : Z) (x : list Z) : Z :=
  match x with
  | [] => h
  | c :: r => djb2 ((33 * h + c) mod 2 ^ 64) r
  end.

Definition pick (x : list Z) (n : Z) : Z := if n =? 0 then 0 else djb2 5381 x mod n.

Definition wcalls (t : jv) (p : bool) : list Z := grow_calls 0 0 (piece_lens (wdpieces t p)).

Definition wN (t : jv) (p : bool) : Z := Z.of_nat (length (wcalls t p)).

Definition crcs_growth (x : list Z) (took doc : Z) (t : jv) : Z :=
  (if took =? 0 then 0 else pick x took + 1) +
  (if doc =? 0 then 0
   else wN t true + pick x (wN t true) + 1 + wN t false + pick x (wN t false) + 1).

Definition FMAX : Z := 2 ^ 64 - 1.

Section R.
Variable F : ResForm.

Definition wfull (b : rf_R F) (c : Z) (t : jv) (p : bool) : rf_R F :=
  rf_free F (wfold F b (w0 c FMAX) (wdpieces t p)) (w_cap (putN (w0 c FMAX) (wdpieces t p)) + 16).

Definition wstarve (b : rf_R F) (c f : Z) (t : jv) (p : bool) : rf_R F :=
  let st := putN (w0 c f) (wdpieces t p) in
  if w_cap st =? 0 then wfold F b (w0 c f) (wdpieces t p)
  else rf_free F (wfold F b (w0 c f) (wdpieces t p)) (w_cap st + 16).

Definition crs_pass_rooms (b : rf_R F) (c : Z) (x : list Z) (t : jv) (p : bool) : Prop :=
  wr_rooms F b (w0 c FMAX) (wdpieces t p) /\
  wr_rooms F (wfull b c t p) (w0 (c + wN t p) (c + wN t p + pick x (wN t p))) (wdpieces t p).

Definition crs_pass_fold (b : rf_R F) (c : Z) (x : list Z) (t : jv) (p : bool) : rf_R F :=
  wstarve (wfull b c t p) (c + wN t p) (c + wN t p + pick x (wN t p)) t p.

Definition crs_pass_cnt (c : Z) (x : list Z) (t : jv) (p : bool) : Z := c + wN t p + pick x (wN t p) + 1.

Definition crs_doc_rooms (b : rf_R F) (c : Z) (x : list Z) (t : jv) : Prop :=
  crs_pass_rooms b c x t true /\
  crs_pass_rooms (crs_pass_fold b c x t true) (crs_pass_cnt c x t true) x t false.

Definition crs_doc_fold (b : rf_R F) (c : Z) (x : list Z) (t : jv) : rf_R F :=
  crs_pass_fold (crs_pass_fold b c x t true) (crs_pass_cnt c x t true) x t false.

Definition crs_after_doc (b : rf_R F) (c : Z) (x : list Z) (doc : Z) (t : jv) : rf_R F :=
  if doc =? 0 then b else crs_doc_fold b c x t.

Definition crs_parse_left (cnt : Z) (x : list Z) (took : Z) (tr : list ev) (D : list (Z * Z)) : Prop :=
  exists ok res, jr_run jr_strtod x ok = (res, tr) /\ oks ok cnt (cnt + pick x took) (calls tr) /\
    Permutation (map snd D) (map Z.of_nat (lsz tr)) /\ Z.of_nat (length D) = nlive tr.

End R.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition check_reject_clean_starved_contract (KW : Z) : Prop :=
  forall L A regs mem md Lam peak cnt b data size took doc tb t D,
    reader_env B API (CRCS_K KW) L A regs mem md ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 size ->
    getr regs 12 = Z_to_bv 64 took -> getr regs 13 = Z_to_bv 64 doc ->
    0 <= KW -> size <= 0x300000 -> 0 < data -> data + size < 2 ^ 62 ->
    Z.of_nat (length tb) = size -> Mem.bytes_at segs mem data tb ->
    (0 < size -> exists a k, In (a, k) (blocks L A) /\ ~ lin Lam (a + 16) (k - 16) /\ a <= data /\ data + size <= a + k) ->
    (forall i, 0 <= i < size ->
       ~ owned B L A (data + i) /\ ~ alloc_statics (data + i) /\ ~ (errno_addr B <= data + i < errno_addr B + 4)) ->
    took = Z.of_nat (ncalls jr_strtod (zb tb)) ->
    (doc = 0 \/
     (json_read jr_strtod (zb tb) = Some t /\ pj_node segs mem (lin Lam) doc t D /\
      (forall a k, In (a, k) D -> In (a, k) Lam) /\ doc mod 8 = 0 /\ spZ regs <= doc /\
      Z.of_nat (length (wdoc t false)) + 1 < 2 ^ 24 /\ Z.of_nat (length (wdoc t true)) + 1 < 2 ^ 28 /\
      (depth t <= 32)%nat)) ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt < 2 ^ 62 - 2 ^ 30 ->
    rf_ok F A b ->
    (took <> 0 -> room_run F b (snd (jr_run jr_strtod (zb tb) []))) ->
    (took = 0 -> doc <> 0 -> crs_doc_rooms F b cnt (zb tb) t) ->
    (took <> 0 -> doc <> 0 -> forall tr D', crs_parse_left cnt (zb tb) took tr D' ->
       crs_doc_rooms F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) t) ->
    Mem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CRCS) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         rpost B API (CRCS_K KW) L A regs mem md alloc_statics (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         ledger B L' A' mem' Lam' peak' (cnt + crcs_growth (zb tb) took doc t) (2 ^ 64 - 1) /\
         Permutation Lam' Lam /\ peak <= peak' /\
         (doc <> 0 -> pj_node segs mem' (lin Lam') doc t D) /\
         (took = 0 -> rf_ok F A' (crs_after_doc F b cnt (zb tb) doc t)) /\
         (took <> 0 -> exists tr D', crs_parse_left cnt (zb tb) took tr D' /\
            rf_ok F A' (crs_after_doc F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) doc t))).

End K.
