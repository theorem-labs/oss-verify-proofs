From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU VerbsB CommandB printf_facts_c atoi_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import check_words_add_c check_words_chain_c check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_WORDS : Z := 0x14bac.
Definition CHECK_WORDS_FRAME : Z := 208.
Definition CHECK_WORDS_K : Z := 208 + ALLOC_STACK + 80.

Inductive witem := IStar | ILine | IWord (k : Z) | INum (k : Z) | IOpt (k : Z).

Definition call_items (fn : Z) : list witem :=
  match fn with
  | 0 => [IWord 1; INum 2; IStar; IStar]
  | 1 => [INum 1; ILine]
  | 2 => [INum 1]
  | 3 => []
  | 4 => [IWord 0; ILine; IWord 1; IWord 2]
  | 5 => [ILine]
  | 6 => [ILine; IStar; IStar]
  | 7 => [ILine; IStar]
  | 8 => []
  | 9 => [INum 1]
  | 10 => [IOpt 1]
  | 11 => [IWord 1]
  | 12 => [IWord 1; IWord 2]
  | 13 => [IWord 1]
  | 14 => [IWord 1; INum 2]
  | 15 => [IWord 1; IWord 2]
  | 16 => [IWord 1; IWord 2; IWord 3]
  | 17 => [INum 1; IStar; IStar]
  | 18 => [INum 1]
  | 19 => [INum 1; IWord 0]
  | 20 => [IWord 1; IWord 2; IWord 3; IStar]
  | 21 => [IWord 1]
  | 22 => [IWord 1]
  | 23 => [IWord 1]
  | 24 => [IWord 1]
  | _ => [IStar]
  end.

Definition want (r : Z) (ws : list (list byte)) (i : witem) : option (list byte) :=
  match i with
  | IStar => None
  | ILine => Some (join_sp ws)
  | IOpt k => if k <? r then Some (nth (Z.to_nat k) ws []) else None
  | INum k => if k <? r then Some (pf_bytes (pf_dec (atoi_val (nth (Z.to_nat k) ws [])))) else Some []
  | IWord k => if k <? r then Some (nth (Z.to_nat k) ws []) else Some []
  end.

Definition call_words_ok (r : Z) (ws : list (list byte)) (c : rcall) : Prop :=
  (forall a i x, nth_error (snd c) a = Some x -> nth_error (call_items (fst c)) a = Some i ->
     forall y, want r ws i = Some y -> x = y) /\
  (fst c = 0 -> length (snd c) = 4%nat /\
     nth 2 (snd c) [] = add_placement r (nth 3 ws []) /\
     nth 3 (snd c) [] = add_client r (nth 3 ws []) (nth 4 ws [])) /\
  (fst c = 17 -> length (snd c) = 3%nat /\
     nth 1 (snd c) [] = pf_bytes (pf_dec (r - 2)) /\ nth 2 (snd c) [] = pf_bytes (chain_list r ws)) /\
  (fst c = 20 -> length (snd c) = 4%nat /\ nth 3 (snd c) [] = pin_verdict r (nth 4 ws [])).

Definition words_prop (R : rstate) (ws : list (list byte)) : Prop :=
  let r := Z.min (Z.of_nat (length ws)) 64 in
  Forall (call_words_ok r ws) (r_calls R).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_words_contract : Prop :=
  forall L A regs mem md b (W arr q : Z) (wp : list Z) (ws : list (list byte)) (R : rstate) (O : list (Z * Z)),
    segs = rsegs ->
    call_pre_k B MR CHECK_WORDS_K L A regs mem md -> spZ regs <= TASK_SIZE ->
    cmd_mem B mem -> frm_zero fp_csr ->
    le_at B mem G_QUIT (Mem.le4 (Z_to_bv 64 q)) -> outside B L A CHECK_WORDS_K regs G_QUIT 4 ->
    getr regs 10 = Z_to_bv 64 W ->
    words_view B mem W arr wp ws ->
    words_place L A mem arr wp ws ->
    W mod 8 = 0 -> arr mod 8 = 0 ->
    spZ regs <= W + 16 -> W + 32 <= TASK_SIZE ->
    join_need ws + 1 <= 2 ^ 28 ->
    g_rec_rep segs L A mem R O ->
    (forall i, 0 <= i < CHECK_WORDS_FRAME -> ~ owned B L A (spZ regs - i - 1)) ->
    res_ok_slots A b -> room_ag b (join_need ws + 1) ->
    words_prop R ws ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_WORDS) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR CHECK_WORDS_K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         cmd_mem B mem' /\ le_at B mem' G_QUIT (Mem.le4 (Z_to_bv 64 q)) /\
         g_rec_rep segs L' A' mem' R O /\
         words_view B mem' W arr wp ws /\
         res_ok_slots A' (sb_free (sb_malloc b (join_need ws + 1)) (join_need ws + 1))).

End K.
