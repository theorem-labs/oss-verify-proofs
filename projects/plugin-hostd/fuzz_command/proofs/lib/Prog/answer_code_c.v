From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require snprintf_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition ANSWER_CODE : Z := 0x16fa8.
Definition ANSWER_CODE_K : Z := 48 + Z.max snprintf_c.SNPRINTF_K (Z.max HAND_BACK_K ALLOC_STACK).

Definition ac_writes (a : Z) : Prop := G_REC + OFF_ANSWER <= a < G_REC + OFF_ANSWER + 8.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition answer_code_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (R : rstate) (O : list (Z * Z)) (code : Z) (b : sbound) (c' : config) : Prop :=
  let n := Z.of_nat (length (resp code)) + 1 in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' p1 old O',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    Mem.bytes_at segs mem (G_REC + OFF_ANSWER) (Mem.le8 (Z_to_bv 64 old)) /\
    call_post_rec B MR ANSWER_CODE_K L A regs mem md ac_writes (fun a => a = old) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 (snd (rec_answer_code R code)) /\
    p1 mod 16 = 0 /\ fresh_block B p1 n /\
    (exists c1 c2,
       ((old = 0 /\ blocks L A = c1 ++ c2) \/ (exists k, old <> 0 /\ In (old, k) O /\ blocks L A = c1 ++ (old, k) :: c2)) /\
       (forall pn, In pn (blocks L' A') <-> In pn (c1 ++ c2) \/ pn = (p1, n)) /\ ~ In (p1, n) (c1 ++ c2)) /\
    blocks_kept B L A mem mem' (fun a => a = old) /\
    (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) O -> In (q, k) (user_blocks A')) /\
    g_rec_rep segs L' A' mem' (fst (rec_answer_code R code)) O' /\
    (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    Mem.bytes_at segs mem' p1 (resp code ++ [Z_to_bv 8 0]) /\
    ro_agree segs mem' /\ f18_words segs mem' /\ guard_kept B mem mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_free (sb_malloc (sb_malloc b n) n) n) /\
    res_ok_slots A' (sb_shift b A A').

Definition answer_code_contract : Prop :=
  forall L A regs mem md (R : rstate) (O : list (Z * Z)) (code : Z) b,
    call_pre_t B API ANSWER_CODE_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 code -> -2^31 <= code < 2^31 ->
    g_rec_rep segs L A mem R O ->
    frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_malloc (sb_malloc b (Z.of_nat (length (resp code)) + 1)) (Z.of_nat (length (resp code)) + 1))
               (Z.of_nat (length (resp code)) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 ANSWER_CODE) mem (seg_rom segs)) md)
      (answer_code_ret L A regs mem md R O code b).

End K.
