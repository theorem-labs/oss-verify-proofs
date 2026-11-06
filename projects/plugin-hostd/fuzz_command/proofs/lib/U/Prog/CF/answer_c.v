From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition ANSWER : Z := 0x16310.
Definition ANSWER_K : Z := 4128 + Z.max snprintf_c.SNPRINTF_K (Z.max mix_call_c.MIX_CALL_FRAME HAND_BACK_K).

Definition ans_entry (R : rstate) (c : Z) (e : rcall) : Prop :=
  (exists k, nth_error (r_calls R) k = Some e /\ c = G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (c = REC_SC /\ e = r_spill R).

Definition ans_shape (segs : list Segment) (mem : word -> option byte) (sh : Z) (x : list byte) : Prop :=
  Mem.bytes_at segs mem sh (x ++ [Z_to_bv 8 0]) /\ no0 x /\ Z.of_nat (length x) <= LMAX /\ fits x /\
  forall i, 0 <= i <= Z.of_nat (length x) -> Mem.ro_addr segs (Z_to_bv 64 (sh + i)) = true.

Definition ans_writes (a : Z) : Prop :=
  G_REC + OFF_ANSWER <= a < G_REC + OFF_ANSWER + 8 \/ G_REC + OFF_STATE <= a < G_REC + OFF_STATE + 8.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition answer_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (R : rstate) (O : list (Z * Z)) (e : rcall) (x : list byte) (chg : bool) (b : sbound) (c' : config) : Prop :=
  let t := snd (rec_answer R e x chg) in
  let n := Z.of_nat (length t) + 1 in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' p1 p2 old O',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    Mem.bytes_at segs mem (G_REC + OFF_ANSWER) (Mem.le8 (Z_to_bv 64 old)) /\
    call_post_rec B MR ANSWER_K L A regs mem md ans_writes (fun a => a = old) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 p2 /\
    p1 <> p2 /\ p1 mod 16 = 0 /\ p2 mod 16 = 0 /\ fresh_block B p1 n /\ fresh_block B p2 n /\
    (exists c1 c2,
       ((old = 0 /\ blocks L A = c1 ++ c2) \/ (exists k, old <> 0 /\ In (old, k) O /\ blocks L A = c1 ++ (old, k) :: c2)) /\
       (forall pn, In pn (blocks L' A') <-> In pn (c1 ++ c2) \/ pn = (p1, n) \/ pn = (p2, n)) /\
       ~ In (p1, n) (c1 ++ c2) /\ ~ In (p2, n) (c1 ++ c2)) /\
    blocks_kept B L A mem mem' (fun a => a = old) /\
    (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) O -> In (q, k) (user_blocks A')) /\
    g_rec_rep segs L' A' mem' (fst (rec_answer R e x chg)) O' /\
    (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
    (forall pn, In pn O' -> fst pn <> p2) /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
    Mem.bytes_at segs mem' p1 (t ++ [Z_to_bv 8 0]) /\
    Mem.bytes_at segs mem' p2 (t ++ [Z_to_bv 8 0]) /\
    ro_agree segs mem' /\ f18_words segs mem' /\ guard_kept B mem mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc b n) n) /\
    res_ok_slots A' (sb_shift b A A').

Definition answer_contract : Prop :=
  forall L A regs mem md (R : rstate) (O : list (Z * Z)) (c sh : Z) (e : rcall) (x : list byte) (chg : bool) b,
    call_pre_t B API ANSWER_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 sh ->
    chg = negb (bv_unsigned (getr regs 12) =? 0) ->
    g_rec_rep segs L A mem R O ->
    (r_refuse R = 0 -> ans_shape segs mem sh x) ->
    (r_refuse R = 0 -> chg = true ->
       ans_entry R c e /\
       forall q k a, In (q, k) (blocks L A) -> q + k <= a < 8 * ((q + k + 7) / 8) -> present mem a) ->
    frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_ag (sb_malloc (sb_malloc b (Z.of_nat (length (snd (rec_answer R e x chg))) + 1))
                  (Z.of_nat (length (snd (rec_answer R e x chg))) + 1))
               (Z.of_nat (length (snd (rec_answer R e x chg))) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 ANSWER) mem (seg_rom segs)) md) (answer_ret L A regs mem md R O e x chg b).

End K.
