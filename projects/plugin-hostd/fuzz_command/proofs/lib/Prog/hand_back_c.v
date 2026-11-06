From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP
RecKindB xstrdup_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition HAND_BACK : Z := 0x15b80.
Definition HAND_BACK_K : Z := XSTRDUP_K + 32.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition hand_back_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (s : Z) (x : list byte) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' p1 p2 old O',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    Mem.bytes_at segs mem (G_REC + OFF_ANSWER) (Mem.le8 (Z_to_bv 64 old)) /\
    call_post_rec B MR HAND_BACK_K L A regs mem md
      (fun a => G_REC + OFF_ANSWER <= a < G_REC + OFF_ANSWER + 8 \/
                (exists k, In (old, k) (blocks L A) /\ old <= a < old + k) \/
                p1 <= a < p1 + Z.of_nat (length x) + 1 \/ p2 <= a < p2 + Z.of_nat (length x) + 1)
      (fun a => a = old) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 p2 /\
    p1 <> p2 /\ p1 mod 16 = 0 /\ p2 mod 16 = 0 /\
    fresh_block B p1 (Z.of_nat (length x) + 1) /\ fresh_block B p2 (Z.of_nat (length x) + 1) /\
    (exists c1 c2,
       ((old = 0 /\ blocks L A = c1 ++ c2) \/
        (exists k, old <> 0 /\ In (old, k) O /\ blocks L A = c1 ++ (old, k) :: c2)) /\
       (forall pn, In pn (blocks L' A') <->
          In pn (c1 ++ c2) \/ pn = (p1, Z.of_nat (length x) + 1) \/ pn = (p2, Z.of_nat (length x) + 1)) /\
       ~ In (p1, Z.of_nat (length x) + 1) (c1 ++ c2) /\ ~ In (p2, Z.of_nat (length x) + 1) (c1 ++ c2)) /\
    blocks_kept B L A mem mem' (fun a => a = old) /\
    (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) O -> In (q, k) (user_blocks A')) /\
    g_rec_rep segs L' A' mem' (fst (hand_back R x)) O' /\
    (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, Z.of_nat (length x) + 1)) /\
    (forall pn, In pn O' -> fst pn <> p2) /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (p2, Z.of_nat (length x) + 1)) /\
    Mem.bytes_at segs mem' p1 (x ++ [Z_to_bv 8 0]) /\
    Mem.bytes_at segs mem' p2 (snd (hand_back R x) ++ [Z_to_bv 8 0]) /\
    Mem.bytes_at segs mem' s (x ++ [Z_to_bv 8 0]) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1)) /\
    res_ok_slots A' (sb_shift b A A').

Definition hand_back_contract : Prop :=
  forall L A regs mem md (s : Z) (x slack : list byte) (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR HAND_BACK_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 s ->
    Mem.bytes_at segs mem s (x ++ Z_to_bv 8 0 :: slack) ->
    no0 x -> Z.of_nat (length x) <= LMAX ->
    (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) ->
    (s + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= spZ regs - HAND_BACK_K \/ spZ regs <= s) ->
    str_home B L A (spZ regs) s (Z.of_nat (length x) + 1) ->
    g_rec_rep segs L A mem R O ->
    (forall pn, In pn O -> iv_apart s (Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack))) (fst pn) (snd pn)) ->
    res_ok_slots A b ->
    room_slots (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 HAND_BACK) mem (seg_rom segs)) md)
      (hand_back_ret L A regs mem md s x R O b).

End K.
