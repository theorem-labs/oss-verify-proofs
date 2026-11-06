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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU RecKindB xmalloc_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition SOCKET_SEND : Z := 0x1737c.
Definition SOCKET_SEND_K : Z := 32 + XMALLOC_K.

Definition socket_send_writes (a : Z) : Prop :=
  G_REC + OFF_NREPLIES <= a < G_REC + OFF_NREPLIES + 4 \/ G_REC + OFF_REPLY <= a < G_REC + OFF_REPLY + 16.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition socket_send_contract : Prop :=
  forall L A regs mem md (buf size : Z) (x : list byte) (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR SOCKET_SEND_K L A regs mem md ->
    getr regs 11 = Z_to_bv 64 buf -> getr regs 12 = Z_to_bv 64 size -> -2 ^ 31 <= size < 2 ^ 31 ->
    g_rec_rep segs L A mem R O -> r_nreplies R < 2 ^ 31 - 1 ->
    (0 < size ->
       size <= LMAX + 2 /\ Z.of_nat (length x) = size /\ Mem.bytes_at segs mem buf x /\
       (buf + size <= spZ regs - SOCKET_SEND_K \/ spZ regs <= buf) /\
       buf_home B L A O (spZ regs) buf size /\
       (forall a, buf <= a < buf + size -> ~ rec_area a) /\
       room_slots (sb_malloc b size) size) ->
    (size <= 0 -> x = []) ->
    ro_agree segs mem -> f18_words segs mem ->
    res_ok_slots A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SOCKET_SEND) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' R' O' (r0 q : Z) (bl1 bl2 : list (Z * Z)),
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_rec B MR SOCKET_SEND_K L A regs mem md socket_send_writes (fun a => In a (map fst O))
           L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 size /\
         R' = fst (socket_send_m R x) /\
         g_rec_rep segs L' A' mem' R' O' /\
         Mem.bytes_at segs mem (G_REC + OFF_REPLY) (Mem.le8 (Z_to_bv 64 r0)) /\
         (match r_reply R with
          | None => r0 = 0 /\ blocks L A = bl1 ++ bl2
          | Some _ => exists k0, In (r0, k0) O /\ blocks L A = bl1 ++ (r0, k0) :: bl2
          end) /\
         (size <= 0 -> blocks L' A' = bl1 ++ bl2 /\ (forall pn, In pn O' <-> In pn O /\ fst pn <> r0)) /\
         (0 < size ->
            (exists c1 c2, blocks L' A' = c1 ++ (q, size) :: c2 /\ c1 ++ c2 = bl1 ++ bl2) /\
            fresh_block B q size /\ q mod 16 = 0 /\
            (forall pn, In pn O' <-> (In pn O /\ fst pn <> r0) \/ pn = (q, size))) /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         others_kept segs L A mem L' A' mem' O /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         sb_le (sb_shift b A A') (if 0 <? size then sb_malloc b size else b) /\
         res_ok_slots A' (sb_shift b A A')).

End K.
