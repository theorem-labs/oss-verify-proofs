From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c relay_event_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RELAY_ADD : Z := 0x13504.
Definition RELAY_ADD_FRAME : Z := 64.
Definition UNLOCK_STACK : Z := 96.
Definition RELAY_ADD_K : Z := RELAY_ADD_FRAME + Z.max REALLOC_STACK UNLOCK_STACK.
Definition G_NSRC : Z := 0x318b8.
Definition G_SRC : Z := 0x318d0.
Definition G_WAKE1 : Z := 0x2162c.
Definition SRC_ENTRY : Z := 56.
Definition SRC_TABLE : Z := 16 * SRC_ENTRY.

Definition new_entry (fd : Z) : list byte := le4 (Z_to_bv 64 fd) ++ repeat (Z_to_bv 8 0) 52.

(* relay_add (fd) with g_nsrc = N, g_capsrc = C, g_src at g (relay.c:410): nothing for fd < 0; a full table grows to
   C ? C * 2 : 16 entries of SRC_ENTRY bytes with realloc (realloc (NULL, ...) when C = 0). *)
Definition relay_add_tr (FD N C : Z) (g : adrF) : trF :=
  if (FD <? 0) || negb (N =? C) then []
  else let cap := if C =? 0 then 16 else C * 2 in
       [if C =? 0 then RMalloc (cap * SRC_ENTRY) else RRealloc (C * SRC_ENTRY) (cap * SRC_ENTRY) g].

(* g_src after relay_add (fd), from base j: the address the growth returned, if any. *)
Definition relay_add_tbl (FD N C : Z) (j : nat) (g : adrF) : adrF :=
  if (FD <? 0) || negb (N =? C) then g else Ret j.

Section AB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition relay_add_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (N C G : Z) (ents tail : list byte),
    let FD := bv_signed (getr regs 10) in
    let g0 := known_at L A G in
    let tr := relay_add_tr FD N C g0 in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR RELAY_ADD_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> in_img Bm a) ->
    (forall a, G_RELAY_LO <= a < G_LOCK_HI -> img_plain Bm a) ->
    (forall a, G_WAKE1 <= a < G_WAKE1 + 4 -> img_plain Bm a) ->
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    bytes_at segs mem G_WAKE1 (le4 (Z_to_bv 64 (-1))) ->
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] ->
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] ->
    - 2 ^ 31 <= FD < 2 ^ 31 ->
    (0 <= FD -> 0 <= N < 4) ->
    ((C = 0 /\ G = 0 /\ N = 0 /\ ents = []) \/
     (C = 16 /\ In (G, SRC_TABLE) (blocks L A) /\ fresh_block Bm G SRC_TABLE /\
      Z.of_nat (length ents) = SRC_ENTRY * N /\ Z.of_nat (length tail) = SRC_TABLE - SRC_ENTRY * N /\
      rw_cells segs mem G [CB (Z.to_nat SRC_TABLE) (ents ++ tail)])) ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF tr -> roomF F qs bnd tr) ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 RELAY_ADD) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (G' : Z) (rest : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API RELAY_ADD_K
           (fun a => G_LOCK + 4 <= a < G_LOCK + 8 \/ G_NSRC <= a < G_NSRC + 8 \/ G_SRC <= a < G_SRC + 8 \/
                     (0 <= FD /\ 0 < C /\ G + SRC_ENTRY * N <= a < G + SRC_ENTRY * (N + 1)))
           (fun _ => False)
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (0 <= FD -> live_at L' A' (resolveF qs (relay_add_tbl FD N C 0 g0)) G' SRC_TABLE)) /\
         ro_agree segs mem' /\
         rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
         bytes_at segs mem' G_WAKE1 (le4 (Z_to_bv 64 (-1))) /\
         (FD < 0 ->
            getr regs' 10 = Z_to_bv 64 (-1) /\ blocks L' A' = blocks L A /\
            rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] /\
            rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)]) /\
         (0 <= FD ->
            getr regs' 10 = Z_to_bv 64 0 /\
            rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 16)] /\
            rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G')] /\
            In (G', SRC_TABLE) (blocks L' A') /\ fresh_block Bm G' SRC_TABLE /\
            Z.of_nat (length rest) = SRC_TABLE - SRC_ENTRY * (N + 1) /\
            rw_cells segs mem' G' [CB (Z.to_nat SRC_TABLE) (ents ++ new_entry FD ++ rest)] /\
            ((C = 0 /\
              exists c1 c2, blocks L' A' = c1 ++ (G', SRC_TABLE) :: c2 /\ c1 ++ c2 = blocks L A) \/
             (C = 16 /\ G' = G /\ blocks L' A' = blocks L A /\
              rest = skipn (Z.to_nat SRC_ENTRY) tail)))).

End AB.
