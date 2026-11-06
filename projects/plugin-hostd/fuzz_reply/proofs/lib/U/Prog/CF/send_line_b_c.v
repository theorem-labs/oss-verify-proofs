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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition SEND_LINE_K : Z := SEND_LINE_FRAME + REALLOC_STACK.
Definition REALLOC_PC : Z := 0x178f8.

(* The relay traces name blocks as RelayRunT does: Known p for a block live when the statement's run starts, Ret i
   for the address its i-th returning request returned. A trace function that a caller reuses takes j, the number of
   addresses the run returned before it, and the addresses of the blocks it touches in that numbering; its own
   requests return Ret j, Ret (j + 1), ... A statement starts at j = 0 with known_at L A for its start blocks. *)

(* fuzz_send's requests (fuzz_reply.c:297-309) for the rem bytes of a live line still to send, from g_send_max = mx,
   g_nout = no, g_capout = cap, the buffer at o: each round sends n = rem, cut to mx when mx <> 0 and rem > mx, and
   when no + n > cap grows the buffer to (no + n) * 2 with realloc (realloc (NULL, ...) when cap = 0, else of the
   cap-byte block at o), the new buffer being the address it returns. The requests in order, the final capacity and
   the final buffer. Each round sends at least one byte, so rem rounds are enough. *)
Fixpoint sl_run (fuel : nat) (mx no cap rem : Z) (j : nat) (o : adrF) : trF * (Z * adrF) :=
  match fuel with
  | O => ([], (cap, o))
  | S f =>
      if rem <=? 0 then ([], (cap, o)) else
      let n := if negb (mx =? 0) && (mx <? rem) then mx else rem in
      if cap <? no + n then
        let c := (no + n) * 2 in
        let r := sl_run f mx (no + n) c (rem - n) (S j) (Ret j) in
        ((if cap =? 0 then RMalloc c else RRealloc cap c o) :: fst r, snd r)
      else sl_run f mx (no + n) cap (rem - n) j o
  end.

(* send_line (line, len) with g_send_max = mx, g_nout = NO, g_capout = CAP, g_out at o: no request when the send is
   off or the controller is dead (live = false); the EINTR round requests nothing. *)
Definition send_line_tr (live : bool) (mx NO CAP LEN : Z) (j : nat) (o : adrF) : trF :=
  if live then fst (sl_run (Z.to_nat LEN) mx NO CAP LEN j o) else [].

(* g_capout after send_line (line, len); the capacity does not depend on the addresses. *)
Definition send_line_cap (live : bool) (mx NO CAP LEN : Z) : Z :=
  if live then fst (snd (sl_run (Z.to_nat LEN) mx NO CAP LEN 0 adr0)) else CAP.

(* g_out after send_line (line, len). *)
Definition send_line_out (live : bool) (mx NO CAP LEN : Z) (j : nat) (o : adrF) : adrF :=
  if live then snd (snd (sl_run (Z.to_nat LEN) mx NO CAP LEN j o)) else o.

Section SB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition send_writes (live : bool) (OUT CAP : Z) (a : Z) : Prop :=
  G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32 \/
  (live = true /\ OUT <= a < OUT + CAP).

Definition send_line_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (Bl O junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word),
    let S := bv_unsigned (getr regs 2) in
    let LINE := bv_unsigned (getr regs 10) in
    let LEN := bv_unsigned (getr regs 11) in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd LEN in
    let o0 := known_at L A OUT in
    let tr := send_line_tr live (bv_unsigned mx) NO CAP LEN 0 o0 in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR SEND_LINE_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    ERR mod 4 = 0 ->
    G_RELAY_HI <= ERR ->
    ro_agree segs mem ->
    bytes_at segs mem LINE Bl -> Z.of_nat (length Bl) = LEN ->
    (LINE + LEN <= G_RELAY_LO \/ G_RELAY_HI <= LINE) ->
    (LINE + LEN <= ERR \/ ERR + 4 <= LINE) ->
    (LINE + LEN <= S - SEND_LINE_K \/ S <= LINE) ->
    (forall a, G_RELAY_LO <= a < G_RELAY_HI -> img_plain Bm a) ->
    (forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    ((forall a, LINE <= a < LINE + LEN -> img_plain Bm a) \/
     (exists q k, In (q, k) (blocks L A) /\ q <= LINE /\ LINE + LEN <= q + k /\ q <> OUT)) ->
    (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
    rw_cells segs mem G_CLIENT [C4 (Z_to_bv 64 cl)] ->
    rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)] ->
    rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] ->
    rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)] ->
    rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
    rw_cells segs mem ERR [C4 ev] ->
    ((CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
     (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
      bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO /\
      (LINE + LEN <= OUT \/ OUT + CAP <= LINE))) ->
    2 * (NO + LEN) < 2 ^ 63 ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF tr -> roomF F qs bnd tr) ->
    let off := send_off cl br LEN in
    let br' := if off then br else dd in
    let ei' := if off then ei else 0 in
    let ev' := if off then ev
               else if dd =? 1 then Z_to_bv 64 EPIPE_V
               else if ei =? 1 then Z_to_bv 64 EINTR_V
               else ev in
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 SEND_LINE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API SEND_LINE_K (send_writes live OUT CAP) (fun q => live = true /\ q = OUT)
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true -> live_at L' A' (resolveF qs (send_line_out live (bv_unsigned mx) NO CAP LEN 0 o0)) OUT' CAP')) /\
         ro_agree segs mem' /\
         bytes_at segs mem' LINE Bl /\
         rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         (live = false ->
            blocks L' A' = blocks L A /\
            rw_cells segs mem' ERR [C4 ev'] /\
            rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
         (live = true ->
            NO + LEN <= CAP' /\ CAP' = send_line_cap live (bv_unsigned mx) NO CAP LEN /\
            fresh_block Bm OUT' CAP' /\ (exists ev'', rw_cells segs mem' ERR [C4 ev'']) /\
            (forall q m, In (q, m) (blocks L A) -> q <> OUT -> 0 < m -> q <> OUT') /\
            (exists b1 b2 c1 c2, blocks L' A' = c1 ++ (OUT', CAP') :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
               ((CAP = 0 /\ blocks L A = b1 ++ b2) \/ (0 < CAP /\ blocks L A = b1 ++ (OUT, CAP) :: b2))) /\
            bytes_at segs mem' OUT' (O ++ Bl ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - LEN /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + LEN)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End SB.
