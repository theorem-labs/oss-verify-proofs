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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c relay_event_c send_line_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition RELAY_EVENT_K : Z := RELAY_EVENT_FRAME + SEND_LINE_K.

(* relay_event (line) of an EL-byte line (relay.c:403): send_line (line, EL + 1) under g_lock. *)
Definition relay_event_tr (live : bool) (mx NO CAP EL : Z) (j : nat) (o : adrF) : trF :=
  send_line_tr live mx NO CAP (EL + 1) j o.

(* g_out after relay_event (line). *)
Definition relay_event_out (live : bool) (mx NO CAP EL : Z) (j : nat) (o : adrF) : adrF :=
  send_line_out live mx NO CAP (EL + 1) j o.

Section EB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition event_writes (live : bool) (OUT CAP : Z) (a : Z) : Prop :=
  send_writes live OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8.

Definition relay_event_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (e slack O junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word),
    let S := bv_unsigned (getr regs 2) in
    let LP := bv_unsigned (getr regs 10) in
    let EL := Z.of_nat (length e) in
    let LEN := EL + 1 in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd LEN in
    let o0 := known_at L A OUT in
    let tr := relay_event_tr live (bv_unsigned mx) NO CAP EL 0 o0 in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR RELAY_EVENT_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    ERR mod 4 = 0 ->
    G_LOCK_HI <= ERR ->
    ro_agree segs mem ->
    bytes_at segs mem LP (e ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) e ->
    (- (LP + EL + 1)) mod 8 <= Z.of_nat (length slack) ->
    (LP + LEN <= G_RELAY_LO \/ G_LOCK_HI <= LP) ->
    (LP + LEN <= ERR \/ ERR + 4 <= LP) ->
    (LP + LEN <= S - RELAY_EVENT_K \/ S <= LP) ->
    (forall a, G_RELAY_LO <= a < G_LOCK_HI -> img_plain Bm a) ->
    (forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (exists q k, In (q, k) (blocks L A) /\ fresh_block Bm q k /\ q <= LP /\ LP + LEN <= q + k /\ q <> OUT) ->
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
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
      (LP + LEN <= OUT \/ OUT + CAP <= LP))) ->
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
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 RELAY_EVENT) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API RELAY_EVENT_K (event_writes live OUT CAP) (fun q => live = true /\ q = OUT)
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true -> live_at L' A' (resolveF qs (relay_event_out live (bv_unsigned mx) NO CAP EL 0 o0)) OUT' CAP')) /\
         ro_agree segs mem' /\
         bytes_at segs mem' LP (e ++ [Z_to_bv 8 0]) /\
         rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
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
            bytes_at segs mem' OUT' (O ++ e ++ [Z_to_bv 8 0] ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - LEN /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + LEN)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End EB.
