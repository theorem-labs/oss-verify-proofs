From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c RelayFrame RelayRunT
RelayRunF send_line_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition GESTURE_END_K : Z := GESTURE_END_FRAME + SEND_LINE_K.

(* gesture_end (held) of a key of XL >= 1 bytes (relay.c:125): send_line (held, XL), then send_line (" end", 5) from
   g_nout, g_capout and g_out the first left. The second send is live exactly when the first is: a live first send
   leaves g_client_broken = g_send_dead = 0, and an off or dead one leaves the second off. *)
Definition gesture_end_tr (live : bool) (mx NO CAP XL : Z) (j : nat) (o : adrF) : trF :=
  let t1 := send_line_tr live mx NO CAP XL j o in
  t1 ++ send_line_tr live mx (NO + XL) (send_line_cap live mx NO CAP XL) 5 (j + nretF t1)
         (send_line_out live mx NO CAP XL j o).

(* g_capout after gesture_end (held). *)
Definition gesture_end_cap (live : bool) (mx NO CAP XL : Z) : Z :=
  send_line_cap live mx (NO + XL) (send_line_cap live mx NO CAP XL) 5.

(* g_out after gesture_end (held). *)
Definition gesture_end_out (live : bool) (mx NO CAP XL : Z) (j : nat) (o : adrF) : adrF :=
  send_line_out live mx (NO + XL) (send_line_cap live mx NO CAP XL) 5 (j + nretF (send_line_tr live mx NO CAP XL j o))
    (send_line_out live mx NO CAP XL j o).

Section GB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition gesture_end_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (x slack O junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word),
    let S := bv_unsigned (getr regs 2) in
    let H := bv_unsigned (getr regs 10) in
    let XL := Z.of_nat (length x) in
    let LEN := XL + 5 in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd LEN in
    let o0 := known_at L A OUT in
    let tr := gesture_end_tr live (bv_unsigned mx) NO CAP XL 0 o0 in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR GESTURE_END_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    G_RELAY_HI <= ERR ->
    ro_agree segs mem ->
    bytes_at segs mem H (x ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) x ->
    (- (H + XL + 1)) mod 8 <= Z.of_nat (length slack) ->
    1 <= XL ->
    (H + XL + 1 <= G_RELAY_LO \/ G_RELAY_HI <= H) ->
    (H + XL + 1 <= ERR \/ ERR + 4 <= H) ->
    (H + XL + 1 <= S - GESTURE_END_K \/ S <= H) ->
    (forall a, G_RELAY_LO <= a < G_RELAY_HI -> img_plain Bm a) ->
    (forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a) ->
    (exists q k, In (q, k) (blocks L A) /\ fresh_block Bm q k /\ q <= H /\ H + XL + 1 <= q + k /\ q <> OUT) ->
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
      (H + XL + 1 <= OUT \/ OUT + CAP <= H))) ->
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
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 GESTURE_END) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API GESTURE_END_K (send_writes live OUT CAP) (fun q => live = true /\ q = OUT)
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true -> live_at L' A' (resolveF qs (gesture_end_out live (bv_unsigned mx) NO CAP XL 0 o0)) OUT' CAP')) /\
         ro_agree segs mem' /\
         bytes_at segs mem' H (x ++ [Z_to_bv 8 0]) /\
         rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         (live = false ->
            blocks L' A' = blocks L A /\
            rw_cells segs mem' ERR [C4 ev'] /\
            rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
         (live = true ->
            NO + LEN <= CAP' /\ CAP' = gesture_end_cap live (bv_unsigned mx) NO CAP XL /\
            fresh_block Bm OUT' CAP' /\ (exists ev'', rw_cells segs mem' ERR [C4 ev'']) /\
            (forall q m, In (q, m) (blocks L A) -> q <> OUT -> 0 < m -> q <> OUT') /\
            (exists b1 b2 c1 c2, blocks L' A' = c1 ++ (OUT', CAP') :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
               ((CAP = 0 /\ blocks L A = b1 ++ b2) \/ (0 < CAP /\ blocks L A = b1 ++ (OUT, CAP) :: b2))) /\
            bytes_at segs mem' OUT' (O ++ x ++ END5 ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - LEN /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + LEN)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End GB.
