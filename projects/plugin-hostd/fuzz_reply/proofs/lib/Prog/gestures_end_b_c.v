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
  RelayRunF send_line_b_c gesture_end_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition GESTURES_END : Z := 0x130ec.
Definition GESTURES_END_FRAME : Z := 32.
Definition GESTURES_END_K : Z := GESTURES_END_FRAME + Z.max GESTURE_END_K ALLOC_STACK.

Definition key_addr (k : Z * list byte * list byte) : Z := fst (fst k).
Definition key_text (k : Z * list byte * list byte) : list byte := snd (fst k).
Definition key_slack (k : Z * list byte * list byte) : list byte := snd k.

Definition keys_total (ks : list (Z * list byte * list byte)) : Z :=
  fold_right (fun k acc => Z.of_nat (length (key_text k)) + 5 + acc) 0 ks.

Definition keys_out (ks : list (Z * list byte * list byte)) : list byte :=
  concat (map (fun k => key_text k ++ END5) ks).

Definition key_ptrs (ks : list (Z * list byte * list byte)) : list byte :=
  concat (map (fun k => le8 (Z_to_bv 64 (key_addr k))) ks).

Definition key_lens (ks : list (Z * list byte * list byte)) : list Z :=
  map (fun k => Z.of_nat (length (key_text k))) ks.

(* The held keys ks as gestures_end's run takes them: each key's length and address, nm naming the start blocks. *)
Definition key_runs (nm : Z -> adrF) (ks : list (Z * list byte * list byte)) : list (Z * adrF) :=
  map (fun k => (Z.of_nat (length (key_text k)), nm (key_addr k))) ks.

(* The held keys xks (length, address) ended in array order (relay.c:136-140), each gesture_end (key) then free (key)
   of its strndup block of |key| + 1 bytes, from g_nout = no, g_capout = cap, g_out at o: the requests, the final
   g_capout and g_out. Every gesture_end of the run is live exactly when the first is: a live one leaves
   g_client_broken = g_send_dead = 0, an off one leaves the next off, a dead one sets g_client_broken. *)
Fixpoint keys_end_run (live : bool) (mx no cap : Z) (xks : list (Z * adrF)) (j : nat) (o : adrF) : trF * (Z * adrF) :=
  match xks with
  | [] => ([], (cap, o))
  | (xl, ka) :: r =>
      let g := gesture_end_tr live mx no cap xl j o in
      let p := keys_end_run live mx (no + xl + 5) (gesture_end_cap live mx no cap xl) r (j + nretF g)
                 (gesture_end_out live mx no cap xl j o) in
      (g ++ RFree (xl + 1) ka :: fst p, snd p)
  end.

(* gestures_end (s) of a source holding the keys xks in an array at HP of KH bytes, at address ha (relay.c:132): the
   keys' run, then free (s->held): no request when HP = 0 (free (NULL)). *)
Definition gestures_end_tr (live : bool) (mx NO CAP : Z) (xks : list (Z * adrF)) (HP KH : Z) (j : nat) (o ha : adrF)
    : trF :=
  fst (keys_end_run live mx NO CAP xks j o) ++ (if HP =? 0 then [] else [RFree KH ha]).

(* g_capout after gestures_end (s) of keys of lengths xls; the capacity does not depend on the addresses. *)
Definition gestures_end_cap (live : bool) (mx NO CAP : Z) (xls : list Z) : Z :=
  fst (snd (keys_end_run live mx NO CAP (map (fun xl => (xl, adr0)) xls) 0 adr0)).

(* g_out after gestures_end (s). *)
Definition gestures_end_out (live : bool) (mx NO CAP : Z) (xks : list (Z * adrF)) (j : nat) (o : adrF) : adrF :=
  snd (snd (keys_end_run live mx NO CAP xks j o)).

Section GSB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition gestures_writes (live : bool) (OUT CAP SA : Z) (a : Z) : Prop :=
  send_writes live OUT CAP a \/ SA + 40 <= a < SA + 52.

Definition gestures_end_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (ks : list (Z * list byte * list byte)) (HP KH : Z)
         (O junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word),
    let S := bv_unsigned (getr regs 2) in
    let SA := bv_unsigned (getr regs 10) in
    let NH := Z.of_nat (length ks) in
    let TOT := keys_total ks in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd TOT in
    let nm := known_at L A in
    let tr := gestures_end_tr live (bv_unsigned mx) NO CAP (key_runs nm ks) HP KH 0 (nm OUT) (nm HP) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR GESTURES_END_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    G_RELAY_HI <= ERR ->
    ro_agree segs mem ->
    (forall a, G_RELAY_LO <= a < G_RELAY_HI -> img_plain Bm a) ->
    (forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a) ->
    (exists q k, In (q, k) (blocks L A) /\ fresh_block Bm q k /\ q <= SA /\ SA + 56 <= q + k /\
       q <> OUT /\ q <> HP /\ ~ In q (map key_addr ks)) ->
    SA mod 8 = 0 ->
    rw_cells segs mem (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] ->
    NH < 2 ^ 31 - 1 ->
    ((HP = 0 /\ ks = []) \/
     (In (HP, KH) (blocks L A) /\ fresh_block Bm HP KH /\ 8 * NH <= KH /\ 8 <= KH /\ HP <> OUT /\ ~ In HP (map key_addr ks) /\
      bytes_at segs mem HP (key_ptrs ks))) ->
    NoDup (map key_addr ks) ->
    Forall (fun k =>
      In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
      fresh_block Bm (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
      bytes_at segs mem (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
      ~ In (Z_to_bv 8 0) (key_text k) /\ 1 <= Z.of_nat (length (key_text k)) <= 6000 /\
      (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k)) /\
      key_addr k <> OUT) ks ->
    (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
    rw_cells segs mem G_CLIENT [C4 (Z_to_bv 64 cl)] ->
    rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)] ->
    rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] ->
    rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)] ->
    rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
    rw_cells segs mem ERR [C4 ev] ->
    ((CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
     (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
      bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO)) ->
    2 * (NO + TOT) < 2 ^ 63 ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF tr -> roomF F qs bnd tr) ->
    let off := send_off cl br TOT in
    let br' := if off then br else dd in
    let ei' := if off then ei else 0 in
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 GESTURES_END) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API GESTURES_END_K (gestures_writes live OUT CAP SA)
           (fun q => (live = true /\ q = OUT) \/ q = HP \/ In q (map key_addr ks))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true ->
               live_at L' A' (resolveF qs (gestures_end_out live (bv_unsigned mx) NO CAP (key_runs nm ks) 0 (nm OUT)))
                 OUT' CAP')) /\
         ro_agree segs mem' /\
         rw_cells segs mem' (SA + 40) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
         rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         (exists ev'', rw_cells segs mem' ERR [C4 ev'']) /\
         (forall q m, In (q, m) (blocks L' A') <->
            ((In (q, m) (blocks L A) /\ q <> OUT /\ q <> HP /\ ~ In q (map key_addr ks)) \/
             (live = true /\ q = OUT' /\ m = CAP') \/
             (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) /\
         (live = false ->
            rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
         (live = true ->
            NO + TOT <= CAP' /\ CAP' = gestures_end_cap live (bv_unsigned mx) NO CAP (key_lens ks) /\
            fresh_block Bm OUT' CAP' /\
            (forall q m, In (q, m) (blocks L A) -> q <> OUT -> q <> HP -> ~ In q (map key_addr ks) -> 0 < m -> q <> OUT') /\
            bytes_at segs mem' OUT' (O ++ keys_out ks ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End GSB.
