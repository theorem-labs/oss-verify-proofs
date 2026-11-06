From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP VerbsB CommandB
  verbs_receive_c joined_c send_message_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_ROUND_TRIP : Z := 0x14c78.
Definition CRT_FRAME : Z := 992.
Definition CRT_K : Z := CRT_FRAME + SM_K.
(* Peak extra live blocks and bytes of one call above its entry bound: at most 96 record copies of <= LMAX + 1
   bytes, strdup's and joined's blocks (<= 8194 bytes each), then send_message's peak. *)
Definition CRT_PEAK : Z := 98 + SM_PEAK.
Definition CRT_PEAKB : Z := 2 ^ 21.

Definition acted_m (R : rstate) (q : Z) : bool :=
  negb (q =? 0) || negb (Nat.eqb (length (r_calls R)) 0).

Definition rt_ok (R : rstate) (q sb hb : Z) (ws : list (list byte)) : Prop :=
  ws <> [] -> acted_m R q = true ->
  let '(R2, _, quit2) := vr_run (rec_clear (set_host (set_state R sb) hb)) (join_sp ws) in
  r_calls R2 = r_calls R /\ r_reply R2 = r_reply R /\ (if quit2 then 1 else 0) = q /\
  r_state R2 = r_state R /\ r_host R2 = r_host R.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition check_round_trip_contract : Prop :=
  forall L A regs mem md b (W arr sb hb q : Z) (wp : list Z) (ws : list (list byte))
         (R : rstate) (O : list (Z * Z)) (can : word),
    segs = rsegs ->
    call_pre_t B API CRT_K L A regs mem md -> cmd_mem B mem -> frm_zero fp_csr ->
    getr regs 10 = Z_to_bv 64 W -> getr regs 11 = Z_to_bv 64 sb -> getr regs 12 = Z_to_bv 64 hb ->
    0 <= sb < 2 ^ 64 -> 0 <= hb < 2 ^ 64 ->
    words_view B mem W arr wp ws -> words_place L A mem arr wp ws ->
    spZ regs <= W + 16 -> W + 32 <= 2 ^ 64 ->
    join_need ws + 1 <= 8194 ->
    in_live L A O arr (8 * Z.of_nat (length ws)) ->
    (forall k, (k < length ws)%nat -> in_live L A O (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1)) ->
    g_rec_rep segs L A mem R O ->
    (r_refuse R <> 0 -> declared (r_code R) = true) ->
    (acted_m R q = true -> exists X, r_reply R = Some (X ++ [Z_to_bv 8 0]) /\ no0 X) ->
    0 <= q < 2 ^ 32 ->
    le_at B mem G_QUIT (Mem.le4 (Z_to_bv 64 q)) ->
    (forall i, 0 <= i < 4 -> writable_at segs mem (G_QUIT + i)) ->
    outside B L A CRT_K regs G_QUIT 4 ->
    vr_tables B mem can ->
    res_ok_slots A b -> room_slots (sb_up b CRT_PEAK CRT_PEAKB) VR_REQ ->
    rt_ok R q sb hb ws ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md' R' O' b',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\ frm_zero (@fp_csr fx') /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         call_post_ko B MR CRT_K L A regs mem md vr_writes O L' A' regs' mem' md' /\
         cmd_mem B mem' /\
         g_rec_rep segs L' A' mem' R' O' /\
         r_refuse R' = r_refuse R /\ r_code R' = r_code R /\ r_spill R' = r_spill R /\
         r_state R' = r_state R /\ r_host R' = r_host R /\
         le_at B mem' G_QUIT (Mem.le4 (Z_to_bv 64 q)) /\
         words_view B mem' W arr wp ws /\ words_place L' A' mem' arr wp ws /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         blocks_stay L A O L' A' /\
         blocks_kept B L A mem mem' (owned_by O) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> ~ In pn O') /\
         (exists can', vr_tables B mem' can') /\
         res_ok_slots A' b' /\ sb_cap b' = sb_cap b).

End K.
