From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet TxRet PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_ran_out_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 twin pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan (sha256
   27566683952ebd54...), the unstripped twin of the pinned fuzz_preset.ubsan 45b0357d18ff66cd... (facts 8f3e7e1a07f1):
     round_trip_text FUNC LOCAL 0x15334 size 388, the plain build's 96 instructions (other addresses) and an unimp
     after the abort call: addi sp, sp, -0x70 (ra s0 s1 s2 s3 s4 s5 saved); jal pj_write;
     rendered() inlined (struct text of 32 bytes at sp: b, n, cap, failed; tx_put "" / tx_value / tx_put "\n";
     lw failed; free(b) when failed); lbu g_own_ran_out; jal fuzz_alloc_ran_out;
     ran out: jal free (want); jal fuzz_free (text); a0 := 1;
     else: strcmp; strlen; jal parse_noting; jal free (want); jal fuzz_free (text); lbu g_own_ran_out;
     jal fuzz_alloc_ran_out (either nonzero: a0 := 1); rc; jal same; jal memcpy (copy) or jal pj_free; a0 := 0.
   Source (fuzz_preset.c of #102, lines 667-711): int round_trip_text(doc, pretty, copy) returns 1 when memory ran out
   (out_of_memory() = g_own_ran_out || fuzz_alloc_ran_out(), lines 79-82) after the write and the rendering (675-680) or
   after the read-back (694-695), and 0 at the end.  Under rtt_rooms every allocation succeeds (fuzz_realloc's and
   tx_put's contracts exclude the refused arm), so neither flag changes inside the call: the call returns 1 exactly
   when one of the two flag bytes is nonzero at entry (the first test), and the second test is reached only with both
   bytes 0.  The two arms of the post below partition the call on those entry bytes.  The read-back is parse_noting
   now (not pj_parse), so RTT_K takes parse_noting's PN_K.  This is lib/U/Prog/round_trip_text_c.v's statement with
   SRCF's SR (the cut-free form). *)
Definition ROUND_TRIP_TEXT : Z := 0x15334.
Definition RTT_F : Z := 112.
Definition RTT_K : Z := RTT_F + parse_noting_c.PN_K.

Definition rtt_ns (t : jv) (p : bool) : list Z := [0] ++ tv_calls t p 0 ++ (if p then [1] else []).

Definition rtt_writes (copy : Z) (x : Z) : Prop := (copy <> 0 /\ copy <= x < copy + 56) \/ alloc_statics x.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rtt_rel (K : Z) (regs : bvmap 5 word) (E : Z -> Prop)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (forall a k, In (a, k) (blocks L A) -> In (a, k) (blocks L' A')) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> (forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 -> ~ owned B L0 A0 a) ->
     ~ scratch_k B K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) /\
  (forall a, scratch_k B K regs a -> writable_at segs mem' a).

Definition rtt_bw (b : rf_R F) (cnt : Z) (t : jv) (p : bool) : rf_R F := wfold F b (w0 cnt (2 ^ 64 - 1)) (wdpieces t p).
Definition rtt_bt (b : rf_R F) (cnt : Z) (t : jv) (p : bool) : rf_R F := tx_fold F (rtt_bw b cnt t p) 0 0 (rtt_ns t p).
Definition rtt_bp (b : rf_R F) (cnt : Z) (t : jv) (p : bool) : rf_R F := rf_run F (rtt_bt b cnt t p) (PjRoundTrip.ttrace t).
Definition rtt_bf (b : rf_R F) (cnt : Z) (t : jv) (p : bool) : rf_R F :=
  rf_free F (rf_free F (rtt_bp b cnt t p) (tx_capf 0 0 (rtt_ns t p))) (wcap t p + 16).
(* the ran-out arm: the write and the rendering, then free (want) and fuzz_free (text); no read-back *)
Definition rtt_bo (b : rf_R F) (cnt : Z) (t : jv) (p : bool) : rf_R F :=
  rf_free F (rf_free F (rtt_bt b cnt t p) (tx_capf 0 0 (rtt_ns t p))) (wcap t p + 16).

Definition rtt_rooms (b : rf_R F) (cnt : Z) (t : jv) (p : bool) : Prop :=
  wr_rooms F b (w0 cnt (2 ^ 64 - 1)) (wdpieces t p) /\
  tx_rooms F (rtt_bw b cnt t p) 0 0 (rtt_ns t p) /\
  room_run F (rtt_bt b cnt t p) (PjRoundTrip.ttrace t).

(* ro / oo: the entry bytes of g_ran_out (fuzz_alloc_ran_out_c.G_RAN_OUT) and g_own_ran_out (GL_OWN_RAN_OUT, one
   byte each: lbu / sb in every build).  Both are kept.  Left arm: one of them is nonzero, so out_of_memory() holds at
   the first test (fuzz_preset.c:675) and the call returns 1 after free (want) and fuzz_free (text), *copy untouched.
   Right arm: both are 0, and the call returns 0 with the old post. *)
Definition round_trip_text_contract : Prop :=
  forall L A regs mem md (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (doc pretty copy : Z) (t : jv)
         (D : list (Z * Z)) (ro oo : Z),
    let p := negb (pretty =? 0) in
    reader_env B API RTT_K L A regs mem md ->
    st_init_done A = true ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt < 2 ^ 62 ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 doc -> getr regs 11 = Z_to_bv 64 pretty -> getr regs 12 = Z_to_bv 64 copy ->
    (pretty = 0 \/ pretty = 1) ->
    pj_node segs mem (lin Lam) doc t D -> (forall bk, In bk D -> In bk Lam) ->
    doc <> 0 -> spZ regs <= doc ->
    PjRoundTrip.pj_wf jr_strtod t -> (depth t <= 32)%nat -> wlen t p + 1 <= 2 ^ 28 ->
    (copy = 0 \/ copy <> 0 /\ pj_rw segs mem copy /\ spZ regs <= copy /\ (copy + 56 <= doc \/ doc + 56 <= copy)) ->
    rtt_rooms b cnt t p ->
    0 <= ro < 256 -> 0 <= oo < 256 ->
    Mem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) ->
    Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 ROUND_TRIP_TEXT) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' (Lam' : list (Z * Z)) (peak' : Z),
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rtt_rel RTT_K regs (rtt_writes copy) L A mem md L' A' regs' mem' md' /\
         rd_cells B mem' /\
         Mem.bytes_at segs mem' fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) /\
         Mem.bytes_at segs mem' GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)) /\
         ((ro <> 0 \/ oo <> 0) /\ getr regs' 10 = Z_to_bv 64 1 /\
            ledger B L' A' mem' Lam' peak' (cnt + wcalls t p) (2 ^ 64 - 1) /\
            peak <= peak' /\
            pj_node segs mem' (lin Lam') doc t D /\
            Permutation Lam' Lam /\
            rf_ok F A' (rtt_bo b cnt t p) /\
            (copy <> 0 -> forall i, 0 <= i < 56 -> mbyte segs mem' (copy + i) = mbyte segs mem (copy + i))
          \/
          ro = 0 /\ oo = 0 /\ getr regs' 10 = Z_to_bv 64 0 /\
            ledger B L' A' mem' Lam' peak' (cnt + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (2 ^ 64 - 1) /\
            peak <= peak' /\
            pj_node segs mem' (lin Lam') doc t D /\
            (copy = 0 -> Permutation Lam' Lam /\
              exists Db Df, Permutation Db Df /\
                Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) /\
                Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t) /\
                rf_ok F A' (rf_frees F (rtt_bf b cnt t p) Df)) /\
            (copy <> 0 -> rf_ok F A' (rtt_bf b cnt t p) /\
               exists Db, Permutation Lam' (Db ++ Lam) /\ new_blks L A Db /\ pj_node segs mem' (lin Lam') copy t Db /\
                 Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) /\
                 Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t)))).

End K.
