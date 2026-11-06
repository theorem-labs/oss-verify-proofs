From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes WriterSpec WriterValue WriterApp WriterRet TxCalls TxRet PjWriteHyp pj_set_c round_trip_text_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require fuzz_alloc_ran_out_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 plain twin pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain
   (sha256 c8f4d6b8e567b0b1...): check_round_trip FUNC LOCAL 0x13fe4 size 680, frame 0x100 (as before).
   fuzz_preset.c:772-781 (#102): `copy = empty` (memset of 56 bytes), then
   `round_trip_text(doc,0,&copy) || round_trip_text(doc,1,NULL) || (doc->type == PJ_OBJECT && round_trip_rewrite(doc,&copy))`
   with round_trip_rewrite (fuzz_preset.c:715-769) inlined; the value returned is 1 when memory ran out.
   g_ran_out (fuzz_alloc_ran_out_c.G_RAN_OUT) and g_own_ran_out (LedgerCells.GL_OWN_RAN_OUT) are one byte each: every
   access in the twin is lbu / sb.  Under the rooms premises every allocation succeeds and no failure is injected
   (ledger fail = 2 ^ 64 - 1), so neither flag changes: the call returns 1 exactly when a flag is set at entry
   (round_trip_text then returns 1 at once, fuzz_preset.c:675-680), else 0.  The two arms of the post partition these
   two cases by the entry flags ro / oo.
   CRT_K = CRT_F + round_trip_text_c.RTT_K (the deepest callee; RTT_K = 112 + parse_noting_c.PN_K = 13808). *)
Definition CHECK_ROUND_TRIP : Z := 0x13fe4.
Definition CRT_F : Z := 256.
Definition CRT_K : Z := 14064.
Definition MOD_AT_A : Z := 0x1034e.
Definition STAMP_A : Z := 0x103d3.
Definition MOD_AT : list Z := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116].
Definition STAMP : list Z := [50; 48; 50; 54; 45; 49; 48; 45; 50; 53; 84; 48; 48; 58; 48; 48; 58; 48; 48; 90].

Definition crt_tree (t : jv) : jv :=
  match t with
  | JObj ms => JObj (pj_set_model ms MOD_AT (JStr STAMP))
  | _ => t
  end.

Fixpoint crt_at (ms : list (list Z * jv)) : nat :=
  match ms with
  | [] => O
  | (k, _) :: r => if list_eq_dec Z.eq_dec k MOD_AT then O else S (crt_at r)
  end.

Definition crt_set_rel (ms ms' : list (list Z * jv)) (ix : nat) : Prop :=
  (ix <= length ms)%nat /\
  (forall j nm u, (j < ix)%nat -> nth_error ms j = Some (nm, u) -> nm <> MOD_AT) /\
  ((ix < length ms)%nat -> exists u, nth_error ms ix = Some (MOD_AT, u)) /\
  length ms' = (if Nat.eqb ix (length ms) then S (length ms) else length ms) /\
  (forall j nm u, nth_error ms j = Some (nm, u) ->
     exists u', nth_error ms' j = Some (nm, u') /\ (j <> ix -> u' = u)) /\
  nth_error ms' ix = Some (MOD_AT, JStr STAMP).

Definition crt_count (t : jv) (cset : Z) : Z :=
  wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) + wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) +
  match t with
  | JObj _ => 1 + cset + wcalls (crt_tree t) true + Z.of_nat (PjRoundTrip.tcalls (crt_tree t))
  | _ => 0
  end.

Definition crt_cnt1 (cnt : Z) (t : jv) : Z := cnt + wcalls t false + Z.of_nat (PjRoundTrip.tcalls t).

Definition crt_cnt2 (cnt : Z) (t : jv) : Z := crt_cnt1 cnt t + wcalls t true + Z.of_nat (PjRoundTrip.tcalls t).

Definition crt_dl (T : list ev) (E : list (Z * Z)) : Prop :=
  Permutation (map snd E) (map Z.of_nat (lsz T)) /\ Z.of_nat (length E) = nlive T.

Section R.
Variable F : ResForm.

Definition crt_b1 (b : rf_R F) (cnt : Z) (t : jv) : rf_R F := rtt_bf F b cnt t false.

Definition crt_b2 (b : rf_R F) (cnt : Z) (t : jv) (Df : list (Z * Z)) : rf_R F :=
  rf_frees F (rtt_bf F (crt_b1 b cnt t) (crt_cnt1 cnt t) t true) Df.

(* The outcomes of pj_set on the copy (the copy's block list Db has the size facts of the trace T):
   the key is present (its old value's blocks Di are freed), or absent (set_trace at the copy's cap). *)
Definition crt_set_res (b3 : rf_R F) (n : Z) (T : list ev) (b4 : rf_R F) (cset : Z) (Do : list (Z * Z)) : Prop :=
  exists Db, crt_dl T Db /\
  ((cset = 0 /\ exists Di Dr Di' a, Permutation Db (Di ++ Dr) /\ Permutation Di Di' /\ b4 = rf_frees F b3 Di' /\
       Permutation Do (Dr ++ [(a, 21)])) \/
   (exists cap Dold Dnew Dr a a', n <= cap /\ cset = Z.of_nat (length (set_trace n cap 10)) /\
       b4 = rf_run F b3 (set_trace n cap 10) /\
       Permutation Db (Dold ++ Dr) /\ Permutation Do (Dnew ++ (a', 11) :: Dr ++ [(a, 21)]) /\
       (n < cap /\ Dold = [] /\ Dnew = [] \/
        n = cap /\ map snd Dold = (if cap =? 0 then [] else [56 * cap; 8 * cap]) /\
          map snd Dnew = [56 * cap2 cap; 8 * cap2 cap]))).

Definition crt_b5 (b4 : rf_R F) (c4 : Z) (t : jv) : rf_R F :=
  wfold F b4 (w0 c4 (2 ^ 64 - 1)) (wdpieces (crt_tree t) true).

(* Room for the object path, at the bound b2 after the two renderings. *)
Definition crt_obj_rooms (b2 : rf_R F) (cnt2 : Z) (t : jv) (n : Z) : Prop :=
  rf_room F b2 37 /\
  (forall cap, n <= cap -> room_run F (rf_malloc F b2 37) (set_trace n cap 10)) /\
  (forall b4 cset Do, crt_set_res (rf_malloc F b2 37) n (PjRoundTrip.ttrace t) b4 cset Do ->
     wr_rooms F b4 (w0 (cnt2 + 1 + cset) (2 ^ 64 - 1)) (wdpieces (crt_tree t) true) /\
     room_run F (crt_b5 b4 (cnt2 + 1 + cset) t) (PjRoundTrip.ttrace (crt_tree t))).

(* The bound at the return. *)
Definition crt_fin (b : rf_R F) (cnt : Z) (t : jv) (cset : Z) (bf : rf_R F) : Prop :=
  exists Df, crt_dl (PjRoundTrip.ttrace t) Df /\
  match t with
  | JObj ms =>
      exists b4 Do Dp Dp' Do', crt_set_res (rf_malloc F (crt_b2 b cnt t Df) 37) (Z.of_nat (length ms))
                                  (PjRoundTrip.ttrace t) b4 cset Do /\
        crt_dl (PjRoundTrip.ttrace (crt_tree t)) Dp /\ Permutation Dp Dp' /\ Permutation Do Do' /\
        bf = rf_frees F (rf_frees F (rf_free F (rf_run F (crt_b5 b4 (crt_cnt2 cnt t + 1 + cset) t)
                                                   (PjRoundTrip.ttrace (crt_tree t)))
                                       (wcap (crt_tree t) true + 16)) Dp') Do'
  | _ => exists Db Db', crt_dl (PjRoundTrip.ttrace t) Db /\ Permutation Db Db' /\ bf = rf_frees F (crt_b2 b cnt t Df) Db'
  end.

End R.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition check_round_trip_contract : Prop :=
  forall L A regs mem md (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (doc : Z) (t : jv)
         (D : list (Z * Z)) (x : list Z) (ro oo : Z),
    reader_env B API CRT_K L A regs mem md ->
    st_init_done A = true ->
    ledger B L A mem Lam peak cnt (2 ^ 64 - 1) -> cnt < 2 ^ 62 - 2 ^ 30 ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 doc ->
    pj_node segs mem (lin Lam) doc t D -> (forall bk, In bk D -> In bk Lam) ->
    spZ regs <= doc ->
    json_read jr_strtod x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
    wlen t false <= 3 * Z.of_nat (length x) -> wlen t true <= 56 * Z.of_nat (length x) - 54 ->
    rtt_rooms F b cnt t false -> rtt_rooms F (crt_b1 F b cnt t) (crt_cnt1 cnt t) t true ->
    (forall ms, t = JObj ms -> forall Df, crt_dl (PjRoundTrip.ttrace t) Df ->
       crt_obj_rooms F (crt_b2 F b cnt t Df) (crt_cnt2 cnt t) t (Z.of_nat (length ms))) ->
    (forall e, In e (PjRoundTrip.ttrace t) \/ In e (PjRoundTrip.ttrace (crt_tree t)) -> is_call e = true ->
       Z.of_nat (esize e) + 16 <= 2 ^ 27) ->
    0 <= ro < 256 -> 0 <= oo < 256 ->
    Mem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) ->
    Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' (Lam' : list (Z * Z)) (peak' cset : Z)
                        (b' : rf_R F),
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rtt_rel B API CRT_K regs alloc_statics L A mem md L' A' regs' mem' md' /\
         rd_cells B mem' /\ st_init_done A' = true /\
         Mem.bytes_at segs mem' fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) /\
         Mem.bytes_at segs mem' GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)) /\
         ( (* memory had run out: round_trip_text (doc, 0, &copy) wrote and freed its two texts, returned 1, and the
              copy, still empty, was freed *)
           (ro <> 0 \/ oo <> 0) /\ getr regs' 10 = Z_to_bv 64 1 /\
           ledger B L' A' mem' Lam' peak' (cnt + wcalls t false) (2 ^ 64 - 1) /\
           peak <= peak' /\ Permutation Lam' Lam /\
           rf_ok F A' (rtt_bo F b cnt t false) /\
           pj_node segs mem' (lin Lam') doc t D
         \/
           ro = 0 /\ oo = 0 /\ getr regs' 10 = Z_to_bv 64 0 /\
           0 <= cset <= 3 /\ (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) /\
           ledger B L' A' mem' Lam' peak' (cnt + crt_count t cset) (2 ^ 64 - 1) /\
           peak <= peak' /\ Permutation Lam' Lam /\
           rf_ok F A' b' /\ crt_fin F b cnt t cset b' /\
           pj_node segs mem' (lin Lam') doc t D)).

End K.
