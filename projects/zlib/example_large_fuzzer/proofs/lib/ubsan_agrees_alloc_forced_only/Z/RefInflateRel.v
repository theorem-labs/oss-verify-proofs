(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition LFX : Z := 0x2e130.
Definition DFX : Z := 0x2e088.

Definition iwfx (st : inflate_state) : Prop :=
  - 2 ^ 31 <= is_last st < 2 ^ 31
  /\ - 2 ^ 31 <= is_havedict st < 2 ^ 31
  /\ - 2 ^ 31 <= is_flags st < 2 ^ 31
  /\ 0 <= is_dmax st < 2 ^ 32
  /\ 0 <= is_total st < 2 ^ 64
  /\ is_head st = 0
  /\ 0 <= is_bits st < 64 /\ 0 <= is_hold st < 2 ^ is_bits st
  /\ 0 <= is_length st < 2 ^ 32 /\ 0 <= is_offset st < 2 ^ 32 /\ 0 <= is_extra st < 2 ^ 32
  /\ match is_lencode st with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ match is_distcode st with CDyn ofs => 0 <= ofs <= 1444 | _ => True end
  /\ 0 <= is_lenbits st < 2 ^ 32 /\ 0 <= is_distbits st < 2 ^ 32
  /\ 0 <= is_ncode st < 2 ^ 32 /\ 0 <= is_nlen st < 2 ^ 32 /\ 0 <= is_ndist st < 2 ^ 32 /\ 0 <= is_have st < 2 ^ 32
  /\ 0 <= is_next st <= 1444
  /\ arr_len (is_lens st) = 320 /\ arr_len (is_work st) = 288 /\ arr_len (is_codes st) = 1444
  /\ (forall i, 0 <= i < 320 -> 0 <= arr_get (is_lens st) i < 2 ^ 16)
  /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (is_work st) i < 2 ^ 16)
  /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get (is_codes st) i < 2 ^ 32)
  /\ is_sane st = 1 /\ - 2 ^ 31 <= is_back st < 2 ^ 31 /\ 0 <= is_was st < 2 ^ 32.

Definition iwf (st : inflate_state) : Prop :=
  HEAD <= is_mode st <= SYNC
  /\ 0 <= is_wrap st < 16
  /\ match is_window_blk st with
     | Some _ => 8 <= is_wbits st <= 15 /\ arr_len (is_window st) = 2 ^ is_wbits st
                 /\ (is_wsize st = 0 \/ is_wsize st = 2 ^ is_wbits st)
     | None => True
     end
  /\ 0 <= is_wsize st < 2 ^ 32 /\ 0 <= is_whave st < 2 ^ 32 /\ 0 <= is_wnext st < 2 ^ 32
  /\ (is_wsize st <> 0 -> is_wnext st <= is_wsize st /\ is_whave st <= is_wsize st)
  /\ (forall i, 0 <= i < arr_len (is_window st) -> 0 <= arr_get (is_window st) i < 256)
  /\ 8 <= is_wbits st <= 15
  /\ (is_window_blk st = None -> is_wsize st = 0)
  /\ (is_wsize st <> 0 -> is_whave st < is_wsize st -> is_wnext st = is_whave st)
  /\ 0 <= is_check st < 2 ^ 64
  /\ (is_wsize st = 0 -> is_whave st = 0 /\ is_wnext st = 0)
  /\ (is_window_blk st = None -> arr_len (is_window st) = 0)
  /\ iwfx st.

Lemma iwf_set_mode : forall st v, HEAD <= v <= SYNC -> iwf st -> iwf (iset_mode st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

Definition zcall_wf (zc : ZCall) : Prop :=
  zstrm_ok (zc_strm zc) /\ 0 <= zc_avail_out zc < 2 ^ 32 /\ zlength (zc_input zc) < 2 ^ 32 /\ bytes_ok (zc_input zc).
Inductive ireach : inflate_state -> Prop :=
| IR_init : forall zc wb ch s zr,
    ipure (inflateInit2_m ivar_ref hooks_pure zc wb) ch = Some (Some s, zr) -> ireach s
| IR_inflate : forall s zc flush ch s' zr,
    ireach s -> zcall_wf zc -> 0 <= flush < 16 ->
    ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> ireach s'
| IR_setdict : forall s zc dict ch s' zr,
    ireach s -> zstrm_ok (zc_strm zc) -> bytes_ok dict -> 0 < zlength dict < 2 ^ 31 ->
    ipure (inflateSetDictionary_m hooks_pure s zc dict) ch = Some (s', zr) -> ireach s'.

Definition uw_pure (s : inflate_state) (src : arr) (end_ copy : Z) (ch : CH) : option inflate_state :=
  match is_window_blk s with
  | Some _ => Some (updw_core s src end_ copy)
  | None => match ch with
            | None => None
            | Some (b, g) => Some (updw_core (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s)))) src end_ copy)
            end
  end.
Lemma updatewindow_pure : forall s src end_ copy ch,
  updatewindow hooks_pure s src end_ copy ch = MRet (uw_pure s src end_ copy ch, ch).
Proof.
  intros s src end_ copy ch. rewrite updatewindow_unfold. unfold uw_pure.
  destruct (is_window_blk s) as [b|].
  - unfold sbind at 1. unfold sret at 1. cbn [mbind fst snd]. rewrite updw_body_eq. reflexivity.
  - unfold sbind. cbn [zalloc hooks_pure mbind fst snd sret].
    destruct ch as [[b g]|]; cbn [mbind fst snd]; [rewrite updw_body_eq|]; reflexivity.
Qed.

Definition iblocks (st : inflate_state) : list (blk * Z) :=
  match is_window_blk st with Some b => [(b, 2 ^ is_wbits st)] | None => [] end
  ++ [(is_self_blk st, 7176)].  (* zlib 1.4: sizeof(struct inflate_state) *)
