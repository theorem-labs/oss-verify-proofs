(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate HarnessSmall. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateRel RefUpdWin1 RefInflate_runA InflateCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition no_window (s : inflate_state) : bool := match is_window_blk s with Some _ => false | None => true end.

(* [comment removed for export] *)
Definition leave_res (ans : option (ZProg.blk * (Z -> Z))) (flush : Z) (w : iw) : inflate_state * ZRet * bool :=
  let S0 := s_rest (w_s w) (w_r w) in let C0 := c_rest (w_c w) (w_r w) in let r := w_r w in
  let s1 := fst (lv_pre S0 C0 r) in let c1 := snd (lv_pre S0 C0 r) in
  let o := wrap32 (ir_out r - ic_avail_out C0) in
  let rc := ret_model flush (wrap32 (ir_in r - ic_avail_in C0)) o r in
  if lv_cond flush S0 C0 r then
    match uw_pure s1 (ic_outbuf C0) (ic_next_out C0) o ans with
    | None => (lv_mem S0 C0 r, no_window s1)
    | Some s2 => ((s2, zret_of_icall c1 rc), no_window s1)
    end
  else ((s1, zret_of_icall c1 rc), false).

Lemma inflate_p_shape : forall ans s zc flush, inflateStateCheck s = false ->
  inflate_p ans s zc flush
  = (let '(stop, w) := inf_loop ivar_ref flush (W0 s zc) in
     match stop with
     | SRet rc => ((w_s w, zret_of_icall (w_c w) rc), false)
     | SLeave => leave_res ans flush w
     end).
Proof.
  intros ans s zc flush Hc. unfold inflate_p. rewrite (inflate_m_W0 dhooks) by exact Hc.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct stop as [|rc].
  - rewrite inf_leave_eq0. unfold leave_res, sbind. cbn [w_s w_c w_r].
    destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
    + rewrite updatewindow_dh. cbn [mbind fst snd]. unfold no_window.
      destruct (uw_pure (fst (lv_pre (s_rest s' r') (c_rest c' r') r')) _ _ _ ans) as [s2|];
        destruct (is_window_blk (fst (lv_pre (s_rest s' r') (c_rest c' r') r'))); unfold sret; cbn [fst snd]; reflexivity.
    + unfold sret. cbn [mbind fst snd]. reflexivity.
  - unfold sret. cbn [fst snd]. reflexivity.
Qed.
