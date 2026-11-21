(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState Mem Exec ITree Nodes Decode.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Mem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Exec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad.

Module Relim.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState ITree Nodes Decode.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition relim_h (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition relim (L : Z) (mo : Model) : Model := with_vmmaps (relim_h L (m_vmmaps mo)) mo.

Lemma alloc_top_relim : forall L h, alloc_top (relim_h L h) = alloc_top h.
Proof. reflexivity. Qed.

Definition vm_clean (mo : Model) : Prop := m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

Lemma minv_clean : forall mo, minv mo -> vm_clean mo.
Proof. intros mo H. split; [apply minv_lazy| apply minv_materialized]; exact H. Qed.

Lemma relim_with_vmmaps : forall L h mo, relim L (with_vmmaps h mo) = with_vmmaps (relim_h L h) (relim L mo).
Proof. intros L h [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_with_fds : forall L f mo, relim L (with_fds f mo) = with_fds f (relim L mo).
Proof. intros L f [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_with_tid : forall L t mo, relim L (with_tid t mo) = with_tid t (relim L mo).
Proof. intros L t [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_with_halted : forall L c mo, relim L (with_halted c mo) = with_halted c (relim L mo).
Proof. intros L c [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_vm_forget_range : forall L lo hi mo, relim L (vm_forget_range lo hi mo) = vm_forget_range lo hi (relim L mo).
Proof. intros L lo hi [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma relim_forget_vm_ranges : forall L rs mo, relim L (forget_vm_ranges rs mo) = forget_vm_ranges rs (relim L mo).
Proof. induction rs as [|[a n] rs IH]; intros mo; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH, relim_vm_forget_range. reflexivity. Qed.
Lemma m_fds_relim : forall L mo, m_fds (relim L mo) = m_fds mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_fs_relim : forall L mo, m_fs (relim L mo) = m_fs mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_tid_relim : forall L mo, m_tid (relim L mo) = m_tid mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_vmmaps_relim : forall L mo, m_vmmaps (relim L mo) = relim_h L (m_vmmaps mo). Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_vmmaps_with_vmmaps : forall h mo, m_vmmaps (with_vmmaps h mo) = h. Proof. reflexivity. Qed.
Lemma m_vmmaps_with_mmap_backing : forall flags a n mo, m_vmmaps (with_mmap_backing flags a n mo) = m_vmmaps mo.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma m_vm_lazy_relim : forall L mo, m_vm_lazy (relim L mo) = m_vm_lazy mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma m_vm_materialized_relim : forall L mo, m_vm_materialized (relim L mo) = m_vm_materialized mo. Proof. intros L [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma with_vmmaps_relim : forall L h mo, with_vmmaps h (relim L mo) = with_vmmaps h mo.
Proof. intros L h [fd [mp lz mt] io fs pr lm tm]; reflexivity. Qed.
Lemma vm_live_bytes_relim : forall L h, vm_live_bytes (relim_h L h) = vm_live_bytes h. Proof. reflexivity. Qed.
Lemma vm_backed_maps_relim : forall L h, vm_backed_maps (relim_h L h) = vm_backed_maps h. Proof. reflexivity. Qed.
Lemma vm_backing_used_relim : forall L mo, vm_backing_used (relim L mo) = vm_backing_used mo.
Proof. intros L mo. unfold vm_backing_used. rewrite m_vmmaps_relim, vm_backed_maps_relim, m_vm_lazy_relim, m_vm_materialized_relim. reflexivity. Qed.
Lemma vm_backing_used_with_vmmaps_relim : forall L h mo,
  vm_backing_used (with_vmmaps h (relim L mo)) = vm_backing_used (with_vmmaps h mo).
Proof. intros. rewrite with_vmmaps_relim. reflexivity. Qed.
Lemma relim_with_mmap_backing : forall L flags a n mo,
  relim L (with_mmap_backing flags a n mo) = with_mmap_backing flags a n (relim L mo).
Proof.
  intros L flags a n mo. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [|reflexivity].
  unfold vm_add_lazy. destruct mo as [fd [mp lz mt] io fs pr lm tm]; reflexivity.
Qed.
Lemma relim_with_mmap_destroyed : forall L a n h mo,
  relim L (with_mmap_destroyed a n h mo) = with_mmap_destroyed a n (relim_h L h) (relim L mo).
Proof. intros. unfold with_mmap_destroyed. rewrite relim_vm_forget_range, relim_with_vmmaps. reflexivity. Qed.
Lemma relim_with_mmap_replacement : forall L flags a n mo,
  relim L (with_mmap_replacement flags a n mo) = with_mmap_replacement flags a n (relim L mo).
Proof. intros. unfold with_mmap_replacement. rewrite relim_with_mmap_backing, relim_vm_forget_range. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app live_bytes];
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64).
  - rewrite !Z.mod_small by lia. lia.
  - pose proof (Z.mod_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) (2^64) ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) (2^64) ltac:(lia) ltac:(lia)). lia.
  - lia.
Qed.

Lemma live_bytes_maps_subtract : forall maps lo hi, lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn [maps_subtract live_bytes]; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all : forall cuts maps, live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn [maps_subtract_all]; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma vm_backing_used_clean : forall mo, vm_clean mo ->
  vm_backing_used mo = live_bytes (vm_backed_maps (m_vmmaps mo)).
Proof.
  intros mo [Hl Hm]. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat]. lia.
Qed.

Lemma vm_backing_used_le_live' : forall mo, m_vm_materialized mo = [] ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo Hm. unfold vm_backing_used. rewrite Hm. cbn [length Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r.
  unfold vm_backed_maps, vm_live_bytes.
  etransitivity; [apply live_bytes_maps_subtract_all|]. apply live_bytes_maps_subtract_all.
Qed.

Lemma vm_backing_used_le_live : forall mo, vm_clean mo ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof. intros mo [_ Hm]. apply vm_backing_used_le_live'. exact Hm. Qed.

Lemma vm_clean_with_vmmaps : forall h mo, vm_clean mo -> vm_clean (with_vmmaps h mo).
Proof. intros h mo [A B]. split; assumption. Qed.


Lemma page_round_up_Z_nonneg : forall x, 0 <= x -> 0 <= page_round_up_Z x.
Proof. intros x Hx. unfold page_round_up_Z. change page_size with 4096. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. Qed.

Lemma vm_clean_mprotect_model_next : forall m a n, vm_clean m -> vm_clean (mprotect_model_next m a n).
Proof. intros m a n Hc. unfold mprotect_model_next. apply vm_clean_with_vmmaps. exact Hc. Qed.


Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
  end.


Definition nstep_lim (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ vm_live_bytes (m_vmmaps mo') <= B.

Lemma tpath_lim : forall {R} B (t : itree node R) mo tr r mo',
  tlive B t mo -> (tpath (nstep_lim B) t mo tr r mo' <-> tpath nstep t mo tr r mo').
Proof.
  intros R B t. induction t as [x|n k IH]; intros mo tr r mo' Hl; cbn [tpath]; [tauto|].
  cbn [tlive] in Hl. split.
  - intros (rsp & mo1 & evs & tr' & [Hst Hb] & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [|reflexivity].
    apply (IH rsp); [exact (proj2 (Hl _ _ _ Hst))| exact Hp].
  - intros (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp, mo1, evs, tr'. destruct (Hl _ _ _ Hst) as [Hb Hl'].
    split; [split; assumption|]. split; [|reflexivity]. apply IH; assumption.
Qed.

Lemma texit_lim : forall {R} B (t : itree node R) mo tr,
  tlive B t mo -> (texit (nstep_lim B) nexit t mo tr <-> texit nstep nexit t mo tr).
Proof.
  intros R B t. induction t as [x|n k IH]; intros mo tr Hl; cbn [texit]; [tauto|].
  cbn [tlive] in Hl. split.
  - intros [H|(rsp & mo1 & evs & tr' & [Hst Hb] & Hx & ->)]; [left; exact H| right]. exists rsp, mo1, evs, tr'.
    split; [exact Hst|]. split; [|reflexivity]. apply (IH rsp); [exact (proj2 (Hl _ _ _ Hst))| exact Hx].
  - intros [H|(rsp & mo1 & evs & tr' & Hst & Hx & ->)]; [left; exact H| right]. exists rsp, mo1, evs, tr'. destruct (Hl _ _ _ Hst) as [Hb Hl'].
    split; [split; assumption|]. split; [|reflexivity]. apply IH; assumption.
Qed.

Lemma ttrace_lim : forall {R} B (t : itree node R) mo tr,
  tlive B t mo -> (ttrace (nstep_lim B) nexit t mo tr <-> ttrace nstep nexit t mo tr).
Proof.
  intros R B t mo tr Hl. rewrite !ttrace_split. rewrite (texit_lim B t mo tr Hl). split.
  - intros [H|(r & mo' & Hp)]; [left; exact H| right]. exists r, mo'. apply (tpath_lim B t mo tr r mo' Hl). exact Hp.
  - intros [H|(r & mo' & Hp)]; [left; exact H| right]. exists r, mo'. apply (tpath_lim B t mo tr r mo' Hl). exact Hp.
Qed.

Lemma tlive_mono : forall {R} B B' (t : itree node R) mo, B <= B' -> tlive B t mo -> tlive B' t mo.
Proof.
  intros R B B' t. induction t as [x|n k IH]; intros mo HB Hl; cbn [tlive] in *; [exact I|].
  intros rsp mo' evs Hst. destruct (Hl _ _ _ Hst) as [Hb Hl']. split; [lia|]. apply IH; assumption.
Qed.
End Relim.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TIOCGWINSZ : Z := 21523.
Definition STDOUT_BUFSIZ : Z := 1024.
Definition INTERNAL_BUFSIZ : Z := 80.

Record stdout_st := mkStdout {
  so_active : bool;
  so_buf : list Z;
  so_lbf_nl : bool;
  so_first : bool
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.


Definition iov_total (iovs : list (list Z)) : Z := zlength (concat iovs).

Definition iov_start (buf s : list Z) : list (list Z) :=
  match buf with [] => [s] | _ => [buf; s] end.

Definition iov_advance (iovs : list (list Z)) (cnt : Z) : list (list Z) :=
  match iovs with
  | [] => []
  | a :: rest =>
      if zlength a <? cnt
      then match rest with
           | [] => []
           | b :: rest' => zdrop (cnt - zlength a) b :: rest'
           end
      else zdrop cnt a :: rest
  end.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Let M := @M St.
Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

Definition wv_body (fd : Z) (iovs : list (list Z)) : M (list (list Z) + unit) :=
  k <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (iov_total iovs)) ;;
  if k =? iov_total iovs then mret (inr tt)
  else mret (inl (iov_advance iovs k)).

Definition WV_FUEL (iovs : list (list Z)) : nat := S (Z.to_nat (iov_total iovs)).

Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
  mloop (WV_FUEL (iov_start buf s)) (wv_body fd) (iov_start buf s).

Definition stdout_stdio_write (s : list Z) : M unit :=
  so <- rd_so ;;
  stdio_writev 1 (so_buf so) s ;;;
  upd_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_writefn (s : list Z) : M unit :=
  so <- rd_so ;;
  (if so_first so then
     upd_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
     r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
     match r with
     | SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
     | SVal _ => munr
     end
   else mret tt) ;;;
  stdout_stdio_write s.

Definition after_last_nl (s : list Z) : Z :=
  fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
            (combine (map Z.of_nat (seq 0 (length s))) s) 0.

Definition stdout_towrite : M unit :=
  upd_so (fun so => if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_fwritex (s : list Z) : M unit :=
  stdout_towrite ;;;
  so <- rd_so ;;
  if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s
  then stdout_writefn s
  else if so_lbf_nl so then
    let i := after_last_nl s in
    (if 0 <? i then stdout_writefn (firstn (Z.to_nat i) s) else mret tt) ;;;
    upd_so (fun so => mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
  else
    upd_so (fun so => mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

Fixpoint out_pieces (ps : list (list Z)) : M unit :=
  match ps with
  | [] => mret tt
  | p :: ps' => stdout_fwritex p ;;; out_pieces ps'
  end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
  stdout_towrite ;;; out_pieces pieces.

Definition stdout_exit_flush : M unit :=
  so <- rd_so ;;
  if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

Fixpoint stderr_pieces (buf : list Z) (ps : list (list Z)) : M (list Z) :=
  match ps with
  | [] => mret buf
  | p :: ps' =>
      if INTERNAL_BUFSIZ - zlength buf <? zlength p
      then (stdio_writev 2 buf p ;;; stderr_pieces [] ps')
      else stderr_pieces (buf ++ p) ps'
  end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
  buf <- stderr_pieces [] pieces ;;
  stdio_writev 2 buf [].

Definition stderr_fwrite (s : list Z) : M unit :=
  if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

End Stdio.


Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Definition pieces_emit_0 : list (list Z) := [ []; []; [48]; []; [10] ].
Definition pieces_usage (argv0 : list Z) : list (list Z) :=
  [ str "usage: "; []; []; argv0; str " INPUT" ++ [10] ].
Definition pieces_cannot_open (path : list Z) : list (list Z) :=
  [ str "cli: cannot open "; []; []; path; [10] ].
Definition pieces_read_error (path : list Z) : list (list Z) :=
  [ str "cli: read error on "; []; []; path; [10] ].
Definition pieces_oom : list (list Z) := [ str "cli: out of memory" ++ [10] ].
Definition pieces_too_big : list (list Z) :=
  [ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ].
Definition pieces_short_hdr : list (list Z) := [ str "cli: input shorter than header" ++ [10] ].
Definition pieces_cfg_overrun : list (list Z) := [ str "cli: config_len overruns input" ++ [10] ].
Definition pieces_precond_fail (x fn : list Z) : list (list Z) :=
  [ str "p11-kit: '"; []; []; x; str "' not true at "; []; []; fn; [10] ].
Definition pieces_precond_reached (fn : list Z) : list (list Z) :=
  [ str "p11-kit: shouldn't be reached at "; []; []; fn; [10] ].

Example pieces_usage_concat :
  concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_precond_concat :
  concat (pieces_precond_fail (str "lexer->filename != NULL") (str "p11_lexer_init"))
  = str "p11-kit: 'lexer->filename != NULL' not true at p11_lexer_init" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex1 : iov_advance [[48]; [10]] 1 = [[]; [10]].
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex2 : iov_advance [[48;48]; [10;10]] 3 = [[10]].
Proof. vm_compute. reflexivity. Qed.
