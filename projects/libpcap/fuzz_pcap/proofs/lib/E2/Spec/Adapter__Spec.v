(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec.
From Stdlib Require String Ascii.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt StdioCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Adapter.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section WithCeil.
Context {CE : CEIL}.
Section Adapter.
Context {St ptr : Type}.
Variable amalloc : Z -> M St (option ptr).     (* [comment removed for export] *)
Variable afree : ptr -> M St unit.             (* [comment removed for export] *)
Variable emit_d : Z -> M St unit.              (* [comment removed for export] *)
Variable harness : list Z -> M St Z.           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bad_rc (rc : Z) : bool := negb ((rc =? 0) || (rc =? -1)).
#[using="Type"] Lemma bad_rc_0 : bad_rc 0 = false.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bad_rc_m1 : bad_rc (-1) = false.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bad_rc_step0 : forall bad, (bad || bad_rc 0)%bool = bad.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint call_loop (n : nat) (payload : list Z) (bad : bool) : M St bool :=
  match n with
  | O => mret bad
  | S n' =>
      rc' <- harness payload ;;
      emit_d rc' ;;;
      call_loop n' payload (bad || bad_rc rc')
  end.

Definition target_run (config payload : list Z) : M St Z :=
  let c := match config with [] => 0 | b :: _ => b end in
  let calls := 1 + Z.land c 3 in
  owned <- (if (length payload =? 0)%nat then mret (Some None)
            else q <- amalloc (zlength payload) ;;
                 mret (match q with None => None | Some q' => Some (Some q') end)) ;;
  match owned with
  | None => mret 2                                      (* [comment removed for export] *)
  | Some o =>
      bad <- call_loop (Z.to_nat calls) payload false ;;
      (match o with Some q => afree q | None => mret tt end) ;;;
      mret (if bad then 78 else 0)                     (* [comment removed for export] *)
  end.

End Adapter.

End WithCeil.
End Adapter.

(* [comment removed for export] *)
Module StartupModel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
(* The thread descriptor block: a 4096-byte window starting at the thread pointer minus TP_OFF. It lies in
   musl's builtin_tls object in .bss, at a constant address per build; start-up maps nothing for it. *)
Definition TLS_MAPLEN : Z := 4096.
Definition TP_OFF : Z := 200.

(* The window [tb, tb + TLS_MAPLEN) lies inside one segment reservation of the image. *)
Definition tls_in_image (segs : list Segment) (tb : Z) : Prop :=
  0 < tb /\ exists e, In e (segments_reserved segs)
                      /\ bv_unsigned (fst e) <= tb /\ tb + TLS_MAPLEN <= bv_unsigned (fst e) + bv_unsigned (snd e).

#[using="Type"] Lemma tls_in_image_intro : forall segs tb lo sz,
  0 < tb ->
  In (lo, sz) (map (fun e : word * word => (bv_unsigned (fst e), bv_unsigned (snd e))) (segments_reserved segs)) ->
  lo <= tb -> tb + TLS_MAPLEN <= lo + sz -> tls_in_image segs tb.
Proof.
  intros segs tb lo sz H0 Hin Hlo Hhi. split; [exact H0|].
  apply in_map_iff in Hin. destruct Hin as (e & Ee & He). exists e.
  injection Ee as E1 E2. split; [exact He|]. lia.
Qed.

(* [comment removed for export] *)
Section Startup.
  Context {St : Type} (set_tls : Z -> St -> St).

  Definition startup_model (tb : Z) : M St unit :=
    mupd (set_tls tb) ;;;
    _ <- msys NSetTid dec_set_tid ;;
    mret tt.
End Startup.

(* [comment removed for export] *)
Section Exit.
  Context {St : Type} (stdio_exit_model : M St unit).

  Definition exit_model (code : Z) : M St Empty_set :=
    stdio_exit_model ;;;
    msys (NExit code) dec_exit.
End Exit.

(* [comment removed for export] *)
Section Glue.
  Variable segs : list Segment.
  Context {St : Type}.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_post_evt : forall {A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implM segs c s Q' ms ->
    (forall a s' ms', Q' a s' ms' -> evt segs (Q a s') ms') ->
    implM segs c s Q ms.
  Proof.
    (* [comment removed for export] *)
    intros A c s Q Q' ms H HQ. unfold implM in *. eapply impl_cut; [exact H|].
    intros [|[a s']] ms' Hr; cbn in *; [apply evt_done; exact I|]. apply HQ. exact Hr.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_sys_bind : forall {A B} n (dec : resp -> option A) (f : A -> M St B) s Q ms,
    evt segs (fun ms1 => at_node segs n ms1 /\
                         forall rsp a, dec rsp = Some a -> implM segs (f a) s Q (nret ms1 rsp)) ms ->
    implM segs (mbind (msys n dec) f) s Q ms.
  Proof.
    (* [comment removed for export] *)
    intros A B n dec f s Q ms H. unfold implM, mbind, msys, enode, ebind. cbn [ITree.bind]. apply impl_vis.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. specialize (Hk rsp). destruct (dec rsp) as [a|]; cbn.
    - apply Hk. reflexivity.
    - apply evt_done. exact I.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_upd_bind : forall {B} (f : St -> St) (k : unit -> M St B) s Q ms,
    implM segs (k tt) (f s) Q ms -> implM segs (mbind (mupd f) k) s Q ms.
  Proof. intros. exact H. Qed.

  #[using="Type"] Lemma implM_ret_bind : forall {A B} (a : A) (k : A -> M St B) s Q ms,
    implM segs (k a) s Q ms -> implM segs (mbind (mret a) k) s Q ms.
  Proof. intros. exact H. Qed.
End Glue.

End WithCeil.
End StartupModel.

(* [comment removed for export] *)
Module StdioOld.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section WithCeil.
Context {CE : CEIL}.
Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TIOCGWINSZ : Z := 21523.
Definition STDOUT_BUFSIZ : Z := 1024.   (* [comment removed for export] *)
Definition INTERNAL_BUFSIZ : Z := 80.  (* [comment removed for export] *)

(* [comment removed for export] *)
Record stdout_st := mkStdout {
  so_active : bool;      (* [comment removed for export] *)
  so_buf : list Z;        (* [comment removed for export] *)
  so_lbf_nl : bool;      (* [comment removed for export] *)
  so_first : bool         (* [comment removed for export] *)
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Let M := @M St.
Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

(* [comment removed for export] *)
Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
  _ <- msys (NWritev fd (match buf with [] => [to_bytes s] | _ => [to_bytes buf; to_bytes s] end))
            (dec_writev (zlength buf + zlength s)) ;;
  mret tt.

(* [comment removed for export] *)
Definition stdout_stdio_write (s : list Z) : M unit :=
  so <- rd_so ;;
  stdio_writev 1 (so_buf so) s ;;;
  upd_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

(* [comment removed for export] *)
Definition stdout_writefn (s : list Z) : M unit :=
  so <- rd_so ;;
  (if so_first so then
     upd_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
     r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
     match r with
     | SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
     | SVal _ => munr   (* [comment removed for export] *)
     end
   else mret tt) ;;;
  stdout_stdio_write s.

(* [comment removed for export] *)
Definition after_last_nl (s : list Z) : Z :=
  fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
            (combine (map Z.of_nat (seq 0 (length s))) s) 0.

(* [comment removed for export] *)
Definition stdout_towrite : M unit :=
  upd_so (fun so => if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so)).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Fixpoint out_pieces (ps : list (list Z)) : M unit :=
  match ps with
  | [] => mret tt
  | p :: ps' => stdout_fwritex p ;;; out_pieces ps'
  end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
  stdout_towrite ;;; out_pieces pieces.

(* [comment removed for export] *)
Definition stdout_exit_flush : M unit :=
  so <- rd_so ;;
  if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition stderr_fwrite (s : list Z) : M unit :=
  if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

End Stdio.

(* [comment removed for export] *)
Definition str (s : string) : list Z :=
  map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).

(* [comment removed for export] *)
End WithCeil.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Section WithCeil.
Context {CE : CEIL}.
Definition pieces_emit (s : list Z) : list (list Z) := [ []; []; s; [10] ].
(* [comment removed for export] *)
Definition pieces_usage (argv0 : list Z) : list (list Z) :=
  [ str "usage: "; []; []; argv0; str " INPUT" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_cannot_open (path : list Z) : list (list Z) :=
  [ str "cli: cannot open "; []; []; path; [10] ].
(* [comment removed for export] *)
Definition pieces_read_error (path : list Z) : list (list Z) :=
  [ str "cli: read error on "; []; []; path; [10] ].
(* [comment removed for export] *)
Definition pieces_oom : list (list Z) := [ str "cli: out of memory" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_too_big : list (list Z) :=
  [ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_short_hdr : list (list Z) := [ str "cli: input shorter than header" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_cfg_overrun : list (list Z) := [ str "cli: config_len overruns input" ++ [10] ].

(* [comment removed for export] *)
#[using="Type"] Example pieces_usage_concat :
  concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof. vm_compute. reflexivity. Qed.

End WithCeil.
End StdioOld.

(* [comment removed for export] *)
Module Driver.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section WithCeil.
Context {CE : CEIL}.
Definition MAX_INPUT : Z := 67108864.   (* [comment removed for export] *)
Definition READ_CHUNK : Z := 65536.     (* [comment removed for export] *)
Definition HDR_MIN : Z := 6.
Definition COUNT_MAX : Z := 251.

(* [comment removed for export] *)
Inductive diag_msg : Type :=
| DUsage (argv0 : list Z)
| DCannotOpen (path : list Z)
| DReadError (path : list Z)
| DOom
| DTooBig
| DShortHdr
| DCfgOverrun.

Section Driver.
Context {St ptr : Type}.
Variable diag : diag_msg -> M St unit.         (* [comment removed for export] *)
Variable drv_malloc : Z -> M St (option ptr).  (* [comment removed for export] *)
Variable drv_free : ptr -> M St unit.          (* [comment removed for export] *)
Variable read_stage : Z.                       (* [comment removed for export] *)
Variable run : list Z -> list Z -> M St Z.     (* [comment removed for export] *)

Inductive rd_result : Type :=
| RdExit                                   (* [comment removed for export] *)
| RdDone (buf : ptr) (content : list Z).   (* [comment removed for export] *)

(* [comment removed for export] *)
Record rd_st := mkRd { rd_buf : ptr; rd_cap : Z; rd_len : Z; rd_chunks : list (list Z) }.
Definition rd_content (st : rd_st) : list Z := concat (rd_chunks st).

(* [comment removed for export] *)
Definition read_loop_body (fd : Z) (path : list Z) (st : rd_st) : M St (rd_st + rd_result) :=
  let len := rd_len st in
  (* [comment removed for export] *)
  g <- (if len =? rd_cap st then
          if MAX_INPUT <=? rd_cap st then
            diag DTooBig ;;; mret None
          else
            nb <- drv_malloc (rd_cap st * 2) ;;
            match nb with
            | None => diag DOom ;;; mret None
            | Some nb' => drv_free (rd_buf st) ;;;                 (* [comment removed for export] *)
                          mret (Some (mkRd nb' (rd_cap st * 2) (rd_len st) (rd_chunks st)))
            end
        else mret (Some st)) ;;
  match g with
  | None => mret (inr RdExit)
  | Some st1 =>
      s <- mget ;;                       (* [comment removed for export] *)
      let buf := read_stage in           (* [comment removed for export] *)
      let want := rd_cap st1 - len in
      let want := if READ_CHUNK <? want then READ_CHUNK else want in
      a <- msys (NRead fd buf want) (dec_read buf want) ;;
      match a with
      | RdErr _ => diag (DReadError path) ;;; mret (inr RdExit)
      | RdData bs =>
          if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
          else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (len + zlength bs) (rd_chunks st1 ++ [of_bytes bs])))
      end
  end.

(* [comment removed for export] *)
Definition READ_FUEL : nat := Z.to_nat (MAX_INPUT + 16).

Definition read_all (path : list Z) : M St rd_result :=
  r <- msys (NOpen (to_bytes path)) dec_open ;;
  match r with
  | SErr _ => diag (DCannotOpen path) ;;; mret RdExit
  | SVal fd =>
      b <- drv_malloc 65536 ;;
      match b with
      | None => diag DOom ;;; mret RdExit
      | Some buf =>
          res <- mloop READ_FUEL (read_loop_body fd path) (mkRd buf 65536 0 []) ;;
          match res with
          | RdExit => mret RdExit
          | RdDone buf' content => _ <- msys (NClose fd) dec_close ;; mret (RdDone buf' content)
          end
      end
  end.

Definition le16 (l : list Z) : Z := znth l 0 + znth l 1 * 256.
Definition le32 (l : list Z) : Z := znth l 0 + znth l 1 * 2^8 + znth l 2 * 2^16 + znth l 3 * 2^24.

(* [comment removed for export] *)
Definition main_model (argv : list (list Z)) : M St Z :=
  if negb (Z.of_nat (length argv) =? 2) then
    diag (DUsage (nth 0 argv [])) ;;; mret 2
  else
    ra <- read_all (nth 1 argv []) ;;
    match ra with
    | RdExit => mret 2
    | RdDone buf content =>
        let len := zlength content in
        if len <? HDR_MIN then diag DShortHdr ;;; drv_free buf ;;; mret 2
        else
          let cfg_word := le16 content in
          let count_allocs := Z.testbit cfg_word 15 in
          let config_len := Z.land cfg_word 0x7fff in
          if len <? HDR_MIN + config_len then diag DCfgOverrun ;;; drv_free buf ;;; mret 2
          else
            let config := firstn (Z.to_nat config_len) (skipn 2 content) in
            let payload := skipn (Z.to_nat (6 + config_len)) content in
            (* [comment removed for export] *)
            status <- run config payload ;;
            (* [comment removed for export] *)
            let status' := if count_allocs then 0 else status in
            drv_free buf ;;;
            mret status'
    end.

End Driver.

End WithCeil.
End Driver.
