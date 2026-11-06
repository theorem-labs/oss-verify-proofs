(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad STree Malloc.
From Stdlib Require NArith Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AllocBridge.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad STree Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Class AllocSt (St : Type) := mkAllocSt {
  ps_rest_t : Type;
  ps_m : St -> mstate;                  (* [comment removed for export] *)
  ps_brk : St -> Z;                     (* [comment removed for export] *)
  ps_rest : St -> ps_rest_t;            (* [comment removed for export] *)
  set_m : mstate -> St -> St;
  set_brk_ps : Z -> St -> St;
  ps_m_set_m : forall v s, ps_m (set_m v s) = v;
  ps_brk_set_m : forall v s, ps_brk (set_m v s) = ps_brk s;
  ps_rest_set_m : forall v s, ps_rest (set_m v s) = ps_rest s;
  ps_m_set_brk : forall v s, ps_m (set_brk_ps v s) = ps_m s;
  ps_brk_set_brk : forall v s, ps_brk (set_brk_ps v s) = v;
  ps_rest_set_brk : forall v s, ps_rest (set_brk_ps v s) = ps_rest s
}.
End WithCeil.


#[export] Hint Rewrite @ps_m_set_m @ps_brk_set_m @ps_rest_set_m @ps_m_set_brk @ps_brk_set_brk @ps_rest_set_brk : alloc_lens.

Section WithCeil.
Context {CE : CEIL}.
Section Bridge.
Context {St : Type} {AS : AllocSt St}.

Local Notation MP := (Monad.M St).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition neg_errno (e : Z) : Z := 2^64 - e.

Definition MAP_FIXED_Z : Z := 16.

(* [comment removed for export] *)
Inductive fixed_ans : Type := FxKept (e : Z) | FxDone | FxLost (e : Z).
Definition dec_mmap_fixed (addr len : Z) (rsp : resp) : option fixed_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (FxKept e) | None => None end
  | mkEffectU r [] [] [(a, n)] [] [] =>
      if bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len)) then
        match errno_of r with
        | Some e => Some (FxLost e)
        | None => if bv_eqb r (Z_to_bv 64 addr) then Some FxDone else None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition dec_mprotect_rw (addr len : Z) (rsp : resp) : option range_ans :=
  match dec_mprotect addr len rsp with
  | Some (RgErr e) => if e =? ENOSYS then None else Some (RgErr e)
  | Some (RgDone true) => Some (RgDone true)
  | _ => None
  end.

(* [comment removed for export] *)
Definition mremap_val (old : Z) (x : mremap_ans) : Z :=
  match x with MrErr e => neg_errno e | MrSame => old | MrMoved a => a end.

(* [comment removed for export] *)
Definition ev_step (e : ev) : MP Z :=
  match e with
  | EBrk req =>
      if req =? 0 then
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
      else
        (s <- mget ;;
         a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with
         | BrkGrown => mupd (set_brk_ps req) ;;; mret req
         | BrkSame => mret (ps_brk s)
         end)
  | EMmap addr len prot flags =>
      if negb (Z.land flags MAP_FIXED_Z =? 0) then
        (a <- msys (NMmap addr len prot flags) (dec_mmap_fixed addr len) ;;
         mret match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end)
      else if prot =? 0 then
        (a <- msys (NMmap addr len prot flags) (dec_mmap_none len []) ;;
         mret match a with MmErr e => neg_errno e | MmOk x => x end)
      else
        (a <- msys (NMmap addr len prot flags) (dec_mmap len []) ;;
         mret match a with MmErr e => neg_errno e | MmOk x => x end)
  | EMunmap addr len =>
      a <- msys (NMunmap addr len) (dec_munmap addr len) ;;
      mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
  | EMprotect addr len prot =>
      a <- msys (NMprotect addr len prot) (dec_mprotect_rw addr len) ;;
      mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
  | EPeek _ _ _ => munr      (* [comment removed for export] *)
  | EUndef _ => munr         (* [comment removed for export] *)
  | EMremap old oldlen newlen =>                                            (* [comment removed for export] *)
      a <- msys (NMremap old oldlen newlen) (dec_mremap old oldlen newlen [] []) ;;
      mret (mremap_val old a)
  end.

Fixpoint membed {R} (t : stree ev Z R) : MP R :=
  match t with
  | SRet r => mret r
  | SVis e k => z <- ev_step e ;; membed (k z)
  end.

(* [comment removed for export] *)
Definition bptr : Type := (cptr * Z)%type.

Definition fresh_off (cs : mstate) (slot : cptr) (n : Z) : Z :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      fold_off (Z.land (c_mmap_counter (s_ctx cs)) 255) ((get_stride mr - IB - n) / UNIT)
  | None => 0
  end.

Definition raw_malloc (n : Z) : MP (option bptr) :=
  s <- mget ;;
  '(st', p) <- membed (cmalloc (ps_m s) n) ;;
  mupd (set_m st') ;;;
  mret (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end).
Definition raw_free (p : bptr) : MP unit :=
  s <- mget ;;
  st' <- membed (cfree (ps_m s) (Some (fst p))) ;;
  mupd (set_m st').

(* [comment removed for export] *)
Definition ptr_addr (s : St) (p : bptr) : Z := conc (ps_m s) (fst p) + UNIT * snd p.

End Bridge.

Definition reservedZ (segs : list Segment) : list (Z * Z) :=
  map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved segs).

End WithCeil.
End AllocBridge.

(* [comment removed for export] *)
Module KArith.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
#[using="Type"] Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

#[using="Type"] Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

#[using="Type"] Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

#[using="Type"] Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.

#[using="Type"] Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. pose proof (Z.land_nonneg (-x) (PGSZ - 1)). unfold PGSZ in *. lia. Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

#[using="Type"] Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

#[using="Type"] Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

#[using="Type"] Lemma mmap_len_rup : forall l, mmap_len l = round_up_pg l.
Proof. intros l. unfold mmap_len. symmetry. apply round_up_pg_eq. Qed.

#[using="Type"] Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
  intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l).
  pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.

#[using="Type"] Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. exact alloc_ceiling_lt63. Qed.   (* [comment removed for export] *)
(* [comment removed for export] *)

End WithCeil.
End KArith.

(* [comment removed for export] *)
Module KLink.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition BLIVE : Z := 2^30.
Definition RMAX : Z := 2^28.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

(* [comment removed for export] *)
Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

(* [comment removed for export] *)
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 \/ b0 + l0 <= b.

(* [comment removed for export] *)
Definition pin_clear (L : mled) (e : word * word) : Prop :=
  (forall b l, ld_brkreg L = Some (b, l) -> b + l <= elo e \/ ehi e <= b)
  /\ (forall cur, ld_brk L = BPGuard cur -> cur + 2 * PGSZ <= elo e \/ ehi e <= cur).

(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  (* [comment removed for export] *)
  kl_resv : forall r, In r (ld_resv L) ->
      exists e, elo e <= fst r /\ fst r + snd r <= ehi e /\
        (In e (vm_reserved (m_vmmaps mo))
         \/ (In e (vm_maps (m_vmmaps mo)) /\ pin_clear L e
             /\ forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
                   b + mmap_len l <= elo e \/ ehi e <= b));
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps (m_vmmaps mo)) b (b + l);   (* [comment removed for export] *)
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  kl_gran : forall e, In e (vm_maps (m_vmmaps mo)) ->
      ehi e <= bv_unsigned (vm_brk (m_vmmaps mo))
      \/ (0 < bv_unsigned (snd e) /\ bv_unsigned (snd e) mod PGSZ = 0 /\ elo e mod PGSZ = 0);
  (* [comment removed for export] *)
  kl_brk_base : forall b l, ld_brkreg L = Some (b, l) -> b = bv_unsigned (vm_start_brk (m_vmmaps mo));
  (* [comment removed for export] *)
  kl_brk_hi : bv_unsigned (vm_brk (m_vmmaps mo)) <=
      bv_unsigned (vm_start_brk (m_vmmaps mo)) + 2 * PGSZ + match ld_brkreg L with Some (_, l) => l | None => 0 end;
  (* [comment removed for export] *)
  kl_static : bv_unsigned (vm_start_brk (m_vmmaps mo)) + 2 * PGSZ + BLIVE <= bottomup_floor
      /\ BLIVE + RMAX <= vm_limit (m_vmmaps mo);
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  kl_grp_resv : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
      forall e, In e (vm_reserved (m_vmmaps mo)) -> b + mmap_len l <= elo e \/ ehi e <= b;
  (* [comment removed for export] *)
  kl_noacc : forall e, In e (vm_noaccess (m_vmmaps mo)) ->
      (exists b l k, In (b, l, k) (ld_metas L) /\ b <= elo e /\ ehi e <= b + mmap_len l)
      \/ (exists b0 l0, ld_brkreg L = Some (b0, l0) /\ b0 <= elo e /\ ehi e <= b0 + PGSZ);
  (* [comment removed for export] *)
  kl_top : alloc_ceiling = page_round_down_Z (alloc_top (m_vmmaps mo)) }.

Section PS.
Context {St : Type} {AS : AllocSt St}.

(* [comment removed for export] *)
Definition frame_ok (G : St -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_rest s' = ps_rest s -> vm_only mo mo' -> G s mo -> G s' mo'.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : St -> Model -> Prop) (s0 : St)
  : Z -> St -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_rest s = ps_rest s0.

End PS.

(* [comment removed for export] *)

End WithCeil.
End KLink.
