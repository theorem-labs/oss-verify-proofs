(* fuzz_reply, both ASan builds: THE UNIT'S FRAME-WALK CHAIN, and the bridge from the frame records a Put call's walk
   reads to the premise recorded_at of the depot bound (lib/AsDepotIds.v). Shared by lib/A (asan) and lib/B
   (asan-ubsan); it holds no address of either image. The B cut-free glue (c-frame-reloc, 2026-10-28 12:02Z) will
   import wchain from this file and state over it; a later writer that needs the frame records a walk reads should
   do the same and not define a second predicate for them.

   Checked before defining wchain (2026-10-28): the generated layer lib/{A,B}/FrameAPI.v, lib/{A,B}/Contract.v and
   lib/{A,B}/AsanRT.v has no frame-record or return-address chain. It has the real stack's bounds stklo / stkhi
   (Contract.v:126-129, "the runtime's stack-trace walk reads frame words in [sp, stkhi)") and the thread record's
   stack bounds, top at T + 8 and bottom at T + 16 with 0 <= bottom < top and 4096 <= top <= stkhi (a_laws, AH,
   Contract.v:362-375). Those are the `top` and `bot` of the walk below; 4096 <= top is the premise of
   get_stack_trace_chain.

   The walk is AsTRWalkStop.v's model of UnwindFast (llvmorg-20.1.8 sanitizer_stacktrace.cpp:97-147, RISC-V): the
   loop runs while IsValidFrame(frame, top, bottom), frame mod 8 = 0 and size < max_depth; it reads pc1 = frame[-1],
   stops when pc1 < page size, records pc1 unless pc1 = pc, sets bottom = frame and moves to frame[-2]. A frame
   record is (fp, ra) with ra = the word at fp - 8 and the next frame the word at fp - 16, the convention of the
   released chain (origin/ossv/recipes 754c3cdb4cc, boost-beast lib/As/AsChain.v achain: map snd CH is the return
   addresses). It differs from achain in where it ends: achain ends at cur <= aceil or cur mod 8 <> 0; wchain ends
   where UnwindFast's own test ends the walk (against the moving bottom, see AsTRWalkStop.v), which is what
   wchain_one below uses at a non-stack s0.

   pf_site is the site-table form of the released pf_ok (lib/AsTRRec.v, from AsIface.v:299-316): the same shape and
   the same call rule, with "the trace is a row of the site table" in place of "the trace is allowed by the list".
   The depot bound's premise names rows of TRSITES, so the per-image wiring carries both.

   PREMISE OF THE WALK MODEL: the runtime option fast_unwind_on_malloc is 1, so each allocator wrapper records
   through this fast frame-pointer walk, not libunwind. The start-up certificate states it as rt_fast_unwind, the
   generated lemma that sits next to asan_cf_cells in lib/{A,B}/AsanRT.v from the next start-up regeneration. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AsTRWalkStop AsDepotIds AsTRRec.
Import ListNotations.
Local Open Scope Z_scope.

Section Chain.
  Variable ld : Z -> Z.   (* the 8-byte word UnwindFast loads at an address *)
  Variable pg : Z.        (* GetPageSizeCached() *)
  Variable pc : Z.        (* the frame-0 pc of the walk (a record equal to it is not recorded again) *)
  Variable top : Z.       (* the thread's stack top *)

  (* wchain bot fr CH: from frame fr, with bottom bot, the walk reads the frame records CH and then stops. *)
  Inductive wchain : Z -> Z -> list (Z * Z) -> Prop :=
  | wch_stop : forall bot fr,
      ~ (bot < fr < top - 16 /\ fr mod 8 = 0 /\ pg <= ld (fr - 8)) ->
      wchain bot fr []
  | wch_rec : forall bot fr ra nx CH,
      bot < fr -> fr < top - 16 -> fr mod 8 = 0 ->
      ld (fr - 8) = ra -> pg <= ra -> ra <> pc -> ld (fr - 16) = nx ->
      wchain fr nx CH -> wchain bot fr ((fr, ra) :: CH).

  (* The loop records the return addresses of the chain, cut at the depth limit. *)
  Lemma uwalk_wchain : forall bot fr CH, wchain bot fr CH ->
      forall fuel size maxd, (length CH <= fuel)%nat ->
      uwalk ld pg fuel pc top bot fr size maxd = firstn (maxd - size) (map snd CH).
  Proof.
    induction 1 as [bot fr NV | bot fr ra nx CH Hb Ht Ha Hra Hpg Hne Hnx W IH]; intros fuel size maxd Hf.
    - destruct fuel as [|f]; cbn [uwalk map]; rewrite firstn_nil; [reflexivity|]. unfold is_valid_frame.
      destruct (bot <? fr) eqn:E1; destruct (fr <? top - 16) eqn:E2; destruct (fr mod 8 =? 0) eqn:E3;
        destruct (Nat.ltb size maxd); cbn [andb]; try reflexivity.
      destruct (ld (fr - 8) <? pg) eqn:E5; [reflexivity|]. exfalso. apply NV.
      apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3. apply Z.ltb_ge in E5. lia.
    - destruct fuel as [|f]; [cbn in Hf; lia|]. cbn [length] in Hf. cbn [uwalk map].
      destruct (Nat.ltb size maxd) eqn:E4.
      + apply Nat.ltb_lt in E4. unfold is_valid_frame.
        replace (bot <? fr) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (fr <? top - 16) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (fr mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Ha).
        cbn [andb]. rewrite Hra.
        replace (ra <? pg) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (ra =? pc) with false by (symmetry; apply Z.eqb_neq; exact Hne).
        rewrite Hnx, (IH f (S size) maxd ltac:(lia)).
        replace (maxd - size)%nat with (S (maxd - S size)) by lia. reflexivity.
      + apply Nat.ltb_ge in E4. rewrite andb_false_r. replace (maxd - size)%nat with 0%nat by lia. reflexivity.
  Qed.
End Chain.

(* The walking branch (trace-depth limit above 2) of GET_STACK_TRACE records the frame-0 pc and then the return
   addresses of the chain from the wrapper's frame bp, cut at the limit. A site whose walk stops after the wrapper's
   frame record is the case of a chain of one record (wchain_one below). *)
Lemma get_stack_trace_chain : forall ld pg fuel mcs pcs pcl ra bp top bot CH,
    (2 < mcs)%nat -> 4096 <= top -> wchain ld pg pcl top bot bp CH -> (length CH <= fuel)%nat ->
    get_stack_trace ld pg fuel mcs pcs pcl ra bp top bot = firstn mcs (pcl :: map snd CH).
Proof.
  intros ld pg fuel mcs pcs pcl ra bp top bot CH Hm Htop W Hf. unfold get_stack_trace.
  replace (Nat.leb mcs 2) with false by (symmetry; apply Nat.leb_gt; lia). unfold unwind_fast.
  replace (top <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (uwalk_wchain ld pg pcl top bot bp CH W fuel 1 mcs Hf).
  destruct mcs as [|m]; [lia|]. replace (S m - 1)%nat with m by lia. reflexivity.
Qed.

(* The chain of a site whose walk stops after the wrapper's frame record: the caller's s0 (the word at fr - 16) is not
   an address of the real stack (bot, top). With get_stack_trace_chain, its recorded trace is firstn mcs [pc; ra]. *)
Lemma wchain_one : forall ld pg pc top bot fr ra s0c,
    bot < fr -> fr < top - 16 -> fr mod 8 = 0 -> ld (fr - 8) = ra -> pg <= ra -> ra <> pc ->
    ld (fr - 16) = s0c -> ~ (bot < s0c < top) -> wchain ld pg pc top bot fr [(fr, ra)].
Proof.
  intros ld pg pc top bot fr ra s0c Hb Ht Ha Hra Hpg Hne Hs0 Hns.
  apply (wch_rec ld pg pc top bot fr ra s0c []); try assumption.
  apply wch_stop. intros (H1 & _ & _). apply Hns. lia.
Qed.

(* ---- The site-table form of pf_ok ---- *)

(* Each entry (pc0, p) of the function's table, extended by the function's return address ra and the return
   addresses of the chain CH above it, is the (pc0, return addresses) of a row of the site table. *)
Definition pf_site (SITES : list (Z * Z * list Z)) (PF : list (Z * list Z)) (ra : Z) (CH : list (Z * Z)) : Prop :=
  Forall (fun pp : Z * list Z => exists cpc, In (cpc, fst pp, snd pp ++ ra :: map snd CH) SITES) PF.

Lemma pf_site_call : forall SITES PFf PFg raf fpf CHf site,
    pf_site SITES PFf raf CHf -> incl (pf_shift site PFg) PFf -> pf_site SITES PFg site ((fpf, raf) :: CHf).
Proof.
  intros SITES PFf PFg raf fpf CHf site OK INC. unfold pf_site in *. apply Forall_forall. intros [pc0 p] IN. cbn.
  assert (IN' : In (pc0, p ++ [site]) PFf).
  { apply INC. unfold pf_shift. apply in_map_iff. exists (pc0, p). split; [reflexivity| exact IN]. }
  destruct (proj1 (Forall_forall _ _) OK _ IN') as [cpc T]. cbn in T. rewrite <- app_assoc in T. exists cpc. exact T.
Qed.
Lemma pf_site_site : forall SITES PF ra CH pc0 p,
    pf_site SITES PF ra CH -> In (pc0, p) PF -> exists cpc, In (cpc, pc0, p ++ ra :: map snd CH) SITES.
Proof. intros SITES PF ra CH pc0 p OK IN. exact (proj1 (Forall_forall _ _) OK _ IN). Qed.
Lemma pf_site_incl : forall SITES PF PF' ra CH, pf_site SITES PF ra CH -> incl PF' PF -> pf_site SITES PF' ra CH.
Proof. intros SITES PF PF' ra CH OK INC. apply Forall_forall. intros pp IN. exact (proj1 (Forall_forall _ _) OK _ (INC _ IN)). Qed.

(* With the trace_ok body for every row (sites_ok, which trace_list_a.v / trace_list_b.v prove as TRSITES_ok),
   pf_site gives the released pf_ok. *)
Lemma pf_ok_of_pf_site : forall TRL SITES PF ra CH,
    sites_ok TRL SITES -> pf_site SITES PF ra CH -> pf_ok TRL PF ra CH.
Proof.
  intros TRL SITES PF ra CH OKS PS. unfold pf_ok. apply Forall_forall. intros [pc0 p] IN.
  destruct (pf_site_site SITES PF ra CH pc0 p PS IN) as [cpc INS]. cbn [fst snd].
  exact (proj1 (Forall_forall _ _) OKS _ INS).
Qed.

(* A boolean check of pf_site with an empty chain, closed by vm_compute on concrete tables. *)
Definition pf_siteb0 (SITES : list (Z * Z * list Z)) (PF : list (Z * list Z)) (ra : Z) : bool :=
  forallb (fun pp : Z * list Z =>
             existsb (fun s : Z * Z * list Z => Z.eqb (snd (fst s)) (fst pp) && list_eqb (snd s) (snd pp ++ [ra])) SITES)
          PF.
Lemma pf_siteb0_sound : forall SITES PF ra, pf_siteb0 SITES PF ra = true -> pf_site SITES PF ra [].
Proof.
  intros SITES PF ra H. unfold pf_siteb0 in H. unfold pf_site. apply Forall_forall. intros pp IN.
  pose proof (proj1 (forallb_forall _ _) H pp IN) as Hp. apply existsb_exists in Hp as ([[cpc pc0] ras] & INS & E).
  cbn [fst snd] in E. apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply list_eqb_eq in E2.
  exists cpc. cbn [map]. rewrite <- E1, <- E2. exact INS.
Qed.

(* ---- A run's Put calls and the depot bound's premise ---- *)

(* One Put call of the run, through an allocator wrapper: the words the walk loads in the state of the call, the
   wrapper's two frame-0 pcs (short and walking branch), its return address (GET_CALLER_PC), its frame
   (GET_CURRENT_FRAME), and the thread's stack top and bottom. *)
Record put_call := PutCall {
  pt_ld : Z -> Z; pt_pcs : Z; pt_pcl : Z; pt_ra : Z; pt_bp : Z; pt_top : Z; pt_bot : Z }.

(* The trace the call records (AsTRWalkStop.get_stack_trace) under page size pg, loop bound fuel and limit mcs. *)
Definition put_trace (pg : Z) (fuel : nat) (mcs : nat) (c : put_call) : list Z :=
  get_stack_trace (pt_ld c) pg fuel mcs (pt_pcs c) (pt_pcl c) (pt_ra c) (pt_bp c) (pt_top c) (pt_bot c).

(* The per-call premise: the stack top is at least 4096 and the walk from the wrapper's frame reads a chain CH whose
   return addresses, after the walking frame-0 pc, make a row of the site table. *)
Definition walk_at_row (SITES : list (Z * Z * list Z)) (pg : Z) (fuel : nat) (c : put_call) : Prop :=
  4096 <= pt_top c /\
  exists cpc CH, In (cpc, pt_pcl c, map snd CH) SITES
    /\ wchain (pt_ld c) pg (pt_pcl c) (pt_top c) (pt_bot c) (pt_bp c) CH /\ (length CH <= fuel)%nat.

Lemma put_trace_row : forall SITES pg fuel mcs c, (2 < mcs)%nat -> walk_at_row SITES pg fuel c ->
    exists s, In s SITES /\ put_trace pg fuel mcs c = site_trace mcs s.
Proof.
  intros SITES pg fuel mcs c Hm (Htop & cpc & CH & IN & W & Hf). exists (cpc, pt_pcl c, map snd CH).
  split; [exact IN|]. unfold put_trace, site_trace. cbn [fst snd]. exact (get_stack_trace_chain _ _ _ _ _ _ _ _ _ _ _ Hm Htop W Hf).
Qed.

(* The bridge: a run whose Put calls each satisfy walk_at_row records traces that are rows of the site table. *)
Theorem recorded_at_of_walks : forall SITES pg fuel mcs (cs : list put_call),
    (2 < mcs)%nat -> Forall (walk_at_row SITES pg fuel) cs -> recorded_at SITES mcs (map (put_trace pg fuel mcs) cs).
Proof.
  intros SITES pg fuel mcs cs Hm F. unfold recorded_at. apply Forall_map.
  eapply Forall_impl; [|exact F]. intros c Hc. cbv beta. right. exact (put_trace_row SITES pg fuel mcs c Hm Hc).
Qed.

(* The released route's form (boost-beast AS_InstChain.v fch_of_achain, second part): when the chain's trace is
   allowed by a list, the recorded trace is in the list. *)
Lemma put_trace_in : forall TRL pg fuel mcs c CH,
    (2 < mcs)%nat -> 4096 <= pt_top c -> wchain (pt_ld c) pg (pt_pcl c) (pt_top c) (pt_bot c) (pt_bp c) CH ->
    (length CH <= fuel)%nat -> trace_ok TRL (pt_pcl c) (map snd CH) -> In (put_trace pg fuel mcs c) TRL.
Proof.
  intros TRL pg fuel mcs c CH Hm Htop W Hf [_ OK]. unfold put_trace.
  rewrite (get_stack_trace_chain _ _ _ _ _ _ _ _ _ _ _ Hm Htop W Hf). apply OK. lia.
Qed.

(* How a call site discharges walk_at_row from the wiring: the caller's function has pf_site for its table PF with
   its return address ra and the chain CH above it; the call's entry (pc0, p) is in PF; the walk reads the wrapper's
   record and the caller's records, whose return addresses are p ++ ra :: map snd CH. *)
Lemma walk_at_row_of_pf_site : forall SITES PF ra CH pc0 p pg fuel c CHw,
    pf_site SITES PF ra CH -> In (pc0, p) PF -> pt_pcl c = pc0 -> 4096 <= pt_top c ->
    wchain (pt_ld c) pg (pt_pcl c) (pt_top c) (pt_bot c) (pt_bp c) CHw ->
    map snd CHw = p ++ ra :: map snd CH -> (length CHw <= fuel)%nat ->
    walk_at_row SITES pg fuel c.
Proof.
  intros SITES PF ra CH pc0 p pg fuel c CHw PS IN Hpc Htop W Hm Hf.
  destruct (pf_site_site SITES PF ra CH pc0 p PS IN) as [cpc INS].
  split; [exact Htop|]. exists cpc, CHw. rewrite Hpc, Hm. split; [exact INS|]. rewrite <- Hpc. split; assumption.
Qed.

(* The same for a site whose walk stops after the wrapper's frame record (the one-return-address rows). *)
Lemma walk_at_row_one : forall SITES pg fuel c cpc s0c,
    In (cpc, pt_pcl c, [pt_ra c]) SITES -> (1 <= fuel)%nat -> 4096 <= pt_top c ->
    pt_bot c < pt_bp c -> pt_bp c < pt_top c - 16 -> pt_bp c mod 8 = 0 ->
    pt_ld c (pt_bp c - 8) = pt_ra c -> pg <= pt_ra c -> pt_ra c <> pt_pcl c ->
    pt_ld c (pt_bp c - 16) = s0c -> ~ (pt_bot c < s0c < pt_top c) ->
    walk_at_row SITES pg fuel c.
Proof.
  intros SITES pg fuel c cpc s0c IN Hf Htop Hb Ht Ha Hra Hpg Hne Hs0 Hns.
  split; [exact Htop|]. exists cpc, [(pt_bp c, pt_ra c)]. cbn [map length snd]. split; [exact IN|].
  split; [| lia]. exact (wchain_one _ _ _ _ _ _ _ s0c Hb Ht Ha Hra Hpg Hne Hs0 Hns).
Qed.
