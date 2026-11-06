(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition halveF (usage : word) : nat -> word -> word :=
  fix halve (k : nat) (a3 : word) : word :=
    match k with O => a3 | S k' =>
      if negb (is0 (v_andi a3 1)) then a3
      else if negb (c_ltu usage (v_slliw a3 2)) then a3
      else halve k' (v_srliw a3 1)
    end.

(* [comment removed for export] *)
Definition shrinkF (size : word) : nat -> word -> word :=
  fix shrink (k : nat) (a2 : word) : word :=
    match k with O => a2 | S k' =>
      if is0 (v_srli (v_mul size a2) 20) then a2
      else shrink k' (v_srliw a2 1)
    end.

(* [comment removed for export] *)
Definition zlF (size : word) : nat -> word -> M unit :=
  fix zl (k : nat) (a2 : word) : M unit :=
    match k with O => mret tt | S k' => m_sb a2 w0 ;; zl k' (v_add a2 size) end.

Lemma halveF_S : forall usage k a3,
  halveF usage (S k) a3 =
  (if negb (is0 (v_andi a3 1)) then a3
   else if negb (c_ltu usage (v_slliw a3 2)) then a3
   else halveF usage k (v_srliw a3 1)).
Proof. reflexivity. Qed.
Lemma halveF_O : forall usage a3, halveF usage O a3 = a3.
Proof. reflexivity. Qed.
Lemma shrinkF_S : forall size k a2,
  shrinkF size (S k) a2 = (if is0 (v_srli (v_mul size a2) 20) then a2 else shrinkF size k (v_srliw a2 1)).
Proof. reflexivity. Qed.
Lemma shrinkF_O : forall size a2, shrinkF size O a2 = a2.
Proof. reflexivity. Qed.
Lemma zlF_S : forall size k a2, zlF size (S k) a2 = (m_sb a2 w0 ;; zlF size k (v_add a2 size)).
Proof. reflexivity. Qed.
Lemma zlF_O : forall size a2, zlF size O a2 = mret tt.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mlet {A B : Type} (x : A) (f : A -> M B) : M B := f x.

Lemma mlet_eq {A B} : forall (x : A) (f : A -> M B), mlet x f = f x.
Proof. reflexivity. Qed.

Lemma mbind_mlet {A B C} : forall (x : A) (f : A -> M B) (k : B -> M C) s,
  MallocTree.mbind (mlet x f) k s = mlet x (fun y => MallocTree.mbind (f y) k) s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition as_actg (m3 : word) : M (option (word * word)) :=
  mp3 <- m_ld (at_ m3 16) ;;
  ab <- m_lbu (at_ mp3 8) ;;
  let act2 := v_sllw (wlit 2) ab in
  massert (is0 (v_andi (at_ m3 28) 3)) ;;
  fr4 <- m_lw (at_ m3 28) ;;
  m_sw (at_ m3 28) (v_and fr4 (v_subw w0 act2)) ;;
  let mask := v_and fr4 (v_addiw act2 (-1)) in
  m_sw (at_ m3 24) mask ;;
  massert (negb (is0 mask)) ;;
  w32 <- m_lw (at_ m3 32) ;;
  let d := v_addi (v_srli (v_slli w32 52) 58) (-7) in
  (if c_ltu (wlit 31) d then mret tt
   else b <- m_lbu (at_ (v_add A_LOCK d) 888) ;;
        if is0 b then mret tt
        else m_sb (at_ (v_add A_LOCK d) 888) (v_addi b (-1))) ;;
  mret (Some (m3, mask)).

(* [comment removed for export] *)
Definition as_tav (pm m0 : word) : M (option (word * word)) :=
  if is0 m0 then mret None
  else
    am <- m_lw (at_ m0 24) ;;
    if negb (is0 am) then mret (Some (m0, am))
    else
      fr <- m_lw (at_ m0 28) ;;
      nx <- m_ld (at_ m0 8) ;;
      mo <- (if negb (is0 fr)
             then m_sd pm nx ;; mret (Some nx)
             else
               (if c_eq nx m0 then m_sd pm w0
                else pv <- m_ld m0 ;;
                     m_sd (at_ pv 8) nx ;;
                     pv2 <- m_ld m0 ;;
                     nx2 <- m_ld (at_ m0 8) ;;
                     m_sd nx2 pv2 ;;
                     h <- m_ld pm ;;
                     if c_eq h m0 then n3 <- m_ld (at_ m0 8) ;; m_sd pm n3
                     else mret tt) ;;
               m_sd m0 w0 ;; m_sd (at_ m0 8) w0 ;;
               m1 <- m_ld pm ;;
               if is0 m1 then mret None else mret (Some m1)) ;;
      match mo with
      | None => mret None
      | Some m =>
        fr1 <- m_lw (at_ m 28) ;;
        w <- m_ld (at_ m 32) ;;
        mf <- (if negb (is0 (v_andi w 32))
                  && c_eq fr1 (v_addiw (v_sllw (wlit 2) w) (-1))
               then m' <- m_ld (at_ m 8) ;;
                    m_sd pm m' ;;
                    fr' <- m_lw (at_ m' 28) ;;
                    mret (m', fr')
               else mret (m, fr1)) ;;
        let '(m2, fr2) := mf in
        mp <- m_ld (at_ m2 16) ;;
        ai <- m_lbu (at_ mp 8) ;;
        let act := v_addiw (v_sllw (wlit 2) ai) (-1) in
        m3o <- (if negb (is0 (v_and act fr2)) then mret (Some m2)
                else nx3 <- m_ld (at_ m2 8) ;;
                     if negb (c_eq nx3 m2)
                     then m_sd pm nx3 ;; mret (Some nx3)
                     else
                       let a5 := v_andi ai 31 in
                       w5 <- m_ld (at_ m2 32) ;;
                       szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w5 5) 126)) ;;
                       let a6 := v_addi a5 2 in
                       let a4 := v_addi a5 1 in
                       let t0 := v_addi (v_slli a5 4) 48 in
                       let size := v_slli szc 4 in
                       let a7 := v_mul t0 szc in
                       let t0' := v_mul size a6 in
                       let a6' := v_addiw a7 15 in
                       let t0'' := v_addiw t0' 16 in
                       match m_span_loop 40 a6' t0'' a4 size with
                       | None => mcrash
                       | Some cnt =>
                         let lim := v_addi (v_andi w5 31) 1 in
                         let cnt' := if c_ltu cnt lim then cnt else lim in
                         m_sb (at_ mp 8) (v_or (v_andi (v_addi cnt' (-1)) 31) (v_andi ai 224)) ;;
                         mret (Some m2)
                       end) ;;
        match m3o with
        | None => mret None
        | Some m3 =>
          am3 <- m_lw (at_ m3 24) ;; massert (is0 am3) ;;
          as_actg m3
        end
      end.

(* [comment removed for export] *)
Definition as_take (m mask : word) : M word :=
  let first := v_and mask (v_subw w0 mask) in
  m_sw (at_ m 24) (v_subw mask first) ;;
  if is0 first then mcrash
  else m_ctz32 mask.

(* [comment removed for export] *)
Definition as_cnt (sc usage size : word) : M word :=
  if negb (c_lts (wlit 8) sc)
  then let tb := v_add A_SMALL_CNT_TAB (v_add (v_slli sc 1) sc) in
       t0 <- m_lbu tb ;;
       if negb (c_ltu usage (v_slli t0 2)) then mret t0
       else t1 <- m_lbu (at_ tb 1) ;;
            if negb (c_ltu usage (v_slli t1 2)) then mret t1
            else m_lbu (at_ tb 2)
  else t <- m_lbu (v_add A_MED_CNT_TAB (v_andi sc 3)) ;;
       mret (shrinkF size 40 (halveF usage 8 t)).

(* [comment removed for export] *)
Definition as_fail (m : word) : M word :=
  m_free_meta_ag (at_ A_LOCK 24) m ;;
  mret wm1.

(* [comment removed for export] *)
Definition as_tail (s7 pm sc m p cnt aidx c1 : word) : M word :=
  us2 <- m_ld (at_ s7 472) ;;
  m_sd (at_ s7 472) (v_add us2 cnt) ;;
  m_sw (at_ m 24) (v_addi (v_sllw (wlit 2) aidx) (-1)) ;;
  am <- m_lw (at_ m 24) ;;
  m_sw (at_ m 28) (v_add (v_sllw (wlit 2) c1) (v_xori am (-1))) ;;
  m_sd (at_ m 16) p ;;
  m_sd p m ;;
  mp <- m_ld (at_ m 16) ;;
  ab <- m_lbu (at_ mp 8) ;;
  m_sb (at_ mp 8) (v_or (v_andi ab 224) (v_andi aidx 31)) ;;
  wm2 <- m_ld (at_ m 32) ;;
  m_sd (at_ m 32) (v_addi (v_or (v_or (v_srli (v_slli sc 58) 52) (v_andi c1 31))
                                (v_and wm2 PAGEMASK)) 32) ;;
  am2 <- m_lw (at_ m 24) ;;
  m_sw (at_ m 24) (v_addi am2 (-1)) ;;
  nx <- m_ld (at_ m 8) ;; massert (is0 nx) ;;
  pv <- m_ld m ;; massert (is0 pv) ;;
  hd <- m_ld pm ;;
  (if is0 hd then m_sd m m ;; m_sd (at_ m 8) m ;; m_sd pm m
   else m_sd (at_ m 8) hd ;; hp <- m_ld hd ;; m_sd m hp ;;
        m_sd (at_ hp 8) m ;; n2 <- m_ld (at_ m 8) ;; m_sd n2 m) ;;
  mret w0.

(* [comment removed for export] *)
Definition as_nested (fuel' : nat) (sp s7 pm sc m size cnt1 a4 : word) : M word :=
  let a1 := v_addi a4 12 in
  let n16 := v_srli a4 4 in
  j <- (if c_ltu a1 (wlit 157) then mret n16
        else m_size_to_class_big A_SIZE_CLASSES n16) ;;
  let j' := v_addiw j 0 in
  idx <- m_alloc_slot fuel' (at_ sp (-144)) j' a1 ;;
  if c_lts idx w0 then as_fail m
  else
    szj <- m_lhu (v_add A_SIZE_CLASSES (v_slli j' 1)) ;;
    gj <- m_ld (at_ (v_add A_LOCK (v_slli j' 3)) 88) ;;
    ctr <- m_lw (at_ A_LOCK 20) ;;
    p <- m_enframe gj idx (v_addi (v_slli szj 4) (-4)) ctr ;;
    wm <- m_ld (at_ m 32) ;;
    m_sd (at_ m 32) (v_srli (v_slli wm 52) 52) ;;
    c3 <- m_lbu (at_ p (-3)) ;;
    m_sb (at_ p (-3)) (v_addi (v_andi c3 31) 192) ;;
    zlF size (S (Z.to_nat (bv_unsigned cnt1))) (at_ p 12) ;;
    as_tail s7 pm sc m p cnt1 (v_addi cnt1 (-1)) (v_addi cnt1 (-1)).

(* [comment removed for export] *)
Definition as_bn (sc : word) : M (bool * option word) :=
  let d := v_addiw sc (-7) in
  if c_ltu (wlit 31) d then mret (false, None)
  else let a5 := v_add A_LOCK d in
       b <- m_lbu (at_ a5 888) ;;
       us <- m_lbu (at_ a5 856) ;;
       let nosmall := negb (c_ltu b (wlit 100)) in
       (if is0 us then mret tt
        else sq <- m_lbu (at_ A_LOCK 920) ;;
             if c_lts (wlit 9) (v_sub sq us) then mret tt
             else if c_ltu b (wlit 99) then m_sb (at_ a5 888) (v_addi b 1)
             else m_sb (at_ a5 888) (wlit 150)) ;;
       mret (nosmall, Some a5).

(* [comment removed for export] *)
Definition as_mm2 (s7 pm sc req m size usage pg cnt1 a4 : word) (nosmall : bool) (sq : word) : M word :=
    sq' <- (if c_eq sq (wlit 255)
            then m_sd (at_ A_LOCK 856) w0 ;; m_sd (at_ A_LOCK 864) w0 ;;
                 m_sd (at_ A_LOCK 872) w0 ;; m_sd (at_ A_LOCK 880) w0 ;; mret (wlit 1)
            else mret (v_addi sq 1)) ;;
    m_sb (at_ A_LOCK 920) sq' ;;
    usage2 <- (if c_lts (wlit 31) sc then mret usage
               else if negb (is0 (v_andi sc 1)) then mret usage
               else u1 <- m_ld (at_ s7 480) ;; mret (v_add u1 usage)) ;;
    mlet (
      if negb (c_ltu usage2 (v_slliw cnt1 2)) then cnt1
      else if nosmall then cnt1
      else let a5 := v_andi sc 3 in
           let a6 := v_slli pg 3 in
           if c_eq a5 (wlit 1) && c_ltu a6 a4 then wlit 2
           else if c_eq a5 (wlit 2) && c_ltu (v_slli pg 2) a4 then wlit 3
           else if is0 a5 && c_ltu a6 a4 then wlit 3
           else if is0 a5 && c_ltu (v_slli pg 1) a4 then wlit 5
           else cnt1) (fun cnt2 =>
    let needed0 := v_mul size cnt2 in
    mlet (v_addi (v_add needed0 (v_and (v_sub (wlit (2^64 - 16)) needed0) (v_addi pg (-1)))) 16) (fun needed =>
    mlet (
      if nosmall then (cnt2, needed)
      else if c_ltu (wlit 7) cnt2 then (cnt2, needed)
      else let r := v_addi (v_add req (v_and (v_addi pg (-1)) (v_sub (wlit (2^64 - 20)) req))) 20 in
           if c_ltu r (v_addi size 16) then (wlit 1, r)
           else if c_ltu r (v_slli pg 2) then (cnt2, needed)
           else if c_ltu usage2 (v_slliw cnt2 1) then (wlit 1, r)
           else (cnt2, needed)) (fun cn =>
    let '(cnt3, needed3) := cn in
    p <- sys_mmap MMrw needed3 ;;
    if c_eq p wm1 then as_fail m
    else
      wm <- m_ld (at_ m 32) ;;
      let aimax := v_divu (wlit 4080) size in
      ctr <- m_lw (at_ A_LOCK 20) ;;
      m_sd (at_ m 32) (v_or (v_srli (v_slli wm 52) 52) (v_and needed3 PAGEMASK)) ;;
      m_sw (at_ A_LOCK 20) (v_addi ctr 1) ;;
      mlet (if c_ltu cnt3 aimax then cnt3 else aimax) (fun a2 =>
      let aidx := v_and (v_addi (v_sltu a2 (v_addi a2 (-1))) (-1)) (v_addi a2 (-1)) in
      as_tail s7 pm sc m p cnt3 aidx (v_addi cnt3 (-1)))))).

(* [comment removed for export] *)
Definition as_mmapg (s7 pm sc req m size usage pg cnt1 a4 : word) : M word :=
  bn <- as_bn sc ;;
  let '(nosmall, _) := bn in
  sq <- m_lbu (at_ A_LOCK 920) ;;
  as_mm2 s7 pm sc req m size usage pg cnt1 a4 nosmall sq.

(* [comment removed for export] *)
Definition as_group (fuel' : nat) (sp s7 pm sc req : word) : M word :=
  szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;
  m <- m_alloc_meta (at_ sp (-64)) ;;
  if is0 m then mret wm1
  else
  usage <- m_ld (at_ s7 472) ;;
  pg <- m_ld A_PAGE_SIZE ;;
  let size := v_slli szc 4 in
  cnt <- as_cnt sc usage size ;;
  let half := v_srli pg 1 in
  mlet (if c_eq cnt (wlit 1)
        then v_subw (wlit 2) (v_sltu half (v_addi size 16))
        else cnt) (fun cnt1 =>
  let a4 := v_mul size cnt1 in
  if negb (c_ltu half (v_addi a4 16))
  then as_nested fuel' sp s7 pm sc m size cnt1 a4
  else as_mmapg s7 pm sc req m size usage pg cnt1 a4).

(* [comment removed for export] *)
Definition as_res (fuel' : nat) (sp s7 pm sc req : word) : M word :=
  m0 <- m_ld pm ;;
  ta <- as_tav pm m0 ;;
  match ta with
  | Some (m, mask) => as_take m mask
  | None => as_group fuel' sp s7 pm sc req
  end.

Lemma m_alloc_slot_pieces : forall fuel' sp sc req,
  m_alloc_slot (S fuel') sp sc req =
  (cc <- m_canary_load ;;
   let '(gp, cg) := cc in
   let s7 := v_add A_LOCK (v_slli sc 3) in
   let pm := at_ s7 88 in
   res <- as_res fuel' sp s7 pm sc req ;;
   m_canary_check gp cg ;;
   mret res).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_newarea (pagesize : word) : M (option (word * bool)) :=
  sh <- m_ld A_META_SHIFT ;;
  let n := v_sll (wlit 2) sh in
  p <- sys_mmap MMnone (v_mul n pagesize) ;;
  if c_eq p wm1 then MallocTree.mret None
  else sh2 <- m_ld A_META_SHIFT ;;
       m_sd A_AVAIL_AREA_CNT (v_mul (v_addi n (-1)) (v_srli pagesize 12)) ;;
       m_sd A_META_SHIFT (v_addi sh2 1) ;;
       m_sd A_AVAIL_AREAS (v_add p pagesize) ;;
       MallocTree.mret (Some (v_add p pagesize, true)).

(* [comment removed for export] *)
Definition am_brk (pagesize cb : word) : M (option (word * bool)) :=
  if c_eq cb wm1 then MallocTree.mret None
  else if negb (is0 cb)
  then let new := v_add cb pagesize in
       r <- sys_brk_grow new ;;
       MallocTree.mret (Some (new, c_eq r new))
  else r0 <- sys_brk_query ;;
       let al := v_add (v_and (v_addi pagesize (-1)) (v_sub MallocOps.w0 r0)) r0 in
       m_sd A_BRK al ;;
       let new := v_add al (v_slli pagesize 1) in
       r <- sys_brk_grow new ;;
       (if c_eq r new
        then b <- m_ld A_BRK ;;
             g <- sys_mmap_fixed_none b pagesize ;;
             MallocTree.mret (Some (new, true))
        else MallocTree.mret (Some (new, false))).

(* [comment removed for export] *)
Definition am_areas (pagesize aac2 : word) : M (option (word * bool)) :=
  if negb (is0 aac2) then p <- m_ld A_AVAIL_AREAS ;; MallocTree.mret (Some (p, true))
  else am_newarea pagesize.

(* [comment removed for export] *)
Definition am_prov (pagesize aac : word) : M (option (word * bool)) :=
  if negb (is0 aac)
  then p <- m_ld A_AVAIL_AREAS ;; MallocTree.mret (Some (p, true))
  else
    cb <- m_ld A_BRK ;;
    br <- am_brk pagesize cb ;;
    match br with
    | Some (new, true) =>
        m_sd A_BRK new ;;
        m_sd A_AVAIL_AREA_CNT (v_srli pagesize 12) ;;
        MallocTree.mret (Some (v_sub new pagesize, false))
    | _ =>
        aac2 <- (match br with
                 | Some _ => a <- m_ld A_AVAIL_AREA_CNT ;; m_sd A_BRK wm1 ;; MallocTree.mret a
                 | None => MallocTree.mret aac end) ;;
        am_areas pagesize aac2
    end.

(* [comment removed for export] *)
Definition am_tail (p : word) : M word :=
    aac3 <- m_ld A_AVAIL_AREA_CNT ;;
    tl <- m_ld A_AREA_TAIL ;;
    m_sd A_AVAIL_AREA_CNT (v_addi aac3 (-1)) ;;
    m_sd A_AVAIL_AREAS (v_add p (wlit 4096)) ;;
    (if is0 tl then m_sd A_AREA_HEAD p
     else m_sd (at_ tl 8) p) ;;
    sec <- m_ld A_CTX ;;
    m_sd A_AREA_TAIL p ;;
    m_sd p sec ;;
    t1 <- m_ld A_AREA_TAIL ;;
    m_sw (at_ t1 16) (wlit 101) ;;
    t2 <- m_ld A_AREA_TAIL ;;
    let m := at_ t2 24 in
    m_sd A_AVAIL_META (at_ m 40) ;;
    m_sd A_AVAIL_META_CNT (wlit 100) ;;
    m_sd (at_ m 8) MallocOps.w0 ;; m_sd m MallocOps.w0 ;;
    MallocTree.mret m.

(* [comment removed for export] *)
Definition am_okc (pagesize p : word) (test : bool) : M bool :=
  if test && is0 (v_and (v_addi pagesize (-1)) p)
  then pg2 <- m_ld A_PAGE_SIZE ;;
       massert (c_eq pg2 (wlit 4096)) ;;
       r <- sys_mprotect_rw p pagesize ;;
       if is0 r then MallocTree.mret true
       else e <- m_lw A_ERRNO ;; MallocTree.mret (c_eq e (wlit 38))
  else MallocTree.mret true.

Definition am_some (pagesize p : word) (test : bool) : M word :=
  ok <- am_okc pagesize p test ;;
  if negb ok then MallocTree.mret MallocOps.w0
  else am_tail p.

(* [comment removed for export] *)
Definition am_res (pagesize : word) : M word :=
  fmh <- m_ld A_FREE_META_HEAD ;;
  if negb (is0 fmh) then
    let m := fmh in
    nx <- m_ld (at_ m 8) ;;
    (if c_eq nx m then m_sd A_FREE_META_HEAD MallocOps.w0
     else pv <- m_ld m ;;
          m_sd (at_ pv 8) nx ;;
          pv2 <- m_ld m ;;
          nx2 <- m_ld (at_ m 8) ;;
          m_sd nx2 pv2 ;;
          h <- m_ld A_FREE_META_HEAD ;;
          if c_eq h m then n3 <- m_ld (at_ m 8) ;; m_sd A_FREE_META_HEAD n3
          else MallocTree.mret tt) ;;
    m_sd (at_ m 8) MallocOps.w0 ;; m_sd m MallocOps.w0 ;;
    MallocTree.mret m
  else
  amc <- m_ld A_AVAIL_META_CNT ;;
  if negb (is0 amc) then
    m <- m_ld A_AVAIL_META ;;
    m_sd A_AVAIL_META (at_ m 40) ;;
    m_sd A_AVAIL_META_CNT (v_addi amc (-1)) ;;
    m_sd (at_ m 8) MallocOps.w0 ;; m_sd m MallocOps.w0 ;;
    MallocTree.mret m
  else
  aac <- m_ld A_AVAIL_AREA_CNT ;;
  r <- am_prov pagesize aac ;;
  match r with
  | None => MallocTree.mret MallocOps.w0
  | Some (p, test) => am_some pagesize p test
  end.

(* [comment removed for export] *)
Definition am_init (sp : word) : M unit :=
  auxv <- m_ld (at_ A_LIBC 8) ;;
  let s0 := v_mul sp (wlit 0x41c64e6d) in
  sec <- m_scan_auxv AUXV_FUEL auxv MallocOps.w0 s0 ;;
  m_sd A_CTX sec ;;
  m_sw A_INIT_DONE (wlit 1).

Lemma m_alloc_meta_pieces : forall sp,
  m_alloc_meta sp =
  (cc <- m_canary_load ;;
   let '(gp, cg) := cc in
   ini <- m_lw A_INIT_DONE ;;
   (if negb (is0 ini) then MallocTree.mret tt else am_init sp) ;;
   pg <- m_ld (at_ A_LIBC 48) ;;
   massert (c_eq pg (wlit 4096)) ;;
   let pagesize := if c_ltu (wlit 4096) pg then pg else wlit 4096 in
   res <- am_res pagesize ;;
   m_canary_check gp cg ;;
   MallocTree.mret res).
Proof. intros sp. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aslot_at {fx : FPState} (fuel : nat) : Prop :=
  forall md regs mm rom (s : mstate) (sc req sp ret : word)
         (P : word -> mstate -> Prop) (L : word -> mstate -> TSet),
  md_pure md -> ms_vm s = m_vmmaps md -> magree s mm ->
  getr regs 2 = sp -> bv_unsigned sp mod 16 = 0 ->
  0 <= ms_lo s -> ms_lo s <= bv_unsigned sp - alloc_slot_D fuel -> bv_unsigned sp <= ms_hi s -> ms_hi s <= 2^64 ->
  wtop s ->
  (forall a, bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = A_TP ->
  getr regs 10 = sc -> getr regs 11 = req ->
  tsafe (m_alloc_slot fuel (at_ sp (-144)) sc req s) P ->
  (forall r s' mm' regs',
     P r s' -> magree s' mm' -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
     alloc_top (ms_vm s') = alloc_top (ms_vm s) ->
     getr regs' 10 = r -> getr regs' 2 = sp ->
     (forall x, callee_saved x -> getr regs' x = getr regs x) ->
     (forall a, ms_lo s <= bv_unsigned a < ms_hi s ->
                ~ (bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - alloc_slot_D fuel <= bv_unsigned a < bv_unsigned sp -> mm' a <> None) ->
     realizes ml_segs (mkCfg (mkst regs' ret mm' rom) (with_vmmaps (ms_vm s') md)) (L r s')) ->
  realizes ml_segs (mkCfg (mkst regs PC_ALLOC_SLOT mm rom) md)
           (tshape (m_alloc_slot fuel (at_ sp (-144)) sc req s) L).

Lemma alloc_slot_stmt_of_at {fx : FPState} : (forall fuel, aslot_at fuel) -> alloc_slot_stmt.
Proof. intros H md regs mm rom s fuel. intros; eapply (H fuel md regs mm rom s); eassumption. Qed.

Lemma alloc_slot_D_S : forall f, alloc_slot_D (S f) = alloc_slot_D f + 144.
Proof. intros f. unfold alloc_slot_D. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma alloc_slot_D_ge : forall f, 144 <= alloc_slot_D f.
Proof. intros f. unfold alloc_slot_D. lia. Qed.

End WithLayout.
