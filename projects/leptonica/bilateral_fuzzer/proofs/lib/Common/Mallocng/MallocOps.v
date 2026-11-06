(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wlit (z : Z) : word := Z_to_bv 64 z.
Definition w0 : word := Z_to_bv 64 0.
Definition wm1 : word := Z_to_bv 64 (2^64 - 1).        (* [comment removed for export] *)
Definition PAGEMASK : word := Z_to_bv 64 (2^64 - 4096). (* [comment removed for export] *)

Section WithLayout.
Context {ML : MallocLayout}.

Definition DEBRUIJN_MULT     : word := wlit 0x77cb531.
Definition MMAP_THRESHOLD_W  : word := wlit 131052.

Definition is0 (v : word) : bool := c_eq v w0.

(* [comment removed for export] *)
Definition v_divu (x y : word) : word :=
  if (bv_unsigned y =? 0) then wm1 else Z_to_bv 64 (bv_unsigned x / bv_unsigned y).

(* [comment removed for export] *)
Definition m_ctz32 (x : word) : M word :=
  m_lbu (v_add A_DEBRUIJN (v_srliw (v_mul (v_and x (v_subw w0 x)) DEBRUIJN_MULT) 27)).

(* [comment removed for export] *)
Definition m_size_to_class_big (tbl n : word) : M word :=
  let a0 := v_addi n 1 in
  let a2 := v_or (v_srliw a0 2) a0 in
  let a0' := v_srliw a0 1 in
  let a2' := v_or a2 a0' in
  let a2'' := v_srliw a2' 2 in
  let x := v_or a2'' a0' in
  let x1 := v_or (v_srli x 4) x in
  let x2 := v_or (v_srli x1 8) x1 in
  let x3 := v_or (v_srli (v_slli x2 33) 49) x2 in
  let y := v_and (v_addi x3 1) (v_xori x3 (-1)) in
  d <- m_lbu (v_add A_DEBRUIJN (v_srliw (v_mul y DEBRUIJN_MULT) 27)) ;;
  let t := v_xori (v_slli d 2) 124 in
  let i1 := v_sub (wlit 121) t in                                  (* [comment removed for export] *)
  c1 <- m_lhu (v_add tbl (v_slli i1 1)) ;;                          (* [comment removed for export] *)
  (if c_ltu n c1
   then (* [comment removed for export] *)
        let i := v_sub (wlit 120) t in
        c0 <- m_lhu (v_add tbl (v_slli i 1)) ;;
        mret (v_or i (v_xori (v_sltu n c0) 1))
   else let i := v_sub (wlit 122) t in
        c0 <- m_lhu (v_add tbl (v_slli i 1)) ;;
        mret (v_or i (v_xori (v_sltu n c0) 1))).

(* [comment removed for export] *)
Definition m_unlock : M unit :=
  lk <- m_lw A_LOCK ;; massert (negb (c_lts lk w0)).

(* [comment removed for export] *)
Definition m_canary_load : M (word * word) :=
  gp <- m_ld A_GOT_SSP ;; cg <- m_ld gp ;; mret (gp, cg).
Definition m_canary_check (gp cg : word) : M unit :=
  cg2 <- m_ld gp ;; massert (c_eq cg2 cg).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition m_get_meta (p : word) : M word :=
  massert (is0 (v_andi p 15)) ;;                                  (* [comment removed for export] *)
  c4 <- m_lbu (at_ p (-4)) ;;                                     (* [comment removed for export] *)
  c3 <- m_lbu (at_ p (-3)) ;;                                     (* [comment removed for export] *)
  o16 <- m_lhu (at_ p (-2)) ;;                                    (* [comment removed for export] *)
  off <- (if is0 c4 then mret o16                                 (* [comment removed for export] *)
          else massert (is0 o16) ;;                               (* [comment removed for export] *)
               o32 <- m_lwu (at_ p (-8)) ;;                        (* [comment removed for export] *)
               massert (negb (is0 (v_srli o32 16))) ;;             (* [comment removed for export] *)
               mret o32) ;;
  let a2 := v_sub p (v_slli off 4) in                             (* [comment removed for export] *)
  meta <- m_ld (at_ a2 (-16)) ;;                                  (* [comment removed for export] *)
  mm <- m_ld (at_ meta 16) ;;                                     (* [comment removed for export] *)
  let idx := v_andi c3 31 in                                      (* [comment removed for export] *)
  massert (c_eq mm (at_ a2 (-16))) ;;                             (* [comment removed for export] *)
  w <- m_ld (at_ meta 32) ;;                                      (* [comment removed for export] *)
  massert (negb (c_ltu (v_andi w 31) idx)) ;;                     (* [comment removed for export] *)
  av <- m_lw (at_ meta 24) ;;                                     (* [comment removed for export] *)
  let bit := v_sllw (wlit 1) idx in                               (* [comment removed for export] *)
  massert (is0 (v_and av bit)) ;;                                 (* [comment removed for export] *)
  fr <- m_lw (at_ meta 28) ;;                                     (* [comment removed for export] *)
  massert (is0 (v_and fr bit)) ;;                                 (* [comment removed for export] *)
  chk <- m_ld (v_and meta PAGEMASK) ;;                            (* [comment removed for export] *)
  sec <- m_ld A_CTX ;;                                            (* [comment removed for export] *)
  massert (c_eq chk sec) ;;                                       (* [comment removed for export] *)
  let sc := v_srli (v_slli w 52) 58 in                            (* [comment removed for export] *)
  (if c_ltu (wlit 47) sc                                          (* [comment removed for export] *)
   then massert (c_eq sc (wlit 63))                               (* [comment removed for export] *)
   else szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;      (* [comment removed for export] *)
        massert (negb (c_ltu off (v_mul szc idx))) ;;              (* [comment removed for export] *)
        massert (c_ltu off (v_mul (v_addi idx 1) szc))) ;;          (* [comment removed for export] *)
  let maplen := v_srli w 12 in                                    (* [comment removed for export] *)
  (if is0 maplen then mret tt
   else massert (negb (c_ltu (v_addi (v_slli maplen 8) (-1)) off))) ;;  (* [comment removed for export] *)
  mret meta.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition m_free_meta (hd_addr g : word) : M unit :=
  m_sd (at_ g 8) w0 ;; m_sd g w0 ;; m_sd (at_ g 16) w0 ;; m_sd (at_ g 24) w0 ;; m_sd (at_ g 32) w0 ;;
  nx <- m_ld (at_ g 8) ;; massert (is0 nx) ;;
  pv <- m_ld g ;; massert (is0 pv) ;;
  hd <- m_ld hd_addr ;;
  (if is0 hd
   then m_sd g g ;; m_sd (at_ g 8) g ;; m_sd hd_addr g
   else m_sd (at_ g 8) hd ;;
        hp <- m_ld hd ;;
        m_sd g hp ;;
        m_sd (at_ hp 8) g ;;
        n2 <- m_ld (at_ g 8) ;;
        m_sd n2 g).

(* [comment removed for export] *)
Definition m_free_meta_ag (hd_addr g : word) : M unit :=
  m_sd (at_ g 8) w0 ;; m_sd (at_ g 32) w0 ;; m_sd (at_ g 24) w0 ;; m_sd (at_ g 16) w0 ;; m_sd g w0 ;;
  nx <- m_ld (at_ g 8) ;; massert (is0 nx) ;;
  pv <- m_ld g ;; massert (is0 pv) ;;
  hd <- m_ld hd_addr ;;
  (if is0 hd
   then m_sd g g ;; m_sd (at_ g 8) g ;; m_sd hd_addr g
   else m_sd (at_ g 8) hd ;;
        hp <- m_ld hd ;;
        m_sd g hp ;;
        m_sd (at_ hp 8) g ;;
        n2 <- m_ld (at_ g 8) ;;
        m_sd n2 g).

(* [comment removed for export] *)
Definition m_seq_next (ctx : word) : M word :=
  sq <- m_lbu (at_ ctx 912) ;;                                    (* [comment removed for export] *)
  (if c_eq sq (wlit 255)                                          (* [comment removed for export] *)
   then m_sd (at_ ctx 848) w0 ;; m_sd (at_ ctx 856) w0 ;;         (* [comment removed for export] *)
        m_sd (at_ ctx 864) w0 ;; m_sd (at_ ctx 872) w0 ;;
        mret (wlit 1)
   else mret (v_addi sq 1)).

Fixpoint m_nontrivial_free (fuel : nat) (g i : word) : M (word * word) :=
  match fuel with
  | O => mcrash
  | S fuel' =>
  cc <- m_canary_load ;;                                          (* [comment removed for export] *)
  let '(gp, cg) := cc in
  w <- m_ld (at_ g 32) ;;                                         (* [comment removed for export] *)
  fr <- m_lw (at_ g 28) ;;                                        (* [comment removed for export] *)
  av <- m_lw (at_ g 24) ;;                                        (* [comment removed for export] *)
  let self := v_sllw (wlit 1) i in                                (* [comment removed for export] *)
  let mask := v_or av fr in                                       (* [comment removed for export] *)
  let sc := v_srli (v_slli w 52) 58 in                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  ok <- (if is0 (v_andi w 32) then mret false                      (* [comment removed for export] *)
         else if negb (c_eq (v_addw mask self)
                              (v_addiw (v_sllw (wlit 2) w) (-1)))   (* [comment removed for export] *)
         then mret false
         else if c_ltu (wlit 47) sc then mret true                  (* [comment removed for export] *)
         else
           let last := v_andi w 31 in                               (* [comment removed for export] *)
           let maplen := v_srli w 12 in                             (* [comment removed for export] *)
           (* [comment removed for export] *)
           stride_small <-
             (if negb (is0 maplen) && is0 last
              then (* [comment removed for export] *)                     (* [comment removed for export] *)
                   szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;  (* [comment removed for export] *)
                   mret (c_ltu (v_addi (v_and w PAGEMASK) (-16)) (v_slli szc 4))
              else scs <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w 5) 126)) ;;  (* [comment removed for export] *)
                   if is0 maplen then mret true (* [comment removed for export] *)  (* [comment removed for export] *)
                   else szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;
                        mret (c_ltu (v_slli scs 4) (v_slli szc 4))) ;;
           if stride_small then mret true
           else if is0 maplen then mret true
           else
             nx <- m_ld (at_ g 8) ;;                                (* [comment removed for export] *)
             if negb (c_eq nx g) then mret true                     (* [comment removed for export] *)
             else if c_ltu (wlit 31) (v_addi sc (-7)) then mret true (* [comment removed for export] *)
             else b <- m_lbu (at_ (v_add A_CTX (v_addi sc (-7))) 880) ;;  (* [comment removed for export] *)
                  if c_ltu b (wlit 100) then mret true                (* [comment removed for export] *)
                  else us <- m_ld (at_ (v_add A_CTX (v_slli sc 3)) 464) ;;  (* [comment removed for export] *)
                       if c_ltu us (v_addi (v_add (v_slli last 3) last) 9)  (* [comment removed for export] *)
                       then mret false
                       else if c_ltu (wlit 18) last then mret false   (* [comment removed for export] *)
                       else mret true) ;;
  res <- (if ok then
    (* [comment removed for export] *)
    nx <- m_ld (at_ g 8) ;;                                         (* [comment removed for export] *)
    (if is0 nx then mret tt                                         (* [comment removed for export] *)
     else
       massert (c_ltu sc (wlit 48)) ;;                              (* [comment removed for export] *)
       let a1 := v_add A_CTX (v_slli sc 3) in                       (* [comment removed for export] *)
       act <- m_ld (at_ a1 80) ;;                                   (* [comment removed for export] *)
       (* [comment removed for export] *)
       (if c_eq nx g
        then m_sd (at_ a1 80) w0                                    (* [comment removed for export] *)
        else pv <- m_ld g ;;                                        (* [comment removed for export] *)
             m_sd (at_ pv 8) nx ;;                                  (* [comment removed for export] *)
             pv2 <- m_ld g ;;                                       (* [comment removed for export] *)
             nx2 <- m_ld (at_ g 8) ;;                               (* [comment removed for export] *)
             m_sd nx2 pv2 ;;                                        (* [comment removed for export] *)
             h <- m_ld (at_ a1 80) ;;                               (* [comment removed for export] *)
             if c_eq h g then n3 <- m_ld (at_ g 8) ;; m_sd (at_ a1 80) n3  (* [comment removed for export] *)
             else mret tt) ;;
       m_sd g w0 ;; m_sd (at_ g 8) w0 ;;                            (* [comment removed for export] *)
       (if negb (c_eq act g) then mret tt                           (* [comment removed for export] *)
        else m2 <- m_ld (at_ a1 80) ;;                              (* [comment removed for export] *)
             if is0 m2 then mret tt                                 (* [comment removed for export] *)
             else (* [comment removed for export] *)
                  am <- m_lw (at_ m2 24) ;; massert (is0 am) ;;      (* [comment removed for export] *)
                  mp <- m_ld (at_ m2 16) ;;                          (* [comment removed for export] *)
                  ab <- m_lbu (at_ mp 8) ;;                          (* [comment removed for export] *)
                  let act2 := v_sllw (wlit 2) ab in                  (* [comment removed for export] *)
                  massert (is0 (v_andi (at_ m2 28) 3)) ;;            (* [comment removed for export] *)
                  fr2 <- m_lw (at_ m2 28) ;;                         (* [comment removed for export] *)
                  m_sw (at_ m2 28) (v_and fr2 (v_subw w0 act2)) ;;   (* [comment removed for export] *)
                  m_sw (at_ m2 24) (v_and fr2 (v_addi act2 (-1))))) ;;  (* [comment removed for export] *)
    (* [comment removed for export] *)
    w2 <- m_ld (at_ g 32) ;;                                        (* [comment removed for export] *)
    let sc2 := v_srli (v_slli w2 52) 58 in                          (* [comment removed for export] *)
    w3 <- (if c_ltu (wlit 47) sc2 then mret w2                      (* [comment removed for export] *)
           else let a3 := v_add A_CTX (v_slli sc2 3) in             (* [comment removed for export] *)
                us <- m_ld (at_ a3 464) ;;                          (* [comment removed for export] *)
                m_sd (at_ a3 464) (v_add us (v_ori (v_xori w2 (-1)) (-32))) ;;  (* [comment removed for export] *)
                m_ld (at_ g 32)) ;;                                 (* [comment removed for export] *)
    (if negb (is0 (v_srli w3 12))                                   (* [comment removed for export] *)
     then (* [comment removed for export] *)
          sq <- m_seq_next A_CTX ;;                                 (* [comment removed for export] *)
          let d := v_addi sc2 (-7) in                               (* [comment removed for export] *)
          m_sb (at_ A_CTX 912) sq ;;                                (* [comment removed for export] *)
          (if c_ltu (wlit 31) d then mret tt                        (* [comment removed for export] *)
           else m_sb (at_ (v_add A_CTX d) 848) sq) ;;               (* [comment removed for export] *)
          w4 <- m_ld (at_ g 32) ;;                                  (* [comment removed for export] *)
          base <- m_ld (at_ g 16) ;;                                (* [comment removed for export] *)
          m_free_meta (at_ A_CTX 16) g ;;                           (* [comment removed for export] *)
          mret (base, v_and w4 PAGEMASK)                            (* [comment removed for export] *)
     else (* [comment removed for export] *)
          p <- m_ld (at_ g 16) ;;                                   (* [comment removed for export] *)
          mm <- m_get_meta p ;;                                     (* [comment removed for export] *)
          p2 <- m_ld (at_ g 16) ;;                                  (* [comment removed for export] *)
          c3 <- m_lbu (at_ p (-3)) ;;                               (* [comment removed for export] *)
          m_sd p2 w0 ;;                                             (* [comment removed for export] *)
          mi <- m_nontrivial_free fuel' mm (v_andi c3 31) ;;        (* [comment removed for export] *)
          m_free_meta (at_ A_CTX 16) g ;;                           (* [comment removed for export] *)
          mret mi)
  else
    (* [comment removed for export] *)
    (if negb (is0 mask) then mret tt                                (* [comment removed for export] *)
     else massert (c_ltu sc (wlit 48)) ;;                           (* [comment removed for export] *)
          let a3 := v_add A_CTX (v_slli sc 3) in                    (* [comment removed for export] *)
          act <- m_ld (at_ a3 80) ;;                                (* [comment removed for export] *)
          if c_eq act g then mret tt                                (* [comment removed for export] *)
          else (* [comment removed for export] *)
               nx <- m_ld (at_ g 8) ;; massert (is0 nx) ;;          (* [comment removed for export] *)
               pv <- m_ld g ;; massert (is0 pv) ;;                  (* [comment removed for export] *)
               if is0 act
               then m_sd g g ;; m_sd (at_ g 8) g ;; m_sd (at_ a3 80) g  (* [comment removed for export] *)
               else m_sd (at_ g 8) act ;;                           (* [comment removed for export] *)
                    ap <- m_ld act ;;                               (* [comment removed for export] *)
                    m_sd g ap ;;                                    (* [comment removed for export] *)
                    m_sd (at_ ap 8) g ;;                            (* [comment removed for export] *)
                    n2 <- m_ld (at_ g 8) ;;                         (* [comment removed for export] *)
                    m_sd n2 g) ;;                                   (* [comment removed for export] *)
    massert (is0 (v_andi (at_ g 28) 3)) ;;                          (* [comment removed for export] *)
    fr3 <- m_lw (at_ g 28) ;;                                       (* [comment removed for export] *)
    m_sw (at_ g 28) (v_or fr3 self) ;;                              (* [comment removed for export] *)
    mret (w0, w0)) ;;                                               (* [comment removed for export] *)
  m_canary_check gp cg ;;                                         (* [comment removed for export] *)
  mret res
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FREE_FUEL : nat := 9.

Definition m_free (p : word) : M unit :=
  if is0 p then mret tt                                           (* [comment removed for export] *)
  else
  g <- m_get_meta p ;;                                            (* [comment removed for export] *)
  w <- m_ld (at_ g 32) ;;                                         (* [comment removed for export] *)
  c3 <- m_lbu (at_ p (-3)) ;;                                     (* [comment removed for export] *)
  let idx := v_andi c3 31 in                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  stride <- (if negb (is0 (v_srli w 12)) && is0 (v_andi w 31)      (* [comment removed for export] *)
             then mret (v_addi (v_and w PAGEMASK) (-16))            (* [comment removed for export] *)
             else szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w 5) 126)) ;;  (* [comment removed for export] *)
                  mret (v_slli szc 4)) ;;                           (* [comment removed for export] *)
  mem <- m_ld (at_ g 16) ;;                                       (* [comment removed for export] *)
  let a5 := v_add (v_add mem stride) (v_mul stride idx) in        (* [comment removed for export] *)
  let end_ := v_addi a5 12 in                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  let rsv0 := v_srli c3 5 in                                      (* [comment removed for export] *)
  rsv <- (if c_ltu c3 (wlit 160) then mret rsv0                   (* [comment removed for export] *)
          else massert (c_eq rsv0 (wlit 5)) ;;                     (* [comment removed for export] *)
               r32 <- m_lwu (at_ a5 8) ;;                          (* [comment removed for export] *)
               massert (c_ltu (wlit 4) r32) ;;                     (* [comment removed for export] *)
               c5 <- m_lbu (at_ a5 7) ;;                           (* [comment removed for export] *)
               massert (is0 c5) ;;                                 (* [comment removed for export] *)
               mret r32) ;;
  massert (negb (c_ltu (v_sub end_ p) rsv)) ;;                    (* [comment removed for export] *)
  cz <- m_lbu (v_sub end_ rsv) ;; massert (is0 cz) ;;             (* [comment removed for export] *)
  ce <- m_lbu end_ ;; massert (is0 ce) ;;                         (* [comment removed for export] *)
  let all := v_addiw (v_sllw (wlit 2) w) (-1) in                  (* [comment removed for export] *)
  let self := v_sllw (wlit 1) idx in                              (* [comment removed for export] *)
  m_sb (at_ p (-3)) wm1 ;;                                        (* [comment removed for export] *)
  m_sh (at_ p (-2)) w0 ;;                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  fr <- m_lw (at_ g 28) ;;                                        (* [comment removed for export] *)
  av <- m_lw (at_ g 24) ;;                                        (* [comment removed for export] *)
  let mask := v_or av fr in                                       (* [comment removed for export] *)
  massert (is0 (v_and mask self)) ;;                              (* [comment removed for export] *)
  mt <- m_lbu A_NEED_LOCKS ;;                                     (* [comment removed for export] *)
  (if negb (is0 fr) && negb (c_eq (v_addw mask self) all)         (* [comment removed for export] *)
   then (* [comment removed for export] *)
        massert (is0 mt) ;;                                       (* [comment removed for export] *)
        m_sw (at_ g 28) (v_addw fr self)                          (* [comment removed for export] *)
   else
        massert (is0 mt) ;;                                       (* [comment removed for export] *)
        mi <- m_nontrivial_free FREE_FUEL g idx ;;                 (* [comment removed for export] *)
        let '(base, len) := mi in
        m_unlock ;;                                               (* [comment removed for export] *)
        (if is0 len then mret tt                                  (* [comment removed for export] *)
         else e <- m_lw A_ERRNO ;;                                 (* [comment removed for export] *)
              r <- sys_munmap base len ;;                          (* [comment removed for export] *)
              m_sw A_ERRNO e)).                                    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint m_scan_auxv (fuel : nat) (auxv i secret : word) : M word :=
  match fuel with
  | O => mcrash
  | S fuel' =>
    key <- m_ld (v_add auxv i) ;;                                  (* [comment removed for export] *)
    if c_eq key (wlit 25)                                          (* [comment removed for export] *)
    then val <- m_ld (at_ (v_add auxv i) 8) ;;                     (* [comment removed for export] *)
         massert (c_ltu val (wlit (2^64 - 24))) ;;                 (* [comment removed for export] *)
         rnd <- m_ld (at_ val 8) ;;                                 (* [comment removed for export] *)
         auxv' <- m_ld (at_ A_LIBC 8) ;;                            (* [comment removed for export] *)
         m_scan_auxv fuel' auxv' (v_addi i 16) rnd                 (* [comment removed for export] *)
    else if is0 key then mret secret                               (* [comment removed for export] *)
    else m_scan_auxv fuel' auxv (v_addi i 16) secret
  end.

Definition AUXV_FUEL : nat := 64%nat.

Definition m_alloc_meta (sp : word) : M word :=
  cc <- m_canary_load ;;                                          (* [comment removed for export] *)
  let '(gp, cg) := cc in
  ini <- m_lw A_INIT_DONE ;;                                      (* [comment removed for export] *)
  (if negb (is0 ini) then mret tt                                 (* [comment removed for export] *)
   else auxv <- m_ld (at_ A_LIBC 8) ;;                            (* [comment removed for export] *)
        let s0 := v_mul sp (wlit 0x41c64e6d) in                   (* [comment removed for export] *)
        sec <- m_scan_auxv AUXV_FUEL auxv w0 s0 ;;                 (* [comment removed for export] *)
        m_sd A_CTX sec ;;                                         (* [comment removed for export] *)
        m_sw A_INIT_DONE (wlit 1)) ;;                              (* [comment removed for export] *)
  pg <- m_ld (at_ A_LIBC 48) ;;                                   (* [comment removed for export] *)
  massert (c_eq pg (wlit 4096)) ;;                                (* [comment removed for export] *)
  let pagesize := if c_ltu (wlit 4096) pg then pg else wlit 4096 in  (* [comment removed for export] *)
  res <- (
  fmh <- m_ld A_FREE_META_HEAD ;;                                 (* [comment removed for export] *)
  if negb (is0 fmh) then
    (* [comment removed for export] *)
    let m := fmh in
    nx <- m_ld (at_ m 8) ;;                                       (* [comment removed for export] *)
    (if c_eq nx m then m_sd A_FREE_META_HEAD w0                   (* [comment removed for export] *)
     else pv <- m_ld m ;;                                         (* [comment removed for export] *)
          m_sd (at_ pv 8) nx ;;                                   (* [comment removed for export] *)
          pv2 <- m_ld m ;;                                        (* [comment removed for export] *)
          nx2 <- m_ld (at_ m 8) ;;                                (* [comment removed for export] *)
          m_sd nx2 pv2 ;;                                         (* [comment removed for export] *)
          h <- m_ld A_FREE_META_HEAD ;;                           (* [comment removed for export] *)
          if c_eq h m then n3 <- m_ld (at_ m 8) ;; m_sd A_FREE_META_HEAD n3  (* [comment removed for export] *)
          else mret tt) ;;
    m_sd (at_ m 8) w0 ;; m_sd m w0 ;;                             (* [comment removed for export] *)
    mret m
  else
  amc <- m_ld A_AVAIL_META_CNT ;;                                 (* [comment removed for export] *)
  if negb (is0 amc) then
    m <- m_ld A_AVAIL_META ;;                                     (* [comment removed for export] *)
    m_sd A_AVAIL_META (at_ m 40) ;;                               (* [comment removed for export] *)
    m_sd A_AVAIL_META_CNT (v_addi amc (-1)) ;;                    (* [comment removed for export] *)
    m_sd (at_ m 8) w0 ;; m_sd m w0 ;;                             (* [comment removed for export] *)
    mret m
  else
  aac <- m_ld A_AVAIL_AREA_CNT ;;                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  r <- (if negb (is0 aac)
        then p <- m_ld A_AVAIL_AREAS ;; mret (Some (p, true))      (* [comment removed for export] *)
        else
          cb <- m_ld A_BRK ;;                                      (* [comment removed for export] *)
          br <- (if c_eq cb wm1 then mret None                     (* [comment removed for export] *)
                 else if negb (is0 cb)                             (* [comment removed for export] *)
                 then let new := v_add cb pagesize in              (* [comment removed for export] *)
                      r <- sys_brk_grow new ;;                     (* [comment removed for export] *)
                      mret (Some (new, c_eq r new))                (* [comment removed for export] *)
                 else r0 <- sys_brk_query ;;                        (* [comment removed for export] *)
                      let al := v_add (v_and (v_addi pagesize (-1)) (v_sub w0 r0)) r0 in  (* [comment removed for export] *)
                      m_sd A_BRK al ;;                             (* [comment removed for export] *)
                      let new := v_add al (v_slli pagesize 1) in    (* [comment removed for export] *)
                      r <- sys_brk_grow new ;;                     (* [comment removed for export] *)
                      (if c_eq r new
                       then b <- m_ld A_BRK ;;                      (* [comment removed for export] *)
                            g <- sys_mmap_fixed_none b pagesize ;;  (* [comment removed for export] *)
                            mret (Some (new, true))
                       else mret (Some (new, false)))) ;;
          match br with
          | Some (new, true) =>
              m_sd A_BRK new ;;                                    (* [comment removed for export] *)
              m_sd A_AVAIL_AREA_CNT (v_srli pagesize 12) ;;        (* [comment removed for export] *)
              mret (Some (v_sub new pagesize, false))              (* [comment removed for export] *)
          | _ =>
              aac2 <- (match br with
                       | Some _ => a <- m_ld A_AVAIL_AREA_CNT ;; m_sd A_BRK wm1 ;; mret a  (* [comment removed for export] *)
                       | None => mret aac end) ;;
              if negb (is0 aac2) then p <- m_ld A_AVAIL_AREAS ;; mret (Some (p, true))  (* [comment removed for export] *)
              else
                sh <- m_ld A_META_SHIFT ;;                          (* [comment removed for export] *)
                let n := v_sll (wlit 2) sh in                      (* [comment removed for export] *)
                p <- sys_mmap MMnone (v_mul n pagesize) ;;          (* [comment removed for export] *)
                if c_eq p wm1 then mret None                       (* [comment removed for export] *)
                else sh2 <- m_ld A_META_SHIFT ;;                    (* [comment removed for export] *)
                     m_sd A_AVAIL_AREA_CNT (v_mul (v_addi n (-1)) (v_srli pagesize 12)) ;;  (* [comment removed for export] *)
                     m_sd A_META_SHIFT (v_addi sh2 1) ;;            (* [comment removed for export] *)
                     m_sd A_AVAIL_AREAS (v_add p pagesize) ;;       (* [comment removed for export] *)
                     mret (Some (v_add p pagesize, true))
          end) ;;
  match r with
  | None => mret w0                                               (* [comment removed for export] *)
  | Some (p, test) =>
    ok <- (if test && is0 (v_and (v_addi pagesize (-1)) p)        (* [comment removed for export] *)
           then pg2 <- m_ld A_PAGE_SIZE ;;                         (* [comment removed for export] *)
                massert (c_eq pg2 (wlit 4096)) ;;
                r <- sys_mprotect_rw p pagesize ;;                  (* [comment removed for export] *)
                if is0 r then mret true                            (* [comment removed for export] *)
                else e <- m_lw A_ERRNO ;; mret (c_eq e (wlit 38))   (* [comment removed for export] *)
           else mret true) ;;
    if negb ok then mret w0                                       (* [comment removed for export] *)
    else
    aac3 <- m_ld A_AVAIL_AREA_CNT ;;                              (* [comment removed for export] *)
    tl <- m_ld A_AREA_TAIL ;;                                     (* [comment removed for export] *)
    m_sd A_AVAIL_AREA_CNT (v_addi aac3 (-1)) ;;                   (* [comment removed for export] *)
    m_sd A_AVAIL_AREAS (v_add p (wlit 4096)) ;;                   (* [comment removed for export] *)
    (if is0 tl then m_sd A_AREA_HEAD p                            (* [comment removed for export] *)
     else m_sd (at_ tl 8) p) ;;                                   (* [comment removed for export] *)
    sec <- m_ld A_CTX ;;                                          (* [comment removed for export] *)
    m_sd A_AREA_TAIL p ;;                                         (* [comment removed for export] *)
    m_sd p sec ;;                                                 (* [comment removed for export] *)
    t1 <- m_ld A_AREA_TAIL ;;                                     (* [comment removed for export] *)
    m_sw (at_ t1 16) (wlit 101) ;;                                (* [comment removed for export] *)
    t2 <- m_ld A_AREA_TAIL ;;                                     (* [comment removed for export] *)
    let m := at_ t2 24 in                                         (* [comment removed for export] *)
    m_sd A_AVAIL_META (at_ m 40) ;;                               (* [comment removed for export] *)
    m_sd A_AVAIL_META_CNT (wlit 100) ;;                           (* [comment removed for export] *)
    m_sd (at_ m 8) w0 ;; m_sd m w0 ;;                             (* [comment removed for export] *)
    mret m
  end) ;;
  m_canary_check gp cg ;;                                         (* [comment removed for export] *)
  mret res.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition m_enframe (g idx n ctr : word) : M word :=
  w <- m_ld (at_ g 32) ;;                                         (* [comment removed for export] *)
  stride <- (if negb (is0 (v_srli w 12)) && is0 (v_andi w 31)      (* [comment removed for export] *)
             then mret (v_addi (v_and w PAGEMASK) (-16))            (* [comment removed for export] *)
             else szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w 5) 126)) ;;  (* [comment removed for export] *)
                  mret (v_slli szc 4)) ;;                           (* [comment removed for export] *)
  mem <- m_ld (at_ g 16) ;;                                       (* [comment removed for export] *)
  let p0 := v_add mem (v_mul stride idx) in                       (* [comment removed for export] *)
  c13 <- m_lbu (at_ p0 13) ;;                                     (* [comment removed for export] *)
  let t0 := v_addi (v_sub stride n) (-4) in                       (* [comment removed for export] *)
  let p := at_ p0 16 in                                           (* [comment removed for export] *)
  off0 <- (if is0 c13 then mret ctr                               (* [comment removed for export] *)
           else o <- m_lhu (at_ p (-2)) ;; mret (v_addi o 1)) ;;   (* [comment removed for export] *)
  c4 <- m_lbu (at_ p (-4)) ;;                                     (* [comment removed for export] *)
  let slack := v_srli t0 4 in                                     (* [comment removed for export] *)
  let off1 := v_andi off0 255 in                                  (* [comment removed for export] *)
  massert (is0 c4) ;;                                             (* [comment removed for export] *)
  off <- (if negb (c_ltu slack off1) then mret off1               (* [comment removed for export] *)
          else let m1 := v_or slack (v_srli t0 5) in               (* [comment removed for export] *)
               let m2 := v_or (v_srli m1 2) m1 in                  (* [comment removed for export] *)
               let m3 := v_or (v_srli m2 4) m2 in                  (* [comment removed for export] *)
               let o2 := v_and off1 m3 in                          (* [comment removed for export] *)
               let o3 := v_addw (v_and (v_subw w0 (v_sltu slack o2)) (v_xori slack (-1))) o2 in  (* [comment removed for export] *)
               massert (negb (c_ltu slack o3)) ;;                  (* [comment removed for export] *)
               mret o3) ;;
  r <- (if is0 off then mret (p, mem)                             (* [comment removed for export] *)
        else let q := v_add p (v_slliw off 4) in                   (* [comment removed for export] *)
             m_sb (at_ p (-3)) (wlit (2^64 - 32)) ;;               (* [comment removed for export] *)
             m_sh (at_ p (-2)) off ;;                              (* [comment removed for export] *)
             m_sb (at_ q (-4)) w0 ;;                               (* [comment removed for export] *)
             mem2 <- m_ld (at_ g 16) ;;                            (* [comment removed for export] *)
             mret (q, mem2)) ;;
  let '(q, memv) := r in
  let a4 := v_add p stride in                                     (* [comment removed for export] *)
  let offu := v_srli (v_addi (v_subw q memv) (-16)) 4 in          (* [comment removed for export] *)
  let end4 := v_addi a4 (-4) in                                   (* [comment removed for export] *)
  let rsv := v_subw end4 (v_add n q) in                           (* [comment removed for export] *)
  m_sb (at_ q (-3)) idx ;;                                        (* [comment removed for export] *)
  m_sh (at_ q (-2)) offu ;;                                       (* [comment removed for export] *)
  code <- (if is0 rsv then mret w0                                (* [comment removed for export] *)
           else let r1 := v_subw end4 (v_add n q) in               (* [comment removed for export] *)
                m_sb (v_add end4 (v_subw w0 r1)) w0 ;;              (* [comment removed for export] *)
                if c_lts r1 (wlit 5) then mret r1                  (* [comment removed for export] *)
                else m_sb (at_ a4 (-9)) w0 ;;                       (* [comment removed for export] *)
                     m_sw (at_ a4 (-8)) r1 ;;                       (* [comment removed for export] *)
                     mret (wlit 5)) ;;
  c <- m_lbu (at_ q (-3)) ;;                                      (* [comment removed for export] *)
  m_sb (at_ q (-3)) (v_or (v_slli code 5) (v_andi c 31)) ;;       (* [comment removed for export] *)
  mret q.                                                         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint m_span_loop (fuel : nat) (a6 t0 a4 a5 : word) : option word :=
  match fuel with
  | O => None
  | S fuel' =>
    let t1 := v_xor a6 t0 in                                       (* [comment removed for export] *)
    let t0' := v_addw t0 a5 in                                     (* [comment removed for export] *)
    let a4' := v_addiw a4 1 in                                     (* [comment removed for export] *)
    let a6' := v_addw a6 a5 in                                     (* [comment removed for export] *)
    if c_lts t1 (wlit 4096) then m_span_loop fuel' a6' t0' a4' a5   (* [comment removed for export] *)
    else Some a4'   (* [comment removed for export] *)
  end.

Fixpoint m_alloc_slot (fuel : nat) (sp : word) (sc req : word) : M word :=
  match fuel with
  | O => mcrash
  | S fuel' =>
  cc <- m_canary_load ;;                                          (* [comment removed for export] *)
  let '(gp, cg) := cc in
  let s7 := v_add A_LOCK (v_slli sc 3) in                         (* [comment removed for export] *)
  let pm := at_ s7 88 in                                          (* [comment removed for export] *)
  res <- (
  m0 <- m_ld pm ;;                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  ta <- (if is0 m0 then mret None                                 (* [comment removed for export] *)
         else
           am <- m_lw (at_ m0 24) ;;                               (* [comment removed for export] *)
           if negb (is0 am) then mret (Some (m0, am))               (* [comment removed for export] *)
           else
             fr <- m_lw (at_ m0 28) ;;                              (* [comment removed for export] *)
             nx <- m_ld (at_ m0 8) ;;                               (* [comment removed for export] *)
             mo <- (if negb (is0 fr)
                    then m_sd pm nx ;; mret (Some nx)               (* [comment removed for export] *)
                    else (* [comment removed for export] *)
                      (if c_eq nx m0 then m_sd pm w0                (* [comment removed for export] *)
                       else pv <- m_ld m0 ;;                         (* [comment removed for export] *)
                            m_sd (at_ pv 8) nx ;;                   (* [comment removed for export] *)
                            pv2 <- m_ld m0 ;;                        (* [comment removed for export] *)
                            nx2 <- m_ld (at_ m0 8) ;;                (* [comment removed for export] *)
                            m_sd nx2 pv2 ;;                         (* [comment removed for export] *)
                            h <- m_ld pm ;;                          (* [comment removed for export] *)
                            if c_eq h m0 then n3 <- m_ld (at_ m0 8) ;; m_sd pm n3  (* [comment removed for export] *)
                            else mret tt) ;;
                      m_sd m0 w0 ;; m_sd (at_ m0 8) w0 ;;           (* [comment removed for export] *)
                      m1 <- m_ld pm ;;                              (* [comment removed for export] *)
                      if is0 m1 then mret None else mret (Some m1)) ;;  (* [comment removed for export] *)
             match mo with
             | None => mret None
             | Some m =>
               fr1 <- m_lw (at_ m 28) ;;                            (* [comment removed for export] *)
               w <- m_ld (at_ m 32) ;;                              (* [comment removed for export] *)
               mf <- (if negb (is0 (v_andi w 32))                   (* [comment removed for export] *)
                         && c_eq fr1 (v_addiw (v_sllw (wlit 2) w) (-1))  (* [comment removed for export] *)
                      then m' <- m_ld (at_ m 8) ;;                   (* [comment removed for export] *)
                           m_sd pm m' ;;                            (* [comment removed for export] *)
                           fr' <- m_lw (at_ m' 28) ;;                (* [comment removed for export] *)
                           mret (m', fr')
                      else mret (m, fr1)) ;;
               let '(m2, fr2) := mf in
               mp <- m_ld (at_ m2 16) ;;                            (* [comment removed for export] *)
               ai <- m_lbu (at_ mp 8) ;;                            (* [comment removed for export] *)
               let act := v_addiw (v_sllw (wlit 2) ai) (-1) in      (* [comment removed for export] *)
               m3o <- (if negb (is0 (v_and act fr2)) then mret (Some m2)  (* [comment removed for export] *)
                       else nx3 <- m_ld (at_ m2 8) ;;                (* [comment removed for export] *)
                            if negb (c_eq nx3 m2)
                            then m_sd pm nx3 ;; mret (Some nx3)     (* [comment removed for export] *)
                            else (* [comment removed for export] *)
                              let a5 := v_andi ai 31 in             (* [comment removed for export] *)
                              w5 <- m_ld (at_ m2 32) ;;              (* [comment removed for export] *)
                              szc <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w5 5) 126)) ;;  (* [comment removed for export] *)
                              let a6 := v_addi a5 2 in              (* [comment removed for export] *)
                              let a4 := v_addi a5 1 in              (* [comment removed for export] *)
                              let t0 := v_addi (v_slli a5 4) 48 in   (* [comment removed for export] *)
                              let size := v_slli szc 4 in           (* [comment removed for export] *)
                              let a7 := v_mul t0 szc in             (* [comment removed for export] *)
                              let t0' := v_mul size a6 in           (* [comment removed for export] *)
                              let a6' := v_addiw a7 15 in           (* [comment removed for export] *)
                              let t0'' := v_addiw t0' 16 in         (* [comment removed for export] *)
                              match m_span_loop 40 a6' t0'' a4 size with
                              | None => mcrash
                              | Some cnt =>
                                let lim := v_addi (v_andi w5 31) 1 in  (* [comment removed for export] *)
                                let cnt' := if c_ltu cnt lim then cnt else lim in  (* [comment removed for export] *)
                                m_sb (at_ mp 8) (v_or (v_andi (v_addi cnt' (-1)) 31) (v_andi ai 224)) ;;  (* [comment removed for export] *)
                                mret (Some m2)                       (* [comment removed for export] *)
                              end) ;;
               match m3o with
               | None => mret None
               | Some m3 =>
                 (* [comment removed for export] *)
                 am3 <- m_lw (at_ m3 24) ;; massert (is0 am3) ;;     (* [comment removed for export] *)
                 mp3 <- m_ld (at_ m3 16) ;;                          (* [comment removed for export] *)
                 ab <- m_lbu (at_ mp3 8) ;;                          (* [comment removed for export] *)
                 let act2 := v_sllw (wlit 2) ab in                  (* [comment removed for export] *)
                 massert (is0 (v_andi (at_ m3 28) 3)) ;;             (* [comment removed for export] *)
                 fr4 <- m_lw (at_ m3 28) ;;                          (* [comment removed for export] *)
                 m_sw (at_ m3 28) (v_and fr4 (v_subw w0 act2)) ;;    (* [comment removed for export] *)
                 let mask := v_and fr4 (v_addiw act2 (-1)) in        (* [comment removed for export] *)
                 m_sw (at_ m3 24) mask ;;                           (* [comment removed for export] *)
                 massert (negb (is0 mask)) ;;                        (* [comment removed for export] *)
                 (* [comment removed for export] *)
                 w32 <- m_lw (at_ m3 32) ;;                          (* [comment removed for export] *)
                 let d := v_addi (v_srli (v_slli w32 52) 58) (-7) in (* [comment removed for export] *)
                 (if c_ltu (wlit 31) d then mret tt                  (* [comment removed for export] *)
                  else b <- m_lbu (at_ (v_add A_LOCK d) 888) ;;      (* [comment removed for export] *)
                       if is0 b then mret tt                        (* [comment removed for export] *)
                       else m_sb (at_ (v_add A_LOCK d) 888) (v_addi b (-1))) ;;  (* [comment removed for export] *)
                 mret (Some (m3, mask))
               end
             end) ;;
  match ta with
  | Some (m, mask) =>
      let first := v_and mask (v_subw w0 mask) in                 (* [comment removed for export] *)
      m_sw (at_ m 24) (v_subw mask first) ;;                      (* [comment removed for export] *)
      if is0 first then mcrash (* [comment removed for export] *)
      else m_ctz32 mask                                           (* [comment removed for export] *)
  | None =>
  (* [comment removed for export] *)
  szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;            (* [comment removed for export] *)
  m <- m_alloc_meta (at_ sp (-64)) ;;                             (* [comment removed for export] *)
  if is0 m then mret wm1                                          (* [comment removed for export] *)
  else
  usage <- m_ld (at_ s7 472) ;;                                   (* [comment removed for export] *)
  pg <- m_ld A_PAGE_SIZE ;;                                       (* [comment removed for export] *)
  let size := v_slli szc 4 in                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  cnt <- (if negb (c_lts (wlit 8) sc)                              (* [comment removed for export] *)
          then let tb := v_add A_SMALL_CNT_TAB (v_add (v_slli sc 1) sc) in  (* [comment removed for export] *)
               t0 <- m_lbu tb ;;                                   (* [comment removed for export] *)
               if negb (c_ltu usage (v_slli t0 2)) then mret t0     (* [comment removed for export] *)
               else t1 <- m_lbu (at_ tb 1) ;;                        (* [comment removed for export] *)
                    if negb (c_ltu usage (v_slli t1 2)) then mret t1  (* [comment removed for export] *)
                    else m_lbu (at_ tb 2)                           (* [comment removed for export] *)
          else t <- m_lbu (v_add A_MED_CNT_TAB (v_andi sc 3)) ;;    (* [comment removed for export] *)
               (* [comment removed for export] *)
               let c0 := (fix halve (k : nat) (a3 : word) : word :=
                            match k with O => a3 | S k' =>
                              if negb (is0 (v_andi a3 1)) then a3           (* [comment removed for export] *)
                              else if negb (c_ltu usage (v_slliw a3 2)) then a3  (* [comment removed for export] *)
                              else halve k' (v_srliw a3 1)           (* [comment removed for export] *)
                            end) 8%nat t in
               (* [comment removed for export] *)
               mret ((fix shrink (k : nat) (a2 : word) : word :=
                        match k with O => a2 | S k' =>
                          if is0 (v_srli (v_mul size a2) 20) then a2
                          else shrink k' (v_srliw a2 1)
                        end) 40%nat c0)) ;;
  let half := v_srli pg 1 in                                      (* [comment removed for export] *)
  let cnt1 := if c_eq cnt (wlit 1)                                (* [comment removed for export] *)
              then v_subw (wlit 2) (v_sltu half (v_addi size 16)) (* [comment removed for export] *)
              else cnt in
  let a4 := v_mul size cnt1 in                                    (* [comment removed for export] *)
  if negb (c_ltu half (v_addi a4 16))                             (* [comment removed for export] *)
  then
    (* [comment removed for export] *)
    let a1 := v_addi a4 12 in                                     (* [comment removed for export] *)
    let n16 := v_srli a4 4 in                                     (* [comment removed for export] *)
    j <- (if c_ltu a1 (wlit 157) then mret n16                     (* [comment removed for export] *)
          else m_size_to_class_big A_SIZE_CLASSES n16) ;;          (* [comment removed for export] *)
    let j' := v_addiw j 0 in                                      (* [comment removed for export] *)
    idx <- m_alloc_slot fuel' (at_ sp (-144)) j' a1 ;;            (* [comment removed for export] *)
    if c_lts idx w0 then                                          (* [comment removed for export] *)
      m_free_meta_ag (at_ A_LOCK 24) m ;;                         (* [comment removed for export] *)
      mret wm1                                                    (* [comment removed for export] *)
    else
      szj <- m_lhu (v_add A_SIZE_CLASSES (v_slli j' 1)) ;;         (* [comment removed for export] *)
      gj <- m_ld (at_ (v_add A_LOCK (v_slli j' 3)) 88) ;;          (* [comment removed for export] *)
      ctr <- m_lw (at_ A_LOCK 20) ;;                               (* [comment removed for export] *)
      p <- m_enframe gj idx (v_addi (v_slli szj 4) (-4)) ctr ;;    (* [comment removed for export] *)
      wm <- m_ld (at_ m 32) ;;                                     (* [comment removed for export] *)
      m_sd (at_ m 32) (v_srli (v_slli wm 52) 52) ;;                (* [comment removed for export] *)
      c3 <- m_lbu (at_ p (-3)) ;;                                  (* [comment removed for export] *)
      m_sb (at_ p (-3)) (v_addi (v_andi c3 31) 192) ;;             (* [comment removed for export] *)
      (* [comment removed for export] *)
      (fix zl (k : nat) (a2 : word) : M unit :=
         match k with O => mret tt | S k' => m_sb a2 w0 ;; zl k' (v_add a2 size) end)
        (S (Z.to_nat (bv_unsigned cnt1))) (at_ p 12) ;;
      let aidx := v_addi cnt1 (-1) in                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      us2 <- m_ld (at_ s7 472) ;;                                  (* [comment removed for export] *)
      m_sd (at_ s7 472) (v_add us2 cnt1) ;;                        (* [comment removed for export] *)
      m_sw (at_ m 24) (v_addi (v_sllw (wlit 2) aidx) (-1)) ;;      (* [comment removed for export] *)
      am <- m_lw (at_ m 24) ;;                                     (* [comment removed for export] *)
      m_sw (at_ m 28) (v_add (v_sllw (wlit 2) aidx) (v_xori am (-1))) ;;  (* [comment removed for export] *)
      m_sd (at_ m 16) p ;;                                         (* [comment removed for export] *)
      m_sd p m ;;                                                  (* [comment removed for export] *)
      mp <- m_ld (at_ m 16) ;;                                     (* [comment removed for export] *)
      ab <- m_lbu (at_ mp 8) ;;                                    (* [comment removed for export] *)
      m_sb (at_ mp 8) (v_or (v_andi ab 224) (v_andi aidx 31)) ;;   (* [comment removed for export] *)
      wm2 <- m_ld (at_ m 32) ;;                                    (* [comment removed for export] *)
      m_sd (at_ m 32) (v_addi (v_or (v_or (v_srli (v_slli sc 58) 52) (v_andi aidx 31))
                                    (v_and wm2 PAGEMASK)) 32) ;;    (* [comment removed for export] *)
      (* [comment removed for export] *)
      am2 <- m_lw (at_ m 24) ;;                                    (* [comment removed for export] *)
      m_sw (at_ m 24) (v_addi am2 (-1)) ;;                         (* [comment removed for export] *)
      nx <- m_ld (at_ m 8) ;; massert (is0 nx) ;;                  (* [comment removed for export] *)
      pv <- m_ld m ;; massert (is0 pv) ;;                          (* [comment removed for export] *)
      hd <- m_ld pm ;;                                             (* [comment removed for export] *)
      (if is0 hd then m_sd m m ;; m_sd (at_ m 8) m ;; m_sd pm m    (* [comment removed for export] *)
       else m_sd (at_ m 8) hd ;; hp <- m_ld hd ;; m_sd m hp ;;     (* [comment removed for export] *)
            m_sd (at_ hp 8) m ;; n2 <- m_ld (at_ m 8) ;; m_sd n2 m) ;;  (* [comment removed for export] *)
      mret w0                                                      (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    let d := v_addiw sc (-7) in                                   (* [comment removed for export] *)
    bn <- (if c_ltu (wlit 31) d then mret (false, None)            (* [comment removed for export] *)
           else let a5 := v_add A_LOCK d in                        (* [comment removed for export] *)
                b <- m_lbu (at_ a5 888) ;;                          (* [comment removed for export] *)
                us <- m_lbu (at_ a5 856) ;;                         (* [comment removed for export] *)
                let nosmall := negb (c_ltu b (wlit 100)) in        (* [comment removed for export] *)
                (if is0 us then mret tt                            (* [comment removed for export] *)
                 else sq <- m_lbu (at_ A_LOCK 920) ;;               (* [comment removed for export] *)
                      if c_lts (wlit 9) (v_sub sq us) then mret tt  (* [comment removed for export] *)
                      else if c_ltu b (wlit 99) then m_sb (at_ a5 888) (v_addi b 1)  (* [comment removed for export] *)
                      else m_sb (at_ a5 888) (wlit 150)) ;;         (* [comment removed for export] *)
                mret (nosmall, Some a5)) ;;
    let '(nosmall, _) := bn in
    (* [comment removed for export] *)
    sq <- m_lbu (at_ A_LOCK 920) ;;                               (* [comment removed for export] *)
    sq' <- (if c_eq sq (wlit 255)
            then m_sd (at_ A_LOCK 856) w0 ;; m_sd (at_ A_LOCK 864) w0 ;;
                 m_sd (at_ A_LOCK 872) w0 ;; m_sd (at_ A_LOCK 880) w0 ;; mret (wlit 1)
            else mret (v_addi sq 1)) ;;
    m_sb (at_ A_LOCK 920) sq' ;;                                  (* [comment removed for export] *)
    usage2 <- (if c_lts (wlit 31) sc then mret usage               (* [comment removed for export] *)
               else if negb (is0 (v_andi sc 1)) then mret usage    (* [comment removed for export] *)
               else u1 <- m_ld (at_ s7 480) ;; mret (v_add u1 usage)) ;;  (* [comment removed for export] *)
    (* [comment removed for export] *)
    let cnt2 :=
      if negb (c_ltu usage2 (v_slliw cnt1 2)) then cnt1           (* [comment removed for export] *)
      else if nosmall then cnt1                                   (* [comment removed for export] *)
      else let a5 := v_andi sc 3 in
           let a6 := v_slli pg 3 in                               (* [comment removed for export] *)
           if c_eq a5 (wlit 1) && c_ltu a6 a4 then wlit 2         (* [comment removed for export] *)
           else if c_eq a5 (wlit 2) && c_ltu (v_slli pg 2) a4 then wlit 3  (* [comment removed for export] *)
           else if is0 a5 && c_ltu a6 a4 then wlit 3              (* [comment removed for export] *)
           else if is0 a5 && c_ltu (v_slli pg 1) a4 then wlit 5   (* [comment removed for export] *)
           else cnt1 in
    let needed0 := v_mul size cnt2 in                             (* [comment removed for export] *)
    let needed := v_addi (v_add needed0 (v_and (v_sub (wlit (2^64 - 16)) needed0) (v_addi pg (-1)))) 16 in  (* [comment removed for export] *)
    let '(cnt3, needed3) :=
      if nosmall then (cnt2, needed)                              (* [comment removed for export] *)
      else if c_ltu (wlit 7) cnt2 then (cnt2, needed)             (* [comment removed for export] *)
      else let r := v_addi (v_add req (v_and (v_addi pg (-1)) (v_sub (wlit (2^64 - 20)) req))) 20 in  (* [comment removed for export] *)
           if c_ltu r (v_addi size 16) then (wlit 1, r)           (* [comment removed for export] *)
           else if c_ltu r (v_slli pg 2) then (cnt2, needed)      (* [comment removed for export] *)
           else if c_ltu usage2 (v_slliw cnt2 1) then (wlit 1, r)  (* [comment removed for export] *)
           else (cnt2, needed) in
    p <- sys_mmap MMrw needed3 ;;                                 (* [comment removed for export] *)
    if c_eq p wm1 then
      m_free_meta_ag (at_ A_LOCK 24) m ;;                         (* [comment removed for export] *)
      mret wm1                                                    (* [comment removed for export] *)
    else
      wm <- m_ld (at_ m 32) ;;                                     (* [comment removed for export] *)
      let aimax := v_divu (wlit 4080) size in                      (* [comment removed for export] *)
      ctr <- m_lw (at_ A_LOCK 20) ;;                               (* [comment removed for export] *)
      m_sd (at_ m 32) (v_or (v_srli (v_slli wm 52) 52) (v_and needed3 PAGEMASK)) ;;  (* [comment removed for export] *)
      m_sw (at_ A_LOCK 20) (v_addi ctr 1) ;;                       (* [comment removed for export] *)
      let a2 := if c_ltu cnt3 aimax then cnt3 else aimax in        (* [comment removed for export] *)
      let aidx := v_and (v_addi (v_sltu a2 (v_addi a2 (-1))) (-1)) (v_addi a2 (-1)) in  (* [comment removed for export] *)
      (* [comment removed for export] *)
      us2 <- m_ld (at_ s7 472) ;;                                  (* [comment removed for export] *)
      m_sd (at_ s7 472) (v_add us2 cnt3) ;;                        (* [comment removed for export] *)
      m_sw (at_ m 24) (v_addi (v_sllw (wlit 2) aidx) (-1)) ;;      (* [comment removed for export] *)
      am <- m_lw (at_ m 24) ;;                                     (* [comment removed for export] *)
      m_sw (at_ m 28) (v_add (v_sllw (wlit 2) (v_addi cnt3 (-1))) (v_xori am (-1))) ;;  (* [comment removed for export] *)
      m_sd (at_ m 16) p ;;                                         (* [comment removed for export] *)
      m_sd p m ;;                                                  (* [comment removed for export] *)
      mp <- m_ld (at_ m 16) ;;                                     (* [comment removed for export] *)
      ab <- m_lbu (at_ mp 8) ;;                                    (* [comment removed for export] *)
      m_sb (at_ mp 8) (v_or (v_andi ab 224) (v_andi aidx 31)) ;;   (* [comment removed for export] *)
      wm2 <- m_ld (at_ m 32) ;;                                    (* [comment removed for export] *)
      m_sd (at_ m 32) (v_addi (v_or (v_or (v_srli (v_slli sc 58) 52) (v_andi (v_addi cnt3 (-1)) 31))
                                    (v_and wm2 PAGEMASK)) 32) ;;    (* [comment removed for export] *)
      am2 <- m_lw (at_ m 24) ;;                                    (* [comment removed for export] *)
      m_sw (at_ m 24) (v_addi am2 (-1)) ;;                         (* [comment removed for export] *)
      nx <- m_ld (at_ m 8) ;; massert (is0 nx) ;;                  (* [comment removed for export] *)
      pv <- m_ld m ;; massert (is0 pv) ;;                          (* [comment removed for export] *)
      hd <- m_ld pm ;;                                             (* [comment removed for export] *)
      (if is0 hd then m_sd m m ;; m_sd (at_ m 8) m ;; m_sd pm m
       else m_sd (at_ m 8) hd ;; hp <- m_ld hd ;; m_sd m hp ;;
            m_sd (at_ hp 8) m ;; n2 <- m_ld (at_ m 8) ;; m_sd n2 m) ;;
      mret w0
  end) ;;
  m_canary_check gp cg ;;                                         (* [comment removed for export] *)
  mret res
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ALLOC_FUEL : nat := 5%nat.

Definition m_malloc (sp : word) (n : word) : M word :=
  if negb (c_ltu n (wlit 0x7fffffffffffefff))                    (* [comment removed for export] *)
  then m_sw A_ERRNO (wlit 12) ;; mret w0                          (* [comment removed for export] *)
  else
  if negb (c_ltu n MMAP_THRESHOLD_W) then                         (* [comment removed for export] *)
    (* [comment removed for export] *)
    let needed := v_addi n 20 in                                  (* [comment removed for export] *)
    p <- sys_mmap MMrw needed ;;                                  (* [comment removed for export] *)
    if c_eq p wm1 then mret w0                                    (* [comment removed for export] *)
    else
    mt <- m_lbu A_NEED_LOCKS ;; massert (is0 mt) ;;               (* [comment removed for export] *)
    sq <- m_lbu (at_ A_LOCK 920) ;;                               (* [comment removed for export] *)
    sq' <- (if c_eq sq (wlit 255)
            then m_sd (at_ A_LOCK 856) w0 ;; m_sd (at_ A_LOCK 864) w0 ;;  (* [comment removed for export] *)
                 m_sd (at_ A_LOCK 872) w0 ;; m_sd (at_ A_LOCK 880) w0 ;; mret (wlit 1)
            else mret (v_addi sq 1)) ;;                            (* [comment removed for export] *)
    m_sb (at_ A_LOCK 920) sq' ;;                                  (* [comment removed for export] *)
    g <- m_alloc_meta (at_ sp (-64)) ;;                           (* [comment removed for export] *)
    (if is0 g then                                                (* [comment removed for export] *)
       m_unlock ;;                                                 (* [comment removed for export] *)
       r <- sys_munmap p needed ;; mret w0                         (* [comment removed for export] *)
     else
       m_sd (at_ g 16) p ;;                                       (* [comment removed for export] *)
       m_sd p g ;;                                                (* [comment removed for export] *)
       m_sd (at_ g 32) (v_or (v_andi (v_addi (v_add n (wlit 4064)) 51) (-2048)) (wlit 4064)) ;;  (* [comment removed for export] *)
       m_sw (at_ g 28) w0 ;;                                      (* [comment removed for export] *)
       m_sw (at_ g 24) w0 ;;                                      (* [comment removed for export] *)
       c <- m_lw (at_ A_LOCK 20) ;;                                (* [comment removed for export] *)
       m_sw (at_ A_LOCK 20) (v_addi c 1) ;;                        (* [comment removed for export] *)
       ctr <- m_lw (at_ A_LOCK 20) ;;                              (* [comment removed for export] *)
       m_unlock ;;                                                 (* [comment removed for export] *)
       m_enframe g w0 n ctr)                                      (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    let a0 := v_addi n 3 in                                       (* [comment removed for export] *)
    let n16 := v_srli a0 4 in                                     (* [comment removed for export] *)
    sc0 <- (if c_ltu n (wlit 157) then mret n16                    (* [comment removed for export] *)
            else m_size_to_class_big A_SIZE_CLASSES n16) ;;        (* [comment removed for export] *)
    mt <- m_lbu A_NEED_LOCKS ;; massert (is0 mt) ;;               (* [comment removed for export] *)
    let sc1 := v_addiw sc0 0 in                                   (* [comment removed for export] *)
    g0 <- m_ld (at_ (v_add A_LOCK (v_slli sc1 3)) 88) ;;           (* [comment removed for export] *)
    (* [comment removed for export] *)
    r <- (if negb (is0 g0) then mret (sc0, Some g0)                (* [comment removed for export] *)
          else if c_eq sc1 (wlit 6) then mret (sc0, Some g0)       (* [comment removed for export] *)
          else if c_ltu (wlit 27) (v_addiw sc0 (-4)) then mret (sc0, Some g0)  (* [comment removed for export] *)
          else if negb (is0 (v_andi sc0 1)) then mret (sc0, None)  (* [comment removed for export] *)
          else us <- m_ld (at_ (v_add A_LOCK (v_slli sc1 3)) 472) ;;  (* [comment removed for export] *)
               if negb (is0 us) then mret (sc0, None)              (* [comment removed for export] *)
               else
                 let sco := v_ori sc0 1 in                          (* [comment removed for export] *)
                 let a1 := v_add A_LOCK (v_slli (v_addiw sco 0) 3) in  (* [comment removed for export] *)
                 g1 <- m_ld (at_ a1 88) ;;                           (* [comment removed for export] *)
                 u1 <- m_ld (at_ a1 472) ;;                          (* [comment removed for export] *)
                 u2 <- (if is0 g1 then mret (v_addi u1 3)            (* [comment removed for export] *)
                        else am <- m_lw (at_ g1 24) ;;               (* [comment removed for export] *)
                             if negb (is0 am) then mret u1           (* [comment removed for export] *)
                             else fm <- m_lw (at_ g1 28) ;;           (* [comment removed for export] *)
                                  if negb (is0 fm) then mret u1      (* [comment removed for export] *)
                                  else mret (v_addi u1 3)) ;;         (* [comment removed for export] *)
                 let sc2 := if c_ltu u2 (wlit 13) then sco else sc0 in  (* [comment removed for export] *)
                 g2 <- m_ld (at_ (v_add A_LOCK (v_slli (v_addiw sc2 0) 3)) 88) ;;  (* [comment removed for export] *)
                 mret (sc2, Some g2)) ;;
    let '(sc, go) := r in
    mk <- (match go with                                          (* [comment removed for export] *)
           | None => mret w0                                      (* [comment removed for export] *)
           | Some g => if is0 g then mret w0 else m_lw (at_ g 24)  (* [comment removed for export] *)
           end) ;;
    let first := v_and mk (v_subw w0 mk) in                       (* [comment removed for export] *)
    gi <- (if negb (is0 first)
           then (* [comment removed for export] *)
                match go with
                | None => mcrash
                | Some g => idx <- m_lbu (v_add A_DEBRUIJN (v_srliw (v_mul (v_and mk (v_subw w0 mk)) DEBRUIJN_MULT) 27)) ;;  (* [comment removed for export] *)
                            m_sw (at_ g 24) (v_subw mk first) ;;    (* [comment removed for export] *)
                            mret (Some (g, idx))
                end
           else let sc3 := v_addiw sc 0 in                        (* [comment removed for export] *)
                idx <- m_alloc_slot ALLOC_FUEL (at_ sp (-144)) sc3 n ;;  (* [comment removed for export] *)
                if c_lts idx w0 then m_unlock ;; mret None         (* [comment removed for export] *)
                else g <- m_ld (at_ (v_add A_LOCK (v_slli sc3 3)) 88) ;;  (* [comment removed for export] *)
                     mret (Some (g, idx))) ;;
    match gi with
    | None => mret w0
    | Some (g, idx) =>
        ctr <- m_lw (at_ A_LOCK 20) ;;                             (* [comment removed for export] *)
        m_unlock ;;                                               (* [comment removed for export] *)
        m_enframe g idx n ctr                                     (* [comment removed for export] *)
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition m_allzerop (p : word) : M word :=
  (* [comment removed for export] *)
  meta <- m_get_meta p ;;
  w <- m_ld (at_ meta 32) ;;                                      (* [comment removed for export] *)
  let sc := v_srli (v_slli w 52) 58 in                            (* [comment removed for export] *)
  let maplen := v_srli w 12 in                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  if c_eq (v_and w (wlit 3072)) (wlit 3072) then mret (wlit 1)     (* [comment removed for export] *)
  else if negb (is0 maplen) && is0 (v_andi w 31)                   (* [comment removed for export] *)
       then szc2 <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;  (* [comment removed for export] *)
            mret (v_sltu (v_addi (v_and w PAGEMASK) (-16)) (v_slli szc2 4))  (* [comment removed for export] *)
       else szc2 <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;  (* [comment removed for export] *)
            mret (v_sltu (v_slli szc2 4) (v_slli szc2 4)).          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zero_bytes (n : word) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat (bv_unsigned n)).

Definition m_memset0 (d n : word) : M word :=
  (if is0 n then mret tt else m_stbytes d (zero_bytes n)) ;; mret d.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint m_zscan (fuel : nat) (a1 a0 a2 : word) : M (word * word) :=
  match fuel with
  | O => mcrash
  | S fuel' =>
    lo <- m_ld (at_ a0 (-16)) ;;                                   (* [comment removed for export] *)
    hi <- m_ld (at_ a0 (-8)) ;;                                    (* [comment removed for export] *)
    if negb (is0 (v_or lo hi)) then mret (v_sub a0 a2, a2)         (* [comment removed for export] *)
    else let a2' := v_addi a2 (-16) in                             (* [comment removed for export] *)
         let a0' := v_addi a0 (-16) in                             (* [comment removed for export] *)
         if negb (is0 a2') then m_zscan fuel' a1 a0' a2'           (* [comment removed for export] *)
         else mret (v_sub a1 a2', a2')                             (* [comment removed for export] *)
  end.

Definition ZSCAN_FUEL : nat := 257%nat.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint m_mal0_loop (fuel : nat) (p pp : word) : M word :=
  match fuel with
  | O => mcrash
  | S fuel' =>
    let a1 := v_addi (v_addi pp (-2048)) (-2048) in                (* [comment removed for export] *)
    r <- m_zscan ZSCAN_FUEL a1 pp (wlit 4096) ;;                   (* [comment removed for export] *)
    let '(d, len) := r in
    pp' <- m_memset0 d len ;;                                      (* [comment removed for export] *)
    let s1 := v_sub pp' p in                                       (* [comment removed for export] *)
    if is0 (v_srli s1 12) then mret s1                             (* [comment removed for export] *)
    else m_mal0_loop fuel' p pp'                                   (* [comment removed for export] *)
  end.

Definition m_calloc (fuel : nat) (sp : word) (m n : word) : M word :=
  if negb (is0 n) && negb (is0 (v_mulhu n m))                     (* [comment removed for export] *)
  then m_sw A_ERRNO (wlit 12) ;; mret w0                          (* [comment removed for export] *)
  else
  let sz := v_mul n m in                                          (* [comment removed for export] *)
  p <- m_malloc (at_ sp (-48)) sz ;;                              (* [comment removed for export] *)
  if is0 p then mret w0                                           (* [comment removed for export] *)
  else
  rep <- m_lw A_MALLOC_REPLACED ;;                                (* [comment removed for export] *)
  keep <- (if is0 rep                                             (* [comment removed for export] *)
           then z <- m_allzerop p ;; mret (negb (is0 z))            (* [comment removed for export] *)
           else mret false) ;;                                    (* [comment removed for export] *)
  if keep then mret p                                             (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  len <- (if is0 (v_srli sz 12) then mret sz                       (* [comment removed for export] *)
          else let pp0 := v_add p sz in                            (* [comment removed for export] *)
               let i := v_srli (v_slli pp0 52) 52 in               (* [comment removed for export] *)
               pp <- m_memset0 (v_and pp0 PAGEMASK) i ;;           (* [comment removed for export] *)
               let d := v_sub pp p in                              (* [comment removed for export] *)
               if is0 (v_srli d 12) then mret d                    (* [comment removed for export] *)
               else m_mal0_loop fuel p pp) ;;                      (* [comment removed for export] *)
  m_memset0 p len.                                                (* [comment removed for export] *)

End WithLayout.
