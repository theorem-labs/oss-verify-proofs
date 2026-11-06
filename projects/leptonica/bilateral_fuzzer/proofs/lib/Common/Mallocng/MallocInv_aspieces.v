(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_aspieces () := "C69OSSVerify5KrLib6Common8Mallocng:MallocTree5mbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree6mcrashC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree1MC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib6Common8Mallocng9MallocOps=m_canary_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LOCKC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib6Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_ldC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib6Common8MallocngBMallocInv_aspieces;as_tryavailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_aspieces7as_takeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>A_SIZE_CLASSESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5m_lhuC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib6Common8Mallocng9MallocOps<m_alloc_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps3is0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4mretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;A_PAGE_SIZEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_aspieces6as_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps4wlitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4c_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_sltuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib6Common8Mallocng9MallocOps<m_alloc_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_aspieces9as_nestedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_aspieces7as_mmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps>m_canary_checkC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib6Common8Mallocng9MallocOps3wm1C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00".
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
Definition as_tryavail (pm m0 : word) : M (option (word * word)%type) :=
  (if is0 m0 then mret None
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
                 mret (Some (m3, mask))
               end
             end).

(* [comment removed for export] *)
Definition as_take (m mask : word) : M word :=
  let first := v_and mask (v_subw w0 mask) in
  m_sw (at_ m 24) (v_subw mask first) ;;
  if is0 first then mcrash
  else m_ctz32 mask.

(* [comment removed for export] *)
Definition as_cnt (sc usage size : word) : M word :=
  (if negb (c_lts (wlit 8) sc)
          then let tb := v_add A_SMALL_CNT_TAB (v_add (v_slli sc 1) sc) in
               t0 <- m_lbu tb ;;
               if negb (c_ltu usage (v_slli t0 2)) then mret t0
               else t1 <- m_lbu (at_ tb 1) ;;
                    if negb (c_ltu usage (v_slli t1 2)) then mret t1
                    else m_lbu (at_ tb 2)
          else t <- m_lbu (v_add A_MED_CNT_TAB (v_andi sc 3)) ;;
               let c0 := (fix halve (k : nat) (a3 : word) : word :=
                            match k with O => a3 | S k' =>
                              if negb (is0 (v_andi a3 1)) then a3
                              else if negb (c_ltu usage (v_slliw a3 2)) then a3
                              else halve k' (v_srliw a3 1)
                            end) 8%nat t in
               mret ((fix shrink (k : nat) (a2 : word) : word :=
                        match k with O => a2 | S k' =>
                          if is0 (v_srli (v_mul size a2) 20) then a2
                          else shrink k' (v_srliw a2 1)
                        end) 40%nat c0)).

(* [comment removed for export] *)
Definition as_tail (sc m p aidx cnt s7 pm : word) : M word :=
  us2 <- m_ld (at_ s7 472) ;;
  m_sd (at_ s7 472) (v_add us2 cnt) ;;
  m_sw (at_ m 24) (v_addi (v_sllw (wlit 2) aidx) (-1)) ;;
  am <- m_lw (at_ m 24) ;;
  m_sw (at_ m 28) (v_add (v_sllw (wlit 2) (v_addi cnt (-1))) (v_xori am (-1))) ;;
  m_sd (at_ m 16) p ;;
  m_sd p m ;;
  mp <- m_ld (at_ m 16) ;;
  ab <- m_lbu (at_ mp 8) ;;
  m_sb (at_ mp 8) (v_or (v_andi ab 224) (v_andi aidx 31)) ;;
  wm2 <- m_ld (at_ m 32) ;;
  m_sd (at_ m 32) (v_addi (v_or (v_or (v_srli (v_slli sc 58) 52) (v_andi (v_addi cnt (-1)) 31))
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
Definition as_nested (rec : word -> word -> word -> M word) (sp sc size m cnt1 a4 s7 pm : word) : M word :=
  let a1 := v_addi a4 12 in
  let n16 := v_srli a4 4 in
  j <- (if c_ltu a1 (wlit 157) then mret n16
        else m_size_to_class_big A_SIZE_CLASSES n16) ;;
  let j' := v_addiw j 0 in
  idx <- rec (at_ sp (-144)) j' a1 ;;
  if c_lts idx w0 then
    m_free_meta_ag (at_ A_LOCK 24) m ;;
    mret wm1
  else
    szj <- m_lhu (v_add A_SIZE_CLASSES (v_slli j' 1)) ;;
    gj <- m_ld (at_ (v_add A_LOCK (v_slli j' 3)) 88) ;;
    ctr <- m_lw (at_ A_LOCK 20) ;;
    p <- m_enframe gj idx (v_addi (v_slli szj 4) (-4)) ctr ;;
    wm <- m_ld (at_ m 32) ;;
    m_sd (at_ m 32) (v_srli (v_slli wm 52) 52) ;;
    c3 <- m_lbu (at_ p (-3)) ;;
    m_sb (at_ p (-3)) (v_addi (v_andi c3 31) 192) ;;
    (fix zl (k : nat) (a2 : word) : M unit :=
       match k with O => mret tt | S k' => m_sb a2 w0 ;; zl k' (v_add a2 size) end)
      (S (Z.to_nat (bv_unsigned cnt1))) (at_ p 12) ;;
    let aidx := v_addi cnt1 (-1) in
  as_tail sc m p aidx cnt1 s7 pm.

(* [comment removed for export] *)
Definition as_mmap (sc req m usage pg size cnt1 a4 s7 pm : word) : M word :=
  let d := v_addiw sc (-7) in
  bn <- (if c_ltu (wlit 31) d then mret (false, None)
         else let a5 := v_add A_LOCK d in
              b <- m_lbu (at_ a5 888) ;;
              us <- m_lbu (at_ a5 856) ;;
              let nosmall := negb (c_ltu b (wlit 100)) in
              (if is0 us then mret tt
               else sq <- m_lbu (at_ A_LOCK 920) ;;
                    if c_lts (wlit 9) (v_sub sq us) then mret tt
                    else if c_ltu b (wlit 99) then m_sb (at_ a5 888) (v_addi b 1)
                    else m_sb (at_ a5 888) (wlit 150)) ;;
              mret (nosmall, Some a5)) ;;
  let '(nosmall, _) := bn in
  sq <- m_lbu (at_ A_LOCK 920) ;;
  sq' <- (if c_eq sq (wlit 255)
          then m_sd (at_ A_LOCK 856) w0 ;; m_sd (at_ A_LOCK 864) w0 ;;
               m_sd (at_ A_LOCK 872) w0 ;; m_sd (at_ A_LOCK 880) w0 ;; mret (wlit 1)
          else mret (v_addi sq 1)) ;;
  m_sb (at_ A_LOCK 920) sq' ;;
  usage2 <- (if c_lts (wlit 31) sc then mret usage
             else if negb (is0 (v_andi sc 1)) then mret usage
             else u1 <- m_ld (at_ s7 480) ;; mret (v_add u1 usage)) ;;
  let cnt2 :=
    if negb (c_ltu usage2 (v_slliw cnt1 2)) then cnt1
    else if nosmall then cnt1
    else let a5 := v_andi sc 3 in
         let a6 := v_slli pg 3 in
         if c_eq a5 (wlit 1) && c_ltu a6 a4 then wlit 2
         else if c_eq a5 (wlit 2) && c_ltu (v_slli pg 2) a4 then wlit 3
         else if is0 a5 && c_ltu a6 a4 then wlit 3
         else if is0 a5 && c_ltu (v_slli pg 1) a4 then wlit 5
         else cnt1 in
  let needed0 := v_mul size cnt2 in
  let needed := v_addi (v_add needed0 (v_and (v_sub (wlit (2^64 - 16)) needed0) (v_addi pg (-1)))) 16 in
  let '(cnt3, needed3) :=
    if nosmall then (cnt2, needed)
    else if c_ltu (wlit 7) cnt2 then (cnt2, needed)
    else let r := v_addi (v_add req (v_and (v_addi pg (-1)) (v_sub (wlit (2^64 - 20)) req))) 20 in
         if c_ltu r (v_addi size 16) then (wlit 1, r)
         else if c_ltu r (v_slli pg 2) then (cnt2, needed)
         else if c_ltu usage2 (v_slliw cnt2 1) then (wlit 1, r)
         else (cnt2, needed) in
  p <- sys_mmap MMrw needed3 ;;
  if c_eq p wm1 then
    m_free_meta_ag (at_ A_LOCK 24) m ;;
    mret wm1
  else
    wm <- m_ld (at_ m 32) ;;
    let aimax := v_divu (wlit 4080) size in
    ctr <- m_lw (at_ A_LOCK 20) ;;
    m_sd (at_ m 32) (v_or (v_srli (v_slli wm 52) 52) (v_and needed3 PAGEMASK)) ;;
    m_sw (at_ A_LOCK 20) (v_addi ctr 1) ;;
    let a2 := if c_ltu cnt3 aimax then cnt3 else aimax in
    let aidx := v_and (v_addi (v_sltu a2 (v_addi a2 (-1))) (-1)) (v_addi a2 (-1)) in
    as_tail sc m p aidx cnt3 s7 pm.

Lemma m_alloc_slot_unfold : forall fuel (sp sc req : word),
  m_alloc_slot (S fuel) sp sc req =
  (cc <- m_canary_load ;;
   let '(gp, cg) := cc in
   let s7 := v_add A_LOCK (v_slli sc 3) in
   let pm := at_ s7 88 in
   res <- (
     m0 <- m_ld pm ;;
     ta <- as_tryavail pm m0 ;;
     match ta with
     | Some (m, mask) => as_take m mask
     | None =>
       szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;
       m <- m_alloc_meta (at_ sp (-64)) ;;
       if is0 m then mret wm1
       else
         usage <- m_ld (at_ s7 472) ;;
         pg <- m_ld A_PAGE_SIZE ;;
         let size := v_slli szc 4 in
         cnt <- as_cnt sc usage size ;;
         let half := v_srli pg 1 in
         let cnt1 := if c_eq cnt (wlit 1) then v_subw (wlit 2) (v_sltu half (v_addi size 16)) else cnt in
         let a4 := v_mul size cnt1 in
         if negb (c_ltu half (v_addi a4 16))
         then as_nested (m_alloc_slot fuel) sp sc size m cnt1 a4 s7 pm
         else as_mmap sc req m usage pg size cnt1 a4 s7 pm
     end) ;;
   m_canary_check gp cg ;;
   mret res).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_aspieces ()) ["WithLayout"] "p'0h02a4h12cci002cch23cnth34cnt1h44fuelh54halfh61mi011mh72m0h82pgh92pmh:3reqh;3resh<2s7h=2sch>4sizeh?2sph@3szchA2tai022tahB5usagei032cgi042gpi054maski061pp;1p;2p;3p;9p;:p;4p-1R0g0000R1p4p7210R2p8P0p10015p4p710p8P2g002;R2p4p710p8g003<j10Tg003aj1VTg004?j1BTP2j1>Tg004bR2j2UTg005Bj1OTg006Nj1GTg007Vj13Tg008;j12Tg008Yj25Tg009Tj2:Tg00:Nj24Tg00;Cj26Tg00<GR0j1TTg00<ij2STg00><j2QTg00?Kj1NTg00@[j2KTg00A`j1HTg00B>j2FTg00CIj1ETg00DKj27Tg00EOj1ATg00F\j3CTg00Gjj2DTg00Hej18Tg00Ihj2@Tg00Jaj29Tg00K\j2?Tg00LWj2ITg00MRj2JTg00NLj2=Tg00OFj1LTg00Odj2MTg00Pol9<Tg00R@l:PTP1j41Tg00SOj3;Tg00T\j2RTg00U6g00UUR1#0R3#0R4#0#0R5#0#0R6#V#BR7%>7R81U77R9P7p,2MLR:#OP2P7P7P8f0R;%G:f4R<%31R=#2'5':P7%33#3#0#0#0#2,4;P7P7P7P7P716:;%T9R>P7f1R?/S;P0P9P8P;P2P7P7P8P;1Q?;n2001106000120101105P7P7%N:f8%21R1'5':,K:P7P7f:%H6'4,F:g00V:R6P8%E;g00VZ,77P7P7f5R2%3=#0#3#3#0#0#0#2'4,6:P7P7%A:,6:f3R=%24'5P7P7P7f=f2R4;C;1D41P7P6P7%81,@?%23#8%25R5,94,?;'IP?n0100000020000P71J=;P7P6P819;5,=4#LfC,M:fBfAR4P<f7R5P?P;f<R8f;R6M9<P4f@P5f6P2P<P?P;P8P6M:Pn0100000020000b0b3b5X27C1b>X87C1XB7C1n0100000020001X67C1X@7C1n10110200021010601XA>C1X77C1g00W\R>P7A;:<=177?V>C1X;7C1b9b<n2001100000121104103X19C1'RX:7X=7W?W4o"). Qed.

Lemma m_alloc_slot_O : forall (sp sc req : word), m_alloc_slot O sp sc req = mcrash.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_aspieces ()) ["WithLayout"] "h03reqh12sch22spp;1p;2g003<j10Tg003aj15Tg004?j12Tg002;j11Tg0015j14Tg00T\j23Tg00UU#0#0#0#0#0#0#5#2R0%10%40'3X00X10W2o"). Qed.

End WithLayout.
