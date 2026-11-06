(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_ntpieces () := "C69OSSVerify5KrLib6Common8Mallocng:MallocTree5mbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree1MC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_sdC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_ldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps3is0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree7massertC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_ntpieces8nt_queueC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4unit00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib6Common8Mallocng9MallocOps2w0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib6Common8Mallocng9MallocOps=m_canary_loadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4m_lwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps4wlitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_sllwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_srliC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_ntpieces9nt_okcompC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOpsAm_nontrivial_freeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_ntpieces:nt_freegrpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngBMallocInv_ntpieces7nt_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9MallocOps>m_canary_checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree4mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib6Common8Mallocng:MallocTree6mcrashC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
Definition nt_okcomp (g w mask self sc : word) : M bool :=
  if is0 (v_andi w 32) then mret false
         else if negb (c_eq (v_addw mask self)
                              (v_addiw (v_sllw (wlit 2) w) (-1)))
         then mret false
         else if c_ltu (wlit 47) sc then mret true
         else
           let last := v_andi w 31 in
           let maplen := v_srli w 12 in
           stride_small <-
             (if negb (is0 maplen) && is0 last
              then
                   szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;
                   mret (c_ltu (v_addi (v_and w PAGEMASK) (-16)) (v_slli szc 4))
              else scs <- m_lhu (v_add A_SIZE_CLASSES (v_andi (v_srli w 5) 126)) ;;
                   if is0 maplen then mret true
                   else szc <- m_lhu (v_add A_SIZE_CLASSES (v_slli sc 1)) ;;
                        mret (c_ltu (v_slli scs 4) (v_slli szc 4))) ;;
           if stride_small then mret true
           else if is0 maplen then mret true
           else
             nx <- m_ld (at_ g 8) ;;
             if negb (c_eq nx g) then mret true
             else if c_ltu (wlit 31) (v_addi sc (-7)) then mret true
             else b <- m_lbu (at_ (v_add A_CTX (v_addi sc (-7))) 880) ;;
                  if c_ltu b (wlit 100) then mret true
                  else us <- m_ld (at_ (v_add A_CTX (v_slli sc 3)) 464) ;;
                       if c_ltu us (v_addi (v_add (v_slli last 3) last) 9)
                       then mret false
                       else if c_ltu (wlit 18) last then mret false
                       else mret true.

(* [comment removed for export] *)
Definition nt_deq (a1 g nx : word) : M unit :=
  if c_eq nx g
  then m_sd (at_ a1 80) w0
  else pv <- m_ld g ;;
       m_sd (at_ pv 8) nx ;;
       pv2 <- m_ld g ;;
       nx2 <- m_ld (at_ g 8) ;;
       m_sd nx2 pv2 ;;
       h <- m_ld (at_ a1 80) ;;
       if c_eq h g then n3 <- m_ld (at_ g 8) ;; m_sd (at_ a1 80) n3
       else mret tt.

(* [comment removed for export] *)
Definition nt_activate (a1 : word) : M unit :=
  m2 <- m_ld (at_ a1 80) ;;
  if is0 m2 then mret tt
  else
       am <- m_lw (at_ m2 24) ;; massert (is0 am) ;;
       mp <- m_ld (at_ m2 16) ;;
       ab <- m_lbu (at_ mp 8) ;;
       let act2 := v_sllw (wlit 2) ab in
       massert (is0 (v_andi (at_ m2 28) 3)) ;;
       fr2 <- m_lw (at_ m2 28) ;;
       m_sw (at_ m2 28) (v_and fr2 (v_subw w0 act2)) ;;
       m_sw (at_ m2 24) (v_and fr2 (v_addi act2 (-1))).

(* [comment removed for export] *)
Definition nt_deqact (g nx sc : word) : M unit :=
  massert (c_ltu sc (wlit 48)) ;;
  let a1 := v_add A_CTX (v_slli sc 3) in
  act <- m_ld (at_ a1 80) ;;
  nt_deq a1 g nx ;;
  m_sd g w0 ;; m_sd (at_ g 8) w0 ;;
  (if negb (c_eq act g) then mret tt
   else nt_activate a1).

(* [comment removed for export] *)
Definition nt_usage (g w2 sc2 : word) : M word :=
  if c_ltu (wlit 47) sc2 then mret w2
  else let a3 := v_add A_CTX (v_slli sc2 3) in
       us <- m_ld (at_ a3 464) ;;
       m_sd (at_ a3 464) (v_add us (v_ori (v_xori w2 (-1)) (-32))) ;;
       m_ld (at_ g 32).

(* [comment removed for export] *)
Definition nt_fg_root (g sc2 : word) : M (word * word)%type :=
  sq <- m_seq_next A_CTX ;;
  let d := v_addi sc2 (-7) in
  m_sb (at_ A_CTX 912) sq ;;
  (if c_ltu (wlit 31) d then mret tt
   else m_sb (at_ (v_add A_CTX d) 848) sq) ;;
  w4 <- m_ld (at_ g 32) ;;
  base <- m_ld (at_ g 16) ;;
  m_free_meta (at_ A_CTX 16) g ;;
  mret (base, v_and w4 PAGEMASK).

(* [comment removed for export] *)
Definition nt_fg_nested (rec : word -> word -> M (word * word)%type) (g : word) : M (word * word)%type :=
  p <- m_ld (at_ g 16) ;;
  mm <- m_get_meta p ;;
  p2 <- m_ld (at_ g 16) ;;
  c3 <- m_lbu (at_ p (-3)) ;;
  m_sd p2 w0 ;;
  mi <- rec mm (v_andi c3 31) ;;
  m_free_meta (at_ A_CTX 16) g ;;
  mret mi.

Definition nt_fg (rec : word -> word -> M (word * word)%type) (g : word) : M (word * word)%type :=
  w2 <- m_ld (at_ g 32) ;;
  let sc2 := v_srli (v_slli w2 52) 58 in
  w3 <- nt_usage g w2 sc2 ;;
  (if negb (is0 (v_srli w3 12))
   then nt_fg_root g sc2
   else nt_fg_nested rec g).

(* [comment removed for export] *)
Definition nt_freegrp (rec : word -> word -> M (word * word)%type) (g w sc : word) : M (word * word)%type :=
  nx <- m_ld (at_ g 8) ;;
  (if is0 nx then mret tt
   else nt_deqact g nx sc) ;;
  nt_fg rec g.

(* [comment removed for export] *)
Definition nt_queue (hda g act : word) : M unit :=
  if is0 act
  then m_sd g g ;; m_sd (at_ g 8) g ;; m_sd hda g
  else m_sd (at_ g 8) act ;;
       ap <- m_ld act ;;
       m_sd g ap ;;
       m_sd (at_ ap 8) g ;;
       n2 <- m_ld (at_ g 8) ;;
       m_sd n2 g.

(* [comment removed for export] *)
Definition nt_requeue (g sc : word) : M unit :=
  massert (c_ltu sc (wlit 48)) ;;
  let a3 := v_add A_CTX (v_slli sc 3) in
  act <- m_ld (at_ a3 80) ;;
  if c_eq act g then mret tt
  else
       nx <- m_ld (at_ g 8) ;; massert (is0 nx) ;;
       pv <- m_ld g ;; massert (is0 pv) ;;
       nt_queue (at_ a3 80) g act.

(* [comment removed for export] *)
Definition nt_keep (g mask self sc : word) : M (word * word)%type :=
  (if negb (is0 mask) then mret tt
   else nt_requeue g sc) ;;
  massert (is0 (v_andi (at_ g 28) 3)) ;;
  fr3 <- m_lw (at_ g 28) ;;
  m_sw (at_ g 28) (v_or fr3 self) ;;
  mret (w0, w0).

Lemma m_free_meta_unfold : forall hda g,
  m_free_meta hda g =
  (m_sd (at_ g 8) w0 ;; m_sd g w0 ;; m_sd (at_ g 16) w0 ;; m_sd (at_ g 24) w0 ;; m_sd (at_ g 32) w0 ;;
   nx <- m_ld (at_ g 8) ;; massert (is0 nx) ;;
   pv <- m_ld g ;; massert (is0 pv) ;;
   hd <- m_ld hda ;;
   nt_queue hda g hd).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_ntpieces ()) ["WithLayout"] "h01gh12hdh23hdah32nxh42pvp;1p;2p;3p;4g0000R0p4p7210g0015R1p4p710p8g0026j10Tg002[j1>Tg0039j1<TP1j17Tg003\j15Tg004:j23Tg004oj32Tg0063j1;Tg006Xj26Tg007\j1:Tg008^j18Tg009ej39TP0j44Tg00;5j2=Tg00;OR0P0f1R1f0R2C4p=1g00;oR3#0#0#0R4#0R5#0R6#0#>#<R7%70p,2MLR8%54R4,32g00<TR932A2819f2%55'3=289f3%;3#0#0#0#5'3=289f4%56'3=289P7P0f5/34,68%:2#8R4P7P0f7,68P7P0f:R9,68f;?992X17C4V0,14X47C4V0'1X37C4V0'1V0'1V0'1V0'1V0'1'=X07W2o"). Qed.

Lemma m_free_meta_ag_unfold : forall hda g,
  m_free_meta_ag hda g =
  (m_sd (at_ g 8) w0 ;; m_sd (at_ g 32) w0 ;; m_sd (at_ g 24) w0 ;; m_sd (at_ g 16) w0 ;; m_sd g w0 ;;
   nx <- m_ld (at_ g 8) ;; massert (is0 nx) ;;
   pv <- m_ld g ;; massert (is0 pv) ;;
   hd <- m_ld hda ;;
   nt_queue hda g hd).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_ntpieces ()) ["WithLayout"] "h01gh12hdh23hdah32nxh42pvp;1p;2p;3p;4g0026j10Tg002[j1>Tg0039j1<Tg0015j17Tg003\j15Tg004:j23Tg004oj32Tg0063j1;Tg006Xj26Tg007\j1:Tg008^j18Tg009ej39Tg0000j44Tg00;5j2=Tg00;OR0P0f1R1f0R2C4p=1g00;oR3#0#0#0R4#0R5#0R6#0#>#<R7%70p,2MLR8%54R4,32g00<TR932%56,31=289f2%;3#0#0#0#5'3=289f3%55'3=289f4=289P7P0f5/34,68%:2#8R4P7P0f7,68P7P0f:R9,68f;?992X17C4V0,14X47C4V0'1X37C4V0'1V0'1V0'1V0'1V0'1'=X07W2o"). Qed.

Lemma m_ntfree_unfold : forall fuel (g i : word),
  m_nontrivial_free (S fuel) g i =
  (cc <- m_canary_load ;;
   let '(gp, cg) := cc in
   w <- m_ld (at_ g 32) ;;
   fr <- m_lw (at_ g 28) ;;
   av <- m_lw (at_ g 24) ;;
   let self := v_sllw (wlit 1) i in
   let mask := v_or av fr in
   let sc := v_srli (v_slli w 52) 58 in
   ok <- nt_okcomp g w mask self sc ;;
   res <- (if ok then nt_freegrp (m_nontrivial_free fuel) g w sc else nt_keep g mask self sc) ;;
   m_canary_check gp cg ;;
   mret res).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_ntpieces ()) ["WithLayout"] "p'0h02avh12cci002cch22frh34fuelh41gh51ih64maskh72oki012okh83resh92sch:4selfh;1wi022cgi032gpp;1p;2p;5p;4p;3g0026j10Tg002[j1GTg0039j1;Tg00=UR0j26Tg0015j1FTg00>5j1@Tg003\j12Tg004:j24Tg006Xj27Tg0063j13Tg00?Aj25Tg00@Ej18Tg00AHj29Tg00BCj2ETg00C<j2DTg00D7j2CTg00E2j5?Tg00FCj2=Tg00GSj4>Tg00Hej4<Tg00J4j3ATg00KAj2BTg0000j41Tg00;5j2:Tg00LEg00;oR1#0#0#0#0#0R2#0#G#;R31633R4#FR5P4P4p,2MLR6#@P0P3P3P5f0R0P3P4f4R7%22'4,76P3P4f5R2%31R8#3#0R9#0#2'4,56P3P4f6R:%08R8#0#0#2'4,56%21#8/9:P3f1R1f2R;'EP3%38#0#0#2,D7%39#0#2'CP3g00LdR9P4f:P2P1P;P0D?P4P4P9P5P0f<,=6f;R0P:P1C>P0P;f3P1C<n0110100020000g00;OR;P4f9f85A61B41V;C1X84C1X79C1b9b6b:X03C1X23C1X;3C1n2001100000121103102X14C1':X53W4W3o"). Qed.

Lemma m_ntfree_O : forall (g i : word), m_nontrivial_free O g i = mcrash.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_ntpieces ()) ["WithLayout"] "h01gh11ip;1p;2g0026j10Tg002[j16Tg0039j12Tg00=Uj21Tg0015j15Tg00MDj14Tg00;5j23Tg00;o#0#0#0#0#0#0#6#2R01100R1#5%41'3X10W0o"). Qed.

End WithLayout.

