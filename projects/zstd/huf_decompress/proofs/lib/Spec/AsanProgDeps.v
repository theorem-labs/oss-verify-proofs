(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanEmbed
  Harness Adapter Driver ProgA.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanProgDeps () := "C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<AsanProgDeps5aliftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<AsanProgDeps7aset_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib4Spec<AsanProgDeps6aps_soC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00k59OSSVerify5KrLib4Spec<AsanProgDeps3APS01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib4Spec<AsanProgDeps;aptr_addr_MC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Record APS := mkAPS {
  aps_m  : astate;          (* [comment removed for export] *)
  aps_so : stdout_st;       (* [comment removed for export] *)
  aps_resv : list (Z * Z);  (* [comment removed for export] *)
  aps_atop : Z              (* [comment removed for export] *)
}.
Definition aset_m (v : astate) (s : APS) : APS := mkAPS v (aps_so s) (aps_resv s) (aps_atop s).
Definition aset_so (v : stdout_st) (s : APS) : APS := mkAPS (aps_m s) v (aps_resv s) (aps_atop s).

(* [comment removed for export] *)
Definition aps_init (space_beg ptr_array : Z) (resv : list (Z * Z)) (atop : Z) : APS :=
  mkAPS (ainit space_beg ptr_array) stdout_init resv atop.

Local Notation MA := (Monad.M APS) (only parsing).

(* [comment removed for export] *)
Definition alift {R} (t : AM R) : MA R :=
  fun s => ebind (aembed (aps_atop s) t) (fun r => Ret (Ok (r, s))).

(* [comment removed for export] *)
Definition amalloc_M (n : Z) : MA (option AsanCtrl.aptr) :=
  s <- mget ;;
  x <- alift (AsanCtrl.amalloc (aps_atop s) (aps_resv s) (aps_m s) n) ;;
  mupd (aset_m (fst x)) ;;;
  mret (snd x).

Definition afree_M (p : AsanCtrl.aptr) : MA unit :=
  s <- mget ;;
  st' <- alift (AsanCtrl.afree (aps_m s) (Some p)) ;;
  mupd (aset_m st').

Definition aannot_M (p : AsanCtrl.aptr) (cap old new : Z) : MA unit :=
  s <- mget ;;
  st' <- alift (aannotate (aps_m s) p cap old new) ;;
  mupd (aset_m st').

Definition aptr_addr_M (s : APS) (p : AsanCtrl.aptr) : Z := AsanCtrl.aptr_addr (aps_m s) p.

(* [comment removed for export] *)
Definition AAllocAsan : AAlloc :=
  mkAAlloc APS AsanCtrl.aptr amalloc_M afree_M aannot_M aptr_addr_M aps_so aset_so.

(* [comment removed for export] *)
Lemma aps_get_set : forall v s, aps_so (aset_so v s) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanProgDeps ()) [] "h01sh11vp;2p-1R0p10000R1p4p710p8P0p1000ap4p7210p8p1001Vp4p710R0P1p4p7210p8P0p1002RR1p4p7210p8P0P1p4p73110p8g003Fj20Tg003`R1g004[f1,01W0W1o"). Qed.
Lemma aps_set_set : forall v w s, aset_so v (aset_so w s) = aset_so v s.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanProgDeps ()) [] "h01sh11vh21wp;2g005Wj21Tg003Fj20Tg003`R0g004[R1f2f0'1,01W0X20W1o"). Qed.
Lemma aps_set_get : forall s, aset_so (aps_so s) s = s.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanProgDeps ()) [] "p'0h01mh12rvh21sh32soh42tpi001ai018aps_atopi025aps_mi038aps_resvi046aps_sop;1p;2p;3p;4p1001Vp4p710R0p1006Up4p710p8p1007Jp4p70R1p10000p4p7210p8P1P0p8P1p1008Ap4p7210p8P1p1000aR0p4p7210p8P1P0p4p73110p8P1p10095p4p7210p8g009Rj16Tg005Wj25Tg00:Oj30Tg00:ij21Tg00;Ij14Tg00;ij42Tg003Fj23Tg004[R1P1f0R0#6/50=010P0g00<eg003`g00=`R2/12#4f3R3f2R4f1R5P0C2,31X42W1W3W0P3P4P5P0O4n01100000140102104103101W2o"). Qed.
Lemma aps_addr_so : forall v s p, aptr_addr_M (aset_so v s) p = aptr_addr_M s p.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanProgDeps ()) [] "h01ph11sh21vp;2g00>>j21Tg003Fj20Tg003`g004[g007Jg00=`f1f0'1'0W0W1W2o"). Qed.

(* [comment removed for export] *)
Lemma alift_ret : forall {R} (r : R) (s : APS), alift (SRet r) s = Ret (Ok (r, s)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanProgDeps ()) [] "h01Rh11rh21sp;2p;1p;4p;3p200R0p1001Vp4p710p8g00:ij26Tg00?@j15Tg00@8j20Tg00@nj41Tg00ANj24Tg00BFj32Tg003Fj23Tf0R1g004[R2g00C<R3f2R4/62R5#5R6'0P4P2f1P1C1,459236'3W2W1X00o"). Qed.

(* [comment removed for export] *)
Definition progAsan_tree (s0 : APS) (rs : Z) (argv : list (list Z)) : itree node (exc unit) := progA_tree AAllocAsan s0 rs argv.
