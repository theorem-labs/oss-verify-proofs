(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AKinvM AInstDepot AInstPop AInstGen AVst AVstT.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Ltac2 gd_tbl_AInstSec () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.prod"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_hulls"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "ARUN_1.InstSec.saneL"; "ARUN_1.InstSec.vL"; "ARUN_1.InstSec.vLP"; "Stdlib.ZArith.BinInt.Z.min"; "Stdlib.ZArith.BinInt.Z.mul"; "ARUN_1.InstSec.base"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vranges_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.RES_DEPOT"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.VLIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_cb20"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.J20"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_cb23"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.J23"; "Corelib.Init.Logic.iff"; "ARUN_1.InstSec.CSb"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.InstSec.Ks"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.Kd"; "ARUN_1.InstSec.CSs"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.CSd"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.hull64"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "ARUN_1.InstSec.Gl"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "ARUN_1.InstSec.Gp"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.HKv"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "ARUN_1.InstSec.Gn"; "ARUN_1.InstSec.Gs"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "Stdlib.Lists.List.fold_right"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_lazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_eager"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.sane"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "ARUN_1.InstSec.vexit_s"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition RES_SLICE : Z := 0x20000 + 4096 * (0x20000 / 32768 + 3).
Definition RES_MAP (msz : Z) : Z := msz + 4096 * (msz / 32768 + 3).
Definition RES_SEC (msz : Z) : Z := RES_MAP msz + RES_SLICE + RES_DEPOT.

Section InstSec.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.
  Hypothesis GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0.
  Hypothesis GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0.

  Variable v0 : vst.
  Variable H : Z * Z.          (* [comment removed for export] *)
  Variables (U0 r0 msz : Z).   (* [comment removed for export] *)
  Variables nb0 bl0 : list Z.
  Hypothesis VR0 : vranges_ok AL v0.
  Hypothesis VWF0 : vwf AL v0.
  Hypothesis HH : In H (v_hulls v0).
  Hypothesis H68 : 0x65f000 <= fst H.
  Hypothesis HU : fst H <= U0 /\ U0 + 0x20000 <= fst H + snd H /\ U0 mod 4096 = 0.
  Hypothesis EU0 : U0 = fst H + 0x20000 * r0.
  Hypothesis APT_P : forall t, In t (v_tr v0) -> U0 + 0x20000 <= t_lo t \/ t_hi t <= U0.
  Hypothesis UN0 : v_unit v0 U0 0x20000.   (* [comment removed for export] *)
  Hypothesis MSZ : 0x11000 <= msz /\ msz mod 4096 = 0.
  Hypothesis SLACK : v_eb v0 + 4096 * vnb v0 + RES_SEC msz <= VLIMIT.
  Hypothesis CB20 : v_cb20 v0 + (msz / 2^20 + 2) < J20.
  Hypothesis CB23 : v_cb23 v0 + (msz / 2^23 + 2) + (2^20 / 2^23 + 2) < J23.

  (* [comment removed for export] *)
  Definition saneL (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "(0.(1.+65?000.O1.)(0.(2.$3.(4.O1.+1000.)=)(0.(1.(5.O1.Vmsz,)(6.VhAR,))(0.(7.(1.(5.O1.Vmsz,)+7???7000.)(1.+10007???8000.O1.))(0.Px,$3.P,(8.VAL,Vv0,R1.)(9.(0.(1.O1.R2.)(:.R2.(5.O1.Vmsz,))))PH',(;.$3.$3.)P,(<.(;.$3.$3.)R1.(=.Vv0,))(7.(1.(5.O1.Vmsz,)(>.$3.$3.R2.))(1.(5.(>.$3.$3.R2.)(?.$3.$3.R2.))O1.)))))))")
(* [comment removed for export] *).

  Definition vL (a : Z) : vst := v_add_eager v0 a msz true.
  Definition vLP (a : Z) : vst := v_add_sub (vL a) U0 0x20000 true.

  Definition base (sc : list (Z * Z)) (r : Z) (v : vst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "(7.(0.(2.(10.(;.$3.$3.))O3.(11.(;.$3.$3.)))(0.(2.$3.O2.Vr0,)(2.$12.O1.Vv0,)))(13.$3.La,$3.(0.(2.(10.(;.$3.$3.))O3.(14.(;.$3.$3.)(15.$3.$3.R1.Vmsz,)(11.(;.$3.$3.))))(0.(16.R1.)(7.(0.(2.$3.O2.Vr0,)(2.$12.O1.(17.R1.)))(0.(2.$3.O2.(5.Vr0,+1.))(2.$12.O1.(18.R1.))))))))")
(* [comment removed for export] *).

  Definition Ks (sc : list (Z * Z)) (r : Z) (nb bl : list Z) (mo : Model) : Prop :=
    exists v, base sc r v /\ Kd AL v nb0 bl0 nb bl mo.
  Definition CSb (sc : list (Z * Z)) (r : Z) (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "(7.(8.VAL,Vv0,O1.)(7.(13.$3.La,$3.(0.(<.(;.$3.$3.)(15.$3.$3.R1.Vmsz,)O3.)(0.(16.R1.)(0.(1.R1.O1.)(:.O1.(5.R1.Vmsz,))))))(0.(1.VU0,O1.)(:.O1.(19.(5.(>.$3.$3.VH,)(1:.+20000.O2.))(5.(>.$3.$3.VH,)(?.$3.$3.VH,)))))))")
(* [comment removed for export] *).
  Definition CSs (sc : list (Z * Z)) (r : Z) (nb bl : list Z) (x : Z) : Prop := CSb sc r x \/ Dnew nb0 bl0 nb bl x.
  (* [comment removed for export] *)
  Definition Gl (sc : list (Z * Z)) (r m : Z) : Prop := sc = [] /\ r = r0 /\ m = msz.
  Definition Gp (sc : list (Z * Z)) (r : Z) : Prop := r = r0 /\ length sc = 1%nat.
  Definition Gn (sc : list (Z * Z)) (r : Z) (nb bl : list Z) : Prop := nb = nb0 /\ bl = bl0.
  Definition Gs (sc : list (Z * Z)) (r : Z) (nb bl : list Z) : Prop := bl = bl0 /\ (nb = nb0 \/ exists x, nb = nb0 ++ [x]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L20892999462.2900000HS3hAR2AL1H2U03msz3H682HU". (* [comment removed for export] *)
  #[using="hAR AL v0 H msz VWF0 HH H68 HU MSZ"] Lemma U00 : 0 <= U0. Proof. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59315036641.700000CS1H2U02r03EU01x1A1B". (* [comment removed for export] *)
  #[using="EU0"] Lemma slice_r0 : forall x, ~ (U0 <= x < Z.min (fst H + 0x20000 * r0) (fst H + snd H)).
  Proof. intros x [A B]. apply Z.min_glb_lt_iff in B. clear - A B EU0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L29277659196.7L65767658107.800000C00WS1H2U02r03EU01x1A1BS1H2U02r02HU3EU01x1B". (* [comment removed for export] *)
  #[using="HU EU0"] Lemma slice_r1 : forall x, U0 <= x < Z.min (fst H + 0x20000 * (r0 + 1)) (fst H + snd H) <-> U0 <= x < U0 + 0x20000.
  Proof.
    intros x. split.
    - intros [A B]. apply Z.min_glb_lt_iff in B. clear - A B EU0. lia.
    - intros [A B]. split; [exact A|]. apply Z.min_glb_lt_iff. clear - A B EU0 HU. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma vcs_eagerT : forall v lo n x, vcs AL (v_add_eager v lo n true) x <-> vcs AL v x \/ lo <= x < lo + n.
  Proof.
    intros v lo n x. unfold vcs. cbn [v_stk v_img v_tr v_add_eager]. split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [left; left; exact A| left; right; left; exact A| right; unfold t_hi in R; cbn in R; exact R|].
      left. right. right. exists t. split; [exact Ht| split; [exact TC| exact R]].
    - intros [[A|[A|(t & Ht & TC & R)]]|R]; [left; exact A| right; left; exact A| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]|].
      right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn [t_cs t_lo t_len]. split; [reflexivity| exact R].
  Qed.
  #[using="Type"] Lemma vcs_subT : forall v lo n x, vcs AL (v_add_sub v lo n true) x <-> vcs AL v x \/ lo <= x < lo + n.
  Proof.
    intros v lo n x. unfold vcs. cbn [v_stk v_img v_tr v_add_sub]. split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [left; left; exact A| left; right; left; exact A| right; unfold t_hi in R; cbn in R; exact R|].
      left. right. right. exists t. split; [exact Ht| split; [exact TC| exact R]].
    - intros [[A|[A|(t & Ht & TC & R)]]|R]; [left; exact A| right; left; exact A| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]|].
      right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn [t_cs t_lo t_len]. split; [reflexivity| exact R].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926615958.36L20895211806.36L26985825249.36L38849812302.5 L50655523930.5 L59582475468.36L66302206036.5 00000F00\01601F01V02002AS3hAR2AL2U03msz4U00'1aS3hAR2AL2U03msz4U00'1aS3hAR2AL2U03msz4U00'1a3A68S2v03msz4CB232M0S2v03msz4CB202M0S3hAR2AL2U03msz3MSZ4U00'1aS2v03msz5SLACK2M0". (* [comment removed for export] *)
  #[using="VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Lemma base_facts : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pv,$12.P,(1;.R3.R2.R1.)(0.(1<.VAL,R2.)(0.(1.(5.(5.(1=.R2.)(1:.+1000.(1>.R2.)))$1?.)$20.)(0.(:.(21.R2.)$22.)(0.(:.(5.(23.R2.)(5.(24.(25.+2.+14.)(25.+2.+17.))+2.))$26.)Px,$3.(27.(28.R5.R4.R1.)(8.VAL,R3.R1.))))))")
(* [comment removed for export] *).
  Proof.
    pose proof U00 as U00'. pose proof MSZ as [M0 MAL].
    intros sc r v [(-> & -> & ->)|(a & -> & SA & [(-> & ->)|(-> & ->)])].
    - split; [exact VR0|]. split; [unfold RES_SEC, RES_MAP, RES_SLICE in SLACK; pose proof (Z.div_pos msz 32768) as DP; clear - SLACK M0 DP; lia|]. split; [pose proof (Z.div_pos msz (2^20)) as DP; clear - CB20 M0 DP; lia|].
      split; [pose proof (Z.div_pos msz (2^23)) as DP; clear - CB23 M0 DP; lia|].
      intros x. unfold CSb. split; [intros [A|[(a & E & _)|R]]; [exact A| destruct E| exfalso; exact (slice_r0 x R)]| intros A; left; exact A].
    - dpose SA as (A68 & AAL & ACE & ALH & _). unfold vL. split; [apply vranges_ok_eager; [exact VR0| lia| lia]|].
      split; [rewrite vnb_add_eager; cbn [v_eb v_add_eager]; unfold RES_SEC, RES_MAP, RES_SLICE in SLACK; pose proof (Z.div_pos msz 32768) as DP; clear - SLACK M0 DP; lia|].
      split; [cbn [v_cb20 v_add_eager]; exact CB20|]. split; [cbn [v_cb23 v_add_eager]; exact CB23|].
      intros x. unfold CSb. rewrite vcs_eagerT. split.
      + intros [A|[(a' & [E|[]] & _ & R)|R]]; [left; exact A| injection E as ->; right; exact R| exfalso; exact (slice_r0 x R)].
      + intros [A|R]; [left; exact A| right; left; exists a; split; [left; reflexivity| split; [exact SA| exact R]]].
    - dpose SA as (A68 & AAL & ACE & ALH & _). unfold vLP, vL. split; [apply vranges_ok_sub; [apply vranges_ok_eager; [exact VR0| lia| lia]| lia| lia]|].
      split; [rewrite vnb_add_sub, vnb_add_eager; cbn [v_eb v_add_sub v_add_eager]; unfold RES_SEC, RES_MAP, RES_SLICE in SLACK; pose proof (Z.div_pos msz 32768) as DP; clear - SLACK M0 DP; lia|].
      split; [cbn [v_cb20 v_add_sub v_add_eager]; exact CB20|]. split; [cbn [v_cb23 v_add_sub v_add_eager]; exact CB23|].
      intros x. unfold CSb. rewrite vcs_subT, vcs_eagerT. split.
      + intros [A|[(a' & [E|[]] & _ & R)|R]]; [left; left; exact A| injection E as ->; left; right; exact R| right; apply slice_r1; exact R].
      + intros [[A|R]|R]; [left; exact A| right; left; exists a; split; [left; reflexivity| split; [exact SA| exact R]]| right; right; apply slice_r1; exact R].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Lemma Ks_cases : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.P,(2:.R5.R4.R3.R2.R1.)(13.$12.Lv,$12.(0.(1;.R7.R6.R1.)(0.(2;.VhAR,VAL,R1.Vnb0,Vbl0,R5.R4.R3.)(0.(1<.VAL,R1.)(0.(1.(5.(5.(1=.R1.)(1:.+1000.(1>.R1.)))$1?.)$20.)(0.(:.(21.R1.)$22.)(0.(:.(5.(23.R1.)(5.(24.(25.+2.+14.)(25.+2.+17.))+2.))$26.)Px,$3.(27.(2<.R8.R7.R6.R5.R1.)(2=.VhAR,VAL,R2.Vnb0,Vbl0,R6.R5.R1.)))))))))")
(* [comment removed for export] *).
  Proof.
    (intros sc r nb bl mo dd_H; ddestruct dd_H as (v & B & K)). dpose (base_facts sc r v B) as (VR & SL & C1 & C2 & EQ).
    exists v. split; [exact B|]. split; [exact K|]. split; [exact VR|]. split; [exact SL|]. split; [exact C1|]. split; [exact C2|].
    intros x. unfold CSs, CSd, Dnew. rewrite EQ. tauto.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26939874085.54L26939874085.56L26944018597.6200000d01i030S3hAR2AL2v02U03msz1x1Y4STK04STK23HG13HS13AW13G643S64S3hAR2AL2U03msz1x1Y2G12G23HG13HS13HG33HS33HG23HS23AW03AW13G643S643ACBS3hAR2AL3IML2U03msz1x1t1R3HG13HS13HG33HS33AW13G643S643ACB2T02T12T22T61B". (* [comment removed for export] *)
  #[using="hAR ALWF IML IMH GOT64 GSB64 H U0 msz VWF0 H68 HU MSZ"] Lemma vcs0_range : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Px,$3.P,(8.VAL,Vv0,R1.)(0.(0.(1.=R2.)(:.R2.(25.+2.+2?.)))(0.(7.(1.(5.R2.+1.)+7???7000.)(1.+10007???8000.R2.))(0.(9.(0.(1.(2>.(2?.VAL,))R2.)(:.R2.(5.(2>.(5.(2?.VAL,)+7.))+40.))))(9.(0.(1.(2>.(30.VAL,))R2.)(:.R2.(5.(2>.(5.(30.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. dpose VWF0 as (TWF & _ & _ & _ & _ & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & _ & BANDCS & _).
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). pose proof GOT64 as G64. pose proof GSB64 as S64.
    aceilb. rewrite IMH in *.
    destruct Hx as [Y|[(Y & G1 & G2)|(t & Ht & TC & R)]].
    - lia.
    - rewrite IMG0, IMG1 in Y. lia.
    - pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _ & _ & _ & T6). pose proof (BANDCS t Ht TC) as B.
      unfold t_hi in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L26937893271.56L26939875247.6000001D02PS3hAR2AL1H2U03msz3H682HU1r1x2R12R23HG13HS13HG33HS33HG23HS23G643S642W22W53ACB4IMH'2H0S3hAR2AL1H2U03msz1x1a1R3HG13HS13HG33HS33HG23HS23G643S643ACB4IMH'3A683ACE3ALH". (* [comment removed for export] *)
  #[using="ALWF IML IMH GOT64 GSB64 VWF0 HH H68 HU MSZ"] Lemma CSb_range : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Px,$3.P,(28.R3.R2.R1.)(0.(0.(1.=R2.)(:.R2.(25.+2.+2?.)))(0.(7.(1.(5.R2.+1.)+7???7000.)(1.+10007???8000.R2.))(0.(9.(0.(1.(2>.(2?.VAL,))R2.)(:.R2.(5.(2>.(5.(2?.VAL,)+7.))+40.))))(9.(0.(1.(2>.(30.VAL,))R2.)(:.R2.(5.(2>.(5.(30.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros sc r x Hx.
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3;
          pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2).
    dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). pose proof GOT64 as G64. pose proof GSB64 as S64.
    dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH) as (W0 & W1 & W2 & W3 & W4 & W5). aceilb. pose proof IMH as IMH'.
    destruct Hx as [A|[(a & _ & SA & R)|[R1 R2]]].
    - exact (vcs0_range x A).
    - dpose SA as (A68 & AAL & ACE & ALH & _). lia.
    - apply Z.min_glb_lt_iff in R2. pose proof U00. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26939874085.49000015S3hAR2AL5GOT645GSB642U03msz1x1b2SB1R3HG13HS13HG33HS33HG23HS24IMH'3ACB". (* [comment removed for export] *)
  #[using="ALWF IML IMH GOT64 GSB64 VWF0 HH H68 HU MSZ"] Lemma CSs_range : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Px,$3.P,(2<.R5.R4.R3.R2.R1.)(0.(0.(1.=R2.)(:.R2.(25.+2.+2?.)))(0.(7.(1.(5.R2.+1.)+7???7000.)(1.+10007???8000.R2.))(0.(9.(0.(1.(2>.(2?.VAL,))R2.)(:.R2.(5.(2>.(5.(2?.VAL,)+7.))+40.))))(9.(0.(1.(2>.(30.VAL,))R2.)(:.R2.(5.(2>.(5.(30.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl x [A|[(b & _ & SB & R)|(b & _ & SB & R)]]; [exact (CSb_range sc r x A)| |].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3;
          pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2).
    - dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). pose proof IMH as IMH'. unfold sane in SB. aceilb. lia.
    - dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). pose proof IMH as IMH'. unfold sane in SB. aceilb. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L24113840608.45L34213488593.45L35076878331.50L55345830981.45L59309005527.44L59309021649.48L59579064880.37L63368316718.44L63368414506.43L63380896567.49L68390599587.43L68394632638.49L9846669346.44 00000@00P01601F02?03;03F03S03^03i04904I04YS2AL2U03msz1c2H0S2AL2U03msz1c2H1S2AL5GOT645GSB642U03msz1c1i2Hi4IMH'2H0S2AL2U03msz1c2R1S2AL3IMH5GOT645GSB642U03msz3HG13HS13HG33HS31i2Hi2R12R32R4S2AL3IMH5GOT645GSB642U03msz3HG13HS13HG33HS31c2R12R22H02S12S2S2AL2U03mszS2AL2U03msz1cS2AL2U03mszS2AL2U03mszS2AL2U03msz1c2R1S2AL2U03msz1c2R1S2AL2U03msz1c2R1". (* [comment removed for export] *)
  #[using="ALWF ASB IML IMH GOT64 GSB64 VWF0 HH H68 HU MSZ"] Theorem S_CSOK : forall sc r nb bl, cs_ok AL (CSs sc r nb bl).
  Proof.
    intros sc r nb bl. split; [| split; [| split]].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3;
          pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2).
    - intros c Hc. dpose (CSs_range sc r nb bl c Hc) as (R1 & R2 & R3 & R4). unfold shadow_of. rewrite ASB.
      pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). assert (c / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47 / 8) with 17592186044416 in *.
      split; [lia|]. split; [lia|]. split; [lia|]. intros Hs. pose proof (CSs_range sc r nb bl _ Hs) as (S1 & S2 & _). lia.
    - intros i Hi. split; intros Hc; pose proof (CSs_range sc r nb bl _ Hc) as (R1 & R2 & R3 & R4); lia.
    - intros c i Hc Hi. pose proof (CSs_range sc r nb bl c Hc) as (R1 & _). dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). pose proof IMH as IMH'.
      unfold shadow_of. rewrite ASB. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). lia.
    - rewrite ASB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2510930669.3400000?S2AL2U03msz1x1R". (* [comment removed for export] *)
  #[using="ALWF IML IMH GOT64 GSB64 VWF0 HH H68 HU MSZ"] Theorem S_noshadow : forall sc r nb bl x, CSs sc r nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Proof. intros sc r nb bl x Hx. dpose (CSs_range sc r nb bl x Hx) as (_ & R & _). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Theorem S_CSmono_l : forall sc r p y, CSs sc r nb0 bl0 y -> CSs (sc ++ [p]) r nb0 bl0 y.
  Proof.
    intros sc r p y [[A|[(a & Ha & SA & R)|R]]|A]; [left; left; exact A| left; right; left| left; right; right; exact R| right; exact A].
    exists a. split; [apply in_app_iff; left; exact Ha| split; [exact SA| exact R]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L48872191983.3300000GS2AL1H2U03msz1r1y2R22H0". (* [comment removed for export] *)
  #[using="VWF0 HH H68 HU MSZ"] Theorem S_CSmono_p : forall sc r y, CSs sc r nb0 bl0 y -> CSs sc (r + 1) nb0 bl0 y.
  Proof.
    intros sc r y [[A|[A|[R1 R2]]]|A]; [left; left; exact A| left; right; left; exact A| left; right; right| right; exact A].
    split; [exact R1|]. apply Z.min_glb_lt_iff in R2. apply Z.min_glb_lt_iff. pose proof U00. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Theorem S_CSmono_n : forall sc r nb bl a x, CSs sc r nb bl x -> CSs sc r (nb ++ [a]) bl x.
  Proof.
    intros sc r nb bl a x [A|[(b & Hb & SB & R)|A]]; [left; exact A| right; left| right; right; exact A].
    exists b. split; [| auto]. rewrite skipn_app. apply in_app_iff. left. exact Hb.
  Qed.
  #[using="Type"] Theorem S_CSmono_s : forall sc r nb bl a x, CSs sc r nb bl x -> CSs sc r nb (bl ++ [a]) x.
  Proof.
    intros sc r nb bl a x [A|[A|(b & Hb & SB & R)]]; [left; exact A| right; left; exact A| right; right].
    exists b. split; [| auto]. rewrite skipn_app. apply in_app_iff. left. exact Hb.
  Qed.
  #[using="Type"] Theorem S_CSlift : forall sc r nb bl a n, crange (vcs AL v0) a n -> crange (CSs sc r nb bl) a n.
  Proof. intros sc r nb bl a n C x Hx. left. left. apply C. exact Hx. Qed.
  (* [comment removed for export] *)
  Hypothesis CSPA0 : crange (vcs AL v0) (fst H) (0x20000 * r0).
  Hypothesis HLEN : snd H = 0x800000.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L20844778873.10L26474403058.10L53432075460.8 L7997341125.3  00000:00G00^00gS1H1r1x2HxS1H1r2RB1x2HxS1H2U02r03EU01r1x2Hx2LTS2U01x2GE". (* [comment removed for export] *)
  #[using="r0 EU0 CSPA0 HLEN"] Theorem S_CSPA : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)P,(1.=R3.)P,(1.(1:.+20000.R4.)+800000.)(31.(2<.R6.R5.R4.R3.)(>.$3.$3.VH,)(1:.+20000.R5.))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl R0 RB x Hx. destruct (Z_lt_ge_dec x U0) as [LT|GE].
    - left. left. apply CSPA0. clear - Hx LT EU0. lia.
    - left. right. right. split; [clear - GE; lia| apply Z.min_glb_lt; rewrite ?HLEN; clear - Hx GE EU0 RB HLEN; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem S_KL : forall sc r nb bl, kinv AL (CSs sc r nb bl) (Ks sc r nb bl).
  Proof.
    intros sc r nb bl. split.
    - intros mo K. ddestruct (Ks_cases sc r nb bl mo K) as (v & _ & KD & VR & _). exact (ki_halted (D_KL AL v nb0 bl0 VR nb bl) mo KD).
    - intros mo K. ddestruct (Ks_cases sc r nb bl mo K) as (v & _ & KD & VR & _). exact (ki_top (D_KL AL v nb0 bl0 VR nb bl) mo KD).
    - intros mo acc K OK. ddestruct (Ks_cases sc r nb bl mo K) as (v & B & KD & VR & _ & _ & _ & EQ).
      ddestruct (ki_mat (D_KL AL v nb0 bl0 VR nb bl) mo acc KD ltac:(eapply acc_ok_mono; [| exact OK]; intros x Hx; apply EQ; exact Hx)) as (mo' & E & KD' & MM).
      exists mo'. split; [exact E|]. split; [exists v; split; [exact B| exact KD']| exact MM].
  Qed.

  #[using="GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem S_apart : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.Pa,(32.&40.)Pn,(32.&40.)P,(2:.R7.R6.R5.R4.R3.)P,(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R4.))(38.(37.R4.)))R3.R2.)$39.)P,(1.+10000.(3:.&40.R3.))P,(1.(5.(3:.&40.R5.)(3:.&40.R4.))(6.VhAR,))Px,$3.P,(7.(2<.R<.R;.R:.R9.R1.)(0.(1.(3;.VAL,)R1.)(:.R1.(3<.VAL,))))(9.(0.(1.(3:.&40.R8.)R2.)(:.R2.(5.(3:.&40.R8.)(3:.&40.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo a n K RF N16 CE x Hx. ddestruct (Ks_cases sc r nb bl mo K) as (v & _ & KD & _ & _ & _ & _ & EQ).
    apply (D_apart AL v nb0 bl0 nb bl mo a n KD RF N16 CE x). destruct Hx as [Hx|Hx]; [left; apply EQ; exact Hx| right; exact Hx].
  Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L44381426134.2L48782861859.3L51489968921.5L51494262789.700000700@00N00aS1w3N16S1a1w3N16S1a1w1y2Hy3BNDS1H4HLEN1a1w1y2Hy1X". (* [comment removed for export] *)
  #[using="GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 HLEN"] Theorem S_apart_l : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pmo,$29.Pa,(32.&40.)Pw,(32.&40.)P,(2:.R5.R4.Vnb0,Vbl0,R3.)P,(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R4.))(38.(37.R4.)))R3.R2.)$39.)P,(1.+10000.(3:.&40.R3.))P,(1.(5.(3:.&40.R5.)(3:.&40.R4.))(6.VhAR,))Py,$3.P,(7.(2<.R:.R9.Vnb0,Vbl0,R1.)(7.(0.(1.(3;.VAL,)R1.)(:.R1.(3<.VAL,)))(7.(0.(1.+7???7000.R1.)(:.R1.+10007???8000.))(0.(1.(>.$3.$3.VH,)R1.)(:.R1.(5.(>.$3.$3.VH,)+800000.))))))(9.(0.(1.(3:.&40.R8.)R2.)(:.R2.(5.(3:.&40.R8.)(3:.&40.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros sc r mo a w K RF N16 CE y Hy. ddestruct (Ks_cases sc r nb0 bl0 mo K) as (v & B & KD & _ & _ & _ & _ & EQ).
    ddestruct (Kd_cases AL v nb0 bl0 nb0 bl0 mo KD) as (v1 & HK & EQ1 & CASE).
    destruct Hy as [Hy|[Hy|[Hy|Hy]]].
    - apply (D_apart AL v nb0 bl0 nb0 bl0 mo a w KD RF N16 CE y). left. apply EQ. exact Hy.
    - apply (D_apart AL v nb0 bl0 nb0 bl0 mo a w KD RF N16 CE y). right. exact Hy.
    - pose proof (HKv_fresh_band AL v1 mo a w HK RF ltac:(clear - N16; lia)) as BND. clear - BND Hy. lia.
    - (* [comment removed for export] *)
      dpose HK as (_ & _ & _ & _ & _ & _ & _ & _ & TBL & _ & _ & _ & VW1 & _).
      assert (HH1 : In H (v_hulls v1)).
      { destruct CASE as [(_ & _ & ->)|[(? & _ & _ & _ & ->)|[(? & _ & _ & _ & ->)|(? & ? & _ & _ & _ & _ & ->)]]]; unfold vN, vS, vNS, vN; cbn [v_hulls v_add_eager v_add_lazy];
          (destruct B as [(_ & _ & ->)|(? & _ & _ & [(_ & ->)|(_ & ->)])]; unfold vLP, vL; cbn [v_hulls v_add_eager v_add_sub]; exact HH). }
      pose proof (region_free_clear _ a w ltac:(clear - N16; lia) RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
      pose proof (hull_fresh_apart AL v1 _ _ _ H _ _ TBL VW1 HH1 CLM ltac:(clear - N16; lia)) as X.
      clear - X Hy HLEN. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L11967401455.42L18928482845.42L24273305315.46L31457524356.42L31457702679.5 L44229536163.4 L49414624400.39L50568921550.39L59377646534.42L59580148551.42L59580196445.45L59582606663.40L64903233538.39L64909984778.4400000I00Z00o01001>01J01f02;02L02a03603K03`045S3hAR2AL3IMH2U03msz1a3IMAS3hAR2AL2U03msz1aS3hAR2AL2U03msz3MSZ1aFS2v03msz5SLACKS3msz1a2H'1XS3hAR2AL2U03msz3MSZ1a2A03ACES3hAR2AL3IML2U03msz1aS3hAR2AL2U03msz1aS3hAR2AL2U03msz3MSZ1aS3hAR2AL2U03msz3MSZ1aS3hAR2AL2U03msz3MSZ1aS3hAR2AL2U03msz3MSZ1aS3hAR2AL2U03msz3MSZ1a". (* [comment removed for export] *)
  #[using="ASB IML IMH H68 HU MSZ SLACK"] Theorem S_T_large : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pm,$3.Pmo,$29.Pa,(32.&40.)P,(3=.R5.R4.R3.)P,(2:.R6.R5.Vnb0,Vbl0,R3.)P,(2.$3.(4.(3:.&40.R3.)+1000.)=)P,(:.=(3:.&40.R4.))P,(1.(5.(3:.&40.R5.)R7.)(6.VhAR,))P,(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R7.))(38.(37.R7.)))R6.(3>.&40.R8.))$39.)(0.(2:.(35.(;.$3.$3.)R;.(14.(;.$3.$3.)(15.$3.$3.(3:.&40.R7.)R9.)(11.(;.$3.$3.))))R:.Vnb0,Vbl0,(3?.+22.R7.R9.R8.))(31.(2<.(35.(;.$3.$3.)R;.(14.(;.$3.$3.)(15.$3.$3.(3:.&40.R7.)R9.)(11.(;.$3.$3.))))R:.Vnb0,Vbl0,)(3:.&40.R7.)R9.))")
(* [comment removed for export] *).
  Proof.
    (intros sc r m mo a dd_H; ddestruct dd_H as (-> & -> & ->); intros dd_H; ddestruct dd_H as (v & B & KD); intros AAL A0 ACE RF). pose proof MSZ as [M0 MAL].
    destruct B as [(_ & _ & ->)|(? & E & _)]; [| discriminate E].
    destruct KD as [(_ & _ & K)|[(x & E & _)|[(y & _ & E & _)|(x & y & E & _)]]]; [| exfalso; symmetry in E; exact (app_cons_neq _ _ E)..].
    assert (NZ : bv_unsigned (Z_to_bv 64 msz) = msz) by (apply u64_lit; aceilb; lia).
    pose proof (HKv_fresh_above_img AL v0 mo a (Z_to_bv 64 msz) K RF A0 IML ltac:(rewrite IMH; lia) ltac:(rewrite NZ; lia) ltac:(rewrite NZ; exact ACE)) as IMA. rewrite IMH in IMA.
    pose proof (HKv_fresh_band AL v0 mo a (Z_to_bv 64 msz) K RF ltac:(rewrite NZ; lia)) as BND. rewrite NZ in BND.
    assert (SA : saneL (bv_unsigned a)).
    { split; [exact IMA|]. split; [exact AAL|]. split; [exact ACE|]. split; [exact BND|]. split.
      - intros x Hx R. apply (HKv_apart AL v0 mo a (Z_to_bv 64 msz) K RF ltac:(rewrite NZ; lia) ltac:(rewrite NZ; exact ACE) x (or_introl Hx)). rewrite NZ. exact R.
      - intros H' HH'. dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & TBL & _ & _ & _ & VW & _).
        pose proof (region_free_clear _ a (Z_to_bv 64 msz) ltac:(rewrite NZ; lia) RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
        rewrite NZ in CLM.
        pose proof (hull_fresh_apart AL v0 _ _ _ H' _ _ TBL VW HH' CLM ltac:(lia)) as X. clear - X. lia. }
    split.
    - exists (vL (bv_unsigned a)). split; [right; exists (bv_unsigned a); split; [reflexivity| split; [exact SA| left; split; reflexivity]]|].
      left. split; [reflexivity|]. split; [reflexivity|].
      unfold vL. apply (HKv_grant_eager AL v0 mo a msz true K); try assumption; try (rewrite ASB; lia); try lia.
      all: first [ rewrite IMH; exact IMA
                 | rewrite vnb_add_eager; cbn [v_eb v_add_eager]; unfold RES_SEC, RES_MAP, RES_SLICE, RES_DEPOT in SLACK; pose proof (Z.div_pos msz 32768) as DP; clear - SLACK M0 DP; lia ].
    - intros z Hz. left. right. left. exists (bv_unsigned a). split; [apply in_app_iff; right; left; reflexivity| split; [exact SA| exact Hz]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59314955108.2000006S2r01E". (* [comment removed for export] *)
  #[using="Type"] Lemma Ks_p : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pmo,$29.P,(40.R2.Vr0,)P,(2:.R3.Vr0,Vnb0,Vbl0,R2.)(13.$3.La,$3.(0.(2.(10.(;.$3.$3.))R5.(14.(;.$3.$3.)(15.$3.$3.R1.Vmsz,)(11.(;.$3.$3.))))(0.(16.R1.)(41.VhAR,VAL,(17.R1.)R4.))))")
(* [comment removed for export] *).
  Proof.
    (intros sc mo [_ L1] dd_H; ddestruct dd_H as (v & B & KD)).
    destruct B as [(-> & _ & _)|(a & -> & SA & [(_ & ->)|(E & _)])]; [cbn in L1; discriminate L1| | exfalso; clear - E; lia].
    destruct KD as [(_ & _ & K)|[(x & E & _)|[(y & _ & E & _)|(x & y & E & _)]]]; [| exfalso; symmetry in E; exact (app_cons_neq _ _ E)..].
    exists a. auto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7032082499.600000BS1H2U03msz2HU1a2AP". (* [comment removed for export] *)
  #[using="H HH HU APT_P"] Lemma APT_L : forall a, saneL a -> forall t, In t (v_tr (vL a)) -> U0 + 0x20000 <= t_lo t \/ t_hi t <= U0.
  Proof.
    intros a SA t [<-|Ht]; [| exact (APT_P t Ht)]. unfold t_hi. cbn [t_lo t_len].
    ddestruct SA as (_ & _ & _ & _ & _ & HA). pose proof (HA H HH) as AP. clear - AP HU. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L64685434581.500000>S2v03msz5SLACK". (* [comment removed for export] *)
  #[using="MSZ SLACK"] Lemma SLACK_L : forall a, v_eb (vL a) + 0x20000 + 4096 * vnb (v_add_sub (vL a) U0 0x20000 true) <= VLIMIT.
  Proof.
    intros a. unfold vL. rewrite vnb_add_sub, vnb_add_eager. cbn [v_eb v_add_eager]. pose proof MSZ as [M0 _].
    unfold RES_SEC, RES_MAP, RES_SLICE, RES_DEPOT in SLACK. pose proof (Z.div_pos msz 32768) as DP. clear - SLACK M0 DP. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18928860435.36L26983613284.37L51852964023.36L59580486519.3800000@00S00c017S2AL2U03msz1a2L1S2AL2U03msz1a2L12H0S2AL2U03msz1a2L1S2AL2U03msz3MSZ1a2L1". (* [comment removed for export] *)
  #[using="ASB IMH H VR0 HH H68 HU APT_P UN0 MSZ SLACK"] Theorem S_LEDGER_P : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pmo,$29.P,(40.R3.R2.)P,(2:.R4.R3.Vnb0,Vbl0,R2.)(0.(2.$33.(34.(36.(37.R3.))(3>.&40.VU0,)(3>.&40.+20000.))$39.)(7.(2.$33.(42.(38.(37.R3.))(3>.&40.VU0,)(3>.&40.+20000.))$39.)(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R3.))(38.(37.R3.)))(3>.&40.VU0,)(3>.&40.+20000.))$39.)))")
(* [comment removed for export] *).
  Proof.
    intros sc r mo G K. pose proof G as [-> L1]. ddestruct (Ks_p sc mo G K) as (a & -> & SA & HK).
    ddestruct (HKv_commit_sub AL (vL a) mo H U0 0x20000 true ltac:(unfold vL; apply vranges_ok_eager; [exact VR0| destruct SA; lia| pose proof MSZ as [? ?]; lia]) HK ASB ltac:(rewrite IMH; lia)
                HH (proj1 HU) (proj1 (proj2 HU)) (proj2 (proj2 HU)) eq_refl ltac:(lia) H68 ltac:(unfold vL; cbn [v_unit v_add_eager]; exact UN0) (APT_L a SA) (SLACK_L a)) as (_ & MC & RFR & _).
    split; [exact RFR| left; exact MC].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18928860435.37L26983613284.38L51852964023.37L59580486519.3900000@00S00c017S2AL2U03msz1a2L1S2AL2U03msz1a2L12H0S2AL2U03msz1a2L1S2AL2U03msz3MSZ1a2L1". (* [comment removed for export] *)
  #[using="ASB IMH VR0 HH H68 HU EU0 APT_P UN0 MSZ SLACK"] Theorem S_TP_commit : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pmo,$29.P,(40.R3.R2.)P,(2:.R4.R3.Vnb0,Vbl0,R2.)P,(2.$33.(42.(38.(37.R3.))(3>.&40.VU0,)(3>.&40.+20000.))$39.)(0.(2:.R6.(5.R5.+1.)Vnb0,Vbl0,(43.+32.VU0,+20000.R4.))(31.(2<.R6.(5.R5.+1.)Vnb0,Vbl0,)VU0,+20000.))")
(* [comment removed for export] *).
  Proof.
    intros sc r mo G K MC. pose proof G as [-> L1]. ddestruct (Ks_p sc mo G K) as (a & -> & SA & HK).
    destruct (HKv_commit_sub AL (vL a) mo H U0 0x20000 true ltac:(unfold vL; apply vranges_ok_eager; [exact VR0| destruct SA; lia| pose proof MSZ as [? ?]; lia]) HK ASB ltac:(rewrite IMH; lia)
                HH (proj1 HU) (proj1 (proj2 HU)) (proj2 (proj2 HU)) eq_refl ltac:(lia) H68 ltac:(unfold vL; cbn [v_unit v_add_eager]; exact UN0) (APT_L a SA) (SLACK_L a)) as (K' & _).
    split.
    - exists (vLP a). split; [right; exists a; split; [reflexivity| split; [exact SA| right; split; reflexivity]]|]. left. auto.
    - intros x Hx. left. right. right. apply slice_r1. exact Hx.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L18928403116.45L50980101594.46L59315137787.5 L59577438640.45L59579215501.46L64175380941.4600000I00b00m01F01_02@S3hAR2AL2U03msz1a2L14U00'S3hAR2AL2U03msz1a2L14U00'S1H2U02HU1XS3hAR2AL2U03msz1a2L14U00'S3hAR2AL2U03msz1a2L14U00'S3hAR2AL1H2U03msz2HU1a2L14U00'2W2". (* [comment removed for export] *)
  #[using="VWF0 HH H68 HU MSZ"] Theorem S_TP_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pmo,$29.P,(40.R3.R2.)P,(2:.R4.R3.Vnb0,Vbl0,R2.)P,(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R3.))(38.(37.R3.)))(3>.&40.VU0,)(3>.&40.+20000.))$39.)(0.(2:.R6.(5.R5.+1.)Vnb0,Vbl0,(44.+32.VU0,+20000.R4.))(31.(2<.R6.(5.R5.+1.)Vnb0,Vbl0,)VU0,+20000.))")
(* [comment removed for export] *).
  Proof.
    intros sc r mo G K RF. pose proof G as [-> L1]. ddestruct (Ks_p sc mo G K) as (a & -> & SA & HK). exfalso.
    (* [comment removed for export] *)
    dpose HK as (_ & _ & _ & _ & _ & _ & _ & _ & TBL & _ & _ & _ & VW & _).
    pose proof U00 as U00'. aceilb. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH) as (W0 & W1 & W2 & _).
    pose proof (region_free_clear _ (Z_to_bv 64 U0) (Z_to_bv 64 0x20000) ltac:(rewrite u64_lit by lia; lia) RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
    rewrite !u64_lit in CLM by lia.
    pose proof (hull_fresh_apart AL (vL a) _ _ _ H _ _ TBL VW ltac:(unfold vL; cbn [v_hulls v_add_eager]; exact HH) CLM ltac:(lia)) as X. clear - X HU W1. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L18928860435.36L26983613284.37L51852964023.36L59580486519.3800000@00S00c017S2AL2U03msz1a2L1S2AL2U03msz1a2L12H0S2AL2U03msz1a2L1S2AL2U03msz3MSZ1a2L1". (* [comment removed for export] *)
  #[using="ASB IMH H VR0 HH H68 HU APT_P UN0 MSZ SLACK"] Theorem S_ROOM_P : forall sc r mo, Gp sc r -> Ks sc r nb0 bl0 mo -> fixrw_grantable 0x32 U0 0x20000 mo.
  Proof.
    intros sc r mo G K. pose proof G as [-> L1]. ddestruct (Ks_p sc mo G K) as (a & -> & SA & HK).
    ddestruct (HKv_commit_sub AL (vL a) mo H U0 0x20000 true ltac:(unfold vL; apply vranges_ok_eager; [exact VR0| destruct SA; lia| pose proof MSZ as [? ?]; lia]) HK ASB ltac:(rewrite IMH; lia)
                HH (proj1 HU) (proj1 (proj2 HU)) (proj2 (proj2 HU)) eq_refl ltac:(lia) H68 ltac:(unfold vL; cbn [v_unit v_add_eager]; exact UN0) (APT_L a SA) (SLACK_L a)) as (_ & _ & _ & RM).
    exact RM.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L26983627866.45L30588209061.4 L3263482037.4  L51852964023.47L59580148551.4400000Q00^00j01E01eS3hAR2AL1H2U03msz2sc2L14U00'1a2H0S1H2U03H682HUS1H2U02HU2W5S3hAR2AL1H2U03msz1a2L14U00'S3hAR2AL1H2U03msz3MSZ2sc2L14U00'". (* [comment removed for export] *)
  #[using="ASB IMH VR0 VWF0 HH H68 HU EU0 APT_P UN0 MSZ"] Theorem S_SCAR_P : forall sc r, Gp sc r -> hole_site AL (CSs sc r nb0 bl0) (Ks sc r nb0 bl0) U0 0x20000.
  Proof.
    intros sc r G. pose proof G as [-> L1]. pose proof MSZ as [M0 MAL]. pose proof U00 as U00'.
    dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH) as (W0 & W1 & W2 & W3 & W4 & W5).
    exists (fun mh => exists a, sc = [(a, msz)] /\ saneL a /\ HKh AL (vL a) U0 0x20000 mh). split.
    - (* [comment removed for export] *)
      assert (VRL : forall a, saneL a -> vranges_ok AL (vL a)).
      { intros a SA. unfold vL. apply vranges_ok_eager; [exact VR0| destruct SA; lia| lia]. }
      assert (INC : forall a x, sc = [(a, msz)] -> saneL a -> CSs sc r0 nb0 bl0 x -> vcs AL (vL a) x).
      { intros a x -> SA [[X|[(a' & Ha' & _ & R)|X]]|[(b & Hb & _)|(b & Hb & _)]].
        + unfold vL. apply (proj2 (vcs_eagerT _ _ _ _)). left. exact X.
        + destruct Ha' as [E|[]]. assert (Ea : a' = a) by congruence. subst a'. unfold vL. apply (proj2 (vcs_eagerT _ _ _ _)). right. exact R.
        + exfalso. exact (slice_r0 x X).
        + rewrite skipn_all in Hb. destruct Hb.
        + rewrite skipn_all in Hb. destruct Hb. }
      split.
      + (intros mo dd_H; ddestruct dd_H as (a & E & SA & KH)). exact (ki_halted (HKh_kinv AL (vL a) U0 0x20000 (VRL a SA)) mo KH).
      + (intros mo dd_H; ddestruct dd_H as (a & E & SA & KH)). exact (ki_top (HKh_kinv AL (vL a) U0 0x20000 (VRL a SA)) mo KH).
      + (intros mo acc dd_H; ddestruct dd_H as (a & E & SA & KH); intros OK).
        destruct (ki_mat (HKh_kinv AL (vL a) U0 0x20000 (VRL a SA)) mo acc KH (acc_ok_mono AL _ _ acc (fun x Hx => INC a x E SA Hx) OK)) as (mo' & EM & KH' & MM).
        exists mo'. split; [exact EM|]. split; [exists a; auto| exact MM].
    - intros mo K MC. ddestruct (Ks_p sc mo G K) as (a & -> & SA & HK). exists a. split; [reflexivity|]. split; [exact SA|].
      apply (HKh_of_destroy AL (vL a) mo U0 0x20000 HK ASB ltac:(rewrite IMH; lia)).
      + unfold vL. cbn [v_unit v_add_eager]. exact UN0.
      + clear - H68 HU. lia.
      + clear - HU W5. lia.
      + exact (APT_L a SA).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Theorem S_SEC_APART : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.Pp,(;.$3.$3.)PH',(;.$3.$3.)P,(2:.R7.R6.R5.R4.R3.)P,(<.(;.$3.$3.)R3.R8.)P,(<.(;.$3.$3.)R3.(=.Vv0,))(7.(1.(5.(>.$3.$3.R5.)(?.$3.$3.R5.))(>.$3.$3.R4.))(1.(5.(>.$3.$3.R4.)(?.$3.$3.R4.))(>.$3.$3.R5.)))")
(* [comment removed for export] *).
  Proof.
    (intros sc r nb bl mo p H' dd_H; ddestruct dd_H as (v & B & _); intros Hp HH'). destruct B as [(-> & _)|(a & -> & SA & _)]; [destruct Hp|].
    destruct Hp as [<-|[]]. cbn [fst snd]. ddestruct SA as (_ & _ & _ & _ & _ & HA). exact (HA H' HH').
  Qed.

  (* [comment removed for export] *)
  #[using="ASB IML IMH GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem S_T_node : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.Pa,(32.&40.)P,(45.R6.R5.R4.R3.)P,(2:.R7.R6.R5.R4.R3.)P,(2.$3.(4.(3:.&40.R3.)+1000.)=)P,(:.=(3:.&40.R4.))P,(1.(5.(3:.&40.R5.)(25.+2.+14.))(6.VhAR,))P,(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R7.))(38.(37.R7.)))R6.(3>.&40.(25.+2.+14.)))$39.)(0.(2:.R<.R;.(35.$3.R:.(14.$3.(3:.&40.R7.)(11.$3.)))R9.(3?.+22.R7.(25.+2.+14.)R8.))(31.(2<.R<.R;.(35.$3.R:.(14.$3.(3:.&40.R7.)(11.$3.)))R9.)(3:.&40.R7.)(25.+2.+14.)))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo a G K AAL A0 ACE RF. ddestruct (Ks_cases sc r nb bl mo K) as (v & B & KD & VR & SL & _ & _ & EQ).
    destruct (D_T_node AL ASB IML IMH v nb0 bl0 SL nb bl mo a G KD AAL A0 ACE RF) as [K' C'].
    split; [exists v; split; [exact B| exact K']|]. intros x Hx.
    dpose (base_facts sc r v B) as (_ & _ & _ & _ & EQB). unfold CSs, Dnew. unfold CSd in C'. specialize (C' x Hx). rewrite EQB. exact C'.
  Qed.
  #[using="ASB IML IMH GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem S_T_store : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.Pa,(32.&40.)P,(46.R6.R5.R4.R3.)P,(2:.R7.R6.R5.R4.R3.)P,(2.$3.(4.(3:.&40.R3.)+1000.)=)P,(:.=(3:.&40.R4.))P,(1.(5.(3:.&40.R5.)(25.+2.+17.))(6.VhAR,))P,(2.$33.(34.(35.(;.(32.&40.)(32.&40.))(36.(37.R7.))(38.(37.R7.)))R6.(3>.&40.(25.+2.+17.)))$39.)(0.(2:.R<.R;.R:.(35.$3.R9.(14.$3.(3:.&40.R7.)(11.$3.)))(3?.+4022.R7.(25.+2.+17.)R8.))(31.(2<.R<.R;.R:.(35.$3.R9.(14.$3.(3:.&40.R7.)(11.$3.))))(3:.&40.R7.)(25.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo a G K AAL A0 ACE RF. ddestruct (Ks_cases sc r nb bl mo K) as (v & B & KD & VR & SL & _ & _ & EQ).
    destruct (D_T_store AL ASB IML IMH v nb0 bl0 SL nb bl mo a G KD AAL A0 ACE RF) as [K' C'].
    split; [exists v; split; [exact B| exact K']|]. intros x Hx.
    dpose (base_facts sc r v B) as (_ & _ & _ & _ & EQB). unfold CSs, Dnew. unfold CSd in C'. specialize (C' x Hx). rewrite EQB. exact C'.
  Qed.
  #[using="GOT64 GSB64 H VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem S_ROOM_n : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.P,(45.R5.R4.R3.R2.)P,(2:.R6.R5.R4.R3.R2.)(13.(32.&40.)La,(32.&40.)(47.VhAR,+22.(25.+2.+14.)R4.R1.))")
(* [comment removed for export] *).
  Proof. intros sc r nb bl mo G K. ddestruct (Ks_cases sc r nb bl mo K) as (v & _ & KD & VR & SL & C1 & _ & _). exact (D_ROOM_n AL v nb0 bl0 VR SL C1 nb bl mo G KD). Qed.
  #[using="GOT64 GSB64 H VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem S_ROOM_s : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.P,(46.R5.R4.R3.R2.)P,(2:.R6.R5.R4.R3.R2.)(13.(32.&40.)La,(32.&40.)(47.VhAR,+4022.(25.+2.+17.)R4.R1.))")
(* [comment removed for export] *).
  Proof. intros sc r nb bl mo G K. ddestruct (Ks_cases sc r nb bl mo K) as (v & _ & KD & VR & SL & _ & C2 & _). exact (D_ROOM_s AL v nb0 bl0 VR C2 nb bl mo G KD). Qed.

  (* [comment removed for export] *)
  Definition vexit_s (v : vst) (sn sb : list Z) : vst := ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "(48.$12.$3.Lb,$3.Lv,$12.(49.R1.R2.(25.+2.+17.))(48.$12.$3.La,$3.Lv,$12.(4:.R1.R2.(25.+2.+14.)$39.)O3.O2.)O1.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L26981597536.43L26981597536.45L50158913248.43L50158913248.45L61889852661.43L61889852661.45L67792983824.43L67792983824.4500000D00]00h01301G01`01k026S3hAR2AL2U03msz1a2SAS3hAR2AL2U03msz1a1b2SA2SBS2AL2U03mszS2AL2U03mszS3hAR2AL2U03msz1b2SBS3hAR2AL2U03msz1a1b2SA2SBS2AL2U03mszS2AL2U03msz". (* [comment removed for export] *)
  #[using="GOT64 GSB64 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23"] Theorem Ks_exit : ltac2:(CDefT.buildp (gd_tbl_AInstSec ()) "Psc,(10.(;.$3.$3.))Pr,$3.Pnb,(10.$3.)Pbl,(10.$3.)Pmo,$29.P,(2:.R5.R4.R3.R2.R1.)(13.$12.Lv,$12.(13.(10.$3.)Lsn,(10.$3.)(13.(10.$3.)Lsb,(10.$3.)(0.(1;.R9.R8.R3.)(0.(2.(10.$3.)R7.(35.$3.Vnb0,R2.))(0.(2.(10.$3.)R6.(35.$3.Vbl0,R1.))(0.(4;.$3.(4<.VhAR,(25.+2.+14.))R2.)(0.(4;.$3.(4<.VhAR,(25.+2.+17.))R1.)(0.(4=.(4>.$3.R2.)#1.)(0.(4=.(4>.$3.R1.)#1.)(0.(41.VhAR,VAL,(4?.R3.R2.R1.)R5.)(0.(1<.VAL,(4?.R3.R2.R1.))Px,$3.(27.(2<.R:.R9.R8.R7.R1.)(8.VAL,(4?.R4.R3.R2.)R1.))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo K. ddestruct (Ks_cases sc r nb bl mo K) as (v & B & KD & VR & _ & _ & _ & EQ).
    ddestruct (Kd_cases AL v nb0 bl0 nb bl mo KD) as (v1 & HK & EQ1 & CASE).
    assert (G : forall sn sb, nb = nb0 ++ sn -> bl = bl0 ++ sb -> Forall (sane (2^20)) sn -> Forall (sane (2^23)) sb -> (length sn <= 1)%nat -> (length sb <= 1)%nat ->
                 v1 = vexit_s v sn sb -> vranges_ok AL v1 ->
                 exists v sn sb, base sc r v /\ nb = nb0 ++ sn /\ bl = bl0 ++ sb /\ Forall (sane (2^20)) sn /\ Forall (sane (2^23)) sb
                   /\ (length sn <= 1)%nat /\ (length sb <= 1)%nat
                   /\ HKv AL (vexit_s v sn sb) mo /\ vranges_ok AL (vexit_s v sn sb) /\ (forall x, CSs sc r nb bl x <-> vcs AL (vexit_s v sn sb) x)).
    { intros sn sb E1 E2 F1 F2 L1 L2 EV VR1. dexists v, sn, sb. rewrite <- EV.
      split; [exact B|]. split; [exact E1|]. split; [exact E2|]. split; [exact F1|]. split; [exact F2|]. split; [exact L1|]. split; [exact L2|].
      split; [exact HK|]. split; [exact VR1|]. intros x. rewrite EQ. apply EQ1. }
    destruct CASE as [(-> & -> & ->)|[(a & -> & -> & SA & ->)|[(b & -> & -> & SB & ->)|(a & b & -> & -> & SA & SB & ->)]]].
    - apply (G [] []); rewrite ?app_nil_r; auto.
    - apply (G [a] []); rewrite ?app_nil_r; auto. unfold vN, sane in *. apply vranges_ok_eager; [exact VR| lia| lia].
    - apply (G [] [b]); rewrite ?app_nil_r; auto. unfold vS, sane in *. apply vranges_ok_lazy; [exact VR| lia| lia].
    - apply (G [a] [b]); auto. unfold vNS, vN, sane in *. apply vranges_ok_lazy; [apply vranges_ok_eager; [exact VR| lia| lia]| lia| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
      End InstSec.

End ARUN_1.
