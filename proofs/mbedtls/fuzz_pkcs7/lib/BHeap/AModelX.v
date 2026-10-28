(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AModelX () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "ARUN_1.wf_chunk'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Stdlib.Lists.List.NoDup"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.depot"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_n"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kDepotNodesL2"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_total"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "ARUN_1.wf_depot'"; "ARUN_1.hfr"; "ARUN_1.FR_MAXm"; "ARUN_1.sframes"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_gsh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sum"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.npg_shadow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_extra"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_exh"; "ARUN_2.epi"; "ARUN_2.csum"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_elems"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_nres"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kPtrArrayChunks"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "ARUN_2.EM"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "ARUN_2.CMAX24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "ARUN_2.wf_L'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_region"; "wf_chunks'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_quar"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_sec"; "wf_depot'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_budget"; "ARUN_2.wf_big"; "ARUN_2.wf_x"; "ARUN_2.wf_ghost"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_cls"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.compact"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_set"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition fits_chk (x : Z) : bool := x <=? class_size (class_of x).
Fixpoint allz (f : Z -> bool) (x : Z) (n : nat) : bool := match n with O => true | S n' => f x && allz f (x + 1) n' end.
#[using="Type"] Lemma fits_tbl : allz fits_chk 1 65536 = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma allz_spec : forall f x n y, allz f x n = true -> x <= y < x + Z.of_nat n -> f y = true.
Proof.
  intros f x n. revert x. induction n as [|n IH]; intros x y H R; [lia|]. cbn in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec y x) as [->|NE]; [exact H1|]. apply (IH (x + 1)); [exact H2| lia].
Qed.
#[using="Type"] Lemma class_fits : forall x, 1 <= x <= 65536 -> x <= class_size (class_of x).
Proof.
  intros x Hx. assert (E : Z.of_nat 65536 = 65536) by (vm_compute; reflexivity).
  pose proof (allz_spec fits_chk 1 65536 x fits_tbl) as H. rewrite E in H. specialize (H ltac:(lia)). unfold fits_chk in H. apply Z.leb_le in H. exact H.
Qed.

#[using="Type"] Lemma class_size_mod16 : forall c, 1 <= c <= 31 -> class_size c mod 16 = 0.
Proof.
  intros c Hc. unfold class_size. destruct (Z.eqb_spec c 31); [reflexivity|]. destruct (Z.leb_spec c 16).
  - replace (32 * c) with ((2 * c) * 16) by lia. apply Z_mod_mult.
  - assert (H0 : 0 <= (c - 16) / 2) by (apply Z.div_pos; lia).
    assert (E : 512 * 2 ^ ((c - 16) / 2) = 256 * 2 ^ ((c - 16) / 2) * 2) by lia.
    assert (D : 512 * 2 ^ ((c - 16) / 2) / 2 = 256 * 2 ^ ((c - 16) / 2)) by (rewrite E, Z.div_mul by lia; reflexivity).
    destruct (Z.odd (c - 16)).
    + rewrite D. replace (512 * 2 ^ ((c - 16) / 2) + 256 * 2 ^ ((c - 16) / 2)) with ((48 * 2 ^ ((c - 16) / 2)) * 16) by lia. apply Z_mod_mult.
    + replace (512 * 2 ^ ((c - 16) / 2)) with ((32 * 2 ^ ((c - 16) / 2)) * 16) by lia. apply Z_mod_mult.
Qed.

#[using="Type"] Lemma rz_size_mod16 : forall n, rz_size n mod 16 = 0.
Proof. intros n. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity. Qed.

#[using="Type"] Lemma rz_size_nfix : forall n, 0 <= n -> rz_size (nfix n) = rz_size n.
Proof.
  intros n Hn. unfold nfix. destruct (Z.le_gt_cases 1 n) as [H|H].
  - rewrite Z.max_l by lia. reflexivity.
  - rewrite Z.max_r by lia. unfold rz_size, rz_log. assert (n = 0) as -> by lia. reflexivity.
Qed.

#[using="Type"] Lemma needed_le_class : forall n, 0 <= n -> from_primary n = true -> needed n <= class_size (pclass n).
Proof.
  intros n Hn FP. unfold pclass. apply class_fits. unfold from_primary, kMaxSize in FP. apply Z.leb_le in FP.
  unfold needed, rounded, round_up in *. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
  pose proof (rz_size_cases n). lia.
Qed.

(* [comment removed for export] *)
Definition wf_chunk' (h : ahst) (k : chunk) : Prop :=
  0 <= ck_n k < 2^28   (* [comment removed for export] *)
  /\ (ck_st k = CHUNK_ALLOCATED \/ ck_st k = CHUNK_QUARANTINE)
  /\ (ck_prim k = from_primary (ck_n k))
  /\ (if ck_prim k
      then ck_cls k = pclass (ck_n k) /\ 1 <= ck_cls k <= 30
           /\ exists i, 0 <= i < carved h (ck_cls k) /\ ck_ab k = chunk_at (h_L h) (ck_cls k) i
      else exists i, nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k)))
           /\ ck_map_beg k mod 4096 = 0 /\ 0 < ck_map_beg k /\ ck_map_beg k + ck_map_size k <= ACEIL
           /\ lowhigh (ck_map_beg k) (ck_map_size k)).   (* [comment removed for export] *)
Definition wf_chunks' (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "(0.(1.$2.(3.O1.)(4.O1.))(0.(5.$6.(7.$2.$6.$8.(4.O1.)))Pi,$9.Psh,$:.P,(;.(<.$:.)(=.$:.(>.(?.O1.))R2.)(10.$:.R1.))(11.$2.Lk,$2.(0.(12.$2.R1.(4.O1.))(0.(;.$13.(14.R1.)$15.)(0.(;.$6.(16.R1.)(17.R3.))(;.$6.(18.R1.)(19.R3.))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition sframes (tf : Z) : Z := tf - 31 * (tf / 2^20).
Definition FR_MAXm : Z := 2^32 - 2^21.        (* [comment removed for export] *)
Definition hfr (h : ahst) : Z := Z.max (sframes (s_total (h_dep h)) - 3) (3 * (d_n (h_dep h) - 1)).
Definition wf_depot' (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "ZD,$1:.(1;.O1.)(0.(1<.+1.(1=.R1.))(0.(;.$6.(1>.(1?.$6.(20.R1.)))(21.(22.(1=.R1.)$23.)+1.))(0.(1.$6.Lb,$6.(0.(1<.+65?000.R1.)(0.(1<.(21.R1.(24.+2.+14.))(25.VhAR,))(;.$6.(26.R1.+1000.)=)))(20.R1.))(0.(1<.=(27.R1.))(0.(;.$6.(1>.(1?.$6.(28.R1.)))(22.(29.(21.(27.R1.)(24.+2.+14.))+1.)(24.+2.+14.)))(0.(1.$6.Lb,$6.(0.(1<.+65?000.R1.)(0.(1<.(21.R1.(24.+2.+17.))(25.VhAR,))(;.$6.(26.R1.+1000.)=)))(28.R1.))(0.(1<.(1>.(1?.$6.(20.R1.)))+8000.)(1<.(1>.(1?.$6.(28.R1.)))+1000.))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma wf_depot'_bounds : ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "Ph,$2:.P,(2;.R1.)P,(1<.(21.(2<.R2.)+3.)$2=.)(0.(1<.(21.(1=.(1;.R3.))+2.)(29.(24.+2.+1?.)(24.+2.+1<.)))(1<.(21.(27.(1;.R3.))+80.)(24.+2.+20.)))")
(* [comment removed for export] *).
Proof.
  (intros h dd_H; ddestruct dd_H as (N1 & _ & _ & T0 & LB & _ & _ & LBL); intros HF). unfold hfr, FR_MAXm, sframes in *.
  split; [lia|].
  pose proof (Z.div_mod (s_total (h_dep h)) (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound (s_total (h_dep h)) (2^20) ltac:(lia)).
  pose proof (Z.div_mod (s_total (h_dep h) + 2^20 - 1) (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound (s_total (h_dep h) + 2^20 - 1) (2^20) ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hfr_put : ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "Ph,$2:.Ph',$2:.Pd,$6.Psz,$6.P,(1<.=R2.)P,(0.(1<.+1.R2.)(1<.R2.(21.R3.+2.)))P,(0.(1<.(1=.(1;.R6.))(1=.(1;.R5.)))(1<.(1=.(1;.R5.))(21.(1=.(1;.R6.))+1.)))P,(1<.(2>.(27.(1;.R6.)))(21.(2>.(27.(1;.R7.)))(21.R4.+1.)))(1<.(2<.R7.)(21.(2<.R8.)(21.R6.+3.)))")
(* [comment removed for export] *).
Proof. intros h h' d sz D0 SZ DN SF. unfold hfr in *. lia. Qed.

(* [comment removed for export] *)
End ARUN_1.
Notation l_dtls := l_errno (only parsing).
Section ARUN_2. Context {hAR : arun}.
Definition wf_dtls (L : alayout) : Prop := lowhigh (l_errno L) 4096 /\ l_errno L + 4096 <= ACEIL /\ l_errno L mod 4096 = 0.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wf_gsh (L : alayout) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "(0.(1.(2?.$6.$6.)Lr,(2?.$6.$6.)(0.(1<.=(30.$6.$6.R1.))(0.(1<.=(31.$6.$6.R1.))(1<.(21.(30.$6.$6.R1.)(31.$6.$6.R1.))(24.+2.+2?.))))(32.O1.))(1<.(33.(7.(2?.$6.$6.)$6.Lr,(2?.$6.$6.)(34.(31.$6.$6.R1.))(32.O1.)))(24.+2.+11.)))")
(* [comment removed for export] *).
Definition wf_L' (L : alayout) : Prop := wf_L L /\ (l_stk_hi L <= l_stk_lo L + 2^24 /\ wf_gsh L) /\ wf_dtls L.

(* [comment removed for export] *)
Definition wf_big (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "(0.(1.$:.Lsh,$:.(1<.(24.+2.+10.)(19.R1.))(>.(?.O1.)))(0.(1.(2?.$6.$6.)Lg,(2?.$6.$6.)(1<.(24.+2.+10.)(31.$6.$6.R1.))(35.(36.O1.)))(0.(1<.(1>.(1?.(2?.$6.$6.)(37.(38.O1.))))+10.)(1.(2?.$6.$6.)Lr,(2?.$6.$6.)(1<.(31.$6.$6.R1.)(24.+2.+18.))(37.(38.O1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EM : Z := 128.                 (* [comment removed for export] *)
Definition cls31 : list Z := map Z.of_nat (seq 1 31).
Definition csum (f : Z -> Z) : Z := fold_right (fun c acc => f c + acc) 0 cls31.
Definition frozen (h : ahst) (c : Z) : bool := kUserLimit <? r_mapped_user (h_reg h c) + kUserMapSize.
Definition epi (h : ahst) (c : Z) : Z :=  (* [comment removed for export] *)
  if frozen h c then 2 - (if a_exh (h_acct h) c then 0 else 1)
                       - (if class_size c <=? r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c) then 1 else 0)
  else 0.
#[using="Type"] Lemma csum_le : forall f g, (forall c, 1 <= c <= 31 -> f c <= g c) -> csum f <= csum g.
Proof.
  intros f g H. unfold csum.
  assert (G : forall l, Forall (fun c => 1 <= c <= 31) l -> fold_right (fun c acc => f c + acc) 0 l <= fold_right (fun c acc => g c + acc) 0 l).
  { induction l as [|c l IH]; intros HF; cbn; [lia|]. inversion HF; subst. specialize (IH ltac:(assumption)). specialize (H c ltac:(assumption)). lia. }
  apply G. unfold cls31. apply Forall_forall. intros c Hc. apply in_map_iff in Hc. ddestruct Hc as (n & <- & Hn). apply in_seq in Hn. lia.
Qed.
#[using="Type"] Lemma csum_nonneg : forall f, (forall c, 1 <= c <= 31 -> 0 <= f c) -> 0 <= csum f.
Proof. intros f H. pose proof (csum_le (fun _ => 0) f H) as L. assert (E : csum (fun _ => 0) = 0) by (unfold csum, cls31; cbn; reflexivity). rewrite E in L. exact L. Qed.
#[using="Type"] Lemma epi_nonneg : forall h c, 0 <= epi h c.
Proof. intros h c. unfold epi. destruct (frozen h c); [| lia]. destruct (a_exh (h_acct h) c); destruct (class_size c <=? _); lia. Qed.
#[using="Type"] Lemma epi_le2 : forall h c, epi h c <= 2.
Proof. intros h c. unfold epi. destruct (frozen h c); [| lia]. destruct (a_exh (h_acct h) c); destruct (class_size c <=? _); lia. Qed.
#[using="Type"] Lemma epi_frame : ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "Ph,$2:.Ph',$2:.Pc,$6.P,(;.$39.(3:.R2.R1.)(3:.R3.R1.))P,(;.$13.(3;.(36.R3.)R2.)(3;.(36.R4.)R2.))(;.$6.(3<.R4.R3.)(3<.R5.R3.))")
(* [comment removed for export] *).
Proof. intros h h' c HR HX. unfold epi, frozen. rewrite HR, HX. reflexivity. Qed.
#[using="Type"] Lemma csum_epi_frame : ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "Ph,$2:.Ph',$2:.P,Pc,$6.P,(0.(1<.+1.R1.)(1<.R1.+1?.))(;.$39.(3:.R3.R2.)(3:.R4.R2.))P,Pc,$6.P,(0.(1<.+1.R1.)(1<.R1.+1?.))(;.$13.(3;.(36.R4.)R2.)(3;.(36.R5.)R2.))(;.$6.(3=.(3<.R3.))(3=.(3<.R4.)))")
(* [comment removed for export] *).
Proof. intros h h' HR HX. apply Z.le_antisymm; apply csum_le; intros c Hc; rewrite (epi_frame h h' c (HR c Hc) (HX c Hc)); lia. Qed.
(* [comment removed for export] *)
Definition CMAX24 : Z := 340900.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition c24_hid (P : Prop) : Prop := P.
Definition wf_x (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "(0.Pc,$6.P,(0.(1<.=R1.)(3>.R1.$3?.))(1<.(40.(3:.O1.R2.))(21.(41.+4.(42.O1.R2.))$43.))(0.(5.$6.(44.$45.$6.$46.(47.$45.(48.(49.O1.))(48.(4:.O1.)))))(0.P,(;.$13.(4;.O1.)$15.)Pc,$6.P,(0.(1<.=R1.)(3>.R1.$3?.))(;.$6.(4<.(3:.O1.R2.))=)(0.(1<.(41.(41.+2.+?<01.)(1>.(1?.$:.(>.(?.O1.)))))(4=.O1.))(0.(1<.(41.(41.+2.+?<01.)(29.(4>.(?.O1.))$4?.))(4=.O1.))(0.(50.(0.(;.$6.(51.(36.O1.))=)(;.$6.(52.(36.O1.))=))(0.(53.(51.(36.O1.))$54.)(0.(3>.=(51.(36.O1.)))(0.(1<.(21.(51.(36.O1.))$54.)(25.VhAR,))(0.(;.$6.(26.(51.(36.O1.))+1000.)=)(0.(50.(1<.(21.(51.(36.O1.))$54.)(55.(38.O1.)))(1<.(21.(55.(38.O1.))+2000011000.)(51.(36.O1.))))(0.(50.(1<.(21.(51.(36.O1.))$54.)(56.(38.O1.)))(1<.(21.(56.(38.O1.))+800000.)(51.(36.O1.))))(1<.=(52.(36.O1.))))))))))(0.(1<.(52.(36.O1.))(41.$57.(3=.(3<.O1.))))(0.(1<.(42.O1.$58.)$59.)(1<.(5:.(5;.O1.))$5<.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition wf_ghost (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "(1.(2?.$6.$6.)Lg,(2?.$6.$6.)(0.(53.(30.$6.$6.R1.)(31.$6.$6.R1.))(0.(3>.=(31.$6.$6.R1.))(0.(1<.(21.(30.$6.$6.R1.)(31.$6.$6.R1.))(25.VhAR,))(0.(;.$6.(26.(30.$6.$6.R1.)+1000.)=)(0.(;.$6.(26.(31.$6.$6.R1.)+1000.)=)(0.(50.(1<.(21.(30.$6.$6.R1.)(31.$6.$6.R1.))(55.(38.O1.)))(1<.(21.(55.(38.O1.))+2000011000.)(30.$6.$6.R1.)))(50.(1<.(21.(30.$6.$6.R1.)(31.$6.$6.R1.))(56.(38.O1.)))(1<.(21.(56.(38.O1.))+800000.)(30.$6.$6.R1.)))))))))(35.(36.O1.)))")
(* [comment removed for export] *).

Definition awf' (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "(0.(5=.(38.O1.))(0.(5>.O1.)(0.(5?.O1.)(0.(60.VhAR,O1.)(0.(61.O1.)(0.(62.O1.)(0.(63.VhAR,O1.)(0.(64.VhAR,O1.)(0.(65.O1.)(0.(66.O1.)(67.O1.)))))))))))")
(* [comment removed for export] *).


#[using="Type"] Lemma NoDup_app_l_r : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1 l2 x ND H1 H2. induction l1 as [|a l1 IH]; [destruct H1|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [<-|H1]; [apply NI; apply in_app_iff; right; exact H2| exact (IH ND' H1)].
Qed.
#[using="Type"] Lemma owned_cache_not_chunk : forall h c q, NoDup (owned h c) -> In q (cache_set h c) -> In q (chunk_set h c) -> False.
Proof.
  intros h c q ND HC HK. unfold owned in ND. apply NoDup_app_remove_l in ND. rewrite app_assoc in ND. apply NoDup_app_remove_r in ND.
  exact (NoDup_app_l_r _ _ q ND HC HK).
Qed.

#[using="Type"] Lemma compact_chunk_at : forall L c i, class_size c mod 16 = 0 -> compact L c (chunk_at L c i) = i * (class_size c / 16).
Proof.
  intros L c i M. unfold compact, chunk_at. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D.
  replace (region_beg L c + i * class_size c - region_beg L c) with ((i * (class_size c / 16)) * 16) by lia. apply Z_div_mult. lia.
Qed.

#[using="Type"] Lemma in_chunk_set : ltac2:(CDefT.buildp (gd_tbl_AModelX ()) "Ph,$2:.Pc,$6.Pk,$2.P,(12.$2.R1.(4.R3.))P,(;.$13.(14.R2.)$68.)P,(;.$6.(69.R3.)R4.)(12.$6.(6:.(38.R6.)R5.(8.R4.))(6;.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros h c k Hk P C. unfold chunk_set. apply in_map_iff. exists k. split; [reflexivity|]. apply filter_In. split; [exact Hk|]. rewrite P, C, Z.eqb_refl. reflexivity.
Qed.

End ARUN_2.
