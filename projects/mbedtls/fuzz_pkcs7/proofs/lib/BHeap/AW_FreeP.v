(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeP () : Init.string Init.list := ["OSSVerify.KrLib.BHeap.AModel.AH"; "OSSVerify.KrLib.BHeap.AModel.h_L"; "OSSVerify.KrLib.BHeap.AModel.h_cache"; "OSSVerify.KrLib.BHeap.AModel.h_cinit"; "OSSVerify.KrLib.BHeap.AModel.h_chunks"; "OSSVerify.KrLib.BHeap.AModel.h_tq"; "OSSVerify.KrLib.BHeap.AModel.h_gq"; "OSSVerify.KrLib.BHeap.AModel.h_sec"; "OSSVerify.KrLib.BHeap.AModel.h_dep"; "OSSVerify.KrLib.BHeap.AModel.h_ia"; "OSSVerify.KrLib.BHeap.AModel.h_fake"; "OSSVerify.KrLib.BHeap.AModel.h_pa_committed"; "OSSVerify.KrLib.BHeap.AModel.h_havol"; "OSSVerify.KrLib.BHeap.AModel.h_acct"; "OSSVerify.KrLib.BHeap.AModel.h_reg"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.BHeap.AModel.alayout"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.BHeap.AModel.r_mapped_user"; "OSSVerify.KrLib.BHeap.AModel.r_mapped_fa"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.BHeap.AModel.d_nb"; "OSSVerify.KrLib.BHeap.AModel.d_bl"; "OSSVerify.KrLib.BHeap.AModel.shdr"; "OSSVerify.KrLib.BHeap.AModel.s_chunks"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.BHeap.AModel.a_sech"; "OSSVerify.KrLib.BHeap.AModel.a_emb"; "OSSVerify.KrLib.BHeap.AModel.a_esz"; "OSSVerify.KrLib.BHeap.AModel.pcl"; "OSSVerify.KrLib.BHeap.AModel.region"; "ARUN_1.set_reg"; "ARUN_1.set_cache"; "ARUN_1.fupd"; "ARUN_1.pc_dropn"; "OSSVerify.KrLib.BHeap.AModel.RG"; "OSSVerify.KrLib.BHeap.AModel.r_alloc_user"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.BHeap.AModel.r_fa"; "ARUN_1.pc_lastn"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.BHeap.AModel.kFreeArrayMapSize"; "OSSVerify.KrLib.BHeap.AModel.kUserMapSize"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.BHeap.AModel.class_size"; "ARUN_1.h_push"; "ARUN_1.set_chunks"; "ARUN_1.rm_ab"; "OSSVerify.KrLib.BHeap.AModel.ck_ab"; "OSSVerify.KrLib.BHeap.AModel.ck_cls"; "OSSVerify.KrLib.BHeap.AModel.compact"; "OSSVerify.KrLib.BHeap.AModel.sec"; "ARUN_1.set_acct"; "ARUN_1.set_sec"; "OSSVerify.KrLib.BHeap.AModel.SE"; "ARUN_1.swap_remove"; "OSSVerify.KrLib.BHeap.AModel.s_nres"; "OSSVerify.KrLib.BHeap.AModel.AC"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.BHeap.AModel.ck_map_beg"; "OSSVerify.KrLib.BHeap.AModel.ck_map_size"; "OSSVerify.KrLib.BHeap.AModel.a_exh"; "OSSVerify.KrLib.BHeap.AModel.QC"; "OSSVerify.KrLib.BHeap.AModel.batch"; "Stdlib.Lists.List.removelast"; "OSSVerify.KrLib.BHeap.AModel.q_batches"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.BHeap.AModel.BA"; "OSSVerify.KrLib.BHeap.AModel.b_addr"; "OSSVerify.KrLib.BHeap.AModel.b_elems"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.BHeap.AModel.b_size"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Nat.sub"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.BHeap.AModel.q_bytes"; "OSSVerify.KrLib.BHeap.AModel.chunk"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.BHeap.AModel.ck_st"; "OSSVerify.KrLib.BHeap.AModel.CHUNK_QUARANTINE"; "Stdlib.Lists.List.filter"; "Stdlib.ZArith.BinInt.Z.eqb"; "OSSVerify.KrLib.BHeap.AModel.CHUNK_ALLOCATED"; "OSSVerify.KrLib.BHeap.AModel.ahst"; "Stdlib.Lists.List.NoDup"; "OSSVerify.KrLib.BHeap.AModel.blocks"; "ARUN_1.h_rec_prim"; "ARUN_1.h_lcd"; "ARUN_1.h_popq"; "ARUN_1.h_poptb"; "OSSVerify.KrLib.BHeap.AModel.kBatchClass"; "Stdlib.Lists.List.hd"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.BHeap.AModel.b_count"; "OSSVerify.KrLib.BHeap.AModel.kBatchCap"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.BHeap.AModel.ck_hdr"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.BHeap.AModel.carved"; "OSSVerify.KrLib.BHeap.AModel.chunk_at"; "OSSVerify.KrLib.BHeap.AModelX.wf_L'"; "OSSVerify.KrLib.BHeap.AModel.wf_cache"; "OSSVerify.KrLib.BHeap.AModel.wf_region"; "OSSVerify.KrLib.BHeap.AModelX.wf_chunks'"; "ARUN_1.wf_quar_r"; "OSSVerify.KrLib.BHeap.AModel.wf_sec"; "OSSVerify.KrLib.BHeap.AModelX.wf_depot'"; "OSSVerify.KrLib.BHeap.AModel.wf_budget"; "OSSVerify.KrLib.BHeap.AModelX.wf_big"; "OSSVerify.KrLib.BHeap.AModelX.wf_x"; "OSSVerify.KrLib.BHeap.AModelX.wf_ghost"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition set_reg (h : ahst) (f : Z -> region) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)O1.(2.O2.)(3.O2.)(4.O2.)(5.O2.)(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_cache (h : ahst) (f : Z -> pcl) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)O1.(3.O2.)(4.O2.)(5.O2.)(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_chunks (h : ahst) (ks : list chunk) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)O1.(5.O2.)(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_tq (h : ahst) (q : qcache) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)O1.(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_gq (h : ahst) (q : qcache) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)(5.O2.)O1.(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_sec (h : ahst) (s : sec) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)(5.O2.)(6.O2.)O1.(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_dep (h : ahst) (d : depot) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)(5.O2.)(6.O2.)(7.O2.)O1.(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_ia (h : ahst) (b : bool) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)(5.O2.)(6.O2.)(7.O2.)(8.O2.)O1.(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).
Definition set_havol (h : ahst) (v : Z) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)(5.O2.)(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)O1.(=.O2.))")
(* [comment removed for export] *).
Definition set_acct (h : ahst) (a : acct) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)(3.O2.)(4.O2.)(5.O2.)(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)O1.)")
(* [comment removed for export] *).
Definition set_cinit (h : ahst) (b : bool) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(0.(1.O2.)(>.O2.)(2.O2.)O1.(4.O2.)(5.O2.)(6.O2.)(7.O2.)(8.O2.)(9.O2.)(:.O2.)(;.O2.)(<.O2.)(=.O2.))")
(* [comment removed for export] *).

Definition fupd {A : Type} (f : Z -> A) (c : Z) (a : A) : Z -> A := fun j => if j =? c then a else f j.

#[using="Type"] Lemma fupd_same : forall {A} (f : Z -> A) c a, fupd f c a c = a.
Proof. intros. unfold fupd. rewrite Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kview_eq (h h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(?.(10.$11.(1.O1.)(1.O2.))(?.Pc,$12.(?.(10.$12.(13.(>.O1.R1.))(13.(>.O2.R1.)))(10.$12.(14.(>.O1.R1.))(14.(>.O2.R1.))))(?.(10.(15.$12.)(16.(8.O1.))(16.(8.O2.)))(?.(10.(15.$12.)(17.(8.O1.))(17.(8.O2.)))(?.(10.(15.$18.)(19.(7.O1.))(19.(7.O2.)))(?.(10.$12.(;.O1.)(;.O2.))(?.(10.(15.(1:.$12.$12.))(1;.(=.O1.))(1;.(=.O2.)))(?.(10.$12.(1<.(=.O1.))(1<.(=.O2.)))(10.$12.(1=.(=.O1.))(1=.(=.O2.)))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma kview_eq_trans : forall h1 h2 h3, kview_eq h1 h2 -> kview_eq h2 h3 -> kview_eq h1 h3.
Proof.
  (intros h1 h2 h3 dd_H; ddestruct dd_H as (A & B & C & D & E & F & G & G2 & G3); intros dd_H; ddestruct dd_H as (A' & B' & C' & D' & E' & F' & G' & G2' & G3')). split; [congruence|].
  split; [intros c; destruct (B c), (B' c); split; congruence|]. repeat split; congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kview_set_tq : forall h q, kview_eq h (set_tq h q).        Proof. intros; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rm_ab (ab : Z) (ks : list chunk) : list chunk := List.filter (fun k => negb (ck_ab k =? ab)) ks.

(* [comment removed for export] *)
Definition quar_ab (ab : Z) (ks : list chunk) : list chunk :=
  map (fun k => if ck_ab k =? ab then CK (ck_ab k) (ck_n k) (ck_prim k) (ck_cls k) CHUNK_QUARANTINE else k) ks.

(* [comment removed for export] *)
Definition pc_push (p : pcl) (q : Z) : pcl := PC (pc_max p) (pc_csize p) (pc_chunks p ++ [q]).
(* [comment removed for export] *)
Definition pc_dropn (p : pcl) (cnt : nat) : pcl := PC (pc_max p) (pc_csize p) (firstn (length (pc_chunks p) - cnt) (pc_chunks p)).
Definition pc_lastn (p : pcl) (cnt : nat) : list Z := skipn (length (pc_chunks p) - cnt) (pc_chunks p).

(* [comment removed for export] *)
Definition h_push (h : ahst) (c q : Z) : ahst := set_cache h (fupd (h_cache h) c (pc_push (h_cache h c) q)).

(* [comment removed for export] *)
Definition h_drain (h : ahst) (c : Z) (cnt : nat) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "Zp,$1>.(2.O3.O2.)Zr,$1?.(>.O3.O2.)(20.(21.O3.(22.$1>.(2.O3.)O2.(23.R2.O1.)))(22.$1?.(>.O3.)O2.(24.(13.R1.)(25.R1.)(14.R1.)(26.$12.(27.R1.)(28.R2.O1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition h_fagrow (h : ahst) (c : Z) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "Zr,$1?.(>.O2.O1.)(20.O2.(22.$1?.(>.O2.)O1.(24.(13.R1.)(25.R1.)(29.(14.R1.)$2:.)(27.R1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition h_ugrow (h : ahst) (c : Z) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "Zr,$1?.(>.O2.O1.)(20.O2.(22.$1?.(>.O2.)O1.(24.(29.(13.R1.)$2;.)(25.R1.)(14.R1.)(27.R1.))))")
(* [comment removed for export] *).
Definition h_carve (h : ahst) (c : Z) (nw : Z) (news : list Z) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "Zr,$1?.(>.O4.O3.)(20.O4.(22.$1?.(>.O4.)O3.(24.(13.R1.)(29.(25.R1.)(2<.O2.(2=.O3.)))(14.R1.)(26.$12.(27.R1.)O1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition h_rec_prim (h : ahst) (k : chunk) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(2>.(2?.O2.(30.(31.O1.)(4.O2.)))(32.O1.)(33.(1.O2.)(32.O1.)(31.O1.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition swap_remove {A : Type} (i : nat) (l : list A) : list A :=
  match nth_error l (length l - 1) with
  | None => l
  | Some lst => firstn i (removelast l) ++ (if (i <? length l - 1)%nat then lst :: skipn (i + 1) (removelast l) else [])
  end.
Definition h_rec_sec (h : ahst) (k : chunk) (i : nat) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "ZS,$34.(7.O3.)(35.(36.(2?.O3.(30.(31.O2.)(4.O3.)))(37.(38.$18.O1.(19.R1.))(39.R1.)))(3:.(3;.(1:.$12.$12.)(3<.$12.$12.(3=.O2.)(3>.O2.))(1;.(=.O3.)))(1<.(=.O3.))(1=.(=.O3.))(3?.(=.O3.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition h_rec_batch (h : ahst) (b : batch) : ahst := h_push h kBatchClass (compact (h_L h) kBatchClass (b_addr b)).

(* [comment removed for export] *)
Definition q_append (q : qcache) (e n : Z) : qcache := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(40.(26.$41.(42.$41.(43.O3.))(44.$41.$41.Lb,$41.(45.(46.R1.)(26.$12.(47.R1.)(3;.$12.O2.(48.$12.)))(29.(49.R1.)O1.))(4:.$41.(4;.(4<.$41.(43.O3.))#1.)(43.O3.))))(29.(4=.O3.)O1.))")
(* [comment removed for export] *).
Definition q_newbatch (q : qcache) (ba e n : Z) : qcache :=
  QC (q_batches q ++ [BA ba [e] (kBatchSize + n)]) (q_bytes q + (n + kBatchSize)).
(* [comment removed for export] *)
Definition q_transfer (g t : qcache) : qcache := QC (q_batches g ++ q_batches t) (q_bytes g + q_bytes t).
(* [comment removed for export] *)
Definition q_popn (g : qcache) (n : nat) (bytes : Z) : qcache := QC (skipn n (q_batches g)) (q_bytes g - bytes).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
#[using="Type"] Lemma live_rm_quar : ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "Pks,(15.$4>.)Pab,$12.P,Pk,$4>.P,(4?.$4>.R1.R3.)P,(10.$12.(31.R2.)R3.)(10.$12.(50.R3.)$51.)(10.(15.$4>.)(52.$4>.Lk,$4>.(53.(50.R1.)$54.)(30.R2.R3.))(52.$4>.Lk,$4>.(53.(50.R1.)$54.)R3.))")
(* [comment removed for export] *).
Proof.
  intros ks ab H. induction ks as [|k ks IH]; [reflexivity|]. cbn.
  destruct (Z.eqb_spec (ck_ab k) ab) as [E|NE]; cbn.
  - rewrite (H k ltac:(left; reflexivity) E). cbn. apply IH. intros k' Hk' E'. apply H; [right; exact Hk'| exact E'].
  - unfold rm_ab in IH. rewrite IH; [reflexivity|]. intros k' Hk' E'. apply H; [right; exact Hk'| exact E'].
Qed.

#[using="Type"] Lemma blocks_rec_prim : ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "Ph,$55.Pk,$4>.P,(4?.$4>.R1.(4.R2.))P,(10.$12.(50.R2.)$51.)P,(56.$12.(44.$4>.$12.$31.(4.R4.)))(10.(15.(1:.$12.$12.))(57.(58.R5.R4.))(57.R5.))")
(* [comment removed for export] *).
Proof.
  intros h k Hk Hst ND. unfold blocks, live, h_rec_prim, h_push. cbn. f_equal. apply live_rm_quar.
  intros k' Hk' E. assert (k' = k) as ->; [| exact Hst].
  clear Hst. induction (h_chunks h) as [|x l IH]; [destruct Hk|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hk as [->|Hk], Hk' as [->|Hk']; [reflexivity| | | exact (IH Hk ND' Hk')].
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hk'.
  - exfalso. apply NI. rewrite E. apply in_map. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fgrow (f : option bool) (c : Z) (h : ahst) : ahst := match f with Some true => h_fagrow h c | _ => h end.

(* [comment removed for export] *)
Definition h_lcd (h : ahst) (c q : Z) (dr : bool) (cnt : nat) (f : option bool) : ahst :=
  h_push (if dr then fgrow f c (h_drain h c cnt) else h) c q.

(* [comment removed for export] *)
Definition b_pop (b : batch) : batch := BA (b_addr b) (tl (b_elems b)) (b_size b).
Definition h_popq (h : ahst) : ahst :=
  set_tq h (QC (match q_batches (h_tq h) with [] => [] | b :: tb => b_pop b :: tb end) (q_bytes (h_tq h))).
(* [comment removed for export] *)
Definition h_poptb (h : ahst) : ahst := set_tq h (QC (tl (q_batches (h_tq h))) (q_bytes (h_tq h))).

(* [comment removed for export] *)
Definition h_recp (h : ahst) (k : chunk) (dr : bool) (cnt : nat) (f : option bool) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(59.(5:.(2?.O5.(30.(31.O4.)(4.O5.))))(32.O4.)(33.(1.O5.)(32.O4.)(31.O4.))O3.O2.O1.)")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition h_recs (h : ahst) (k : chunk) (i : nat) : ahst := h_popq (h_rec_sec h k i).
(* [comment removed for export] *)
Definition h_recb (h : ahst) (dr : bool) (cnt : nat) (f : option bool) : ahst := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(59.(5;.O4.)$5<.(33.(1.O4.)$5<.(46.(5=.$41.(45.=(48.$12.)=)(43.(5.O4.)))))O3.O2.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition wf_batch_r (h : ahst) (b : batch) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(?.(5>.(5?.O1.)$60.)(?.(61.$12.Le,$12.(62.$4>.Lk,$4>.(?.(4?.$4>.R1.(4.O2.))(?.(10.$12.(50.R1.)$51.)(10.$12.(63.R1.)R2.))))(47.O1.))(62.$12.Li,$12.(?.(?.(5>.=R1.)(64.R1.(65.O2.$5<.)))(10.$12.(46.O1.)(66.(1.O2.)$5<.R1.))))))")
(* [comment removed for export] *).
Definition wf_quar_r (h : ahst) : Prop :=
  match q_batches (h_tq h) with [] => True | b :: tb => wf_batch_r h b /\ Forall (wf_batch_r h) tb end
  (* [comment removed for export] *)
  /\ wf_qcache h (h_gq h) kQuarantineMax
  /\ NoDup (map b_addr (q_batches (h_tq h) ++ q_batches (h_gq h)))
  /\ (forall k, In k (h_chunks h) -> ck_st k = CHUNK_QUARANTINE ->
        exists! b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) /\ In (ck_hdr k) (b_elems b)).
Definition WFR (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeP ()) "(?.(67.VhAR,(1.O1.))(?.(68.O1.)(?.(69.O1.)(?.(6:.VhAR,O1.)(?.(6;.O1.)(?.(6<.O1.)(?.(6=.VhAR,O1.)(?.(6>.VhAR,O1.)(?.(6?.O1.)(?.(70.VhAR,O1.)(71.VhAR,O1.)))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma wf_batch_r_of : forall h b, wf_batch h b -> wf_batch_r h b.
Proof. (intros h b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). split; [lia|]. exact (conj B3 B4). Qed.

#[using="Type"] Lemma WFR_of_awf' : forall h, awf' h -> WFR h.
Proof.
  (intros h dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG)).
  split; [exact WL|]. split; [exact WC|]. split; [exact WR|]. split; [exact WK|]. split; [| exact (conj WS (conj WD (conj WB (conj WBIG (conj WX WG)))))].
  ddestruct WQ as ((T1 & T2 & T3) & WG' & ND & UQ). split; [| split; [exact WG'| split; [exact ND| exact UQ]]].
  destruct (q_batches (h_tq h)) as [|b tb] eqn:E; [exact I|].
  inversion T1 as [|b' tb' Hb Htb]; subst. split; [apply wf_batch_r_of; exact Hb| eapply Forall_impl; [intros a; apply wf_batch_r_of| exact Htb]].
Qed.

End ARUN_1.
