(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require PropExec StoreOk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Facts () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mrd"; "stdpp.bitvector.definitions.bv_add"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_params"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.wt"; "Corelib.Numbers.BinNums.Z"; "wlitu"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.winst"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv_unsigned"; "qbase"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.at_"; "apos"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ainst"; "Sound.qaddr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "zbyte"; "fbytes"; "qaddr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "Corelib.Init.Datatypes.bool"; "fwr"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Nat.mul"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64s"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWord"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWr"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CZero"; "Corelib.Lists.ListDef.repeat"; "fchk"; "fchkw"; "Sound4.fchkd"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.app"; "romdef"; "Corelib.Lists.ListDef.map"; "Img.imgb"; "Corelib.Lists.ListDef.seq"].


Local Notation bv_wrap64_mod := ABoot.PropExec.bv_wrap64_mod.
Local Notation u64_range := ABoot.PropExec.u64_range.

(* [comment removed for export] *)
Lemma asegs_ASEGS : asegs = ASEGS. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mrd_overlay : forall segs m a b, m a = Some b -> mrd segs m a = Some b.
Proof. intros segs m a b H. unfold mrd. rewrite H. reflexivity. Qed.
Lemma mrd_rom : forall segs m a, m a = None -> mrd segs m a = Lib.PropExec.seg_rom segs a.
Proof. intros segs m a H. unfold mrd. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_nth : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Psegs,(0.$1.)PM,P,(2.&40.)(3.(2.&8.))Pn,$4.Pa,(2.&40.)Pbs,(0.(2.&8.))Pk,$4.P,(5.(3.(0.(2.&8.)))(6.R6.R5.R3.R4.)(7.(0.(2.&8.))R2.))P,(8.R2.R5.)(5.(3.(2.&8.))(9.R8.R7.(:.&40.R5.(;.&40.(<.R3.))))(=.(2.&8.)R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs M n. induction n as [|n IH]; intros a bs k Hr Hk; [lia|].
  cbn [ABoot.PropExec.rdn] in Hr.
  destruct (match M a with Some b => Some b | None => ABoot.PropExec.seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
  destruct (ABoot.PropExec.rdn segs M (a + 1)%bv n) as [rest|] eqn:Er; [|discriminate].
  injection Hr as <-.
  destruct k as [|k].
  - cbn [nth_error]. rewrite woff0. unfold mrd. exact Eb.
  - cbn [nth_error]. rewrite <- woffk_S. exact (IH (a + 1)%bv rest k Er ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive qbase : Type := QLit | QTpl (b : wt).

(* [comment removed for export] *)
Definition apos (q : qbase) (a : at_) : option Z :=
  match q, a with
  | QLit, ALit z => Some z
  | QTpl b, AOff b' off => if wt_eqb b' b then Some off else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition zbyte (v : Z) (i : Z) : byte := Z_to_bv 8 ((v mod 2 ^ 64) / 2 ^ (8 * i)).

(* [comment removed for export] *)
Definition wlitu (t : wt) : option Z :=
  match wlit t with Some z => if ((0 <=? z) && (z <? 2 ^ 64))%bool then Some z else None | None => None end.
Lemma wlitu_sound : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pp,$>.Pt,$?.Pz,$10.P,(5.(3.$10.)(11.R2.)(7.$10.R1.))(12.(5.(2.&40.)(13.R4.R3.)(;.&40.R2.))(12.(12.(14.=R2.)(15.R2.(16.+2.+40.)))(5.$10.(17.&40.(13.R4.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros p t z H. unfold wlitu in H. destruct (wlit t) as [z'|] eqn:E; [|discriminate H].
  destruct ((0 <=? z') && (z' <? 2 ^ 64))%bool eqn:G; [|discriminate H]. injection H as ->.
  apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
  pose proof (wlit_sound p t z E) as W. split; [exact W|]. split; [lia|]. rewrite W, Z_to_bv_unsigned, ABoot.PropExec.bv_wrap64_mod. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Definition rom_byte (z : Z) : option byte := Lib.PropExec.seg_rom ASEGS (Z_to_bv 64 z).

(* [comment removed for export] *)
Definition cbyte (q : qbase) (c : ct) (z : Z) : option byte :=
  match c with
  | TWord a w v =>
      match apos q a, wlit v with
      | Some o, Some lit => if ((o <=? z) && (z <? o + Z.of_nat w))%bool then Some (zbyte lit (z - o)) else None
      | _, _ => None
      end
  | TZero a n =>
      match apos q a, wlitu n with
      | Some o, Some len => if ((o <=? z) && (z <? o + len))%bool then Some (Z_to_bv 8 0) else None
      | _, _ => None
      end
  | TFill a n c8 =>
      match apos q a, wlitu n with
      | Some o, Some len => if ((o <=? z) && (z <? o + len))%bool then Some (Z_to_bv 8 c8) else None
      | _, _ => None
      end
  | TImg lo hi =>
      match q with
      | QLit => if ((lo <=? z) && (z <? hi))%bool then rom_byte z else None
      | QTpl _ => None
      end
  | _ => None
  end.

Fixpoint fbyte (q : qbase) (L : list ct) (z : Z) : option byte :=
  match L with
  | [] => None
  | c :: L' => match cbyte q c z with Some b => Some b | None => fbyte q L' z end
  end.

Fixpoint fbytes (q : qbase) (L : list ct) (z : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match fbyte q L z, fbytes q L (z + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Definition cwr (q : qbase) (c : ct) (z : Z) (n : Z) : bool :=
  match c with
  | TWr a len => match apos q a, wlitu len with
                 | Some o, Some l => ((o <=? z) && (z + n <=? o + l))%bool
                 | _, _ => false
                 end
  | _ => false
  end.
Definition fwr (q : qbase) (L : list ct) (z : Z) (n : Z) : bool := existsb (fun c => cwr q c z n) L.

(* [comment removed for export] *)
Definition cdef (q : qbase) (c : ct) (z : Z) : bool :=
  match c with
  | TWord a w _ => match apos q a with Some o => ((o <=? z) && (z <? o + Z.of_nat w))%bool | None => false end
  | TZero a n | TFill a n _ | TUnk a n =>
      match apos q a, wlitu n with
      | Some o, Some len => ((o <=? z) && (z <? o + len))%bool
      | _, _ => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Fixpoint fdef (q : qbase) (L : list ct) (z : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => (existsb (fun c => cdef q c z) L && fdef q L (z + 1) n')%bool
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbv_mod : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia. Qed.
Lemma zbv_add_mod : forall x i, Z_to_bv 64 (x mod 2 ^ 64 + i) = Z_to_bv 64 (x + i).
Proof. intros x i. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.
Lemma u_zbv : forall x, bv_unsigned (Z_to_bv 64 x) = x mod 2 ^ 64.
Proof. intros x. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. Qed.
Lemma wadd_lit : forall x k, (Z_to_bv 64 x + Z_to_bv 64 k)%bv = Z_to_bv 64 (x + k).
Proof. intros x k. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Z.add_mod by lia. reflexivity. Qed.

Section Sound.
  Variable mem : word -> option byte.
  Variable p : me_params.

  (* [comment removed for export] *)
  Definition qaddr (q : qbase) (z : Z) : Z :=
    match q with QLit => z | QTpl b => bv_unsigned (winst p b) + z end.

  (* [comment removed for export] *)
  #[using="Type"] Lemma apos_addr : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pa,$19.Po,$10.P,(5.(3.$10.)(1:.R3.R2.)(7.$10.R1.))Pi,$10.(5.(2.&40.)(;.&40.(1;.(17.&40.(1<.Vp,R4.))R1.))(;.&40.(1=.R5.(1;.R3.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros q a o H i. destruct q as [|b]; destruct a as [x|b' off]; cbn [apos] in H; try discriminate H.
    - injection H as ->. cbn [ainst qaddr]. rewrite u_zbv. rewrite zbv_add_mod. reflexivity.
    - destruct (wt_eqb b' b) eqn:E; [|discriminate H]. injection H as ->. apply wt_eqb_eq in E. subst b'.
      cbn [ainst qaddr]. unfold ABoot.PropExec.v_addi. rewrite u_zbv, zbv_add_mod. f_equal. lia.
  Qed.
  #[using="Type"] Lemma apos_addw : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pa,$19.Po,$10.P,(5.(3.$10.)(1:.R3.R2.)(7.$10.R1.))Pk,$4.(5.(2.&40.)(:.&40.(1<.Vp,R4.)(;.&40.(<.R1.)))(;.&40.(1=.R5.(1;.R3.(<.R1.)))))")
(* [comment removed for export] *).
  Proof.
    intros q a o H k. rewrite <- (apos_addr q a o H). rewrite <- wadd_lit. f_equal. symmetry. apply bv_eq. rewrite u_zbv.
    pose proof (u64_range (ainst p a)). rewrite Z.mod_small by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma nth_error_hd_skipn : forall {X} (l : list X) k, nth_error l k = hd_error (skipn k l).
  Proof. intros X l. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
  #[using="Type"] Lemma zbyte_le : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pw,$4.Pv,$10.Pk,$4.P,(8.R1.R3.)(5.(3.(2.&8.))(=.(2.&8.)(1>.R4.(;.&40.R3.))R2.)(7.(2.&8.)(1?.R3.(<.R2.))))")
(* [comment removed for export] *).
  Proof.
    intros w v k Hk. unfold zbyte, word_to_le_bytes. rewrite u_zbv.
    rewrite nth_error_hd_skipn, (AX2S.skipn_Z_to_le_bytes w k) by lia.
    destruct (w - k)%nat as [|r] eqn:E; [lia|]. cbn [Z_to_le_bytes hd_error]. reflexivity.
  Qed.

  Variable L : list ct.
  Hypothesis HF : Forall (AsanMainEntryKit.cell_ok ASEGS mem) (map (cinst p) L).

  #[using="HF"] Lemma HF_in : forall c, In c L -> AsanMainEntryKit.cell_ok ASEGS mem (cinst p c).
  Proof. intros c Hc. exact (proj1 (Forall_forall _ _) HF (cinst p c) (in_map _ _ _ Hc)). Qed.

  #[using="HF"] Lemma cbyte_sound : forall q c z b, In c L -> cbyte q c z = Some b -> mrd ASEGS mem (Z_to_bv 64 (qaddr q z)) = Some b.
  Proof.
    intros q c z b Hc H. pose proof (HF_in c Hc) as HC.
    destruct c as [a w v|a n|a n c8|a n|a n|lo hi]; cbn [cbyte] in H; try discriminate H.
    - (* [comment removed for export] *)
      destruct (apos q a) as [o|] eqn:Ha; [|discriminate H]. destruct (wlit v) as [lit|] eqn:Hv; [|discriminate H].
      destruct ((o <=? z) && (z <? o + Z.of_nat w))%bool eqn:G; [|discriminate H]. injection H as <-.
      apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
      cbn [cinst AsanMainEntryKit.cell_ok] in HC. rewrite (wlit_sound p v lit Hv) in HC.
      pose proof (rdn_nth ASEGS mem w (ainst p a) _ (Z.to_nat (z - o)) HC ltac:(lia)) as R.
      rewrite (apos_addw q a o Ha) in R. replace (o + Z.of_nat (Z.to_nat (z - o))) with z in R by lia.
      rewrite R. rewrite (zbyte_le w lit (Z.to_nat (z - o))) by lia. rewrite Z2Nat.id by lia. reflexivity.
    - (* [comment removed for export] *)
      destruct (apos q a) as [o|] eqn:Ha; [|discriminate H]. destruct (wlitu n) as [len|] eqn:Hn; [|discriminate H].
      destruct ((o <=? z) && (z <? o + len))%bool eqn:G; [|discriminate H]. injection H as <-.
      apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
      ddestruct (wlitu_sound p n len Hn) as (Wn & Hlen & Un).
      cbn [cinst AsanMainEntryKit.cell_ok] in HC. rewrite Un in HC. destruct HC as [Hnw Hz].
      specialize (Hz (z - o) ltac:(lia)). rewrite (apos_addr q a o Ha) in Hz. replace (o + (z - o)) with z in Hz by lia.
      apply mrd_overlay. exact Hz.
    - (* [comment removed for export] *)
      destruct (apos q a) as [o|] eqn:Ha; [|discriminate H]. destruct (wlitu n) as [len|] eqn:Hn; [|discriminate H].
      destruct ((o <=? z) && (z <? o + len))%bool eqn:G; [|discriminate H]. injection H as <-.
      apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
      ddestruct (wlitu_sound p n len Hn) as (Wn & Hlen & Un).
      cbn [cinst AsanMainEntryKit.cell_ok] in HC. rewrite Un in HC. destruct HC as [Hnw Hz].
      specialize (Hz (z - o) ltac:(lia)). rewrite (apos_addr q a o Ha) in Hz. replace (o + (z - o)) with z in Hz by lia.
      apply mrd_overlay. exact Hz.
    - (* [comment removed for export] *)
      destruct q as [|b']; [|discriminate H].
      destruct ((lo <=? z) && (z <? hi))%bool eqn:G; [|discriminate H].
      apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
      cbn [cinst AsanMainEntryKit.cell_ok] in HC. cbn [qaddr]. rewrite (mrd_rom ASEGS mem _ (HC z ltac:(lia))). exact H.
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound2.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Variable L : list ct.
  Hypothesis HF : Forall (AsanMainEntryKit.cell_ok ASEGS mem) (map (cinst p) L).

  #[using="HF"] Lemma fbyte_sound : forall q z b, fbyte q L z = Some b -> mrd ASEGS mem (Z_to_bv 64 (qaddr p q z)) = Some b.
  Proof.
    intros q z b. assert (G : forall l, (forall c, In c l -> In c L) -> fbyte q l z = Some b -> mrd ASEGS mem (Z_to_bv 64 (qaddr p q z)) = Some b).
    { induction l as [|c l IH]; intros Hincl H; [discriminate H|]. cbn [fbyte] in H.
      destruct (cbyte q c z) as [b'|] eqn:Hc.
      - injection H as <-. exact (cbyte_sound mem p L HF q c z b' (Hincl c (or_introl eq_refl)) Hc).
      - apply IH; [intros c' Hc'; apply Hincl; right; exact Hc' | exact H]. }
    apply G. exact (fun c H => H).
  Qed.

  #[using="Type"] Lemma fbytes_length : forall q n z bs, fbytes q L z n = Some bs -> length bs = n.
  Proof.
    intros q n. induction n as [|n IH]; intros z bs H; cbn [fbytes] in H.
    - injection H as <-. reflexivity.
    - destruct (fbyte q L z) as [b|]; [|discriminate H]. destruct (fbytes q L (z + 1) n) as [bs'|] eqn:Hbs; [|discriminate H].
      injection H as <-. cbn [length]. rewrite (IH (z + 1) bs' Hbs). reflexivity.
  Qed.

  #[using="HF"] Lemma fbytes_sound : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pn,$4.Pz,$10.Pbs,(0.(2.&8.))P,(5.(3.(0.(2.&8.)))(20.R4.VL,R2.R3.)(7.(0.(2.&8.))R1.))P,(14.=(21.Vp,R5.R3.))P,(14.(1;.(21.Vp,R6.R4.)(<.R5.))(16.+2.+40.))(22.$23.Vmem,(21.Vp,R7.R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros q n. induction n as [|n IH]; intros z bs H Hlo Hhi; cbn [fbytes] in H.
    - injection H as <-. refine (conj Hlo (conj _ _)). { cbn. lia. } intros i Hi. cbn in Hi. lia.
    - destruct (fbyte q L z) as [b|] eqn:Hb; [|discriminate H]. destruct (fbytes q L (z + 1) n) as [bs'|] eqn:Hbs; [|discriminate H].
      injection H as <-.
      assert (Hq1 : qaddr p q (z + 1) = qaddr p q z + 1) by (destruct q; cbn [qaddr]; lia).
      pose proof (fbytes_length q n (z + 1) bs' Hbs) as LEN.
      assert (B1 : 0 <= qaddr p q (z + 1)) by (rewrite Hq1; lia). assert (B2 : qaddr p q (z + 1) + Z.of_nat n <= 2 ^ 64) by (rewrite Hq1; lia).
      dpose (IH (z + 1) bs' Hbs B1 B2) as (_ & _ & R).
      refine (conj Hlo (conj _ _)). { cbn [length]. rewrite LEN. exact Hhi. }
      intros [|i] Hi; cbn [nth_error].
      + unfold wa. rewrite Z.add_0_r. exact (fbyte_sound q z b Hb).
      + cbn [length] in Hi. specialize (R i ltac:(lia)). rewrite Hq1 in R. unfold wa in R |- *.
        replace (qaddr p q z + Z.of_nat (S i)) with (qaddr p q z + 1 + Z.of_nat i) by lia. exact R.
  Qed.

  #[using="HF"] Lemma fwr_sound : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pn,$10.P,(5.$24.(25.R3.VL,R2.R1.)$26.)P,(14.=(21.Vp,R4.R3.))P,(14.(1;.(21.Vp,R5.R4.)R3.)(16.+2.+40.))(27.$23.Vmem,(21.Vp,R6.R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros q z n H Hlo Hhi. unfold fwr in H. apply existsb_exists in H as [c [Hc Hw]].
    pose proof (HF_in mem p L HF c Hc) as HC.
    destruct c as [a w v|a n0|a n0 c8|a n0|a len|lo hi]; cbn [cwr] in Hw; try discriminate Hw.
    destruct (apos q a) as [o|] eqn:Ha; [|discriminate Hw]. destruct (wlitu len) as [l|] eqn:Hl; [|discriminate Hw].
    apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2.
    ddestruct (wlitu_sound p len l Hl) as (Wl & Hrange & Ul).
    cbn [cinst AsanMainEntryKit.cell_ok] in HC. rewrite Ul in HC. destruct HC as [Hnw Hs].
    split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    specialize (Hs (z - o + i) 1%nat ltac:(lia) ltac:(cbn; lia)).
    pose proof (store_ok_wview ASEGS mem _ 1%nat 0%nat Hs ltac:(lia)) as WV.
    rewrite Z.add_0_r in WV. unfold wa in WV |- *. rewrite u_zbv, zbv_mod in WV.
    rewrite (apos_addr p q a o Ha) in WV. replace (o + (z - o + i)) with (z + i) in WV by lia.
    destruct q; cbn [qaddr] in WV |- *; [exact WV | replace (bv_unsigned (winst p b) + z + i) with (bv_unsigned (winst p b) + (z + i)) by lia; exact WV].
  Qed.

  
  (* [comment removed for export] *)
  #[using="HF"] Lemma facts_ro_cells : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pcs,(0.$28.)Pbs,(0.(2.&8.))P,(5.(3.(0.(2.&8.)))(20.R4.VL,R3.(29.R2.))(7.(0.(2.&8.))R1.))P,(5.(0.(2.&8.))(2:.R3.)R2.)P,(2;.R4.)P,(14.=(21.Vp,R7.R6.))P,(14.(1;.(21.Vp,R8.R7.)(<.(29.R6.)))(16.+2.+40.))(2<.$2=.Vmem,(21.Vp,R9.R8.)R7.)")
(* [comment removed for export] *).
  Proof.
    intros q z cs bs Hf Hb Hwf Hlo Hhi. unfold ro_cells, cells_at. split; [exact Hwf|]. rewrite Hb.
    replace (length bs) with (cells_size cs) by (rewrite <- Hb; symmetry; apply cells_bytes_length; exact Hwf).
    exact (fbytes_sound q _ z bs Hf Hlo Hhi).
  Qed.
  #[using="HF"] Lemma facts_rw_cells : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pcs,(0.$28.)Pbs,(0.(2.&8.))P,(5.(3.(0.(2.&8.)))(20.R4.VL,R3.(29.R2.))(7.(0.(2.&8.))R1.))P,(5.(0.(2.&8.))(2:.R3.)R2.)P,(2;.R4.)P,(5.$24.(25.R7.VL,R6.(<.(29.R5.)))$26.)P,(14.=(21.Vp,R8.R7.))P,(14.(1;.(21.Vp,R9.R8.)(<.(29.R7.)))(16.+2.+40.))(2>.$2=.Vmem,(21.Vp,R:.R9.)R8.)")
(* [comment removed for export] *).
  Proof.
    intros q z cs bs Hf Hb Hwf Hw Hlo Hhi. split; [exact (facts_ro_cells q z cs bs Hf Hb Hwf Hlo Hhi)|].
    exact (fwr_sound q z _ Hw Hlo Hhi).
  Qed.
      #[using="HF"] Lemma facts_u64arr : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pws,(0.(2.&40.))Pbs,(0.(2.&8.))P,(5.(3.(0.(2.&8.)))(20.R4.VL,R3.(2?.#8.(30.(2.&40.)R2.)))(7.(0.(2.&8.))R1.))P,(5.(0.(2.&8.))(31.R3.)R2.)P,(5.$24.(25.R6.VL,R5.(32.+8.(<.(30.(2.&40.)R4.))))$26.)P,(14.=(21.Vp,R7.R6.))P,(14.(1;.(21.Vp,R8.R7.)(32.+8.(<.(30.(2.&40.)R6.))))(16.+2.+40.))(33.$2=.Vmem,(21.Vp,R9.R8.)R7.)")
(* [comment removed for export] *).
  Proof.
    intros q z ws bs Hf Hb Hw Hlo Hhi. split; [| exact (fwr_sound q z _ Hw Hlo Hhi)].
    rewrite Hb. pose proof (fbytes_sound q _ z bs Hf Hlo ltac:(rewrite Nat2Z.inj_mul in *; cbn [Z.of_nat] in *; lia)) as B. exact B.
  Qed.
  (* [comment removed for export] *)
  End Sound2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cword.
  Variable mem : word -> option byte.

  #[using="Type"] Lemma cword_bytes_at : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pa,(2.&40.)Pw,$4.Pv,(2.&40.)P,(34.$23.Vmem,(35.R3.R2.R1.))P,(14.(1;.(17.&40.R4.)(<.R3.))(16.+2.+40.))(22.$2=.Vmem,(17.&40.R5.)(1>.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros a w v HC Hhi. cbn [AsanMainEntryKit.cell_ok] in HC. pose proof (u64_range a) as Ra.
    split; [lia|]. split; [rewrite length_word_to_le_bytes || (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes); exact Hhi|].
    intros i Hi. rewrite asegs_ASEGS. unfold wa. rewrite <- (rdn_nth ASEGS mem w a _ i HC).
    - f_equal. rewrite <- wadd_lit. f_equal. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - revert Hi. rewrite length_word_to_le_bytes || (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes). exact (fun H => H).
  Qed.
  #[using="Type"] Lemma cword_ro_cells : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pa,(2.&40.)Pw,$4.Pv,(2.&40.)Pcs,(0.$28.)P,(34.$23.Vmem,(35.R4.R3.R2.))P,(5.(0.(2.&8.))(2:.R2.)(1>.R4.R3.))P,(2;.R3.)P,(14.(1;.(17.&40.R7.)(<.R6.))(16.+2.+40.))(2<.$2=.Vmem,(17.&40.R8.)R5.)")
(* [comment removed for export] *).
  Proof.
    intros a w v cs HC Hb Hwf Hhi. unfold ro_cells, cells_at. split; [exact Hwf|]. rewrite Hb. exact (cword_bytes_at a w v HC Hhi).
  Qed.
  #[using="Type"] Lemma cwr_wr_at : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pa,(2.&40.)Pn,(2.&40.)P,(34.$23.Vmem,(36.R2.R1.))(27.$2=.Vmem,(17.&40.R3.)(17.&40.R2.))")
(* [comment removed for export] *).
  Proof.
    intros a n HC. cbn [AsanMainEntryKit.cell_ok] in HC. destruct HC as [Hnw Hs]. pose proof (u64_range a) as Ra.
    split; [lia|]. split; [exact Hnw|]. intros i Hi.
    specialize (Hs i 1%nat ltac:(lia) ltac:(cbn; lia)).
    pose proof (store_ok_wview ASEGS mem _ 1%nat 0%nat Hs ltac:(lia)) as WV.
    rewrite Z.add_0_r in WV. unfold wa in WV |- *. rewrite u_zbv, zbv_mod in WV. rewrite asegs_ASEGS. exact WV.
  Qed.
    (* [comment removed for export] *)
  #[using="Type"] Lemma czero_bytes_at : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pa,(2.&40.)Pn,(2.&40.)Pk,$4.P,(34.$23.Vmem,(37.R3.R2.))P,(14.(<.R2.)(17.&40.R3.))(22.$2=.Vmem,(17.&40.R5.)(38.(2.&8.)(;.&8.=)R3.))")
(* [comment removed for export] *).
  Proof.
    intros a n k HC Hk. cbn [AsanMainEntryKit.cell_ok] in HC. destruct HC as [Hnw Hz]. pose proof (u64_range a) as Ra.
    split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    rewrite asegs_ASEGS. unfold wa. rewrite (mrd_overlay ASEGS mem _ _ (Hz (Z.of_nat i) ltac:(lia))).
    symmetry. apply nth_error_repeat. exact Hi.
  Qed.
End Cword.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => ((bv_unsigned x =? bv_unsigned y) && bytes_eqb a' b')%bool
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [bytes_eqb] in H; try discriminate H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | exact (IH b H2)].
Qed.
(* [comment removed for export] *)
Definition fchk (q : qbase) (L : list ct) (z : Z) (cs : list cell) : bool :=
  match fbytes q L z (cells_size cs) with Some bs => bytes_eqb bs (cells_bytes cs) | None => false end.
(* [comment removed for export] *)
Definition fchkw (q : qbase) (L : list ct) (z : Z) (cs : list cell) : bool :=
  (fchk q L z cs && fwr q L z (Z.of_nat (cells_size cs)))%bool.
Definition fchk32 (q : qbase) (L : list ct) (z : Z) (ws : list word) : bool :=
  (match fbytes q L z (4 * length ws) with Some bs => bytes_eqb bs (u32s ws) | None => false end && fwr q L z (4 * Z.of_nat (length ws)))%bool.
Definition fchk64 (q : qbase) (L : list ct) (z : Z) (ws : list word) : bool :=
  (match fbytes q L z (8 * length ws) with Some bs => bytes_eqb bs (u64s ws) | None => false end && fwr q L z (8 * Z.of_nat (length ws)))%bool.

Section Sound3.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Variable L : list ct.
  Hypothesis HF : Forall (AsanMainEntryKit.cell_ok ASEGS mem) (map (cinst p) L).

  #[using="HF"] Lemma chk_ro_cells : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pcs,(0.$28.)P,(5.$24.(39.R3.VL,R2.R1.)$26.)P,(2;.R2.)P,(14.=(21.Vp,R5.R4.))P,(14.(1;.(21.Vp,R6.R5.)(<.(29.R4.)))(16.+2.+40.))(2<.$2=.Vmem,(21.Vp,R7.R6.)R5.)")
(* [comment removed for export] *).
  Proof.
    intros q z cs H Hwf Hlo Hhi. unfold fchk in H. destruct (fbytes q L z (cells_size cs)) as [bs|] eqn:Hf; [|discriminate H].
    apply bytes_eqb_eq in H. exact (facts_ro_cells mem p L HF q z cs bs Hf (eq_sym H) Hwf Hlo Hhi).
  Qed.
  #[using="HF"] Lemma chk_rw_cells : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pcs,(0.$28.)P,(5.$24.(3:.R3.VL,R2.R1.)$26.)P,(2;.R2.)P,(14.=(21.Vp,R5.R4.))P,(14.(1;.(21.Vp,R6.R5.)(<.(29.R4.)))(16.+2.+40.))(2>.$2=.Vmem,(21.Vp,R7.R6.)R5.)")
(* [comment removed for export] *).
  Proof.
    intros q z cs H Hwf Hlo Hhi. unfold fchkw in H. apply andb_prop in H as [H1 H2].
    split; [exact (chk_ro_cells q z cs H1 Hwf Hlo Hhi) | exact (fwr_sound mem p L HF q z _ H2 Hlo Hhi)].
  Qed.
      #[using="HF"] Lemma chk_wr_at : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.Pn,$10.P,(5.$24.(25.R3.VL,R2.R1.)$26.)P,(14.=(21.Vp,R4.R3.))P,(14.(1;.(21.Vp,R5.R4.)R3.)(16.+2.+40.))(27.$2=.Vmem,(21.Vp,R6.R5.)R4.)")
(* [comment removed for export] *).
  Proof. intros. apply (fwr_sound mem p L HF); assumption. Qed.
End Sound3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_le_bytes_to_word : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2 ^ 64).
  pose proof (Lib.PropExec.bytes_le_to_Z_bound bs) as B. rewrite Hl in B. pose proof (Lib.PropExec.bytes_le_to_Z_nonneg bs) as B0.
  rewrite Z.mod_small by (cbn in B; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Section Sound4.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Variable L : list ct.
  Hypothesis HF : Forall (AsanMainEntryKit.cell_ok ASEGS mem) (map (cinst p) L).

  Definition fchkd (q : qbase) (L : list ct) (z : Z) (n : nat) : bool := match fbytes q L z n with Some _ => true | None => false end.

  #[using="HF"] Lemma chk_ex_C8 : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.P,(5.$24.(3;.R2.VL,R1.#8.)$26.)P,(14.=(21.Vp,R3.R2.))P,(14.(1;.(21.Vp,R4.R3.)+8.)(16.+2.+40.))(3<.(2.&40.)Lc,(2.&40.)(2<.$2=.Vmem,(21.Vp,R6.R5.)(3=.$28.(3>.R1.)(3?.$28.))))")
(* [comment removed for export] *).
  Proof.
    intros q z H Hlo Hhi. unfold fchkd in H. destruct (fbytes q L z 8) as [bs|] eqn:Hf; [|discriminate H].
    pose proof (fbytes_length L q 8 z bs Hf) as LEN.
    exists (le_bytes_to_word bs). apply (facts_ro_cells mem p L HF q z [C8 (le_bytes_to_word bs)] bs Hf).
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply le8_le_bytes_to_word. exact LEN.
    - cbn. tauto. - exact Hlo. - exact Hhi.
  Qed.
  #[using="HF"] Lemma chk_ex_C4 : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.P,(5.$24.(3;.R2.VL,R1.#4.)$26.)P,(14.=(21.Vp,R3.R2.))P,(14.(1;.(21.Vp,R4.R3.)+4.)(16.+2.+40.))(3<.(2.&40.)Lc,(2.&40.)(2<.$2=.Vmem,(21.Vp,R6.R5.)(3=.$28.(40.R1.)(3?.$28.))))")
(* [comment removed for export] *).
  Proof.
    intros q z H Hlo Hhi. unfold fchkd in H. destruct (fbytes q L z 4) as [bs|] eqn:Hf; [|discriminate H].
    pose proof (fbytes_length L q 4 z bs Hf) as LEN.
    exists (le_bytes_to_word bs). apply (facts_ro_cells mem p L HF q z [C4 (le_bytes_to_word bs)] bs Hf).
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply le4_le_bytes_to_word. exact LEN.
    - cbn. tauto. - exact Hlo. - exact Hhi.
  Qed.
  #[using="HF"] Lemma chk_ex_C1 : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.P,(5.$24.(3;.R2.VL,R1.#1.)$26.)P,(14.=(21.Vp,R3.R2.))P,(14.(1;.(21.Vp,R4.R3.)+1.)(16.+2.+40.))(3<.(2.&8.)Lb,(2.&8.)(2<.$2=.Vmem,(21.Vp,R6.R5.)(3=.$28.(41.R1.)(3?.$28.))))")
(* [comment removed for export] *).
  Proof.
    intros q z H Hlo Hhi. unfold fchkd in H. destruct (fbytes q L z 1) as [bs|] eqn:Hf; [|discriminate H].
    pose proof (fbytes_length L q 1 z bs Hf) as LEN. destruct bs as [|b [|]]; try discriminate LEN.
    exists b. apply (facts_ro_cells mem p L HF q z [C1 b] [b] Hf); [reflexivity | cbn; tauto | exact Hlo | exact Hhi].
  Qed.
  (* [comment removed for export] *)
  #[using="HF"] Lemma chk_ex_C8w : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.P,(5.$24.(3;.R2.VL,R1.#8.)$26.)P,(5.$24.(25.R3.VL,R2.+8.)$26.)P,(14.=(21.Vp,R4.R3.))P,(14.(1;.(21.Vp,R5.R4.)+8.)(16.+2.+40.))(3<.(2.&40.)Lc,(2.&40.)(2>.$2=.Vmem,(21.Vp,R7.R6.)(3=.$28.(3>.R1.)(3?.$28.))))")
(* [comment removed for export] *).
  Proof. intros q z H W Hlo Hhi. destruct (chk_ex_C8 q z H Hlo Hhi) as [c Hc]. exists c. split; [exact Hc | exact (fwr_sound mem p L HF q z 8 W Hlo Hhi)]. Qed.
    #[using="HF"] Lemma chk_ex_C1w : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pq,$18.Pz,$10.P,(5.$24.(3;.R2.VL,R1.#1.)$26.)P,(5.$24.(25.R3.VL,R2.+1.)$26.)P,(14.=(21.Vp,R4.R3.))P,(14.(1;.(21.Vp,R5.R4.)+1.)(16.+2.+40.))(3<.(2.&8.)Lb,(2.&8.)(2>.$2=.Vmem,(21.Vp,R7.R6.)(3=.$28.(41.R1.)(3?.$28.))))")
(* [comment removed for export] *).
  Proof. intros q z H W Hlo Hhi. destruct (chk_ex_C1 q z H Hlo Hhi) as [c Hc]. exists c. split; [exact Hc | exact (fwr_sound mem p L HF q z 1 W Hlo Hhi)]. Qed.
End Sound4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ro_cells_app : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pmem,P,(2.&40.)(3.(2.&8.))PA,$10.Pcs1,(0.$28.)Pcs2,(0.$28.)P,(2<.$2=.R4.R3.R2.)P,(2<.$2=.R5.(1;.R4.(<.(29.R3.)))R2.)(2<.$2=.R6.R5.(42.$28.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros mem A cs1 cs2 [W1 B1] [W2 B2]. unfold ro_cells, cells_at. split; [apply cells_wf_app; split; assumption|].
  rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
Qed.
Lemma rw_cells_app2 : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pmem,P,(2.&40.)(3.(2.&8.))PA,$10.Pcs1,(0.$28.)Pcs2,(0.$28.)P,(2>.$2=.R4.R3.R2.)P,(2>.$2=.R5.(1;.R4.(<.(29.R3.)))R2.)(2>.$2=.R6.R5.(42.$28.R4.R3.))")
(* [comment removed for export] *).
Proof. intros mem A cs1 cs2 H1 H2. apply CellsX.rw_cells_app. split; assumption. Qed.

(* [comment removed for export] *)
Definition romdef (z : Z) (n : nat) : bool :=
  forallb (fun i => match rom_byte (z + Z.of_nat i) with Some _ => true | None => false end) (seq 0 n).
Section Img.
  Variable mem : word -> option byte.
  Definition imgb (z : Z) : byte :=
    match mem (Z_to_bv 64 z) with Some b => b | None => match rom_byte z with Some b => b | None => Z_to_bv 8 0 end end.
  #[using="Type"] Lemma imgb_mrd : forall z, match rom_byte z with Some _ => true | None => false end = true -> mrd ASEGS mem (Z_to_bv 64 z) = Some (imgb z).
  Proof.
    intros z H. unfold imgb, mrd. destruct (mem (Z_to_bv 64 z)) as [b|]; [reflexivity|].
    unfold rom_byte in *. destruct (Lib.PropExec.seg_rom ASEGS (Z_to_bv 64 z)); [reflexivity | discriminate H].
  Qed.
  #[using="Type"] Lemma img_bytes_at : ltac2:(CDefT.buildp (gd_tbl_AH0Facts ()) "Pz,$10.Pn,$4.P,(5.$24.(43.R2.R1.)$26.)P,(14.=R3.)P,(14.(1;.R4.(<.R3.))(16.+2.+40.))(22.$2=.Vmem,R5.(44.$4.(2.&8.)Li,$4.(45.(1;.R6.(<.R1.)))(46.#0.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros z n H Hlo Hhi. split; [exact Hlo|]. split; [rewrite length_map, length_seq; exact Hhi|].
    intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi).
    rewrite seq_nth by exact Hi. cbn [option_map Nat.add]. rewrite asegs_ASEGS. unfold wa. apply imgb_mrd.
    exact (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)).
  Qed.
  #[using="Type"] Lemma img_ex_C4 : forall z, romdef z 4 = true -> 0 <= z -> z + 4 <= 2 ^ 64 -> exists e, ro_cells asegs mem z [C4 e].
  Proof.
    intros z H Hlo Hhi. set (bs := map (fun i => imgb (z + Z.of_nat i)) (seq 0 4)).
    exists (le_bytes_to_word bs). split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r.
    rewrite le4_le_bytes_to_word by reflexivity. apply img_bytes_at; assumption.
  Qed.
  End Img.
