(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXDj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXDj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q25t.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Definition kimg_inside (ilo ihi : Z) (kn : list kentry) : bool :=
forallb (fun K => match K with KImg lo hi => (ilo <=? lo) && (hi <=? ihi) | _ => true end) kn.

Section Transfer.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Variables ilo ihi : Z.

Hypothesis Hvis : forall a : word, ilo <= bv_unsigned a < ihi -> H a = false.

Lemma mrestrict_some : forall m a b, mrestrict H m a = Some b -> m a = Some b.
Proof. intros m a b. unfold mrestrict. destruct (H a); [discriminate| exact (fun x => x)]. Qed.

Lemma kentry_ok_full : forall E m K,
match K with KImg lo hi => ilo <= lo /\ hi <= ihi | _ => True end ->
kentry_ok segs E (mrestrict H m) K -> kentry_ok segs E m K.
Proof.
intros E m K HK Hk. destruct K; cbn [kentry_ok] in *.
- destruct Hk as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
rewrite <- ov_rdn in Hr |- *. exact (proj1 (ov_read_bytes_restrict segs H HH _ _ _ _ Hr)).
- destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi. exact (mrestrict_some _ _ _ (Hz i Hi)).
- destruct Hk as (Hf & Hl & Hz). split; [exact Hf|]. split; [exact Hl|]. intros i Hi. exact (mrestrict_some _ _ _ (Hz i Hi)).
- destruct Hk as (H0 & H1 & Hn). split; [exact H0|]. split; [exact H1|]. intros i Hi.
specialize (Hn i Hi). unfold mrestrict in Hn.
rewrite (Hvis (Z_to_bv 64 i)) in Hn; [exact Hn|].
destruct HK as [Hlo Hhi]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Z.mod_small; lia.
- exact Hk.
- exact Hk.
- destruct Hk as [Hf Hs]. split; [exact Hf|]. intros d k Hd Hn.
exact (proj1 (store_ok_restrict segs H HH k m _ (Hs d k Hd Hn))).
- exact Hk.
- destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi. exact (mrestrict_some _ _ _ (Hz i Hi)).
- destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi Hc. apply (Hz i Hi). unfold mrestrict. rewrite Hc.
destruct (H (Z_to_bv 64 (estart E a + i))); reflexivity.
Qed.

Lemma know_ok_full : forall E m kn,
kimg_inside ilo ihi kn = true ->
know_ok segs E (mrestrict H m) kn -> know_ok segs E m kn.
Proof.
intros E m kn Hi Hk. unfold know_ok in *. rewrite Forall_forall in Hk |- *. intros K HK.
apply kentry_ok_full; [| exact (Hk K HK)].
unfold kimg_inside in Hi. rewrite forallb_forall in Hi. specialize (Hi K HK).
destruct K; try exact I. apply andb_prop in Hi as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
End Transfer.

Definition fact_below (k : list kentry) (top : Z) (K : kentry) : bool :=
match K with
| KWord (SA b off) w _ => match xhi k b with Some h => h + off + Z.of_nat w <=? top | None => false end
| KZero (SA b off) n | KWr (SA b off) n | KUnk (SA b off) n | KFill (SA b off) n _ | KBlob (SA b off) n _ =>
match xhi k b, xhi k n with Some h, Some m => h + off + m <=? top | _, _ => false end
| _ => true
end.

Section Mono.
Variable segs : list Segment.
Variables H1 H2 : word -> bool.
Hypothesis HH1 : H_off_segments segs H1.
Variable top : Z.

Hypothesis H21 : forall a : word, bv_unsigned a < top -> H2 a = true -> H1 a = true.
Variables ilo ihi : Z.
Hypothesis Hvis1 : forall a : word, ilo <= bv_unsigned a < ihi -> H1 a = false.

Lemma avoid2 : forall z, 0 <= z -> z < top -> H1 (Z_to_bv 64 z) = false -> H2 (Z_to_bv 64 z) = false.
Proof.
intros z Hz Ht Hf. destruct (H2 (Z_to_bv 64 z)) eqn:E; [|reflexivity]. exfalso.
assert (Hu : bv_unsigned (Z_to_bv 64 z) < top).
{ rewrite u_lit64. unfold two64. pose proof (Z.mod_le z (2^64) Hz ltac:(lia)). lia. }
rewrite (H21 _ Hu E) in Hf. discriminate.
Qed.

Lemma range_avoids_mono : forall (a : word) n, bv_unsigned a + Z.of_nat n <= top ->
range_avoids H1 a n -> range_avoids H2 a n.
Proof.
intros a n Htop Hav k Hk. specialize (Hav k Hk). unfold woff in *.
pose proof (u64_range a). apply avoid2; [lia | lia | exact Hav].
Qed.

Lemma kentry_ok_mono : forall E m k K,
know_ok segs E (mrestrict H1 m) k ->
match K with KImg lo hi => ilo <= lo /\ hi <= ihi | _ => True end ->
fact_below k top K = true ->
kentry_ok segs E (mrestrict H1 m) K -> kentry_ok segs E (mrestrict H2 m) K.
Proof.
intros E m k K HK HKimg Hb Hk.
assert (XHI : forall e h, xhi k e = Some h -> bv_unsigned (edenot E e) <= h).
{ intros e h He. exact (xhi_sound segs E _ k e h HK He). }
destruct K; cbn [kentry_ok fact_below] in *.
-  destruct a as [b off]. destruct Hk as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
destruct (xhi k b) as [h|] eqn:Eh; [|discriminate]. apply Z.leb_le in Hb. pose proof (XHI _ _ Eh) as Bh.
rewrite <- ov_rdn in Hr |- *. destruct (ov_read_bytes_restrict segs H1 HH1 _ _ _ _ Hr) as [Hm Hav].
rewrite (ov_read_bytes_mrestrict_eq segs H2); [exact Hm|].
apply range_avoids_mono; [| exact Hav]. rewrite (flat_u _ _ _ Hf). unfold estart. cbn [a_base a_off]. lia.
-  destruct a as [b off]. destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi.
specialize (Hz i Hi). unfold mrestrict in Hz |- *.
destruct (H1 (Z_to_bv 64 (estart E {| a_base := b; a_off := off |} + i))) eqn:E1; [discriminate|].
destruct (xhi k b) as [h|] eqn:Eh; [|discriminate]. destruct (xhi k n) as [mm|] eqn:En; [|discriminate].
apply Z.leb_le in Hb. pose proof (XHI _ _ Eh) as B1. pose proof (XHI _ _ En) as B2. unfold elenZ in Hi.
destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
rewrite (avoid2 _) ; [exact Hz | lia | lia | exact E1].
-  destruct a as [b off]. destruct Hk as (Hf & Hl & Hz). split; [exact Hf|]. split; [exact Hl|]. intros i Hi.
specialize (Hz i Hi). unfold mrestrict in Hz |- *.
destruct (H1 (Z_to_bv 64 (estart E {| a_base := b; a_off := off |} + i))) eqn:E1; [discriminate|].
destruct (xhi k b) as [h|] eqn:Eh; [|discriminate]. destruct (xhi k n) as [mm|] eqn:En; [|discriminate].
apply Z.leb_le in Hb. pose proof (XHI _ _ Eh) as B1. pose proof (XHI _ _ En) as B2. unfold elenZ in Hi.
destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
rewrite (avoid2 _) ; [exact Hz | lia | lia | exact E1].
-  destruct Hk as (A1 & A2 & Hn). split; [exact A1|]. split; [exact A2|]. intros i Hi.
specialize (Hn i Hi). unfold mrestrict in Hn |- *.
rewrite (Hvis1 (Z_to_bv 64 i)) in Hn.
2:{ rewrite u64_lit; lia. }
rewrite Hn. destruct (H2 (Z_to_bv 64 i)); reflexivity.
- exact Hk.
- exact Hk.
-  destruct a as [b off]. destruct Hk as [Hf Hs]. split; [exact Hf|]. intros d j Hd Hj.
destruct (store_ok_restrict segs H1 HH1 j m _ (Hs d j Hd Hj)) as [Hm Hav].
rewrite (store_ok_mrestrict_eq segs H2); [exact Hm|].
destruct (xhi k b) as [h|] eqn:Eh; [|discriminate]. destruct (xhi k n) as [mm|] eqn:En; [|discriminate].
apply Z.leb_le in Hb. pose proof (XHI _ _ Eh) as B1. pose proof (XHI _ _ En) as B2. unfold elenZ in Hj.
destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
unfold elenZ in *.
destruct (Nat.eq_dec j 0) as [->|Hj0]. { intros kk Hkk. lia. }
apply range_avoids_mono; [| exact Hav]. rewrite u64_lit by lia. lia.
- exact Hk.
-  destruct a as [b off]. destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi.
specialize (Hz i Hi). unfold mrestrict in Hz |- *.
destruct (H1 (Z_to_bv 64 (estart E {| a_base := b; a_off := off |} + i))) eqn:E1; [discriminate|].
destruct (xhi k b) as [h|] eqn:Eh; [|discriminate]. destruct (xhi k n) as [mm|] eqn:En; [|discriminate].
apply Z.leb_le in Hb. pose proof (XHI _ _ Eh) as B1. pose proof (XHI _ _ En) as B2. unfold elenZ in Hi.
destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
rewrite (avoid2 _) ; [exact Hz | lia | lia | exact E1].
-  destruct a as [b off]. destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi Hc.
specialize (Hz i Hi). unfold mrestrict in Hz, Hc.
destruct (H1 (Z_to_bv 64 (estart E {| a_base := b; a_off := off |} + i))) eqn:E1; [exact (Hz eq_refl)|].
destruct (xhi k b) as [h|] eqn:Eh; [|discriminate]. destruct (xhi k n) as [mm|] eqn:En; [|discriminate].
apply Z.leb_le in Hb. pose proof (XHI _ _ Eh) as B1. pose proof (XHI _ _ En) as B2. unfold elenZ in Hi.
destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
rewrite (avoid2 _) in Hc; [exact (Hz Hc) | lia | lia | exact E1].
Qed.

End Mono.

Definition fact_avoids (H : word -> bool) (E : env) (K : kentry) : Prop :=
match K with
| KWord a w _ => forall i, 0 <= i < Z.of_nat w -> H (Z_to_bv 64 (estart E a + i)) = false
| KZero a n | KWr a n | KUnk a n | KFill a n _ | KBlob a n _ => forall i, 0 <= i < elenZ E n -> H (Z_to_bv 64 (estart E a + i)) = false
| _ => True
end.

Lemma kentry_ok_hide : forall segs (H : word -> bool) E m K,
kentry_ok segs E m K -> fact_avoids H E K -> kentry_ok segs E (mrestrict H m) K.
Proof.
intros segs H E m K Hk Hav. destruct K; cbn [kentry_ok fact_avoids] in *.
- destruct Hk as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
rewrite (rdn_mrestrict_eq segs H); [exact Hr|]. intros j Hj. unfold woff. rewrite (flat_u _ _ _ Hf).
replace (Z_to_bv 64 (estart E a + Z.of_nat j)) with (Z_to_bv 64 (estart E a + Z.of_nat j)) by reflexivity.
apply Hav. lia.
- destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi. unfold mrestrict. rewrite (Hav i Hi). apply Hz. exact Hi.
- destruct Hk as (Hf & Hl & Hz). split; [exact Hf|]. split; [exact Hl|]. intros i Hi. unfold mrestrict. rewrite (Hav i Hi). apply Hz. exact Hi.
- destruct Hk as (A1 & A2 & Hn). split; [exact A1|]. split; [exact A2|]. intros i Hi. unfold mrestrict. rewrite (Hn i Hi). destruct (H _); reflexivity.
- exact Hk.
- exact Hk.
- destruct Hk as [Hf Hs]. split; [exact Hf|]. intros d j Hd Hj. rewrite (store_ok_mrestrict_eq segs H); [exact (Hs d j Hd Hj)|].
intros kk Hkk. unfold woff. rewrite u64_lit. 2:{ destruct Hf as (F1 & F2 & F3 & F4). lia. }
replace (estart E a + d + Z.of_nat kk) with (estart E a + (d + Z.of_nat kk)) by lia. apply Hav. lia.
- exact Hk.
- destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi. unfold mrestrict. rewrite (Hav i Hi). apply Hz. exact Hi.
- destruct Hk as [Hf Hz]. split; [exact Hf|]. intros i Hi. unfold mrestrict. rewrite (Hav i Hi). apply Hz. exact Hi.
Qed.

Definition kn_has (K : kentry) (k : list kentry) : bool := existsb (kentry_eqb K) k.
Lemma kn_has_In : forall K k, kn_has K k = true -> In K k.
Proof.
intros K k H. unfold kn_has in H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin.
Qed.
Definition kn_has_all (ks k : list kentry) : bool := forallb (fun K => kn_has K k) ks.
Lemma kn_has_all_In : forall ks k K, kn_has_all ks k = true -> In K ks -> kn_has K k = true.
Proof. intros ks k K H Hin. unfold kn_has_all in H. rewrite forallb_forall in H. exact (H K Hin). Qed.

Fixpoint blob_free (e : expr) : bool :=
match e with
| ELit _ | EVar _ => true
| EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => blob_free a && blob_free b
| EExt _ _ _ a => blob_free a
| EBlob _ _ _ _ => false
end.
Lemma edenot_ev_agree : forall b E E' e,
(forall n, (n < b)%nat -> ev E n = ev E' n) -> blob_free e = true -> AP.expr_vars_lt b e = true ->
edenot E e = edenot E' e.
Proof.
intros b E E' e Hv. induction e; cbn [blob_free AP.expr_vars_lt edenot]; intros Hb H;
repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
try reflexivity; try discriminate;
try (rewrite IHe1, IHe2 by assumption; reflexivity);
try (rewrite IHe by assumption; reflexivity).
apply Nat.ltb_lt in H. apply Hv. exact H.
Qed.

Definition E_AUXV : expr :=
EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0))
(EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6)))).
Definition stack_fact (K : kentry) : bool :=
match K with
| KWord (SA b off) w _ => (expr_eqb b E_AUXV && (24 <=? off) && (off + Z.of_nat w <=? 184))%bool
| _ => false
end.
Lemma split_auxv : split_lit e_auxv = (E_AUXV, 24).  Proof. vm_compute. reflexivity. Qed.

Definition GB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 10)).
Definition GK : Z := 2146402304.
Definition GLEN : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EVar 10))) (ELit 0x100000100000).
Definition KW_BAND : kentry := KWr (SA GB GK) GLEN.

Definition gap_apart (k : list kentry) (K : kentry) : bool :=
match K with
| KWord (SA b off) w _ => ranges_apart_x k b off (ELit (Z.of_nat w)) GB GK (ELit 20)
| KZero (SA b off) n | KWr (SA b off) n | KUnk (SA b off) n | KFill (SA b off) n _ | KBlob (SA b off) n _ => ranges_apart_x k b off n GB GK (ELit 20)
| _ => true
end.
Definition is_band_fact (K : kentry) : bool := (kentry_eqb K KZ_BAND || kentry_eqb K KW_BAND)%bool.

Definition VB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6)).
Definition VK : Z := 2146402816.
Definition VLEN : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-2)) (EVar 6))) (ELit 0x1000000ffe00).
Definition KZ_BAND_V : kentry := KZero (SA VB VK) VLEN.
Definition KW_BAND_V : kentry := KWr (SA VB VK) VLEN.
Definition kn_rest (ch : acs) : list kentry := List.filter (fun K => negb (is_band_fact K)) (kn ch).
Definition kn_view (ch : acs) : list kentry := KZ_BAND_V :: KW_BAND_V :: kn_rest ch.

Definition F6 : kentry := KRange (EVar 6) 0 2047.

Definition facts_classified (k : list kentry) : bool := forallb (fun K => fact_below k (2^47) K || stack_fact K)%bool k.
Lemma HS2_kimg : forall w ch, HSCLASS_S w ch -> kimg_inside (img_lo BJO6) (img_hi BJO6) (kn ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.
Lemma FACTS_CLASSIFIED : forall w ch, HSCLASS_S w ch -> facts_classified (kn_rest ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.
Lemma GAP_APART : forall w ch, HSCLASS_S w ch -> forallb (gap_apart (kn ch)) (kn_rest ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.
Lemma HS2_band_facts : forall w ch, HSCLASS_S w ch -> In KW_BAND (kn ch) /\ In F6 (kn ch).
Proof. intros w ch HCL. split; apply kn_mem_In; destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity. Qed.
