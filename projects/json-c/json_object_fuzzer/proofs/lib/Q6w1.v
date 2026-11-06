(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63 PrimString PrimStringAxioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNDM.
Import ListNotations.
Import AX2. Import AX2S. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition lit0 (e : expr) : bool := match e with ELit z => Z.eqb z 0 | _ => false end.

Definition lit_byte (z : Z) (i : Z) : Z := (bv_unsigned (wz z) / 2 ^ (8 * i)) mod 256.

Definition img_byte (a : Z) : option Z :=
match QWTC.seg_rom asegs (wz a) with Some b => Some (bv_unsigned b) | None => None end.

Definition kbyte (K : kentry) (a : Z) : option Z :=
match K with
| KWord sa w (ELit z) =>
if lit0 (a_base sa) && (a_off sa <=? a) && (a <? a_off sa + Z.of_nat w) && (Nat.leb w 8) then Some (lit_byte z (a - a_off sa)) else None
| KZero sa (ELit n) =>
if lit0 (a_base sa) && (a_off sa <=? a) && (a <? a_off sa + n) && (n <? 2^64) then Some 0 else None
| KFill sa (ELit n) c =>
if lit0 (a_base sa) && (a_off sa <=? a) && (a <? a_off sa + n) && (n <? 2^64) then Some (bv_unsigned (b8 c)) else None
| KImg lo hi => if (lo <=? a) && (a <? hi) then img_byte a else None
| _ => None
end.

Fixpoint kn_byte (kn : list kentry) (a : Z) : option Z :=
match kn with
| [] => None
| K :: kn' => match kbyte K a with Some z => Some z | None => kn_byte kn' a end
end.

Fixpoint kn_bytes (kn : list kentry) (a : Z) (bs : list byte) : bool :=
match bs with
| [] => true
| b :: bs' => match kn_byte kn a with Some z => Z.eqb z (bv_unsigned b) | None => false end && kn_bytes kn (a + 1) bs'
end.

Definition cell_wfb (c : cell) : bool := match c with CB n bs => Nat.eqb (length bs) n | _ => true end.
Fixpoint cells_wfb (cs : list cell) : bool := match cs with [] => true | c :: cs' => cell_wfb c && cells_wfb cs' end.
Lemma cells_wfb_wf : forall cs, cells_wfb cs = true -> cells_wf cs.
Proof.
induction cs as [|c cs IH]; intros H; cbn in H |- *; [exact I|]. apply andb_prop in H as [H1 H2].
split; [| exact (IH H2)]. destruct c; cbn in H1 |- *; try exact I. apply Nat.eqb_eq. exact H1.
Qed.

Definition kn_near (kn : list kentry) (a n : Z) : list kentry :=
List.filter (fun K => match K with
| KWord sa w (ELit _) => lit0 (a_base sa) && (a_off sa <? a + n) && (a <? a_off sa + Z.of_nat w)
| KZero sa (ELit l) | KFill sa (ELit l) _ => lit0 (a_base sa) && (a_off sa <? a + n) && (a <? a_off sa + l)
| KImg lo hi => (lo <? a + n) && (a <? hi)
| _ => false
end) kn.
Lemma kn_near_sub : forall kn a n K, In K (kn_near kn a n) -> In K kn.
Proof. intros kn a n K H. unfold kn_near in H. apply filter_In in H as [H _]. exact H. Qed.
Definition kn_cells (kn : list kentry) (a : Z) (cs : list cell) : bool :=
cells_wfb cs && (0 <=? a) && (a + Z.of_nat (cells_size cs) <=? 2^64) && kn_bytes (kn_near kn a (Z.of_nat (cells_size cs))) a (cells_bytes cs).

Lemma rdn_bytes_at : forall segs m n a bs,
0 <= a -> a + Z.of_nat n <= 2^64 ->
QWTC.rdn segs m (Z_to_bv 64 a) n = Some bs -> QCUT.bytes_at segs m a bs.
Proof.
intros segs m n. induction n as [|n IH]; intros a bs Ha Hn Hr.
- cbn in Hr. injection Hr as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- cbn [QWTC.rdn] in Hr.
change (match m (Z_to_bv 64 a) with Some b => Some b | None => QWTC.seg_rom segs (Z_to_bv 64 a) end) with (QCUT.mrd segs m (Z_to_bv 64 a)) in Hr.
destruct (QCUT.mrd segs m (Z_to_bv 64 a)) as [b|] eqn:Hb; [|discriminate].
destruct (QWTC.rdn segs m (Z_to_bv 64 a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
assert (Ha1 : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)) by exact (QCUT.wa_succ a).
rewrite Ha1 in Hrest. pose proof (IH (a + 1) rest ltac:(lia) ltac:(lia) Hrest) as (R1 & R2 & R3).
split; [lia|]. split; [cbn [length]; lia|]. intros [|i] Hi.
+ cbn. unfold QCUT.wa. rewrite Z.add_0_r. exact Hb.
+ cbn [nth_error]. unfold QCUT.wa in *. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply R3. cbn [length] in Hi. lia.
Qed.

Section Sound.
Variables (E : env) (m : word -> option byte) (kn : list kentry).
Hypothesis KO : know_ok asegs E m kn.

Lemma lit0_estart : forall sa, lit0 (a_base sa) = true -> estart E sa = a_off sa.
Proof.
intros [b off] H. cbn in H |- *. destruct b; try discriminate. apply Z.eqb_eq in H. subst. unfold estart. cbn.
rewrite Z_to_bv_unsigned. cbn. reflexivity.
Qed.

Lemma nth_error_Z_to_le_bytes : forall w z i, (i < w)%nat ->
nth_error (Z_to_le_bytes w z) i = Some (b8 (z / 2 ^ (8 * Z.of_nat i))).
Proof.
induction w as [|w IH]; intros z i Hi; [lia|].
cbn [Z_to_le_bytes]. destruct i as [|i].
- cbn [nth_error]. f_equal. f_equal. cbn [Z.of_nat Z.mul]. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

Lemma b8_mod : forall x, b8 (x mod 256) = b8 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_modulus 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_mod. lia. Qed.

Lemma kbyte_sound : forall K a z, In K kn -> kbyte K a = Some z -> 0 <= a < 2^64 -> mrd asegs m (wa a) = Some (b8 z).
Proof.
intros K a z Hin HK Ha. pose proof (proj1 (List.Forall_forall _ _) KO K Hin) as OK.
destruct K as [sa w v|sa n|sa n k|lo hi|e q|e lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; cbn [kbyte] in HK; try discriminate.
-  destruct v; try discriminate.
destruct (lit0 (a_base sa)) eqn:L; [| discriminate]. destruct (Z.leb_spec (a_off sa) a); [| discriminate].
destruct (Z.ltb_spec a (a_off sa + Z.of_nat w)); [| discriminate]. destruct (Nat.leb_spec w 8); [| discriminate]. cbn [andb] in HK.
injection HK as <-. cbn [kentry_ok] in OK. destruct OK as (W8 & FL & RD).
pose proof (flat_u E sa _ FL) as AU. rewrite (lit0_estart sa L) in AU.
replace (adenot E sa) with (wz (a_off sa)) in RD by (apply bv_eq; rewrite AU, Z_to_bv_unsigned; destruct FL as (F1 & F2 & _); rewrite (lit0_estart sa L) in F1, F2;
unfold bv_wrap; rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia); reflexivity).
destruct FL as (F1 & F2 & F3 & F4). rewrite (lit0_estart sa L) in F1, F2, F4.
pose proof (rdn_bytes_at asegs m w (a_off sa) _ ltac:(lia) ltac:(lia) RD) as (_ & _ & BA).
specialize (BA (Z.to_nat (a - a_off sa)) ltac:(unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; lia)).
replace (a_off sa + Z.of_nat (Z.to_nat (a - a_off sa))) with a in BA by lia. rewrite BA.
unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by lia. cbn [edenot]. unfold lit_byte. rewrite b8_mod.
replace (Z.of_nat (Z.to_nat (a - a_off sa))) with (a - a_off sa) by lia. reflexivity.
-  destruct n as [n| | | | | | |]; try discriminate.
destruct (lit0 (a_base sa)) eqn:L; [| discriminate]. destruct (Z.leb_spec (a_off sa) a); [| discriminate].
destruct (Z.ltb_spec a (a_off sa + n)); [| discriminate]. destruct (Z.ltb_spec n (2^64)); [| discriminate]. cbn [andb] in HK. injection HK as <-.
cbn [kentry_ok] in OK. destruct OK as (FL & ZB). unfold elenZ in ZB. cbn [edenot] in ZB. rewrite (lit0_estart sa L) in ZB.
rewrite Z_to_bv_unsigned in ZB. unfold bv_wrap in ZB. rewrite Z.mod_small in ZB by (change (bv_modulus 64) with (2^64); lia).
specialize (ZB (a - a_off sa) ltac:(lia)). replace (a_off sa + (a - a_off sa)) with a in ZB by lia.
unfold mrd, wa. rewrite ZB. reflexivity.
-  destruct (Z.leb_spec lo a); [| discriminate]. destruct (Z.ltb_spec a hi); [| discriminate]. cbn [andb] in HK.
unfold img_byte in HK. cbn [kentry_ok] in OK. destruct OK as (_ & _ & NB). specialize (NB a ltac:(lia)).
unfold mrd, wa. rewrite NB. change (QWTC.seg_rom asegs (wz a)) with (Qcrs.seg_rom asegs (wz a)) in HK.
destruct (Qcrs.seg_rom asegs (wz a)) as [b|]; [| discriminate]. injection HK as <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
-  destruct n as [n| | | | | | |]; try discriminate.
destruct (lit0 (a_base sa)) eqn:L; [| discriminate]. destruct (Z.leb_spec (a_off sa) a); [| discriminate].
destruct (Z.ltb_spec a (a_off sa + n)); [| discriminate]. destruct (Z.ltb_spec n (2^64)); [| discriminate]. cbn [andb] in HK. injection HK as <-.
cbn [kentry_ok] in OK. destruct OK as (FL & ZB). unfold elenZ in ZB. cbn [edenot] in ZB. rewrite (lit0_estart sa L) in ZB.
rewrite Z_to_bv_unsigned in ZB. unfold bv_wrap in ZB. rewrite Z.mod_small in ZB by (change (bv_modulus 64) with (2^64); lia).
specialize (ZB (a - a_off sa) ltac:(lia)). replace (a_off sa + (a - a_off sa)) with a in ZB by lia.
unfold mrd, wa. rewrite ZB. symmetry. f_equal. apply b8_mod.
Qed.

Lemma kn_byte_sound : forall kn' a z, (forall K, In K kn' -> In K kn) -> kn_byte kn' a = Some z -> 0 <= a < 2^64 -> mrd asegs m (wa a) = Some (b8 z).
Proof.
induction kn' as [|K kn' IH]; intros a z SUB H Ha; cbn [kn_byte] in H; [discriminate|].
destruct (kbyte K a) as [z'|] eqn:HK.
- injection H as <-. eapply kbyte_sound; [apply SUB; left; reflexivity| exact HK| exact Ha].
- eapply IH; [intros K' HK'; apply SUB; right; exact HK'| exact H| exact Ha].
Qed.

Lemma kn_bytes_sound_sub : forall kn' a bs, (forall K, In K kn' -> In K kn) -> kn_bytes kn' a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> bytes_at asegs m a bs.
Proof.
intros kn' a bs SUB H Ha Hb. split; [exact Ha|]. split; [exact Hb|].
revert a H Ha Hb. induction bs as [|b bs IH]; intros a H Ha Hb i Hi; cbn [length] in Hi; [lia|].
cbn [kn_bytes] in H. destruct (kn_byte kn' a) as [z|] eqn:KB; [| discriminate]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
destruct i as [|i].
- cbn [nth_error]. rewrite Z.add_0_r. rewrite (kn_byte_sound kn' a z SUB KB ltac:(cbn [length] in Hb; lia)).
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, H1. apply bv_wrap_small. apply bv_unsigned_in_range.
- cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
apply (IH (a + 1) H2 ltac:(lia) ltac:(cbn [length] in Hb; lia) i ltac:(lia)).
Qed.

Lemma kn_cells_sound : forall a cs, kn_cells kn a cs = true -> ro_cells asegs m a cs.
Proof.
intros a cs H. unfold kn_cells in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3. apply cells_wfb_wf in H1.
split; [exact H1|]. apply (kn_bytes_sound_sub (kn_near kn a (Z.of_nat (cells_size cs)))); [apply kn_near_sub| exact H4| exact H2| rewrite cells_bytes_length by exact H1; exact H3].
Qed.
End Sound.

Definition img_w (a : Z) : bool :=
match find_segment asegs a 1 with
| Some seg => seg_writable seg && seg_readable seg && match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with Some _ => true | None => false end
| None => false
end.

Fixpoint img_wn (a : Z) (n : nat) : bool :=
match n with O => true | S n' => img_w a && img_wn (a + 1) n' end.

Lemma img_w_wview : forall m a, img_w a = true -> 0 <= a < 2^64 -> wview asegs m (wa a) <> None.
Proof.
intros m a H Ha. unfold img_w in H. unfold wview, wa. destruct (m (wz a)) as [b|]; [discriminate|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia).
destruct (find_segment asegs a 1) as [seg|]; [| discriminate]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 HR]. rewrite H1.
destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))); [discriminate| discriminate].
Qed.

Lemma img_wn_wr_at : forall m a n, img_wn a n = true -> 0 <= a -> a + Z.of_nat n <= 2^64 -> wr_at asegs m a (Z.of_nat n).
Proof.
intros m a n H Ha Hn. split; [exact Ha|]. split; [exact Hn|].
revert a H Ha Hn. induction n as [|n IH]; intros a H Ha Hn i Hi; [lia|].
cbn [img_wn] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec i 0) as [->|NZ].
- rewrite Z.add_0_r. apply img_w_wview; [exact H1| lia].
- replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) H2 ltac:(lia) ltac:(lia) (i - 1) ltac:(lia)).
Qed.

Definition kn_rw_cells (kn : list kentry) (a : Z) (cs : list cell) : bool := kn_cells kn a cs && img_wn a (cells_size cs).

Lemma kn_rw_cells_sound : forall E m kn a cs, know_ok asegs E m kn -> kn_rw_cells kn a cs = true -> rw_cells asegs m a cs.
Proof.
intros E m kn a cs KO H. unfold kn_rw_cells in H. apply andb_prop in H as [H1 H2].
pose proof (kn_cells_sound E m kn KO a cs H1) as RO. split; [exact RO|].
unfold kn_cells in H1. apply andb_prop in H1 as [H1 H4]. apply andb_prop in H1 as [H1 H3]. apply andb_prop in H1 as [_ H0].
apply Z.leb_le in H0. apply Z.leb_le in H3.
apply img_wn_wr_at; [exact H2| exact H0| exact H3].
Qed.

Lemma img_wn_junk : forall E m kn lo hi a n, know_ok asegs E m kn -> In (KImg lo hi) kn \/ True ->
img_wn a n = true -> 0x10000 <= a -> a + Z.of_nat n <= 0x647000 ->
exists bs, rw_cells asegs m a [CB n bs].
Proof.
intros E m kn lo hi a n KO _ H Ha Hn.
assert (RD : forall i, 0 <= i < Z.of_nat n -> exists b, mrd asegs m (wa (a + i)) = Some b).
{ intros i Hi. pose proof (img_w_wview m (a + i)) as W.
assert (Wi : img_w (a + i) = true).
{ clear W. revert a H Ha Hn i Hi. induction n as [|n IH]; intros a H Ha Hn i Hi; [lia|]. cbn [img_wn] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec i 0) as [->|NZ]; [rewrite Z.add_0_r; exact H1|]. replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) H2); lia. }
specialize (W Wi ltac:(lia)). unfold mrd. unfold wview in W. destruct (m (wa (a + i))) as [b|]; [exists b; reflexivity|].
unfold img_w in Wi. unfold wa in *. rewrite Z_to_bv_unsigned in W. unfold bv_wrap in W.
rewrite Z.mod_small in W by (change (bv_modulus 64) with (2^64); lia).
unfold Qcrs.seg_rom, memory_read. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia).
change (Z.of_N 1) with 1.
destruct (find_segment asegs (a + i) 1) as [seg|]; [| discriminate]. apply andb_prop in Wi as [Wi W2]. apply andb_prop in Wi as [W1 WR]. rewrite WR.
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg)))) as [b|] eqn:SB; [| discriminate].
destruct (segment_read_bytes (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg)) + 1) 0) as [rest|]; [exists b; reflexivity|].
cbn [segment_read_bytes] in *. exists b. reflexivity. }
destruct (stk_carve asegs m a (a + Z.of_nat n) n) as (_ & bs & RC).
{ split; [lia|]. split; [lia|]. intros x Hx. split.
- pose proof (img_w_wview m x) as W. apply W; [| lia].
clear RD W. revert a H Ha Hn Hx. induction n as [|n IH]; intros a H Ha Hn Hx; [lia|]. cbn [img_wn] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec x a) as [->|NZ]; [exact H1|]. apply (IH (a + 1) H2); lia.
- destruct (RD (x - a) ltac:(lia)) as [b Hb]. replace (a + (x - a)) with x in Hb by lia. exists b. exact Hb. }
{ lia. }
replace (a + Z.of_nat n - Z.of_nat n) with a in RC by lia. exists bs. exact RC.
Qed.

Fixpoint zden (E : env) (e : expr) : option Z :=
match e with
| ELit z => Some z
| EVar n => Some (bv_unsigned (ev E n))
| EAlu Instr.ALU_ADD a b => match zden E a, zden E b with Some x, Some y => Some (x + y) | _, _ => None end
| EMd Instr.M_MUL a b => match zden E a, zden E b with Some x, Some y => Some (x * y) | _, _ => None end
| _ => None
end.

Lemma zden_sound : forall E e z, zden E e = Some z -> edenot E e = wz z.
Proof.
intros E e. induction e as [z0|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros z H; cbn [zden] in H; try discriminate.
- injection H as <-. reflexivity.
- injection H as <-. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
- destruct op; try discriminate. destruct (zden E a) as [x|] eqn:Ha; [| discriminate]. destruct (zden E b) as [y|] eqn:Hb; [| discriminate].
injection H as <-. cbn [edenot]. rewrite (IHa x eq_refl), (IHb y eq_refl). apply bv_eq. cbn [alu64 alu].
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. pose proof (bv_modulus_pos 64). rewrite <- Z.add_mod by lia. reflexivity.
- destruct op; try discriminate. destruct (zden E a) as [x|] eqn:Ha; [| discriminate]. destruct (zden E b) as [y|] eqn:Hb; [| discriminate].
injection H as <-. cbn [edenot]. rewrite (IHa x eq_refl), (IHb y eq_refl). apply bv_eq. cbn [mul_div].
rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. pose proof (bv_modulus_pos 64). rewrite <- Z.mul_mod by lia. reflexivity.
Qed.

Definition wcell (w : nat) (z : Z) : list cell :=
match w with 1%nat => [C1 (b8 z)] | 2%nat => [C2 (wz z)] | 4%nat => [C4 (wz z)] | 8%nat => [C8 (wz z)] | _ => [] end.

Lemma kn_word : forall E m kn tb off w v zb zv,
know_ok asegs E m kn -> kn_has (KWord (SA tb off) w v) kn = true ->
zden E tb = Some zb -> 0 <= zb < 2^64 -> zden E v = Some zv -> (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%nat ->
ro_cells asegs m (zb + off) (wcell w zv).
Proof.
intros E m kn tb off w v zb zv KO HK Hb Hzb Hv Hw.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as (W8 & FL & RD).
pose proof (zden_sound E tb zb Hb) as EB. pose proof (zden_sound E v zv Hv) as EV.
assert (ES : estart E (SA tb off) = zb + off) by (unfold estart; cbn [a_base a_off]; rewrite EB, Z_to_bv_unsigned; unfold bv_wrap; rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia); reflexivity).
pose proof (flat_u E _ _ FL) as AU. rewrite ES in AU. destruct FL as (F1 & F2 & F3 & F4). rewrite ES in F1, F2, F4.
replace (adenot E (SA tb off)) with (wz (zb + off)) in RD by (apply bv_eq; rewrite AU, Z_to_bv_unsigned; unfold bv_wrap; rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia); reflexivity).
pose proof (rdn_bytes_at asegs m w (zb + off) _ ltac:(lia) ltac:(lia) RD) as BA. rewrite EV in BA. unfold word_to_le_bytes in BA. rewrite Z_to_bv_unsigned in BA.
destruct Hw as [W|[W|[W|W]]]; subst w; (split; [cbn; tauto|]); cbn [cells_bytes cbytes wcell app le8 le4 le2 word_to_le_bytes];
rewrite ?app_nil_r, ?Z_to_bv_unsigned; try exact BA.
replace [b8 zv] with (Z_to_le_bytes 1 (bv_wrap 64 zv)); [exact BA|]. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. apply Z.mod_mod_divide. exists (2^56). reflexivity.
Qed.

Section SymFacts.
Variables (E : env) (m : word -> option byte) (kn : list kentry).
Hypothesis KO : know_ok asegs E m kn.

Lemma estart_sym : forall tb off zb, zden E tb = Some zb -> 0 <= zb < 2^64 -> estart E (SA tb off) = zb + off.
Proof.
intros tb off zb Hz Hzb. unfold estart. cbn [a_base a_off]. rewrite (zden_sound E tb zb Hz), Z_to_bv_unsigned.
unfold bv_wrap. rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia). reflexivity.
Qed.

Lemma elenZ_lit : forall n, 0 <= n < 2^64 -> elenZ E (ELit n) = n.
Proof.
intros n Hn. unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia). reflexivity.
Qed.

Lemma kn_zero_at : forall tb off n zb,
kn_has (KZero (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall i, 0 <= i < n -> m (wa (zb + off + i)) = Some (b8 0).
Proof.
intros tb off n zb HK Hz Hzb Hn i Hi.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as [FL ZB].
rewrite (estart_sym tb off zb Hz Hzb) in ZB. rewrite (elenZ_lit n Hn) in ZB. exact (ZB i Hi).
Qed.

Lemma kn_wr_at : forall tb off n zb,
kn_has (KWr (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a k, zb + off <= a -> 0 <= k -> a + k <= zb + off + n -> wr_at asegs m a k.
Proof.
intros tb off n zb HK Hz Hzb Hn a k H1 H2 H3.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as [FL ST].
unfold flat in FL. rewrite (estart_sym tb off zb Hz Hzb) in ST, FL. rewrite (elenZ_lit n Hn) in ST, FL. destruct FL as (F1 & F2 & F3 & F4).
split; [lia|]. split; [lia|]. intros i Hi.
specialize (ST (a - (zb + off) + i) 1%nat ltac:(lia) ltac:(cbn; lia)).
pose proof (store_ok_wview asegs m _ 1%nat 0%nat ST ltac:(lia)) as W.
unfold wa in W |- *. rewrite Z_to_bv_unsigned in W. unfold bv_wrap in W. rewrite Z.mod_small in W by (change (bv_modulus 64) with (2^64); lia).
replace (zb + off + (a - (zb + off) + i) + Z.of_nat 0) with (a + i) in W by lia. exact W.
Qed.

Lemma kn_wr_some : forall tb off n zb,
kn_has (KWr (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a, zb + off <= a < zb + off + n -> (a + 1 <= 0x10000 \/ 0x647000 <= a) -> exists b, m (wa a) = Some b.
Proof.
intros tb off n zb HK Hz Hzb Hn a Ha Hh.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as [FL _].
unfold flat in FL. rewrite (estart_sym tb off zb Hz Hzb) in FL. rewrite (elenZ_lit n Hn) in FL. destruct FL as (F1 & F2 & F3 & F4).
destruct (kn_wr_at tb off n zb HK Hz Hzb Hn a 1 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & W).
specialize (W 0 ltac:(lia)). rewrite Z.add_0_r in W. rewrite a_wview_overlay in W by (rewrite wa_unsigned by lia; lia).
destruct (m (wa a)) as [b|]; [exists b; reflexivity| exfalso; exact (W eq_refl)].
Qed.

Lemma kn_zero_some : forall tb off n zb,
kn_has (KZero (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a, zb + off <= a < zb + off + n -> exists b, m (wa a) = Some b.
Proof.
intros tb off n zb HK Hz Hzb Hn a Ha. exists (b8 0).
replace a with (zb + off + (a - (zb + off))) by lia. apply (kn_zero_at tb off n zb HK Hz Hzb Hn). lia.
Qed.

Definition zbyteb (b : byte) : bool := Z.eqb (bv_unsigned b) 0.
Definition zcell (c : cell) : bool :=
match c with
| C8 v | C4 v | C2 v => Z.eqb (bv_unsigned v) 0
| C1 b => zbyteb b
| CB n bs => Nat.eqb (length bs) n && forallb zbyteb bs
end.
Fixpoint zcells (cs : list cell) : bool := match cs with [] => true | c :: cs' => zcell c && zcells cs' end.

Lemma zbyteb_eq : forall b, zbyteb b = true -> b = b8 0.
Proof. intros b H. unfold zbyteb in H. apply Z.eqb_eq in H. apply bv_eq. rewrite H, Z_to_bv_unsigned. reflexivity. Qed.

Lemma Z_to_le_bytes_0 : forall w, Z_to_le_bytes w 0 = repeat (b8 0) w.
Proof. induction w as [|w IH]; cbn [Z_to_le_bytes repeat]; [reflexivity|]. rewrite Z.shiftr_0_l, IH. reflexivity. Qed.

Lemma forallb_repeat : forall {A} (f : A -> bool) x n, f x = true -> forallb f (repeat x n) = true.
Proof. intros A f x n H. induction n as [|n IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Lemma zcell_bytes : forall c, zcell c = true -> cell_wf c /\ forallb zbyteb (cbytes c) = true.
Proof.
intros c H. destruct c as [v|v|v|b|n bs]; cbn [zcell cell_wf cbytes] in *.
1-3: apply Z.eqb_eq in H; split; [exact I|]; unfold le8, word_to_le_bytes, le4, le2; rewrite H, Z_to_le_bytes_0; apply forallb_repeat; reflexivity.
- split; [exact I|]. cbn. rewrite H. reflexivity.
- apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. split; [exact H1| exact H2].
Qed.

Lemma zcells_bytes : forall cs, zcells cs = true -> cells_wf cs /\ forallb zbyteb (cells_bytes cs) = true.
Proof.
induction cs as [|c cs IH]; intros H; cbn [zcells cells_wf cells_bytes] in *; [split; [exact I| reflexivity]|].
apply andb_prop in H as [H1 H2]. destruct (zcell_bytes c H1) as [W1 B1]. destruct (IH H2) as [W2 B2].
split; [split; assumption|]. rewrite forallb_app, B1, B2. reflexivity.
Qed.

Lemma kn_zero_bytes_at : forall tb off n zb,
kn_has (KZero (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a bs, forallb zbyteb bs = true -> zb + off <= a -> a + Z.of_nat (length bs) <= zb + off + n ->
bytes_at asegs m a bs.
Proof.
intros tb off n zb HK Hz Hzb Hn a bs Hbs H1 H2.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as [FL _].
unfold flat in FL. rewrite (estart_sym tb off zb Hz Hzb) in FL. rewrite (elenZ_lit n Hn) in FL. destruct FL as (F1 & F2 & F3 & F4).
split; [lia|]. split; [lia|]. intros i Hi.
rewrite forallb_forall in Hbs. destruct (nth_error bs i) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
pose proof (Hbs b (nth_error_In _ _ NB)) as Zb. apply zbyteb_eq in Zb. subst b.
unfold mrd. replace (a + Z.of_nat i) with (zb + off + (a + Z.of_nat i - (zb + off))) by lia.
rewrite (kn_zero_at tb off n zb HK Hz Hzb Hn) by lia. reflexivity.
Qed.

Lemma kn_zero_rw : forall tb off n zb,
kn_has (KZero (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a cs, zcells cs = true -> (a + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x647000 <= a) -> zb + off <= a -> a + Z.of_nat (cells_size cs) <= zb + off + n ->
rw_cells asegs m a cs.
Proof.
intros tb off n zb HK Hz Hzb Hn a cs Hcs Hh H1 H2.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as [FL _].
unfold flat in FL. rewrite (estart_sym tb off zb Hz Hzb) in FL. rewrite (elenZ_lit n Hn) in FL. destruct FL as (F1 & F2 & F3 & F4).
destruct (zcells_bytes cs Hcs) as [WF ZB]. pose proof (cells_bytes_length cs WF) as LEN.
split; [split; [exact WF|]|].
- apply (kn_zero_bytes_at tb off n zb HK Hz Hzb Hn); [exact ZB| lia| rewrite LEN; lia].
- split; [lia|]. split; [lia|]. intros i Hi. rewrite a_wview_overlay by (rewrite wa_unsigned by lia; lia).
replace (a + i) with (zb + off + (a + i - (zb + off))) by lia. rewrite (kn_zero_at tb off n zb HK Hz Hzb Hn) by lia. discriminate.
Qed.

Lemma kn_zero_ro : forall tb off n zb,
kn_has (KZero (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a cs, zcells cs = true -> zb + off <= a -> a + Z.of_nat (cells_size cs) <= zb + off + n ->
ro_cells asegs m a cs.
Proof.
intros tb off n zb HK Hz Hzb Hn a cs Hcs H1 H2.
destruct (zcells_bytes cs Hcs) as [WF ZB]. pose proof (cells_bytes_length cs WF) as LEN.
split; [exact WF|]. apply (kn_zero_bytes_at tb off n zb HK Hz Hzb Hn); [exact ZB| lia| rewrite LEN; lia].
Qed.

Lemma u32s_zero : forall k, forallb zbyteb (u32s (repeat (wz 0) k)) = true.
Proof.
induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s map concat]. change (le4 (wz 0) ++ u32s (repeat (wz 0) k)) with (le4 (wz 0) ++ u32s (repeat (wz 0) k)).
rewrite forallb_app, IH. reflexivity.
Qed.

Lemma kn_zero_u32arr : forall tb off n zb,
kn_has (KZero (SA tb off) (ELit n)) kn = true -> zden E tb = Some zb -> 0 <= zb < 2^64 -> 0 <= n < 2^64 ->
forall a k, (a + 4 * Z.of_nat k <= 0x10000 \/ 0x647000 <= a) -> zb + off <= a -> a + 4 * Z.of_nat k <= zb + off + n ->
u32arr asegs m a (repeat (wz 0) k).
Proof.
intros tb off n zb HK Hz Hzb Hn a k Hh H1 H2.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as [FL _].
unfold flat in FL. rewrite (estart_sym tb off zb Hz Hzb) in FL. rewrite (elenZ_lit n Hn) in FL. destruct FL as (F1 & F2 & F3 & F4).
split.
- apply (kn_zero_bytes_at tb off n zb HK Hz Hzb Hn); [apply u32s_zero| lia| rewrite u32s_length, repeat_length; lia].
- rewrite repeat_length. split; [lia|]. split; [lia|]. intros i Hi. rewrite a_wview_overlay by (rewrite wa_unsigned by lia; lia).
replace (a + i) with (zb + off + (a + i - (zb + off))) by lia. rewrite (kn_zero_at tb off n zb HK Hz Hzb Hn) by lia. discriminate.
Qed.

Lemma kn_range : forall e lo hi z, kn_has (KRange e lo hi) kn = true -> zden E e = Some z -> 0 <= z < 2^64 -> lo <= z <= hi.
Proof.
intros e lo hi z HK Hz Hzb.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK.
rewrite (zden_sound E e z Hz), Z_to_bv_unsigned in OK. unfold bv_wrap in OK. rewrite Z.mod_small in OK by (change (bv_modulus 64) with (2^64); lia). exact OK.
Qed.

Lemma kn_range_small : forall e lo hi z, kn_has (KRange e lo hi) kn = true -> zden E e = Some z ->
- 2^63 <= z < 2^63 -> hi < 2^63 -> lo <= z <= hi.
Proof.
intros e lo hi z HK Hz Hzb Hhi.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK.
rewrite (zden_sound E e z Hz), Z_to_bv_unsigned in OK. unfold bv_wrap in OK. change (bv_modulus 64) with (2^64) in OK.
destruct (Z.lt_ge_cases z 0) as [NEG|POS].
- replace (z mod 2^64) with ((z + 1 * 2^64) mod 2^64) in OK by (rewrite Z.mod_add by lia; reflexivity).
rewrite Z.mod_small in OK by lia. lia.
- rewrite Z.mod_small in OK by lia. exact OK.
Qed.

Lemma kn_range_var : forall v lo hi, kn_has (KRange (EVar v) lo hi) kn = true -> lo <= bv_unsigned (ev E v) <= hi.
Proof.
intros v lo hi HK. apply (kn_range (EVar v) lo hi _ HK); [reflexivity|].
pose proof (bv_unsigned_in_range _ (ev E v)) as R. change (bv_modulus 64) with (2^64) in R. lia.
Qed.

End SymFacts.

Definition seg3 : PrimString.string := AsanUbsan.AsanUbsan_seg_bytes_003.
Definition SEG3_LO : Z := 0xea000.
Definition SEG3_HI : Z := 0x647000.

Definition img_zero (a n : Z) : bool :=
(SEG3_LO <=? a) && (0 <=? n) && (a + n <=? SEG3_HI) &&
match PrimString.compare (PrimString.sub seg3 (Uint63.of_Z (2 * (a - SEG3_LO))) (Uint63.of_Z (2 * n)))
(PrimString.make (Uint63.of_Z (2 * n)) 48%uint63) with Eq => true | _ => false end.

Lemma seg3_len : Uint63.to_Z (PrimString.length seg3) = 11247616.
Proof. vm_compute. reflexivity. Qed.

Lemma land_48 : Uint63.land 48 255 = 48%uint63.
Proof. reflexivity. Qed.
Lemma hex_nybble_48 : hex_nybble 48%uint63 = 0%N.
Proof. reflexivity. Qed.
Lemma max_length_val : Uint63.to_Z PrimString.max_length = 16777211.
Proof. reflexivity. Qed.

Lemma u63_cmp_eq : forall x y : int, Uint63.compare x y = Eq <-> x = y.
Proof.
intros x y. rewrite Uint63.compare_spec, Z.compare_eq_iff. split; [apply Uint63.to_Z_inj| intros ->; reflexivity].
Qed.

Lemma of_Z_small : forall z, 0 <= z < 2^63 -> Uint63.to_Z (Uint63.of_Z z) = z.
Proof. intros z Hz. rewrite Uint63.of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma img_zero_chars : forall a n, img_zero a n = true ->
SEG3_LO <= a /\ 0 <= n /\ a + n <= SEG3_HI /\
forall j, (j < 2 * Z.to_nat n)%nat -> nth (2 * Z.to_nat (a - SEG3_LO) + j) (to_list seg3) 0%uint63 = 48%uint63.
Proof.
intros a n H. unfold img_zero in H.
apply andb_prop in H as [H HC]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. unfold SEG3_LO, SEG3_HI in *.
split; [lia|]. split; [lia|]. split; [lia|].
destruct (PrimString.compare _ _) eqn:CMP; try discriminate. clear HC.
rewrite PrimStringAxioms.compare_spec in CMP. apply (proj1 (list_compare_refl Uint63.compare u63_cmp_eq _ _)) in CMP.
rewrite PrimStringAxioms.sub_spec, PrimStringAxioms.make_spec, land_48 in CMP.
rewrite !of_Z_small in CMP by lia. pose proof max_length_val as ML.
rewrite Nat.min_l in CMP by lia.
intros j Hj.
assert (E : nth j (firstn (Z.to_nat (2 * n)) (skipn (Z.to_nat (2 * (a - 958464))) (to_list seg3))) 0%uint63 = 48%uint63).
{ rewrite CMP. apply nth_repeat_lt. lia. }
rewrite nth_firstn in E. destruct (Nat.ltb_spec j (Z.to_nat (2 * n))); [| lia].
rewrite nth_skipn in E. replace (2 * Z.to_nat (a - 958464) + j)%nat with (Z.to_nat (2 * (a - 958464)) + j)%nat by lia. exact E.
Qed.

Lemma a_find_segment_3 : forall z n, 1 <= n -> 0xea000 <= z -> z + n <= 0x647000 ->
find_segment asegs z n = Some AsanUbsan.AsanUbsan_segment_003.
Proof.
intros z n Hn H1 H2. unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x2e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x3e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0xa6000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xe4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x6000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xea000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55d000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2e000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x3e000 z); destruct (Z.leb_spec0 (z + n) (0x3e000 + 0xa6000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0xe4000 z); destruct (Z.leb_spec0 (z + n) (0xe4000 + 0x6000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0xea000 z); destruct (Z.leb_spec0 (z + n) (0xea000 + 0x55d000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma hex_byte_at_zero : forall j : Z, 0 <= j < 5623808 ->
nth (2 * Z.to_nat j) (to_list seg3) 0%uint63 = 48%uint63 ->
nth (2 * Z.to_nat j + 1) (to_list seg3) 0%uint63 = 48%uint63 ->
hex_byte_at seg3 (Z.to_N j) = Some (b8 0).
Proof.
intros j Hj C0 C1. unfold hex_byte_at.
assert (L1 : Uint63.ltb (Uint63.of_Z (Z.of_N (2 * Z.to_N j + 1))) (PrimString.length seg3) = true).
{ apply Uint63.ltb_spec. rewrite seg3_len, of_Z_small by lia. lia. }
rewrite L1. cbn [orb].
rewrite !PrimStringAxioms.get_spec. rewrite !of_Z_small by lia.
replace (Z.to_nat (Z.of_N (2 * Z.to_N j))) with (2 * Z.to_nat j)%nat by lia.
replace (Z.to_nat (Z.of_N (2 * Z.to_N j + 1))) with (2 * Z.to_nat j + 1)%nat by lia.
rewrite C0, C1, hex_nybble_48. reflexivity.
Qed.

Lemma img_zero_byte : forall a n, img_zero a n = true ->
forall i, 0 <= i < n -> segment_byte_at [seg3] (Z.to_N (a + i - Z.of_N 958464%N)) = Some (b8 0).
Proof.
intros a n H i Hi. destruct (img_zero_chars a n H) as (H1 & H2 & H3 & CH). unfold SEG3_LO, SEG3_HI in *.
cbn [segment_byte_at].
replace (Z.to_N (Uint63.to_Z (PrimString.length seg3) / 2)) with 5623808%N by (rewrite seg3_len; reflexivity).
replace (Z.to_N (a + i - Z.of_N 958464) <? 5623808)%N with true by (symmetry; apply N.ltb_lt; lia).
replace (Z.to_N (a + i - Z.of_N 958464)) with (Z.to_N (a + i - 958464)) by lia.
apply (hex_byte_at_zero (a + i - 958464)); [lia| |].
- replace (2 * Z.to_nat (a + i - 958464))%nat with (2 * Z.to_nat (a - 958464) + 2 * Z.to_nat i)%nat by lia. apply CH. lia.
- replace (2 * Z.to_nat (a + i - 958464) + 1)%nat with (2 * Z.to_nat (a - 958464) + (2 * Z.to_nat i + 1))%nat by lia. apply CH. lia.
Qed.

Lemma img_zero_sound : forall a n, img_zero a n = true ->
forall i, 0 <= i < n -> Qcrs.seg_rom asegs (wa (a + i)) = Some (b8 0).
Proof.
intros a n H i Hi. destruct (img_zero_chars a n H) as (H1 & H2 & H3 & _). unfold SEG3_LO, SEG3_HI in *.
unfold Qcrs.seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
rewrite (a_find_segment_3 (a + i) 1) by lia.
change (seg_readable AsanUbsan.AsanUbsan_segment_003) with true. cbn match.
change (seg_base AsanUbsan.AsanUbsan_segment_003) with 0xea000%N.
change (seg_bytes AsanUbsan.AsanUbsan_segment_003) with [seg3].
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite (img_zero_byte a n H i Hi). reflexivity.
Qed.

Lemma img_zero_wview : forall m a n, img_zero a n = true ->
forall i, 0 <= i < n -> wview asegs m (wa (a + i)) <> None.
Proof.
intros m a n H i Hi. destruct (img_zero_chars a n H) as (H1 & H2 & H3 & _). unfold SEG3_LO, SEG3_HI in *.
unfold wview. destruct (m (wa (a + i))); [discriminate|]. rewrite wa_unsigned by lia.
rewrite (a_find_segment_3 (a + i) 1) by lia.
change (seg_writable AsanUbsan.AsanUbsan_segment_003) with true. cbn match.
change (seg_base AsanUbsan.AsanUbsan_segment_003) with 0xea000%N.
change (seg_bytes AsanUbsan.AsanUbsan_segment_003) with [seg3].
rewrite (img_zero_byte a n H i Hi). discriminate.
Qed.

Section ImgZero.
Variables (E : env) (m : word -> option byte) (kn : list kentry).
Hypothesis KO : know_ok asegs E m kn.

Lemma kimg_none : forall lo hi, kn_has (KImg lo hi) kn = true -> forall a, lo <= a < hi -> m (wa a) = None.
Proof.
intros lo hi HK a Ha. pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK.
destruct OK as (_ & _ & NB). exact (NB a Ha).
Qed.

Lemma kimg_zero_bytes : forall lo hi a n, kn_has (KImg lo hi) kn = true -> lo <= a -> a + n <= hi -> img_zero a n = true ->
wr_at asegs m a n /\ forall i, 0 <= i < n -> bytes_at asegs m (a + i) [b8 0].
Proof.
intros lo hi a n HK Hlo Hhi HZ. destruct (img_zero_chars a n HZ) as (H1 & H2 & H3 & _). unfold SEG3_LO, SEG3_HI in *.
split.
- split; [lia|]. split; [lia|]. intros i Hi. apply (img_zero_wview m a n HZ i Hi).
- intros i Hi. split; [lia|]. split; [cbn [length]; lia|]. intros k Hk. cbn [length] in Hk.
destruct k as [|k]; [| lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
unfold mrd. rewrite (kimg_none lo hi HK) by lia. exact (img_zero_sound a n HZ i Hi).
Qed.

End ImgZero.
