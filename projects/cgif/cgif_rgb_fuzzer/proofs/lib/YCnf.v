(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCjo YCly YClz YCea YP14.

Definition m_region_kept_ck (segs : list Segment) (E : env) (mem mem' : word -> option byte) (r : YQ0b.region) : Prop :=
(forall c, In c (r_chunks r) -> forall i, 0 <= i < c_len c ->
mbyte segs mem' (base_val E (r_base r) + c_off c + i) = mbyte segs mem (base_val E (r_base r) + c_off c + i)) /\
(forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
writable_at segs mem a -> writable_at segs mem' a).
Lemma m_region_kept_ck_of_kept : forall segs E mem mem' r,
forallb (chunk_inside r) (r_chunks r) = true -> region_kept segs E mem mem' r -> m_region_kept_ck segs E mem mem' r.
Proof.
intros segs E mem mem' r Hin [K1 K2]. split; [|exact K2].
intros c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold chunk_inside in Hci.
apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply K1. lia.
Qed.
Lemma m_region_ok_kept_ck : forall segs E mem mem' r,
region_ok segs E mem r -> m_region_kept_ck segs E mem mem' r -> region_ok segs E mem' r.
Proof.
intros segs E mem mem' r (Hlo & Hhi & Hw & Hcs) [K1 K2]. unfold region_ok. cbv zeta.
split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros o Ho. apply K2; [lia|]. apply Hw. exact Ho.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
rewrite (K1 c Hc i Hi). exact Hb2.
Qed.
Lemma m_mem_ok_kept_ck : forall segs E mem mem' rs,
mem_ok segs E mem rs -> Forall (m_region_kept_ck segs E mem mem') rs -> mem_ok segs E mem' rs.
Proof.
intros segs E mem mem' rs (Hwf & Hok & Hpd) Hk. split; [exact Hwf|]. split; [|exact Hpd].
apply Forall_forall. intros r Hr.
exact (m_region_ok_kept_ck segs E mem mem' r (proj1 (Forall_forall _ _) Hok r Hr) (proj1 (Forall_forall _ _) Hk r Hr)).
Qed.
Lemma m_st_ok_after_stretchF_ck : forall (fx fx' : YK11.FPState) segs k E ss ms regs' mem' rs pc (clob : list (bv 5)),
@st_ok segs fx E ss ms ->
ss_resv ss = None ->
ss_atoms_lt k ss = true ->
regions_wf rs = true -> mem_atoms_lt k rs = true ->
submem rs (ss_mem ss) ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
(forall r, reg_in r clob = false -> getr regs' r = getr (ms_regs ms) r) ->
Forall (m_region_kept_ck segs E (ms_mem ms) mem') rs ->
@st_ok segs fx' (havoc E k (map (getr regs') clob)) (ss_after_stretch ss rs k clob pc)
(@mkst fx' regs' (Z_to_bv 64 pc) mem' (seg_rom segs)).
Proof.
intros fx fx' segs k E ss ms regs' mem' rs pc clob HS Hrv Hat Hwf Hmat Hsub Hnd Hnz Hsame Hk.
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape. rewrite Hshape in HS.
pose proof (st_ok_splice_havoc segs k E ss (ms_regs ms) regs' (Z_to_bv 64 (ss_pc ss)) pc
(ms_mem ms) mem' rs [] clob HS Hat) as H.
cbn [map app] in H.
assert (H' : @st_ok segs fx (havoc E k (map (getr regs') clob)) (ss_after_stretch ss rs k clob pc) (@mkst fx regs' (Z_to_bv 64 pc) mem' (seg_rom segs))).
{ apply H.
- exact Hnd.
- exact Hnz.
- reflexivity.
- exact Hmat.
- exact Hsame.
- constructor.
- apply (m_mem_ok_kept_ck segs E (ms_mem ms) mem' rs); [|exact Hk].
eapply mem_ok_sub; [exact Hsub | exact Hwf | exact (st_ok_mem_ok segs E ss _ HS)]. }
destruct H' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok.
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
Lemma m_region_kept_av : forall {fx : YK11.FPState} E H H' (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview trbsegs H' m2 a = aview trbsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H' m2 a) ->
region_kept trbsegs E (mrestrict H m) (mrestrict H' m2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros fx E H H' m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable trbsegs). apply Hp. exact Ha.
Qed.
Lemma m_chunks_off_cell : forall cs elo ehi,
forallb (fun c => (c_off c + c_len c <=? elo) || (ehi <=? c_off c)) cs = true ->
forall c, In c cs -> forall i, 0 <= i < c_len c -> ~ (elo <= c_off c + i < ehi).
Proof.
intros cs elo ehi Hf c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hf c Hc) as Hb. cbv beta in Hb.
apply orb_prop in Hb as [Hb | Hb]; [apply Z.leb_le in Hb | apply Z.leb_le in Hb]; lia.
Qed.
Lemma m_region_kept_ck_av : forall {fx : YK11.FPState} E H H' (m m2 : word -> option byte) n b lo hi wlo whi cs elo ehi,
bv_unsigned (ew E n) = b ->
forallb (chunk_inside (YQ0b.mkRegion (Some n) lo hi wlo whi cs)) cs = true ->
forallb (fun c => (c_off c + c_len c <=? elo) || (ehi <=? c_off c)) cs = true ->
(forall a, b + lo <= a < b + hi -> ~ (b + elo <= a < b + ehi) -> aview trbsegs H' m2 a = aview trbsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H' m2 a) ->
m_region_kept_ck trbsegs E (mrestrict H m) (mrestrict H' m2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros fx E H H' m m2 n b lo hi wlo whi cs elo ehi Hn Hin Hoff Hav Hp.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite Hn.
- intros c Hc i Hi. apply (mbyte_of_aview trbsegs).
pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold chunk_inside in Hci. cbn [YQ0b.r_lo YQ0b.r_hi] in Hci.
apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (m_chunks_off_cell cs elo ehi Hoff c Hc i Hi) as Hne.
apply Hav; lia.
- intros a Ha _. apply (apresent_writable trbsegs). apply Hp. exact Ha.
Qed.
Lemma m_same_of_preserved : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
forall r, reg_in r CLOB = false -> getr regs' r = getr regs r.
Proof. intros regs regs' HP. apply regs_preserved_frame. exact HP. Qed.
Ltac m_jafter_stretchF HS fx2 k regs2 mem2 clob pc idxs Hsame HS2 :=
lazymatch type of HS with
| @st_ok ?segs ?fx1 ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (m_st_ok_after_stretchF_ck fx1 fx2 segs k E ss ms regs2 mem2 rs pc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hsame) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob pc) in
change (ss_after_stretch ss rs k clob pc) with ss2 in HS2
end.
Ltac m_reseatF HS HJ2 fx2 regs2 clob pc keep AG Hsame kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
m_jafter_stretchF HS fx2 K regs2 (mrestrict (w_H W2) mem2) clob pc keep Hsame HS2 end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- (@restrict_mkst_fx fx2) in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.
