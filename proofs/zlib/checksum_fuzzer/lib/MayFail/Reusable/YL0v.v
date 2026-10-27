(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YL0v.v, with its module paths, addresses and numbers changed; 9 of its 714 lines of code are new or changed and 9 lines of the source are left out. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO00.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN35.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition wl_site_common (k : nat) (ss : sstate) : option (nat * nat * Z * Z * Z) :=
if negb (ss_pc ss =? WL_ECALL1) then None else
match sr_get (ss_regs ss) 17, lit_sv (sr_get (ss_regs ss) 10), sr_get (ss_regs ss) 2, sr_get (ss_regs ss) 9, ss_resv ss with
| SLit 66, Some fd, SOff b K, SLit F, None =>
if negb ((fd =? 1) || (fd =? 2)) then None else
if negb (zcanon F =? F) then None else
if negb (ss_atoms_lt k ss) then None else
if negb (sv_eqb (sr_get (ss_regs ss) 12) (SAlu ALU_ADD (sr_get (ss_regs ss) 18) (SLit 0)) || sv_eqb (sr_get (ss_regs ss) 12) (sr_get (ss_regs ss) 18)) then None else
if negb (sv_eqb (sr_get (ss_regs ss) 19) (sr_get (ss_regs ss) 11)) then None else
match find_wregion (ss_mem ss) b (K + 8) (K + 40), atom_lookup (f_atoms (ss_facts ss)) b,
lit_buf src0segs (ss_mem ss) (SLit (F + 120)) 4 with
| Some i, Some f, Some fdz =>
if negb ((0 <=? af_lo f + K) && (af_hi f + K + 40 <=? 2 ^ 47) && (0 <=? F) && (F + 124 <=? af_lo f + K + 8)
&& zlist_eqb fdz [fd; 0; 0; 0]) then None
else Some (i, b, K, F, fd)
| _, _, _ => None
end
| _, _, _, _, _ => None
end.
Definition wl_site2 (k : nat) (ss : sstate) : option (nat * nat * Z * Z * Z * (sv * sv * sv * sv)) :=
match wl_site_common k ss with
| Some (i, b, K, F, fd) =>
if negb (sv_eqb (sr_get (ss_regs ss) 19) (SOff b (K + 8))) then None else
match iov_read2 (ss_mem ss) (Some b) (K + 8) with
| Some (vb0, vl0, vb1, vl1) => Some (i, b, K, F, fd, (vb0, vl0, vb1, vl1))
| None => None
end
| None => None
end.
Definition wl_site1 (k : nat) (ss : sstate) : option (nat * nat * Z * Z * Z * (sv * sv)) :=
match wl_site_common k ss with
| Some (i, b, K, F, fd) =>
if negb (sv_eqb (sr_get (ss_regs ss) 19) (SOff b (K + 24))) then None else
match iov_read1 (ss_mem ss) (Some b) (K + 24) with
| Some (vb1, vl1) => Some (i, b, K, F, fd, (vb1, vl1))
| None => None
end
| None => None
end.
Lemma denot_add0 : forall E v, sv_denot E (SAlu ALU_ADD v (SLit 0)) = sv_denot E v.
Proof.
intros E v. rewrite (denot_lit_U E (SAlu ALU_ADD v (SLit 0))), (denot_lit_U E v). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (U_range E v). apply zcanon_id. lia.
Qed.
Lemma wl_site_common_sound : forall E ss ms k i b K F fd,
st_ok_ecall src0segs E ss ms ->
wl_site_common k ss = Some (i, b, K, F, fd) ->
ss_pc ss = WL_ECALL1 /\ sr_get (ss_regs ss) 17 = SLit 66 /\ sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 fd
/\ (fd = 1 \/ fd = 2) /\ sr_get (ss_regs ss) 2 = SOff b K /\ U E (sr_get (ss_regs ss) 9) = F /\ ss_resv ss = None
/\ ss_atoms_lt k ss = true /\ sv_denot E (sr_get (ss_regs ss) 18) = sv_denot E (sr_get (ss_regs ss) 12) /\ sr_get (ss_regs ss) 11 = sr_get (ss_regs ss) 19
/\ (exists r, nth_error (ss_mem ss) i = Some r /\ r_base r = Some b /\ r_lo r <= K + 8 /\ K + 40 <= r_hi r /\ r_wlo r <= K + 8 /\ K + 40 <= r_whi r)
/\ 0 <= bv_unsigned (ew E b) + K /\ bv_unsigned (ew E b) + K + 40 <= 2 ^ 47 /\ 0 <= F /\ F + 124 <= 2 ^ 64
/\ F + 124 <= bv_unsigned (ew E b) + K + 8
/\ rdn src0segs (ms_mem ms) (Z_to_bv 64 (F + 120)) 4 = Some (map (Z_to_bv 8) [fd; 0; 0; 0]).
Proof.
intros E ss ms k i b K F fd HS H. unfold wl_site_common in H.
destruct (ss_pc ss =? WL_ECALL1) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc. cbn [negb] in H.
destruct (sr_get (ss_regs ss) 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct no as [|p17|]; try discriminate. do 7 (destruct p17 as [p17|p17|]; try discriminate).
destruct (lit_sv (sr_get (ss_regs ss) 10)) as [fd'|] eqn:H10; [|discriminate].
destruct (sr_get (ss_regs ss) 2) as [|b' K'| | | | | | | | |] eqn:H2; try discriminate.
destruct (sr_get (ss_regs ss) 9) as [F'| | | | | | | | | |] eqn:H9; try discriminate.
destruct (ss_resv ss) eqn:Hrv; try discriminate.
destruct (negb ((fd' =? 1) || (fd' =? 2))) eqn:Hfd; [discriminate|].
assert (Hfd12 : fd' = 1 \/ fd' = 2).
{ apply negb_false_iff in Hfd. apply orb_prop in Hfd as [Hf|Hf]; apply Z.eqb_eq in Hf; lia. }
destruct (negb (zcanon F' =? F')) eqn:HFc; [discriminate|]. apply negb_false_iff in HFc. apply Z.eqb_eq in HFc.
destruct (ss_atoms_lt k ss) eqn:Hat; [|discriminate]. cbn [negb] in H.
destruct (sv_eqb (sr_get (ss_regs ss) 12) (SAlu ALU_ADD (sr_get (ss_regs ss) 18) (SLit 0)) || sv_eqb (sr_get (ss_regs ss) 12) (sr_get (ss_regs ss) 18)) eqn:H1218; [|discriminate]. cbn [negb] in H.
destruct (sv_eqb (sr_get (ss_regs ss) 19) (sr_get (ss_regs ss) 11)) eqn:H1911; [|discriminate]. cbn [negb] in H.
assert (D18 : sv_denot E (sr_get (ss_regs ss) 18) = sv_denot E (sr_get (ss_regs ss) 12)).
{ apply orb_prop in H1218 as [H1218|H1218]; apply sv_eqb_eq in H1218; rewrite H1218; [|reflexivity].
symmetry. apply denot_add0. }
apply sv_eqb_eq in H1911.
destruct (find_wregion (ss_mem ss) b' (K' + 8) (K' + 40)) as [i'|] eqn:Hwr; [|discriminate].
destruct (atom_lookup (f_atoms (ss_facts ss)) b') as [f|] eqn:Hf; [|discriminate].
destruct (lit_buf src0segs (ss_mem ss) (SLit (F' + 120)) 4) as [fdz|] eqn:Hfdz; [|discriminate].
destruct ((0 <=? af_lo f + K') && (af_hi f + K' + 40 <=? 2 ^ 47) && (0 <=? F') && (F' + 124 <=? af_lo f + K' + 8)
&& zlist_eqb fdz [fd'; 0; 0; 0]) eqn:Hbnd; [|discriminate]. cbn [negb] in H.
injection H as <- <- <- <- <-.
apply andb_prop in Hbnd as [Hbnd Hfdz4]. apply andb_prop in Hbnd as [Hbnd B4]. apply andb_prop in Hbnd as [Hbnd B3].
apply andb_prop in Hbnd as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply zlist_eqb_eq in Hfdz4. subst fdz.
destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & Hmem & HG).
pose proof (lit_sv_sound E _ _ H10) as [D10 R10].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hbf & _).
pose proof (lit_buf_sound src0segs E (ms_mem ms) _ _ _ _ Hmem Hfdz) as Hfdrd. cbn [sv_denot] in Hfdrd.
destruct (find_wregion_sound _ _ _ _ _ Hwr) as (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi).
unfold M64 in *.
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
- symmetry. exact H1911.
- exists r. repeat split; assumption.
Qed.
Lemma fd_facts : forall fd, fd = 1 \/ fd = 2 ->
fd32 (Z_to_bv 64 fd) = Z_to_bv 64 fd /\ bv_unsigned (Z_to_bv 64 fd) < 2 ^ 31 /\
bytes_le_to_Z (map (Z_to_bv 8) [fd; 0; 0; 0]) = bv_unsigned (Z_to_bv 64 fd).
Proof. intros fd [-> | ->]; (split; [reflexivity|]); (split; [vm_compute; reflexivity|]); vm_compute; reflexivity. Qed.
Theorem wl2_sound : forall E ss ms model ch k i b K F fd vb0 vl0 vb1 vl1 bs0 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms ->
wl_site2 k ss = Some (i, b, K, F, fd, (vb0, vl0, vb1, vl1)) ->
fdchan (Z_to_bv 64 fd) ch model ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 2 ->
U E (sr_get (ss_regs ss) 22) = U E vl0 + U E vl1 ->
rdn src0segs (ms_mem ms) (sv_denot E vb0) (word_to_nat (sv_denot E vl0)) = Some bs0 ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl0 + U E vl1 <= 2 ^ 25 ->
U E vb0 + U E vl0 <= 2 ^ 47 ->
(U E vb0 + U E vl0 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb0) ->
U E vb1 + U E vl1 <= 2 ^ 47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros E ss ms model ch k i b K F fd vb0 vl0 vb1 vl1 bs0 bs1 T Hh Hlz HS Hck Hch H12 H22 Hb0 Hb1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hk.
unfold wl_site2 in Hck.
destruct (wl_site_common k ss) as [[[[[i' b'] K'] F'] fd']|] eqn:Hc; [|discriminate].
destruct (sv_eqb (sr_get (ss_regs ss) 19) (SOff b' (K' + 8))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (iov_read2 (ss_mem ss) (Some b') (K' + 8)) as [[[[x0 y0] x1] y1]|] eqn:Hiov; [|discriminate].
injection Hck as -> -> -> -> -> -> -> -> ->.
destruct (wl_site_common_sound E ss ms k i b K F fd HS Hc)
as (Hpc & H17 & D10 & Hfd12 & H2 & H9 & Hrv & Hat & H18 & H11 & (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi) & B1 & B2 & B3 & B4 & B5 & Hfdrd).
destruct (fd_facts fd Hfd12) as (H32 & Hfd31 & HfdB).
eapply (rz_sym_stdio_writev2 E ss ms model (Z_to_bv 64 fd) ch i b K F r vb0 vl0 vb1 vl1 bs0 bs1 _ k T Hh Hlz HS Hrv Hpc
H17 D10 Hch H32 Hfd31 H12 (eq_trans H18 H12) H2 H19 ltac:(rewrite H11; exact H19) H22 H9
Hi Hrb Hrlo Hrhi Hwlo Hwhi Hiov Hb0 Hb1 Hlen Hnw0 Hd0 Hnw1 Hd1 Hfdrd HfdB B3 B4 (or_introl B5) B1 B2 Hat Hk).
Qed.
Theorem wl1_sound : forall E ss ms model ch k i b K F fd vb1 vl1 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms ->
wl_site1 k ss = Some (i, b, K, F, fd, (vb1, vl1)) ->
fdchan (Z_to_bv 64 fd) ch model ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 ->
U E (sr_get (ss_regs ss) 22) = U E vl1 ->
rdn src0segs (ms_mem ms) (sv_denot E vb1) (word_to_nat (sv_denot E vl1)) = Some bs1 ->
1 <= U E vl1 <= 2 ^ 25 ->
U E vb1 + U E vl1 <= 2 ^ 47 ->
(U E vb1 + U E vl1 <= bv_unsigned (ew E b) + K + 8 \/ bv_unsigned (ew E b) + K + 40 <= U E vb1) ->
(forall ms' ws, st_ok src0segs (havoc E k ws) (wl_after ss i K k) ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) (t_emit (map (WriteEv ch) bs1) T).
Proof.
intros E ss ms model ch k i b K F fd vb1 vl1 bs1 T Hh Hlz HS Hck Hch H12 H22 Hb1 Hlen Hnw1 Hd1 Hk.
unfold wl_site1 in Hck.
destruct (wl_site_common k ss) as [[[[[i' b'] K'] F'] fd']|] eqn:Hc; [|discriminate].
destruct (sv_eqb (sr_get (ss_regs ss) 19) (SOff b' (K' + 24))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (iov_read1 (ss_mem ss) (Some b') (K' + 24)) as [[x1 y1]|] eqn:Hiov; [|discriminate].
injection Hck as -> -> -> -> -> -> ->.
destruct (wl_site_common_sound E ss ms k i b K F fd HS Hc)
as (Hpc & H17 & D10 & Hfd12 & H2 & H9 & Hrv & Hat & H18 & H11 & (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi) & B1 & B2 & B3 & B4 & B5 & Hfdrd).
destruct (fd_facts fd Hfd12) as (H32 & Hfd31 & HfdB).
eapply (rz_sym_stdio_writev1 E ss ms model (Z_to_bv 64 fd) ch i b K F r vb1 vl1 bs1 _ k T Hh Hlz HS Hrv Hpc
H17 D10 Hch H32 Hfd31 H12 (eq_trans H18 H12) H2 H19 ltac:(rewrite H11; exact H19) H22 H9
Hi Hrb Hrlo Hrhi Hwlo Hwhi Hiov Hb1 Hlen Hnw1 Hd1 Hfdrd HfdB B3 B4 (or_introl B5) B1 B2 Hat Hk).
Qed.
Lemma st_ok_ecall_facts : forall E ss ms, st_ok_ecall src0segs E ss ms -> facts_ok E (ss_facts ss).
Proof. intros E ss ms HS. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG). exact HG. Qed.
End e.
Ltac wl_transport E ss ms ms' HGf HF :=
cbn [ms_mem mkst pend_at] in HF;
repeat match goal with
| HW : win_ok _ ?E0 ?m ?lo ?hi |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (win_ok_frame src0segs E (ss_facts ss) (ss_mem ss) m (ms_mem ms') lo hi HGf
ltac:(vm_compute; reflexivity) HF ltac:(vm_compute; reflexivity)) in HW
| fail 1 ]
end
end;
repeat match goal with
| HK : runs_ok ?E0 ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_ok_frame2 E (ss_facts ss) (ss_mem ss) m (ms_mem ms') l HGf
ltac:(vm_compute; reflexivity) HF ltac:(vm_compute; reflexivity)) in HK
| fail 1 ]
end
end;
repeat match goal with
| HR : runs_at ?spv ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_at_frame E (ss_facts ss) (ss_mem ss) m (ms_mem ms') spv l HGf
ltac:(vm_compute; reflexivity) HF ltac:(cbn; lia)) in HR
| fail 1 ]
end
end;
check_transported ms'.
Ltac wl_writev2 HS Hch k :=
lazymatch type of HS with st_ok_ecall _ ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
let r := eval vm_compute in (wl_site2 k ss) in
lazymatch r with
| Some (?i, ?b, ?K, ?F, ?fd, (?vb0, ?vl0, ?vb1, ?vl1)) =>
let Hck := fresh "Hck" in
assert (Hck : wl_site2 k ss = Some (i, b, K, F, fd, (vb0, vl0, vb1, vl1))) by (vm_compute; reflexivity);
eapply (wl2_sound E ss ms model _ k i b K F fd vb0 vl0 vb1 vl1 _ _ _ ltac:(assumption) ltac:(assumption) HS Hck Hch);
clear Hck;
[ eval_sr_get | eval_sr_get | | | | | | |
| let ms' := fresh "ms" in let ws := fresh "ws" in let HS' := fresh "HS'" in let HF := fresh "HF" in
let HGf := fresh "HGf" in
intros ms' ws HS' HF;
pose proof (st_ok_ecall_facts E ss ms HS) as HGf;
wl_transport E ss ms ms' HGf HF;
env_transport (havoc E k ws) (env_agree_havoc E k ws);
clear HF HGf HS; try clear ms; rename HS' into HS; sym_norm HS ]
| _ => fail "wl_writev2: site check failed"
end
end end.
Ltac wl_writev1 HS Hch k :=
lazymatch type of HS with st_ok_ecall _ ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
let r := eval vm_compute in (wl_site1 k ss) in
lazymatch r with
| Some (?i, ?b, ?K, ?F, ?fd, (?vb1, ?vl1)) =>
let Hck := fresh "Hck" in
assert (Hck : wl_site1 k ss = Some (i, b, K, F, fd, (vb1, vl1))) by (vm_compute; reflexivity);
eapply (wl1_sound E ss ms model _ k i b K F fd vb1 vl1 _ _ ltac:(assumption) ltac:(assumption) HS Hck Hch);
clear Hck;
[ eval_sr_get | eval_sr_get | | | |
| let ms' := fresh "ms" in let ws := fresh "ws" in let HS' := fresh "HS'" in let HF := fresh "HF" in
let HGf := fresh "HGf" in
intros ms' ws HS' HF;
pose proof (st_ok_ecall_facts E ss ms HS) as HGf;
wl_transport E ss ms ms' HGf HF;
env_transport (havoc E k ws) (env_agree_havoc E k ws);
clear HF HGf HS; try clear ms; rename HS' into HS; sym_norm HS ]
| _ => fail "wl_writev1: site check failed"
end
end end.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma align8_le : forall q z, q < z -> z mod 8 = 0 -> q - q mod 8 + 8 <= z.
Proof.
intros q z Hlt Hz.
pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
pose proof (Z.div_mod z 8 ltac:(lia)).
remember (q / 8) as a. remember (q mod 8) as r. remember (z / 8) as c. nia.
Qed.
Lemma t_exit_nil : forall c fs, t_exit c fs [].
Proof. intros. left. exact I. Qed.
Definition wr2 (bs : list byte) : list event := map (WriteEv (Z_to_bv 64 2)) bs.
Lemma t_emit_congr : forall l T T', t_eq T T' -> t_eq (t_emit l T) (t_emit l T').
Proof.
intros l T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
Qed.
Lemma shape_1 : forall A B C X,
t_eq (t_emit (wr2 ((A ++ B ++ C) ++ [])) X) (t_emit (wr2 (A ++ B ++ C)) X).
Proof. intros. rewrite app_nil_r. apply t_eq_refl. Qed.
Lemma shape_2 : forall A B C X, X [] ->
t_eq (t_emit (wr2 ((A ++ B) ++ C)) (t_emit (wr2 []) X)) (t_emit (wr2 (A ++ B ++ C)) X).
Proof.
intros A B C X HX. rewrite <- app_assoc. apply t_emit_congr. apply t_emit_nil_eq. exact HX.
Qed.
Lemma shape_3 : forall A B C X,
t_eq (t_emit (wr2 (A ++ B)) (t_emit (wr2 (C ++ [])) X)) (t_emit (wr2 (A ++ B ++ C)) X).
Proof.
intros A B C X. rewrite app_nil_r. unfold wr2.
eapply t_eq_trans; [apply YK0k.t_emit_app|]. rewrite <- map_app, <- app_assoc. apply t_eq_refl.
Qed.
Lemma str_reads : forall m a s,
YP03.bytes_at m a (s ++ [NUL]) ->
forall j, (j <= length s)%nat ->
rdn src0segs m (Z_to_bv 64 (a + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Proof.
intros m a s HB j Hj. apply (proj2 (rdn_mbytes src0segs m 1 _ [_])).
split; [reflexivity|]. intros i Hi. destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
rewrite (bytes_at_mbyte src0segs m _ _ j HB) by (rewrite length_app; cbn; lia).
apply nth_error_nth'. rewrite length_app; cbn; lia.
Qed.
Lemma bsb_over_read : forall sp argv envp rnd m p L,
valid_sp sp ->
YP03.bytes_at m (z_strs (bv_unsigned sp) argv envp) (stack_tail argv envp rnd) ->
z_strs (bv_unsigned sp) argv envp <= p + L -> p + L < z_rand (bv_unsigned sp) argv envp ->
forall a, p + L < a < p + L - (p + L) mod 8 + 8 -> rdn src0segs m (Z_to_bv 64 a) 1 <> None.
Proof.
intros sp argv envp rnd m p L Hsp HB Hlo Hhi a Ha.
pose proof (stack_tail_end sp argv envp rnd) as Hlen.
assert (Hal : p + L - (p + L) mod 8 + 8 <= z_rand (bv_unsigned sp) argv envp).
{ apply align8_le; [lia|]. unfold z_rand.
rewrite <- Zplus_mod_idemp_r, (rand_off_mod8 argv envp), Z.add_0_r.
pose proof (mod8_of_mod16 (bv_unsigned sp) 0 (proj2 (proj2 Hsp))) as Hm8. rewrite Z.add_0_r in Hm8. exact Hm8. }
rewrite (proj2 (rdn_mbytes src0segs m 1 a [match nth_error (stack_tail argv envp rnd)
(Z.to_nat (a - z_strs (bv_unsigned sp) argv envp)) with Some b => b | None => Z_to_bv 8 0 end]));
[discriminate|].
split; [reflexivity|]. intros i Hi. destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
unfold mbyte. replace a with (z_strs (bv_unsigned sp) argv envp + Z.of_nat (Z.to_nat (a - z_strs (bv_unsigned sp) argv envp))) at 1 by lia.
rewrite (HB (Z.to_nat (a - z_strs (bv_unsigned sp) argv envp))) by lia.
destruct (nth_error _ _) eqn:Hn; [reflexivity|]. exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma img_rdn1 : forall E m rs r lo len a,
mem_ok src0segs E m rs -> In r rs -> r_base r = None ->
In (mkChunk lo (CImg len)) (r_chunks r) -> lo <= a < lo + len ->
rdn src0segs m (Z_to_bv 64 a) 1 = rdn src0segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Proof.
intros E m rs r lo len a HM Hin Hb Hc Ha.
pose proof (region_ok_chunk src0segs E m r _ (mem_ok_region src0segs E m rs r HM Hin) Hc) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck.
destruct (Hck (a - lo) ltac:(unfold c_len; cbn; lia)) as (b & Hb1 & Hb2).
cbn [c_off c_val cbyte] in Hb1, Hb2. unfold img_byte in Hb1.
replace (0 + lo + (a - lo)) with a in Hb1, Hb2 by lia.
cbn [rdn]. unfold mbyte in Hb2.
destruct (m (Z_to_bv 64 a)) as [b'|]; [|reflexivity].
injection Hb2 as ->. rewrite Hb1. reflexivity.
Qed.
Definition ROM_LO : Z := src0_D_const_HIGHS_0x8080808080808080.
Definition ROM_HI : Z := src0_D_const_ONES_0x0101010101010100 + 8.
Definition rom_chunk (c : YP09.chunk) : option (Z * Z) :=
match c_val c with
| CImg len => if (c_off c <=? ROM_LO) && (ROM_HI <=? c_off c + len) then Some (c_off c, len) else None
| _ => None
end.
Fixpoint find_rom_chunk (cs : list YP09.chunk) : option (Z * Z) :=
match cs with
| [] => None
| c :: cs' => match rom_chunk c with Some p => Some p | None => find_rom_chunk cs' end
end.
Fixpoint has_rodata (rs : smem) : bool :=
match rs with
| [] => false
| r :: rs' =>
match r_base r, find_rom_chunk (r_chunks r) with
| None, Some _ => true
| _, _ => has_rodata rs'
end
end.
Lemma find_rom_chunk_sound : forall cs lo len, find_rom_chunk cs = Some (lo, len) ->
In (mkChunk lo (CImg len)) cs /\ lo <= ROM_LO /\ ROM_HI <= lo + len.
Proof.
induction cs as [|c cs IH]; cbn; intros lo len H; [discriminate|].
destruct (rom_chunk c) as [[lo' len']|] eqn:Hc.
- injection H as -> ->. unfold rom_chunk in Hc. destruct c as [co cv]; cbn in Hc.
destruct cv as [| |n|]; try discriminate.
destruct ((co <=? ROM_LO) && (ROM_HI <=? co + n)) eqn:Hb; [|discriminate]. injection Hc as -> ->.
apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
split; [left; reflexivity|]. lia.
- destruct (IH lo len H) as (A & B). split; [right; exact A | exact B].
Qed.
Lemma has_rodata_sound : forall rs, has_rodata rs = true ->
exists r lo len, In r rs /\ r_base r = None /\ In (mkChunk lo (CImg len)) (r_chunks r) /\ lo <= ROM_LO /\ ROM_HI <= lo + len.
Proof.
induction rs as [|r rs IH]; cbn; intros H; [discriminate|].
assert (IH' : has_rodata rs = true -> exists r0 lo len, (r = r0 \/ In r0 rs) /\ r_base r0 = None /\ In (mkChunk lo (CImg len)) (r_chunks r0) /\ lo <= ROM_LO /\ ROM_HI <= lo + len).
{ intros H'. destruct (IH H') as (r0 & lo & len & A & B & C & D). exists r0, lo, len. auto. }
destruct (r_base r) eqn:Hb; [apply IH'; exact H|].
destruct (find_rom_chunk (r_chunks r)) as [[lo len]|] eqn:Hf; [|apply IH'; exact H].
destruct (find_rom_chunk_sound _ _ _ Hf) as (A & B).
exists r, lo, len. split; [left; reflexivity|]. auto.
Qed.
Lemma rom_reads : forall E ss ms, st_ok src0segs E ss ms -> has_rodata (ss_mem ss) = true ->
forall a, src0_D_const_HIGHS_0x8080808080808080 <= a < (src0_D_const_ONES_0x0101010101010100 + 8) ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 a) 1 = rdn src0segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Proof.
intros E ss ms HS Hh a Ha. destruct (has_rodata_sound _ Hh) as (r & lo & len & Hin & Hb & Hc & Hlo & Hhi).
unfold ROM_LO, ROM_HI in Hlo, Hhi.
eapply (img_rdn1 E (ms_mem ms) (ss_mem ss) r); [apply (st_ok_mem_ok src0segs E ss ms HS)| exact Hin| exact Hb| exact Hc| lia].
Qed.
Lemma rodata_input_src1 : forall E,
chunk_bytes src0segs E 65536 (CImg 8192) (66428 - 65536) 7 = strB " INPUT" ++ nl.
Proof. intros E. vm_compute. reflexivity. Qed.
Lemma rodata_nl_src1 : forall E,
chunk_bytes src0segs E 65536 (CImg 8192) (66799 - 65536) 1 = nl.
Proof. intros E. vm_compute. reflexivity. Qed.
Lemma rodata_nl2_src1 : forall E,
chunk_bytes src0segs E 65536 (CImg 8192) (66822 - 65536) 1 = nl.
Proof. intros E. vm_compute. reflexivity. Qed.
Definition upd_memchr (n k : nat) : list (reg * sv) :=
[(10%bv:reg, SAlu ALU_ADD (SOff n 0) (SOff k 0)); (11%bv:reg, SLit 0); (12%bv:reg, SLit 0);
(13%bv:reg, SAlu ALU_SUB (SLit 0x7fffffff) (SOff k 0))].
Definition junk_memchr : list reg := [5; 14; 15; 16; 17]%bv.
Definition junk_memcpy : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
End g.
Ltac rdn_buf HS HK :=
lazymatch goal with |- rdn ?segs ?m _ _ = Some (?U ++ ?REST) =>
let Hb := fresh "Hb" in let Hrun := fresh "Hrun" in
cbn [sv_denot]; evalE; rewrite word_to_nat_lit by lia;
pose proof (runs_ok_single_inv _ _ _ _ _ _ HK) as (_ & _ & Hrun);
replace (Z.to_nat _) with (length (U ++ REST))
by (rewrite !length_app;
repeat match goal with |- context [length (strB ?str)] =>
let v := eval compute in (length (strB str)) in change (length (strB str)) with v end;
change (length nl) with 1%nat; lia);
apply (mbytes_at_rdn segs); apply mbytes_at_app;
[ let n := eval compute in (length U) in
pose_lits HS 0%nat (-560) n Hb; revert Hb; evalE; intros Hb;
lazymatch type of Hb with mbytes_at _ _ _ ?zs =>
replace U with zs by (apply byte_list_eq; vm_compute; reflexivity) end;
exact Hb
| let v := eval compute in (Z.of_nat (length U)) in change (Z.of_nat (length U)) with v;
lazymatch type of Hrun with YP03.bytes_at _ ?a _ => replace (_ + v) with a by lia end;
apply bytes_at_mbytes; exact Hrun ]
end.
Ltac fpf_memchr HS HR si bi n k s :=
let H10 := fresh "H10" in let H11 := fresh "H11" in let H12 := fresh "H12" in let Hra := fresh "Hra" in
let HBs := fresh "HBs" in let HBb := fresh "HBb" in let Hp := fresh "Hp" in
let Hover := fresh "Hover" in let Hrom := fresh "Hrom" in
reg_of HS (10%bv:reg) H10; reg_of HS (11%bv:reg) H11; reg_of HS (12%bv:reg) H12; reg_of HS (1%bv:reg) Hra;
lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E ?ss _ =>
pose proof (runs_at_nth _ (ms_mem ms) _ si _ _ HR eq_refl) as HBs;
pose proof (runs_at_nth _ (ms_mem ms) _ bi _ _ HR eq_refl) as HBb;
cbn [nth_error runs_main app] in HBs, HBb;
lazymatch type of HBs with YP03.bytes_at _ ?a _ =>
assert (Hp : bv_unsigned (ew E n) = a) by (evalE; lia);
assert (Hover : forall x,
bv_unsigned (ew E n) + Z.of_nat (length s) < x <
bv_unsigned (ew E n) + Z.of_nat (length s) - (bv_unsigned (ew E n) + Z.of_nat (length s)) mod 8 + 8 ->
rdn src0segs (ms_mem ms) (Z_to_bv 64 x) 1 <> None)
by (rewrite Hp; refine (bsb_over_read _ _ _ _ (ms_mem ms) a (Z.of_nat (length s)) _ HBb _ _); [assumption| lia| lia]);
pose proof (rom_reads _ _ _ HS ltac:(vm_compute; reflexivity)) as Hrom;
let Hnul := lazymatch goal with H : ~ In _ s |- _ => H end in
let Hrd := constr:(fun j (Hj : (j <= length s)%nat) =>
eq_trans (f_equal (fun z => rdn src0segs (ms_mem ms) (Z_to_bv 64 (z + Z.of_nat j)) 1) Hp)
(str_reads (ms_mem ms) a s HBs j Hj)) in
let regs1 := fresh "regs" in let Hms := fresh "Hms" in
let R10 := fresh "R10" in let R11 := fresh "R11" in let R12 := fresh "R12" in let R13 := fresh "R13" in
let Rfr := fresh "Rfr" in
destruct (src0_memchr s (ew E n) (Z_to_bv 64 0x7fffffff) (ms_mem ms) (seg_rom src0segs) (ms_regs ms) Hnul
ltac:(rewrite Hp; lia)
ltac:(rewrite unsigned_lit_small by lia; lia)
Hrd Hover Hrom H10 H11 H12)
as (regs1 & Hms & R10 & R11 & R12 & R13 & Rfr);
rewrite Hra in Hms; change (v_jalr (Z_to_bv 64 119256) 0) with (Z_to_bv 64 0x1d1d8) in Hms;
clear Hover Hrom H10 H11 H12 Hra HBs HBb;
sym_new_atom HS k (Z_to_bv 64 (Z.of_nat (length s)));
let k1 := eval cbv in (k + 1)%nat in
sym_splice_havoc HS Hms k1 (upd_memchr n k) junk_memchr;
[ sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot]; rewrite ?ew_ewset_same, ?ew_ewset_other by lia;
rewrite ?Z.add_0_r;
[ rewrite R10, zalu64_sound; apply Z_to_bv64_eq_mod; unfold zalu64, zcanon, M64; cbn [zalu_raw];
rewrite (unsigned_lit_small (Z.of_nat _)) by lia; pose proof (u64_range (ew E n));
rewrite !(Z.mod_small _ (2^64)) by lia; reflexivity
| exact R11
| exact R12
| rewrite R13, zalu64_sound; apply Z_to_bv64_eq_mod; unfold zalu64, zcanon, M64; cbn [zalu_raw];
rewrite !unsigned_lit_small by lia; rewrite !(Z.mod_small _ (2^64)) by lia; reflexivity ]
| lazymatch goal with H : st_ok _ _ _ _ |- _ => exact (st_ok_mem_ok src0segs _ _ _ H) end
| clear R10 R11 R12 R13 Rfr Hp;
sym_add_fact HS k (mkAF 0 131071 0); [atom_fact_lit|] ]
end end end.
Ltac fpf_lbu_nul HS HR si n k s :=
let H11 := fresh "H11" in let HBs := fresh "HBs" in let Hstep := fresh "Hstep" in
lazymatch type of HS with st_ok _ ?E ?ss ?ms => pose proof (st_ok_reg src0segs E ss ms 11 HS) as H11 end;
eval_sr_get_in H11;
rewrite denot_lit_U, U_add_off_atom in H11 by (evalE; unfold M64; lia);
rewrite !Z.add_0_r in H11;
lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E _ _ =>
pose proof (runs_at_nth _ (ms_mem ms) _ si _ _ HR eq_refl) as HBs; cbn [nth_error runs_main app] in HBs;
assert (Hstep : RiscvSemantics.step src0segs (mkst (ms_regs ms) (Z_to_bv 64 0x18ac8) (ms_mem ms) (seg_rom src0segs))
= MachineOk (mkst (regupd (ms_regs ms) 12 (Z_to_bv 64 0)) (Z_to_bv 64 0x18acc) (ms_mem ms) (seg_rom src0segs)));
[ rewrite (step_lbu src0segs _ (Z_to_bv 64 0x18ac8) _ (seg_rom src0segs) (Z_to_bv 32 0x5c603) 12 11 0 (Z_to_bv 8 0));
[ reflexivity
| apply fetch_lit; vm_compute; reflexivity
| vm_compute; reflexivity
| vm_refl_bv
| rewrite H11;
match goal with |- context [bv_signed ?i] => let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end;
rewrite v_addi_0;
lazymatch type of HBs with YP03.bytes_at _ ?a _ =>
replace (bv_unsigned (ew E n) + bv_unsigned (ew E k)) with (a + Z.of_nat (length s)) by (evalE; lia) end;
rewrite (str_reads _ _ s HBs (length s) ltac:(lia)), nth_middle; reflexivity ]
| sym_step_manual HS Hstep [(12%bv:reg, SLit 0)];
[ intros r Hr; apply getr_other; intros ->; vm_compute in Hr; discriminate Hr
| repeat constructor; cbn [fst snd sv_denot]; apply getr_same; intros Heq; discriminate Heq
| clear H11 HBs ] ]
end end.
Ltac fpf_split_window HS woff :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r :: ?rs =>
let H := fresh "HS'" in
destruct (st_ok_split3_head src0segs E ss ms r rs woff (-480) (SOff 0 woff) (SOff 0 (-480)) HS eq_refl
ltac:(cbn [r_lo]; lia) ltac:(lia) ltac:(cbn [r_hi]; lia) eq_refl eq_refl
ltac:(cbn [sv_denot base_val r_base]; rewrite unsigned_lit_small; [reflexivity| evalE; lia])
ltac:(cbn [sv_denot base_val r_base]; rewrite unsigned_lit_small; [reflexivity| evalE; lia]))
as [H HW]; clear HS; rename H into HS; sym_norm HS
end end.
Ltac fpf_mem_window HS :=
lazymatch type of HS with st_ok _ ?E ?ss _ =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
eapply (st_ok_mem_wbytes_inside src0segs E ss _ _ _ [r0] r1 rest);
[ exact HS | reflexivity | reflexivity | cbn [base_val r_base r_lo]; lia | cbn [base_val r_base r_hi]; lia ]
end end.
Ltac fpf_memcpy_str HS HR HW si k kj s woff :=
let H10 := fresh "H10" in let H11 := fresh "H11" in let H12 := fresh "H12" in let Hra := fresh "Hra" in
let HBs := fresh "HBs" in let Hst := fresh "Hst" in let Hu0 := fresh "Hu0" in
reg_of HS (10%bv:reg) H10; reg_of HS (11%bv:reg) H11; reg_of HS (12%bv:reg) H12; reg_of HS (1%bv:reg) Hra;
lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E ?ss _ =>
lazymatch type of HR with runs_at ?zsp _ _ =>
pose proof (runs_at_nth _ (ms_mem ms) _ si _ _ HR eq_refl) as HBs; cbn [nth_error runs_main app] in HBs;
lazymatch type of HBs with YP03.bytes_at _ ?a _ =>
assert (Hu0 : bv_unsigned (ew E 0) = zsp) by (evalE; reflexivity);
lazymatch type of H11 with _ = ?srcw =>
rewrite <- (Z_to_bv_bv_unsigned 64 srcw) in H11;
replace (bv_unsigned srcw) with a in H11 by (evalE; lia) end;
rewrite <- (Z_to_bv_bv_unsigned 64 (ew E k)) in H12;
replace (bv_unsigned (ew E k)) with (Z.of_nat (length s)) in H12 by (evalE; lia);
assert (Hst : store_ok src0segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (ew E 0) + woff)) (length s) = true)
by (apply (store_ok_of_win src0segs E _ _ _ _ _ HW); cbn [sv_denot]; rewrite !unsigned_lit_small by lia; lia);
let regs2 := fresh "regs" in let Hms := fresh "Hms" in let R10 := fresh "R10" in let Rfr := fresh "Rfr" in
destruct (src0_memcpy s _ _ _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms) H10 H11 H12
ltac:(rewrite unsigned_lit_small by lia; reflexivity)
(bytes_at_rdn src0segs _ _ _ (bytes_at_app_l _ _ _ _ HBs))
Hst
ltac:(rewrite unsigned_lit_small by lia; lia)
ltac:(rewrite unsigned_lit_small by lia; lia)
ltac:(left; rewrite !unsigned_lit_small by lia; lia))
as (regs2 & Hms & R10 & Rfr); clear Hst;
rewrite Hra in Hms; change (v_jalr (Z_to_bv 64 97648) 0) with (Z_to_bv 64 0x17d70) in Hms;
clear H10 H11 H12 Hra HBs;
sym_splice_havoc HS Hms kj (@nil (reg * sv)) junk_memcpy;
[ sym_splice_frame Rfr
| constructor
| fpf_mem_window HS
| clear Rfr R10;
lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes ?m ?d ?bs =>
lazymatch type of HS with st_ok _ ?E' _ _ =>
apply (runs_at_wbytes_below _ _ _ d bs) in HR; [| rewrite unsigned_lit_small by lia; lia];
apply (win_ok_wbytes src0segs _ _ _ _ d bs) in HW;
replace d with (Z_to_bv 64 (zsp + woff)) in * by (f_equal; lia);
assert (HK : runs_ok E' (wbytes m (Z_to_bv 64 (zsp + woff)) bs) [(SOff 0 woff, SOff 0 (-480), zsp + woff, s)]);
[ apply runs_ok_single;
[ cbn [sv_denot]; evalE; lia
| cbn [sv_denot]; evalE; lia
| apply bytes_at_wbytes_same; lia ]
| clear Hu0 ]
end end end ]
end end end end.
Ltac fpf_memcpy_lit HS HR HW HK k kj lit lem woff :=
let H10 := fresh "H10" in let H11 := fresh "H11" in let H12 := fresh "H12" in let Hra := fresh "Hra" in
let Hsrc := fresh "Hsrc" in let Hst := fresh "Hst" in let Hu0 := fresh "Hu0" in let Huk := fresh "Huk" in
let Hlen := fresh "Hlen" in
lazymatch type of HS with st_ok _ ?E ?ss ?ms => pose proof (st_ok_reg src0segs E ss ms 10 HS) as H10 end;
eval_sr_get_in H10; rewrite denot_lit_U, U_add_off_atom in H10 by (evalE; unfold M64; lia);
reg_of HS (11%bv:reg) H11; reg_of HS (12%bv:reg) H12; reg_of HS (1%bv:reg) Hra;
lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
lazymatch type of HS with st_ok _ ?E ?ss _ =>
lazymatch type of HR with runs_at ?zsp _ _ =>
assert (Huk : bv_unsigned (ew E k) = Z.of_nat (length lit) - Z.of_nat (length lit) + (bv_unsigned (ew E k))) by lia;
clear Huk;
assert (Hu0 : bv_unsigned (ew E 0) = zsp) by (evalE; reflexivity);
assert (Hlen : Z.of_nat (length lit) = Z.of_nat (length lit)) by reflexivity;
let n := eval compute in (Z.of_nat (length lit)) in
change (Z.of_nat (length lit) = Z.of_nat (length lit)) with (Z.of_nat (length lit) = n) in Hlen;
lazymatch type of H11 with _ = Z_to_bv 64 ?srcaddr =>
eassert (Hsrc : rdn src0segs (ms_mem ms) (sv_denot E (SLit srcaddr)) (word_to_nat (sv_denot E (SLit n))) = Some _)
by (rdn_of_chunk HS);
cbn [sv_denot base_val] in Hsrc;
let wn := eval compute in (Z.to_nat n) in
change (word_to_nat (Z_to_bv 64 n)) with wn in Hsrc;
match type of Hsrc with _ = Some ?cb => replace cb with lit in Hsrc by (symmetry; apply (lem E)) end;
lazymatch type of H10 with _ = ?d =>
lazymatch type of HK with runs_ok _ _ [(_, _, _, ?s)] =>
assert (Hst : store_ok src0segs (ms_mem ms) d wn = true)
by (apply (store_ok_of_win src0segs E _ _ _ _ _ HW); cbn [sv_denot]; evalE; lia);
let regs3 := fresh "regs" in let Hms := fresh "Hms" in let R10 := fresh "R10" in let Rfr := fresh "Rfr" in
destruct (src0_memcpy lit _ _ _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms) H10 H11 H12
ltac:(rewrite unsigned_lit_small by lia; exact (eq_sym Hlen))
Hsrc Hst
ltac:(rewrite Hlen; evalE; lia)
ltac:(rewrite Hlen; evalE; lia)
ltac:(right; rewrite Hlen; evalE; lia))
as (regs3 & Hms & R10 & Rfr); clear Hst Hsrc;
rewrite Hra in Hms; change (v_jalr (Z_to_bv 64 97648) 0) with (Z_to_bv 64 0x17d70) in Hms;
clear H10 H11 H12 Hra;
sym_splice_havoc HS Hms kj (@nil (reg * sv)) junk_memcpy;
[ sym_splice_frame Rfr
| constructor
| lazymatch type of HS with st_ok _ ?E0 ?ss0 _ =>
let m := eval vm_compute in (ss_mem ss0) in
lazymatch m with ?r0 :: ?r1 :: ?rest =>
eapply (st_ok_mem_wbytes_inside src0segs E0 ss0 _ _ _ [r0] r1 rest);
[ exact HS | reflexivity | reflexivity | cbn [base_val r_base r_lo]; evalE; lia
| cbn [base_val r_base r_hi]; rewrite Hlen; evalE; lia ] end end
| clear Rfr R10;
lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes ?m ?d2 ?bs =>
lazymatch type of HS with st_ok _ ?E' _ _ =>
apply (runs_at_wbytes_below _ _ _ d2 bs) in HR; [| rewrite Hlen; evalE; lia];
apply (win_ok_wbytes src0segs _ _ _ _ d2 bs) in HW;
apply runs_ok_single_inv in HK;
let HKb := fresh "HKb" in
destruct HK as (_ & _ & HKb);
apply (bytes_at_wbytes_out m (zsp + woff + Z.of_nat (length s)) bs) in HKb;
[| lia | rewrite Hlen; lia | lia | lia | left; lia ];
replace d2 with (Z_to_bv 64 (zsp + woff + Z.of_nat (length s))) in * by (f_equal; evalE; lia);
let HK' := fresh "HK'" in
pose proof (bytes_at_app _ _ _ _ HKb (bytes_at_wbytes_same m (zsp + woff + Z.of_nat (length s)) bs
ltac:(lia) ltac:(rewrite Hlen; lia))) as HK';
clear HKb;
assert (HK : runs_ok E' (wbytes m (Z_to_bv 64 (zsp + woff + Z.of_nat (length s))) bs)
[(SOff 0 woff, SOff 0 (-480), zsp + woff, s ++ bs)]);
[ apply runs_ok_single;
[ cbn [sv_denot]; evalE; lia
| rewrite length_app, Nat2Z.inj_add, Hlen; cbn [sv_denot]; evalE; lia
| exact HK' ]
| clear HK' Hu0 Hlen ]
end end end ]
end end end end end end.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma iovcnt_val'' : forall E a b,
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR a b)) (SLit 1))
= Z_to_bv 64 (if U E a =? U E b then 1 else 2).
Proof. exact iovcnt_val'. Qed.
Theorem wl0_sound : forall E ss ms model fd ch b off vb0 vl0 T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall src0segs E ss ms -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 66 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd -> fdchan fd ch model -> fd32 fd = fd ->
sv_denot E (sr_get (ss_regs ss) 12) = Z_to_bv 64 1 ->
U E (sr_get (ss_regs ss) 11) = base_val E b + off ->
iov_read1 (ss_mem ss) b off = Some (vb0, vl0) -> U E vl0 = 0 ->
base_val E b + off + 16 <= 2 ^ 47 -> U E vb0 <= 2 ^ 47 ->
(forall ms', st_ok src0segs E (resume ss (SLit 0) (ss_mem ss) (ss_facts ss)) ms' -> ms_mem ms' = ms_mem ms ->
realizes src0segs (mkCfg ms' model) T) ->
realizes src0segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd ch b off vb0 vl0 T Hh Hlz HS Hrv H17 H10 Hfdc H32 H12 H11 Hiov Hvl0 Hiok Hok0 Hk.
destruct (st_ok_ecall_shape src0segs E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
cbn [ms_mem pend_at] in Hk.
destruct (iov_read1_sound src0segs E mem _ _ _ _ _ Hmem Hiov) as [M0 L0].
assert (Ha11 : getr regs 11 = Z_to_bv 64 (base_val E b + off)).
{ rewrite (Hregs 11%bv), denot_lit_U, H11. reflexivity. }
eapply (rz_writev_empty src0segs regs _ mem (seg_rom src0segs) model fd ch (sv_denot E vb0) T Hh Hlz).
- rewrite (Hregs 17%bv), H17. reflexivity.
- exact Hfdc. - exact H32.
- rewrite (Hregs 10%bv). exact H10.
- rewrite (Hregs 12%bv). exact H12.
- apply ms_read_u64_of_rdn. rewrite Ha11. exact M0.
- apply ms_read_u64_of_rdn.
pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11, u_Z2bv by lia.
rewrite (denot_lit_U E vl0), Hvl0 in L0. exact L0.
- pose proof (U_range E (sr_get (ss_regs ss) 11)) as R. rewrite H11 in R. unfold M64 in R.
rewrite Ha11. unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- pose proof (U_range E vb0) as R0. unfold M64 in R0.
rewrite (denot_lit_U E vb0). unfold access_okb, TASK_SIZE. rewrite u_Z2bv by lia.
apply andb_true_intro; split; apply Z.leb_le; lia.
- apply Hk; [|reflexivity].
change (Z_to_bv 64 0) with (sv_denot E (SLit 0)).
apply st_ok_resume_sv; auto.
Qed.
End h.
Ltac wl_writev0 HS Hch :=
lazymatch type of HS with st_ok_ecall _ ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
lazymatch type of Hch with fdchan ?fd ?ch _ =>
let r := eval vm_compute in (sr_get (ss_regs ss) 11) in
lazymatch r with
| SOff ?b ?off =>
let io := eval vm_compute in (iov_read1 (ss_mem ss) (Some b) off) in
lazymatch io with
| Some (?vb0, ?vl0) =>
eapply (wl0_sound E ss ms model fd ch (Some b) off vb0 vl0 _ ltac:(assumption) ltac:(assumption) HS);
[ reflexivity
| vm_compute; reflexivity
| eval_sr_get; rewrite denot_lit_U, U_SLit; reflexivity
| exact Hch
| reflexivity
| eval_sr_get; first [ rewrite denot_lit_U, U_SLit; reflexivity
| rewrite iovcnt_val, Z.eqb_refl; reflexivity
| rewrite iovcnt_val'', Z.eqb_refl; reflexivity
| rewrite denot_add0, iovcnt_val'', Z.eqb_refl; reflexivity   ]
| eval_sr_get; cbn [base_val]; apply U_off; evalE; unfold M64; lia
| vm_compute; reflexivity
| rewrite ?U_SLit; reflexivity
|   cbn [base_val]; first [ solve [evalE; unfold M64 in *; lia] | idtac ]
|   first [ solve [rewrite U_SLit, zcanon_id by (unfold M64; lia); lia] | solve [rewrite U_off by (evalE; unfold M64; lia); evalE; lia] | idtac ]
| clear HS;
let ms' := fresh "ms" in let Hmm := fresh "Hmm" in
intros ms' HS Hmm;
repeat match goal with
| HR : runs_at _ (ms_mem ms) _ |- _ => rewrite <- Hmm in HR
| HK : runs_ok _ (ms_mem ms) _ |- _ => rewrite <- Hmm in HK
| HW : win_ok _ _ (ms_mem ms) _ _ |- _ => rewrite <- Hmm in HW
end;
clear Hmm; try clear ms; sym_norm HS ]
| _ => fail "wl_writev0: iovec not found"
end
| _ => fail "wl_writev0: a1 is not an offset"
end
end end end.
