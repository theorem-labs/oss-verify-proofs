(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK16 YK0o YK11 YK0j YK0i YK14 YK1c YK1i YK1d YK0v YK15.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition rd_adm (s : InputStream) (cnt : word) (bs : list byte) : Prop :=
(bs = [] /\ s = IEof)
\/ ((1 <= Z.of_nat (length bs))%Z
/\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z
/\ fst (stream_take s (length bs)) = bs).
Definition RdIdx (s : InputStream) (cnt : word) : Type :=
{ bs : list byte | rd_adm s cnt bs }.



Definition rd_next (ms : machine_state) (model : Model) (buf : word)
(bs : list byte) : config :=
match bs with
| [] => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
| _ :: _ =>
mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
end.

Definition stream_firstn (s : InputStream) (k : nat) : list byte :=
fst (stream_take s k).




Section d.
Variable segs : list Segment.

Definition t_read_ch (rch : word) (s : InputStream) (cnt : word)
(K : list byte -> TSet) : TSet :=
t_alt (fun i : RdIdx s cnt =>
t_emit (map (ReadEv rch) (proj1_sig i)) (K (proj1_sig i))).
Definition t_read0 (s : InputStream) (cnt : word) (K : list byte -> TSet) : TSet :=
t_read_ch (Z_to_bv 64 0) s cnt K.

Lemma t_emit_app : forall a b T, t_eq (t_emit a (t_emit b T)) (t_emit (a ++ b) T).
Proof.
intros a b T tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_mono. exact Hp.
+ right. exists tr''. rewrite app_assoc. split; [reflexivity | exact HT].
- intros [Hp | (tr' & -> & HT)].
+ apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
* left. exact Hp.
* right. exists tr'. split; [reflexivity | left; exact Hp].
+ right. exists (b ++ tr').
split; [symmetry; apply app_assoc
| right; exists tr'; split; [reflexivity | exact HT]].
Qed.

Section f.
Variable cap : nat.
Hypothesis Hcap : (Z.of_nat cap < 2 ^ 64)%Z.
Hypothesis Hcap_modeled : (Z.of_nat cap <= rw_bytes_max)%Z.
Variable LH : list byte -> config -> Prop.
Variable Tfin : list byte -> TSet.
Definition dcnt (acc : list byte) : word := Z_to_bv 64 (Z.of_nat (cap - length acc)).



Fixpoint t_drain_ch (rch : word) (n : nat) (s : InputStream) (acc : list byte)
: TSet :=
match n with
| O => Tfin acc
| S n' =>
if (cap <=? length acc)%nat then Tfin acc
else t_read_ch rch s (dcnt acc)
(fun bs =>
match bs with
| [] => Tfin acc
| _ :: _ =>
t_drain_ch rch n' (snd (stream_take s (length bs))) (acc ++ bs)
end)
end.
Definition t_drain (n : nat) (s : InputStream) (acc : list byte) : TSet :=
t_drain_ch (Z_to_bv 64 0) n s acc.
Hypothesis Htfin_ne : forall acc, Tfin acc [].




Hypothesis Hfull : forall acc c,
LH acc c -> (cap <= length acc)%nat -> realizes segs c (Tfin acc).
Hypothesis Hread : forall acc c,
LH acc c -> (length acc < cap)%nat ->
exists ms1 buf x8 w,
m_halted (cfg_model c) = None /\
m_vm_lazy (cfg_model c) = [] /\
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
msteps segs (cfg_ms c) ms1 /\
ms_svc_pending ms1 = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms1 0 = Z_to_bv 64 0 /\
ms_gpr ms1 1 = buf /\
ms_gpr ms1 2 = dcnt acc /\
read_bytes_map (ms_writable_byte segs ms1) buf (dcnt acc) = Some w /\
access_okb buf (bv_unsigned (dcnt acc)) = true /\
realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) /\
(forall bs, rd_adm (m_stdin (cfg_model c)) (dcnt acc) bs -> bs <> [] ->
LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)).





End f.
End d.
